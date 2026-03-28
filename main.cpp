#include <zstd.h>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cstring>
#include <cstddef>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <utility>

using Byte = uint8_t;

static constexpr uint32_t VERSION = 3;
static constexpr size_t HEADER_RS_PARITY = 16;       // fixed, so headers can always be decoded
static constexpr size_t DEFAULT_PAYLOAD_PARITY = 16; // user-adjustable with -p
static constexpr size_t RS_CODE_BYTES = 255;
static constexpr int GF_PRIM = 0x11d;

#pragma pack(push, 1)
struct FileHeader
{
    char magic[8]; // "PZECOMP3"
    uint32_t version;
    uint32_t blockSize;
    uint32_t payloadParity;
    uint32_t interleaveDepth;
    uint64_t originalSize;
    uint64_t blockCount;
    uint64_t reserved0; // low 32 bits = CRC32 over header with this field zeroed
}; // 48 bytes

struct BlockHeader
{
    uint32_t uncompressedSize;
    uint32_t compressedSize;
    uint32_t encodedSize;
    uint32_t crc32;     // CRC32 of compressed payload after RS decode
    uint64_t reserved0; // low 32 bits = CRC32 over block header with this field zeroed
}; // 24 bytes
#pragma pack(pop)

static_assert(sizeof(FileHeader) == 48, "FileHeader size must be 48 bytes");
static_assert(sizeof(BlockHeader) == 24, "BlockHeader size must be 24 bytes");

static void die(const std::string &msg)
{
    throw std::runtime_error(msg);
}

static bool isPowerOfTwo(size_t x)
{
    return x && ((x & (x - 1)) == 0);
}

static size_t bitCount8(Byte x)
{
    size_t c = 0;
    while (x)
    {
        x &= static_cast<Byte>(x - 1);
        ++c;
    }
    return c;
}

static uint32_t crc32(const std::vector<Byte> &data)
{
    static uint32_t table[256];
    static bool init = false;

    if (!init)
    {
        for (uint32_t i = 0; i < 256; ++i)
        {
            uint32_t c = i;
            for (int k = 0; k < 8; ++k)
            {
                c = (c & 1) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1);
            }
            table[i] = c;
        }
        init = true;
    }

    uint32_t c = 0xFFFFFFFFu;
    for (Byte b : data)
    {
        c = table[(c ^ b) & 0xFF] ^ (c >> 8);
    }
    return c ^ 0xFFFFFFFFu;
}

struct GF256
{
    std::array<uint8_t, 512> exp{};
    std::array<uint8_t, 256> log{};

    GF256()
    {
        int tmp = 1;
        for (int i = 0; i < 255; ++i)
        {
            exp[i] = static_cast<uint8_t>(tmp);
            log[static_cast<uint8_t>(tmp)] = static_cast<uint8_t>(i);
            tmp <<= 1;
            if (tmp & 0x100)
                tmp ^= GF_PRIM;
        }
        for (int i = 255; i < 512; ++i)
        {
            exp[i] = exp[i - 255];
        }
        log[0] = 0;
    }

    uint8_t add(uint8_t a, uint8_t b) const { return a ^ b; }

    uint8_t mul(uint8_t a, uint8_t b) const
    {
        if (a == 0 || b == 0)
            return 0;
        return exp[static_cast<size_t>(log[a]) + static_cast<size_t>(log[b])];
    }

    uint8_t div(uint8_t a, uint8_t b) const
    {
        if (a == 0)
            return 0;
        if (b == 0)
            die("GF division by zero");
        int diff = int(log[a]) - int(log[b]);
        if (diff < 0)
            diff += 255;
        return exp[static_cast<size_t>(diff)];
    }

    uint8_t inv(uint8_t a) const
    {
        if (a == 0)
            die("GF inverse of zero");
        return exp[255 - log[a]];
    }

    uint8_t pow(uint8_t a, int p) const
    {
        if (p == 0)
            return 1;
        if (a == 0)
            return 0;
        if (p < 0)
            return pow(inv(a), -p);
        return exp[(static_cast<int>(log[a]) * p) % 255];
    }
};

static const GF256 GF{};

static std::vector<uint8_t> polyAdd(const std::vector<uint8_t> &a, const std::vector<uint8_t> &b)
{
    if (a.empty())
        return b;
    if (b.empty())
        return a;
    const std::vector<uint8_t> *big = &a;
    const std::vector<uint8_t> *small = &b;
    if (b.size() > a.size())
        std::swap(big, small);
    std::vector<uint8_t> out = *big;
    size_t off = big->size() - small->size();
    for (size_t i = 0; i < small->size(); ++i)
        out[i + off] ^= (*small)[i];
    while (!out.empty() && out.front() == 0)
        out.erase(out.begin());
    if (out.empty())
        out.push_back(0);
    return out;
}

static std::vector<uint8_t> polyScale(const std::vector<uint8_t> &p, uint8_t x)
{
    if (x == 0)
        return {0};
    std::vector<uint8_t> out(p.size());
    for (size_t i = 0; i < p.size(); ++i)
        out[i] = GF.mul(p[i], x);
    return out;
}

static std::vector<uint8_t> polyMul(const std::vector<uint8_t> &a, const std::vector<uint8_t> &b)
{
    if (a.empty() || b.empty())
        return {0};
    std::vector<uint8_t> out(a.size() + b.size() - 1, 0);
    for (size_t i = 0; i < a.size(); ++i)
    {
        if (a[i] == 0)
            continue; // Fast bypass
        for (size_t j = 0; j < b.size(); ++j)
        {
            out[i + j] ^= GF.mul(a[i], b[j]);
        }
    }
    while (!out.empty() && out.front() == 0)
        out.erase(out.begin());
    if (out.empty())
        out.push_back(0);
    return out;
}

static uint8_t polyEval(const std::vector<uint8_t> &p, uint8_t x)
{
    uint8_t y = p.front();
    for (size_t i = 1; i < p.size(); ++i)
    {
        y = GF.mul(y, x) ^ p[i];
    }
    return y;
}

class ReedSolomon256
{
public:
    explicit ReedSolomon256(size_t parityBytes = DEFAULT_PAYLOAD_PARITY)
        : nsym_(parityBytes), generator_(makeGenerator(parityBytes))
    {
        if (nsym_ == 0 || nsym_ >= RS_CODE_BYTES)
            die("Invalid RS parity size");
        if (dataBytes() == 0)
            die("Invalid RS data size");
    }

    size_t parityBytes() const { return nsym_; }
    size_t dataBytes() const { return RS_CODE_BYTES - nsym_; }
    size_t codeBytes() const { return RS_CODE_BYTES; }

    std::vector<Byte> encodeFull(const std::vector<Byte> &msg) const
    {
        if (msg.size() != dataBytes())
        {
            die("RS encodeFull: message size must be exactly dataBytes()");
        }

        std::vector<Byte> out = msg;
        out.resize(RS_CODE_BYTES, 0);

        for (size_t i = 0; i < dataBytes(); ++i)
        {
            Byte coef = out[i];
            if (coef == 0)
                continue;
            for (size_t j = 1; j < generator_.size(); ++j)
            {
                out[i + j] ^= GF.mul(generator_[j], coef);
            }
        }

        std::vector<Byte> code;
        code.reserve(RS_CODE_BYTES);
        code.insert(code.end(), msg.begin(), msg.end());
        code.insert(code.end(), out.end() - nsym_, out.end());
        return code;
    }

    std::vector<Byte> decodeFull(const std::vector<Byte> &code,
                                 size_t *correctedSymbols = nullptr,
                                 size_t *correctedBits = nullptr) const
    {
        if (code.size() != RS_CODE_BYTES)
        {
            die("RS decodeFull: codeword size must be 255 bytes");
        }

        if (correctedSymbols)
            *correctedSymbols = 0;
        if (correctedBits)
            *correctedBits = 0;

        std::vector<Byte> msg = code;
        auto synd = calcSyndromes(msg);

        bool hasError = false;
        for (Byte b : synd)
        {
            if (b != 0)
            {
                hasError = true;
                break;
            }
        }

        if (!hasError)
        {
            return std::vector<Byte>(msg.begin(), msg.begin() + dataBytes());
        }

        auto errLoc = findErrorLocator(synd);
        auto errPos = findErrorPositions(errLoc, msg.size());
        if (errPos.empty())
            die("RS: unable to locate errors");

        auto magnitudes = solveMagnitudes(synd, errPos, msg.size());
        if (magnitudes.size() != errPos.size())
            die("RS: unable to solve error magnitudes");

        size_t corrected = 0;
        size_t bitFixes = 0;
        for (size_t i = 0; i < errPos.size(); ++i)
        {
            Byte mag = magnitudes[i];
            if (mag != 0)
            {
                Byte before = msg[errPos[i]];
                Byte after = static_cast<Byte>(before ^ mag);
                msg[errPos[i]] = after;
                ++corrected;
                bitFixes += bitCount8(static_cast<Byte>(before ^ after));
            }
        }

        auto synd2 = calcSyndromes(msg);
        for (Byte b : synd2)
        {
            if (b != 0)
            {
                die("RS: uncorrectable corruption (too many byte errors or bad miscorrection)");
            }
        }

        if (correctedSymbols)
            *correctedSymbols = corrected;
        if (correctedBits)
            *correctedBits = bitFixes;

        return std::vector<Byte>(msg.begin(), msg.begin() + dataBytes());
    }

    std::vector<Byte> encodeShort(const std::vector<Byte> &data) const
    {
        if (data.size() > dataBytes())
            die("RS encodeShort: data too large");
        size_t leadingZeros = dataBytes() - data.size();

        std::vector<Byte> msg(dataBytes(), 0);
        std::copy(data.begin(), data.end(), msg.begin() + leadingZeros);

        auto full = encodeFull(msg);
        return std::vector<Byte>(full.begin() + leadingZeros, full.end());
    }

    std::vector<Byte> decodeShort(const std::vector<Byte> &shortCode,
                                  size_t dataSize,
                                  size_t *correctedSymbols = nullptr,
                                  size_t *correctedBits = nullptr) const
    {
        if (dataSize > dataBytes())
            die("RS decodeShort: dataSize too large");
        size_t leadingZeros = dataBytes() - dataSize;
        size_t expectedShort = dataSize + nsym_;
        if (shortCode.size() != expectedShort)
        {
            die("RS decodeShort: short code size mismatch");
        }

        std::vector<Byte> full(RS_CODE_BYTES, 0);
        std::copy(shortCode.begin(), shortCode.end(), full.begin() + leadingZeros);

        auto decoded = decodeFull(full, correctedSymbols, correctedBits);
        return std::vector<Byte>(decoded.begin() + leadingZeros, decoded.begin() + leadingZeros + dataSize);
    }

private:
    size_t nsym_;
    std::vector<uint8_t> generator_;

    std::vector<uint8_t> makeGenerator(size_t nsym) const
    {
        std::vector<uint8_t> g{1};
        for (size_t i = 0; i < nsym; ++i)
        {
            std::vector<uint8_t> term{1, GF.exp[i]};
            g = polyMul(g, term);
        }
        return g;
    }

    std::vector<Byte> calcSyndromes(const std::vector<Byte> &code) const
    {
        std::vector<Byte> synd(nsym_, 0);
        for (size_t i = 0; i < nsym_; ++i)
        {
            synd[i] = polyEval(code, GF.exp[i]);
        }
        return synd;
    }

    std::vector<uint8_t> findErrorLocator(const std::vector<Byte> &synd) const
    {
        std::vector<uint8_t> errLoc{1};
        std::vector<uint8_t> oldLoc{1};
        errLoc.reserve(nsym_ + 1);
        oldLoc.reserve(nsym_ + 1);

        for (size_t i = 0; i < nsym_; ++i)
        {
            uint8_t delta = synd[i];
            for (size_t j = 1; j < errLoc.size(); ++j)
            {
                delta ^= GF.mul(errLoc[errLoc.size() - 1 - j], synd[i - j]);
            }

            oldLoc.push_back(0);
            if (delta != 0)
            {
                if (oldLoc.size() > errLoc.size())
                {
                    auto newLoc = polyScale(oldLoc, delta);
                    oldLoc = polyScale(errLoc, GF.inv(delta));
                    errLoc = std::move(newLoc);
                }
                errLoc = polyAdd(errLoc, polyScale(oldLoc, delta));
            }
        }

        while (!errLoc.empty() && errLoc.front() == 0)
            errLoc.erase(errLoc.begin());
        if (errLoc.empty())
            errLoc.push_back(0);
        return errLoc;
    }

    std::vector<size_t> findErrorPositions(const std::vector<uint8_t> &errLoc, size_t codeLen) const
    {
        const size_t errs = errLoc.size() > 0 ? errLoc.size() - 1 : 0;
        std::vector<size_t> positions;
        positions.reserve(errs);

        for (size_t i = 0; i < RS_CODE_BYTES; ++i)
        {
            if (polyEval(errLoc, GF.exp[i]) == 0)
            {
                size_t pos = (i + RS_CODE_BYTES - 1) % RS_CODE_BYTES;
                if (pos < codeLen)
                    positions.push_back(pos);
            }
        }

        std::sort(positions.begin(), positions.end());
        positions.erase(std::unique(positions.begin(), positions.end()), positions.end());
        if (positions.size() != errs)
            return {};
        return positions;
    }

    // OPTIMIZATION: Flat 1D Array for Linear System Solver (replaces slow vector<vector>)
    static std::vector<uint8_t> solveLinearSystem(std::vector<uint8_t> A, std::vector<uint8_t> b)
    {
        const size_t n = b.size();
        for (size_t col = 0; col < n; ++col)
        {
            size_t piv = col;
            while (piv < n && A[piv * n + col] == 0)
                ++piv;
            if (piv == n)
                return {};
            if (piv != col)
            {
                for (size_t j = col; j < n; ++j)
                {
                    std::swap(A[piv * n + j], A[col * n + j]);
                }
                std::swap(b[piv], b[col]);
            }

            uint8_t invPivot = GF.inv(A[col * n + col]);
            for (size_t j = col; j < n; ++j)
                A[col * n + j] = GF.mul(A[col * n + j], invPivot);
            b[col] = GF.mul(b[col], invPivot);

            for (size_t row = 0; row < n; ++row)
            {
                if (row == col || A[row * n + col] == 0)
                    continue;
                uint8_t factor = A[row * n + col];
                for (size_t j = col; j < n; ++j)
                {
                    A[row * n + j] ^= GF.mul(factor, A[col * n + j]);
                }
                b[row] ^= GF.mul(factor, b[col]);
            }
        }
        return b;
    }

    std::vector<uint8_t> solveMagnitudes(const std::vector<Byte> &synd, const std::vector<size_t> &errPos, size_t codeLen) const
    {
        const size_t t = errPos.size();
        if (t == 0)
            return {};
        if (t > nsym_ / 2)
            return {};

        std::vector<uint8_t> X;
        X.reserve(t);
        for (size_t p : errPos)
        {
            size_t exp = (codeLen - 1) - p;
            X.push_back(GF.exp[exp % 255]);
        }

        // Initialize 1D flattened matrix
        std::vector<uint8_t> A(t * t, 0);
        std::vector<uint8_t> b(t, 0);
        for (size_t row = 0; row < t; ++row)
        {
            b[row] = synd[row];
            for (size_t col = 0; col < t; ++col)
            {
                A[row * t + col] = GF.pow(X[col], static_cast<int>(row));
            }
        }

        return solveLinearSystem(std::move(A), std::move(b));
    }
};

static std::vector<Byte> zstdCompress(const std::vector<Byte> &data, int level)
{
    size_t bound = ZSTD_compressBound(data.size());
    std::vector<Byte> out(bound);

    size_t sz = ZSTD_compress(out.data(), out.size(), data.data(), data.size(), level);
    if (ZSTD_isError(sz))
        die(std::string("ZSTD_compress failed: ") + ZSTD_getErrorName(sz));

    out.resize(sz);
    return out;
}

static std::vector<Byte> zstdDecompress(const std::vector<Byte> &data, size_t outSize)
{
    std::vector<Byte> out(outSize);

    size_t sz = ZSTD_decompress(out.data(), out.size(), data.data(), data.size());
    if (ZSTD_isError(sz))
        die(std::string("ZSTD_decompress failed: ") + ZSTD_getErrorName(sz));
    if (sz != outSize)
        die("ZSTD decompressed size mismatch");

    return out;
}

static uint32_t headerCrc32File(const FileHeader &fh)
{
    std::vector<Byte> raw(sizeof(FileHeader));
    std::memcpy(raw.data(), &fh, sizeof(FileHeader));
    std::fill(raw.begin() + offsetof(FileHeader, reserved0), raw.begin() + offsetof(FileHeader, reserved0) + sizeof(uint64_t), 0);
    return crc32(raw);
}

static uint32_t headerCrc32Block(const BlockHeader &bh)
{
    std::vector<Byte> raw(sizeof(BlockHeader));
    std::memcpy(raw.data(), &bh, sizeof(BlockHeader));
    std::fill(raw.begin() + offsetof(BlockHeader, reserved0), raw.begin() + offsetof(BlockHeader, reserved0) + sizeof(uint64_t), 0);
    return crc32(raw);
}

static std::vector<Byte> interleaveCodewords(const std::vector<Byte> &encoded, size_t codewordSize, size_t depth)
{
    if (depth <= 1)
        return encoded;
    if (encoded.size() % codewordSize != 0)
        die("interleaveCodewords: encoded size is not a multiple of codeword size");

    size_t codewordCount = encoded.size() / codewordSize;
    std::vector<Byte> out;
    out.reserve(encoded.size());

    for (size_t base = 0; base < codewordCount; base += depth)
    {
        size_t group = std::min(depth, codewordCount - base);
        for (size_t byteIndex = 0; byteIndex < codewordSize; ++byteIndex)
        {
            for (size_t cw = 0; cw < group; ++cw)
            {
                out.push_back(encoded[(base + cw) * codewordSize + byteIndex]);
            }
        }
    }

    return out;
}

static std::vector<Byte> deinterleaveCodewords(const std::vector<Byte> &interleaved, size_t codewordSize, size_t depth)
{
    if (depth <= 1)
        return interleaved;
    if (interleaved.size() % codewordSize != 0)
        die("deinterleaveCodewords: encoded size is not a multiple of codeword size");

    size_t codewordCount = interleaved.size() / codewordSize;
    std::vector<Byte> out(interleaved.size(), 0);
    size_t idx = 0;

    for (size_t base = 0; base < codewordCount; base += depth)
    {
        size_t group = std::min(depth, codewordCount - base);
        for (size_t byteIndex = 0; byteIndex < codewordSize; ++byteIndex)
        {
            for (size_t cw = 0; cw < group; ++cw)
            {
                out[(base + cw) * codewordSize + byteIndex] = interleaved[idx++];
            }
        }
    }

    if (idx != interleaved.size())
        die("deinterleaveCodewords: internal size mismatch");

    return out;
}

static void compressFile(const std::string &inPath,
                         const std::string &outPath,
                         uint32_t blockSize,
                         int level,
                         size_t payloadParity,
                         size_t interleaveDepth,
                         bool verbose)
{
    ReedSolomon256 headerRs(HEADER_RS_PARITY);
    ReedSolomon256 payloadRs(payloadParity);

    std::ifstream in(inPath, std::ios::binary);
    if (!in)
        die("Cannot open input file: " + inPath);

    in.seekg(0, std::ios::end);
    std::streampos endPos = in.tellg();
    if (endPos < 0)
        die("Failed to determine input file size");
    uint64_t originalSize = static_cast<uint64_t>(endPos);
    in.seekg(0, std::ios::beg);

    uint64_t blockCount = (originalSize + blockSize - 1) / blockSize;

    std::ofstream out(outPath, std::ios::binary);
    if (!out)
        die("Cannot open output file: " + outPath);

    FileHeader fh{};
    std::memcpy(fh.magic, "PZECOMP3", 8);
    fh.version = VERSION;
    fh.blockSize = blockSize;
    fh.payloadParity = static_cast<uint32_t>(payloadParity);
    fh.interleaveDepth = static_cast<uint32_t>(interleaveDepth);
    fh.originalSize = originalSize;
    fh.blockCount = blockCount;
    fh.reserved0 = 0;
    fh.reserved0 = headerCrc32File(fh);

    std::vector<Byte> headerRaw(sizeof(FileHeader));
    std::memcpy(headerRaw.data(), &fh, sizeof(FileHeader));
    auto headerEnc = headerRs.encodeShort(headerRaw);
    out.write(reinterpret_cast<const char *>(headerEnc.data()), static_cast<std::streamsize>(headerEnc.size()));
    if (!out)
        die("Failed writing file header");

    std::vector<Byte> inBuf(blockSize);
    uint64_t totalCompressed = 0;
    uint64_t totalEncoded = headerEnc.size();

    if (verbose)
    {
        std::cout << "Compress settings: blockSize=" << blockSize
                  << ", payloadParity=" << payloadParity
                  << ", interleaveDepth=" << interleaveDepth
                  << ", zstdLevel=" << level << "\n";
    }

    for (uint64_t blockIndex = 0; blockIndex < blockCount; ++blockIndex)
    {
        in.read(reinterpret_cast<char *>(inBuf.data()), blockSize);
        std::streamsize got = in.gcount();
        if (got < 0)
            got = 0;

        std::vector<Byte> plain(inBuf.begin(), inBuf.begin() + got);
        auto compressed = zstdCompress(plain, level);
        uint32_t payloadCrc = crc32(compressed);

        size_t chunks = (compressed.size() + payloadRs.dataBytes() - 1) / payloadRs.dataBytes();
        std::vector<Byte> encoded;
        encoded.reserve(chunks * payloadRs.codeBytes());
        for (size_t i = 0; i < compressed.size(); i += payloadRs.dataBytes())
        {
            std::vector<Byte> msg(payloadRs.dataBytes(), 0);
            size_t chunk = std::min(payloadRs.dataBytes(), compressed.size() - i);
            std::copy_n(compressed.begin() + i, chunk, msg.begin());
            auto code = payloadRs.encodeFull(msg);
            encoded.insert(encoded.end(), code.begin(), code.end());
        }

        auto encodedInterleaved = interleaveCodewords(encoded, payloadRs.codeBytes(), interleaveDepth);

        BlockHeader bh{};
        bh.uncompressedSize = static_cast<uint32_t>(plain.size());
        bh.compressedSize = static_cast<uint32_t>(compressed.size());
        bh.encodedSize = static_cast<uint32_t>(encodedInterleaved.size());
        bh.crc32 = payloadCrc;
        bh.reserved0 = 0;
        bh.reserved0 = headerCrc32Block(bh);

        std::vector<Byte> bhRaw(sizeof(BlockHeader));
        std::memcpy(bhRaw.data(), &bh, sizeof(BlockHeader));
        auto bhEnc = headerRs.encodeShort(bhRaw);

        out.write(reinterpret_cast<const char *>(bhEnc.data()), static_cast<std::streamsize>(bhEnc.size()));
        out.write(reinterpret_cast<const char *>(encodedInterleaved.data()), static_cast<std::streamsize>(encodedInterleaved.size()));
        if (!out)
            die("Failed writing block data");

        totalCompressed += compressed.size();
        totalEncoded += bhEnc.size() + encodedInterleaved.size();

        if (verbose)
        {
            std::cout << "Block " << (blockIndex + 1) << "/" << blockCount
                      << " plain=" << plain.size()
                      << " compressed=" << compressed.size()
                      << " payloadEncoded=" << encodedInterleaved.size()
                      << "\n";
        }
    }

    std::cout << "Done. Original=" << originalSize
              << " bytes, compressed payload=" << totalCompressed
              << " bytes, output=" << totalEncoded << " bytes\n";
}

static void decompressFile(const std::string &inPath, const std::string &outPath, bool verbose)
{
    ReedSolomon256 headerRs(HEADER_RS_PARITY);

    std::ifstream in(inPath, std::ios::binary);
    if (!in)
        die("Cannot open input file: " + inPath);

    std::ofstream out(outPath, std::ios::binary);
    if (!out)
        die("Cannot open output file: " + outPath);

    auto headerEncSize = sizeof(FileHeader) + headerRs.parityBytes();
    std::vector<Byte> headerEnc(headerEncSize);
    in.read(reinterpret_cast<char *>(headerEnc.data()), static_cast<std::streamsize>(headerEncSize));
    if (!in)
        die("Failed reading file header");

    size_t headerSymbols = 0;
    size_t headerBits = 0;
    auto headerRaw = headerRs.decodeShort(headerEnc, sizeof(FileHeader), &headerSymbols, &headerBits);
    FileHeader fh{};
    std::memcpy(&fh, headerRaw.data(), sizeof(FileHeader));

    if (std::memcmp(fh.magic, "PZECOMP3", 8) != 0)
        die("Bad magic / not a PZECOMP file");
    if (fh.version != VERSION)
        die("Unsupported version");
    if (fh.payloadParity == 0 || fh.payloadParity >= RS_CODE_BYTES)
        die("Invalid payload parity in header");
    if (fh.interleaveDepth == 0)
        die("Invalid interleave depth in header");

    uint64_t storedFileCrc = fh.reserved0 & 0xffffffffULL;
    fh.reserved0 = 0;
    if (headerCrc32File(fh) != static_cast<uint32_t>(storedFileCrc))
    {
        die("File header CRC mismatch");
    }

    ReedSolomon256 payloadRs(static_cast<size_t>(fh.payloadParity));

    if (verbose)
    {
        std::cout << "Decode settings: blockSize=" << fh.blockSize
                  << ", payloadParity=" << fh.payloadParity
                  << ", interleaveDepth=" << fh.interleaveDepth
                  << "\n";
        std::cout << "Header RS fixed parity=" << HEADER_RS_PARITY
                  << " correctedSymbols=" << headerSymbols
                  << " correctedBits=" << headerBits << "\n";
    }

    uint64_t written = 0;

    for (uint64_t blockIndex = 0; blockIndex < fh.blockCount; ++blockIndex)
    {
        auto bhEncSize = sizeof(BlockHeader) + headerRs.parityBytes();
        std::vector<Byte> bhEnc(bhEncSize);
        in.read(reinterpret_cast<char *>(bhEnc.data()), static_cast<std::streamsize>(bhEncSize));
        if (!in)
            die("Failed reading block header");

        size_t bhCorrectedSymbols = 0;
        size_t bhCorrectedBits = 0;
        auto bhRaw = headerRs.decodeShort(bhEnc, sizeof(BlockHeader), &bhCorrectedSymbols, &bhCorrectedBits);
        BlockHeader bh{};
        std::memcpy(&bh, bhRaw.data(), sizeof(BlockHeader));

        uint64_t storedBlockCrc = bh.reserved0 & 0xffffffffULL;
        bh.reserved0 = 0;
        if (headerCrc32Block(bh) != static_cast<uint32_t>(storedBlockCrc))
        {
            die("Block header CRC mismatch");
        }

        if (bh.compressedSize == 0 && bh.encodedSize != 0)
        {
            die("Invalid block header: compressedSize=0 but encodedSize!=0");
        }

        size_t expectedEncoded = ((bh.compressedSize + payloadRs.dataBytes() - 1) / payloadRs.dataBytes()) * payloadRs.codeBytes();
        if (expectedEncoded != bh.encodedSize)
        {
            die("Invalid block header: encodedSize does not match compressedSize");
        }

        std::vector<Byte> payloadInterleaved(bh.encodedSize);
        in.read(reinterpret_cast<char *>(payloadInterleaved.data()), static_cast<std::streamsize>(bh.encodedSize));
        if (!in)
            die("Failed reading encoded block payload");

        auto payloadEncoded = deinterleaveCodewords(payloadInterleaved, payloadRs.codeBytes(), static_cast<size_t>(fh.interleaveDepth));

        std::vector<Byte> compressed;
        compressed.reserve(bh.compressedSize);
        size_t payloadCorrectedSymbols = 0;
        size_t payloadCorrectedBits = 0;

        for (size_t i = 0; i < payloadEncoded.size(); i += payloadRs.codeBytes())
        {
            std::vector<Byte> code(payloadEncoded.begin() + i, payloadEncoded.begin() + i + payloadRs.codeBytes());
            size_t correctedHereSymbols = 0;
            size_t correctedHereBits = 0;
            auto msg = payloadRs.decodeFull(code, &correctedHereSymbols, &correctedHereBits);
            payloadCorrectedSymbols += correctedHereSymbols;
            payloadCorrectedBits += correctedHereBits;
            compressed.insert(compressed.end(), msg.begin(), msg.end());
        }
        compressed.resize(bh.compressedSize);

        if (crc32(compressed) != bh.crc32)
        {
            die("CRC mismatch after RS decode: payload still corrupted");
        }

        auto plain = zstdDecompress(compressed, bh.uncompressedSize);
        out.write(reinterpret_cast<const char *>(plain.data()), static_cast<std::streamsize>(plain.size()));
        if (!out)
            die("Failed writing decompressed data");

        written += plain.size();

        if (verbose)
        {
            std::cout << "Block " << (blockIndex + 1) << "/" << fh.blockCount
                      << " restored=" << plain.size() << " bytes"
                      << " headerFixes=" << bhCorrectedSymbols << " symbols / " << bhCorrectedBits << " bits"
                      << " payloadFixes=" << payloadCorrectedSymbols << " symbols / " << payloadCorrectedBits << " bits"
                      << "\n";
        }
    }

    if (written != fh.originalSize)
    {
        std::cerr << "Warning: restored size " << written
                  << " differs from header " << fh.originalSize << "\n";
    }

    std::cout << "Done. Restored=" << written << " bytes\n";
}

static void usage(const char *argv0)
{
    std::cerr << "Usage:\n"
              << "  " << argv0 << " c <input> <output> [-l level] [-b blockSize] [-p parity] [-i interleave] [-v]\n"
              << "  " << argv0 << " d <input> <output> [-v]\n";
}

static void validateSettings(uint32_t blockSize, int level, size_t payloadParity, size_t interleaveDepth)
{
    if (blockSize == 0)
        die("Block size must be > 0");
    if (payloadParity == 0 || payloadParity >= RS_CODE_BYTES)
        die("Payload parity must be between 1 and 254");
    if (interleaveDepth == 0)
        die("Interleave depth must be >= 1");
    if (level < ZSTD_minCLevel() || level > ZSTD_maxCLevel())
    {
        die("Zstd level is out of range for this build");
    }
}

int main(int argc, char **argv)
{
    try
    {
        if (argc < 4)
        {
            usage(argv[0]);
            return 1;
        }

        std::string mode = argv[1];
        std::string inPath = argv[2];
        std::string outPath = argv[3];
        int level = 3;
        uint32_t blockSize = 1u << 20; // 1 MiB
        size_t payloadParity = DEFAULT_PAYLOAD_PARITY;
        size_t interleaveDepth = 1;
        bool verbose = false;

        for (int i = 4; i < argc; ++i)
        {
            std::string arg = argv[i];
            if (arg == "-v")
            {
                verbose = true;
            }
            else if (arg == "-l" && i + 1 < argc)
            {
                level = std::stoi(argv[++i]);
            }
            else if (arg == "-b" && i + 1 < argc)
            {
                blockSize = static_cast<uint32_t>(std::stoul(argv[++i]));
            }
            else if (arg == "-p" && i + 1 < argc)
            {
                payloadParity = static_cast<size_t>(std::stoul(argv[++i]));
            }
            else if (arg == "-i" && i + 1 < argc)
            {
                interleaveDepth = static_cast<size_t>(std::stoul(argv[++i]));
            }
            else
            {
                usage(argv[0]);
                return 1;
            }
        }

        validateSettings(blockSize, level, payloadParity, interleaveDepth);

        if (mode == "c")
        {
            compressFile(inPath, outPath, blockSize, level, payloadParity, interleaveDepth, verbose);
        }
        else if (mode == "d")
        {
            decompressFile(inPath, outPath, verbose);
        }
        else
        {
            usage(argv[0]);
            return 1;
        }

        return 0;
    }
    catch (const std::exception &e)
    {
        std::cerr << "Error: " << e.what() << "\n";
        return 2;
    }
}