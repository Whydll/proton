# ProtonByte

[English](#english) | [Türkçe](#türkçe)

## Türkçe

Uzay ortamında veri sıkıştırma ve hata düzeltme.

Bitflip aracı ile radyasyon kaynaklı bit hatalarını test edebilirsiniz.

### Derleme

#### protonbyte:

```
g++ -std=c++20 -O2 main.cpp -lzstd -o protonbyte
```

#### bitflip:

```
g++ -std=c++20 -O2 bitflip.cpp -o bitflip
```

### Kullanım

#### Maksimum güvenlik (daha az sıkıştırma, daha fazla CPU eforu, daha fazla tamir olasılığı)

```
./protonbyte c dosya.ext output.pb -l 19 -b 1048576 -p 128 -i 128 -v
```

#### Dengeli (sıkıştırma, CPU ve güvenlik dengesi)

```
./protonbyte c dosya.ext output.pb -l 9 -b 8388608 -p 16 -i 32 -v
```

#### Burst error korumalı

```
./protonbyte c dosya.ext output.pb -l 15 -b 2097152 -p 32 -i 255 -v
```

#### Geri açma

```
./protonbyte d output.pb -v
```

#### Base

```
./protonbyte c [GİRDİ] [ÇIKTI] -l [SEVİYE] -b [BLOK] -p [PARITY] -i [DERİNLİK]
```

### Parametrelerin kısa özeti

- `-l` (Seviye): Zstd sıkıştırma gücü (1-19). Artarsa dosya küçülür ama işlem uzar.
- `-b` (Blok Boyutu): Verinin bölündüğü parçalar. Büyük bloklar daha iyi sıkıştırır.
- `-p` (Parity): Hata düzeltme kapasitesi. Ne kadar yüksekse o kadar çok hasar tamir edilir.
- `-i` (Interleave): Hataları dağıtma derinliği. Ardışık hataları engellemek için artırılmalıdır.

### Önerilen senaryolar

| Senaryo          | Önerilen Komut                 | Koruma Seviyesi | Hata Toleransı              |
| ---------------- | ------------------------------ | --------------- | --------------------------- |
| Standart Arşiv   | -l 12 -b 1048576 -p 16 -i 8    | Düşük           | Küçük bit hataları          |
| Güvenli Depolama | -l 15 -b 4194304 -p 32 -i 32   | Orta            | Disk bozulmaları (Bit-rot)  |
| Zırhlı           | -l 19 -b 1048576 -p 64 -i 64   | Yüksek          | Radyasyon / SEU hataları    |
| Ekstrem          | -l 19 -b 1048576 -p 128 -i 128 | Maksimum        | Fiziksel medya parçalanması |

### Lisans

Bu proje [MIT Lisansı](LICENSE) ile lisanslanmıştır.

---

## English

<details>
<summary><b>Click to expand English version</b></summary>

Data compression and error correction for deep space.

You can use the bitflip tool to test bit errors caused by radiation.

### Build

#### protonzip:

```
g++ -std=c++20 -O2 main.cpp -lzstd -o protonzip
```

#### bitflip:

```
g++ -std=c++20 -O2 bitflip.cpp -o bitflip
```

### Usage

#### Maximum security (less compression, more CPU effort, higher repair chance)

```
./protonzip c file.ext output.pb -l 19 -b 1048576 -p 128 -i 128 -v
```

#### Balanced (compression, CPU and security balance)

```
./protonzip c file.ext output.pb -l 9 -b 8388608 -p 16 -i 32 -v
```

#### Burst error protected

```
./protonzip c file.ext output.pb -l 15 -b 2097152 -p 32 -i 255 -v
```

#### Extraction

```
./protonzip d output.pb -v
```

#### Base

```
./protonzip c [INPUT] [OUTPUT] -l [LEVEL] -b [BLOCK] -p [PARITY] -i [INTERLEAVE]
```

### Parameters summary

- `-l` (Level): Zstd compression strength (1-19). Higher = smaller file but slower processing.
- `-b` (Block Size): How data is split into blocks. Larger blocks compress better.
- `-p` (Parity): Error correction capacity. Higher = more corrupted data can be repaired.
- `-i` (Interleave): Error spreading depth. Higher = consecutive bit errors are mitigated.

### Recommended scenarios

| Scenario              | Suggested Command         | Protection Level | Error Tolerance           |
| --------------------- | ------------------------- | ---------------- | ------------------------- |
| Standard Archive      | -l 12 -b 1M -p 16 -i 8    | Low              | Small bit errors          |
| Safe Storage          | -l 15 -b 4M -p 32 -i 32   | Medium           | Disk corruption (Bit-rot) |
| Deep Space (Shielded) | -l 19 -b 1M -p 64 -i 64   | High             | Radiation / SEU errors    |
| Voyager (Extreme)     | -l 19 -b 1M -p 128 -i 128 | Maximum          | Physical media damage     |

### License

This project is licensed under the [MIT License](LICENSE).

</details>
