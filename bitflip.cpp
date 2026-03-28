#include <iostream>
#include <vector>
#include <fstream>
#include <ctime>
#include <cstdlib>
#include <cstdint>
#include <algorithm>

using namespace std;

// Rastgele bit bozulması simülasyonu
void simulate_radiation(string filename, int error_count)
{
    // 1. Dosyayı binary modda oku
    ifstream file(filename, ios::binary);
    if (!file)
    {
        cerr << "Hata: Dosya acilamadi!" << endl;
        return;
    }

    vector<uint8_t> buffer((istreambuf_iterator<char>(file)), istreambuf_iterator<char>());
    file.close();

    if (buffer.empty())
    {
        cerr << "Hata: Dosya bos veya okunmadi." << endl;
        return;
    }

    // 2. Rastgelelik için seed
    srand(time(0));

    cout << filename << " uzerinde " << error_count << " adet bit bozulmasi simule ediliyor..." << endl;

    for (int i = 0; i < error_count; i++)
    {
        // Rastgele bir byte sec
        size_t target_byte = rand() % buffer.size();

        // Rastgele bir bit sec
        int bit_pos = rand() % 8;

        // Bit'i tersine çevir
        buffer[target_byte] ^= (1 << bit_pos);

        // Nadiren (10% olasılık) aynı byte'da ek bit hatası ekle
        if ((rand() % 10) == 0)
        {
            int extra_bit;
            do
            {
                extra_bit = rand() % 8;
            } while (extra_bit == bit_pos); // aynı biti tekrar bozma

            buffer[target_byte] ^= (1 << extra_bit);
        }
    }

    // 3. Bozulmus veriyi kaydet
    string output_name = "corrupted_" + filename;
    ofstream outfile(output_name, ios::binary);
    outfile.write((char *)buffer.data(), buffer.size());
    outfile.close();

    cout << "Islem tamamlandi. Bozulmus dosya: " << output_name << endl;
}

int main(int argc, char *argv[])
{
    if (argc < 3)
    {
        cout << "Kullanim: ./radiate <dosya_adi> <hata_sayisi>" << endl;
        cout << "Ornek: ./radiate resim.png 50" << endl;
        return 1;
    }

    string target = argv[1];
    int errors = atoi(argv[2]);

    simulate_radiation(target, errors);

    return 0;
}
