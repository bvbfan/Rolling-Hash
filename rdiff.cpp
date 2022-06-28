
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <vector>

inline uint32_t ROTL32(uint32_t x, int8_t r) {
    return (x << r) | (x >> (32 - r));
}

inline uint32_t ReadLE32(const char* ptr) {
    uint32_t x;
    memcpy(&x, ptr, 4);
    return x;
}

uint32_t MurmurHash3(uint32_t seed, const std::string_view& data) {
    uint32_t h1 = seed;
    const uint32_t c1 = 0xcc9e2d51;
    const uint32_t c2 = 0x1b873593;

    const auto nblocks = data.size() / 4;
    const auto* blocks = data.data();

    for(int i = 0; i < nblocks; i++) {
        uint32_t k1 = ReadLE32(blocks + i * 4);

        k1 *= c1;
        k1 = ROTL32(k1, 15);
        k1 *= c2;

        h1 ^= k1;
        h1 = ROTL32(h1, 13);
        h1 = h1 * 5 + 0xe6546b64;
    }

    // tail
    const auto* tail = data.data() + nblocks * 4;

    uint32_t k1 = 0;

    switch (data.size() & 3) {
        case 3:
            k1 ^= uint32_t(tail[2]) << 16;
            [[fallthrough]];
        case 2:
            k1 ^= uint32_t(tail[1]) << 8;
            [[fallthrough]];
        case 1:
            k1 ^= uint8_t(tail[0]);
            k1 *= c1;
            k1 = ROTL32(k1, 15);
            k1 *= c2;
            h1 ^= k1;
    }

    //----------
    // finalization
    h1 ^= data.size();
    h1 ^= h1 >> 16;
    h1 *= 0x85ebca6b;
    h1 ^= h1 >> 13;
    h1 *= 0xc2b2ae35;
    h1 ^= h1 >> 16;

    return h1;
}

class KarpRabinHash {
public:
    static void init(uint32_t blockSize) {
        BtoN = 1;
        for (auto i = 0u; i < blockSize; ++i) {
            BtoN *= B;
            BtoN &= mask;
        }
        std::srand(std::time(0));
        for (auto i = 0u; i < nbrofchars; i++) {
            hashvalues[i] = std::rand() % mask;
        }
    }

    // this is a convenience function
    static uint32_t hash(const std::string_view& s) {
        uint32_t ret = 0;
        for(auto k = 0u; k < s.size(); ++k) {
            uint32_t x = 1;
            for(int j = 0; j < s.size() - 1 - k; ++j) {
                x = (x * B) & mask;
            }
            x = (x * hashvalues[s[k]]) & mask;
            ret = (ret + x) & mask;
        }
        return ret;
    }

    // add char as an input and remove char an out, the hashvalue is updated
    void update(uint8_t out, uint8_t in) {
        hashvalue = (B * hashvalue + hashvalues[in] - BtoN * hashvalues[out]) & mask;
    }

    static uint32_t BtoN;
    uint32_t hashvalue = 0;
    static constexpr uint32_t B = 37;
    static constexpr uint32_t mask = (1 << 19) - 1;
    static constexpr auto nbrofchars = 1 << 8;
    static uint32_t hashvalues[nbrofchars];
};

uint32_t KarpRabinHash::BtoN;
uint32_t KarpRabinHash::hashvalues[];

struct BlockSignature {
    // Block index
    uint32_t idx;
    // Strong checksum
    uint32_t strong;
    // roll hash
    uint32_t weak;
    // BlockData is used for debugging purpose
    std::string_view data;
};

std::string_view to_string_view(std::string::const_iterator begin, std::string::const_iterator end)
{
    return std::string_view(&(*begin), std::distance(begin, end));
}

constexpr auto seed = 0x1234u;

std::vector<BlockSignature> GenerateSignatures(const std::string& s, uint32_t blockSize) {
    std::vector<BlockSignature> result;
    auto it = s.begin();
    auto end = it + std::min<uint32_t>(s.size(), blockSize);
    for (uint32_t idx = 0; it != end; idx++) {
        auto buf = to_string_view(it, end);
        result.push_back(BlockSignature{idx, MurmurHash3(seed, buf), KarpRabinHash::hash(buf), buf});
        it = end;
        if (end != s.end())
            end += std::min<uint32_t>(std::distance(end, s.end()), blockSize);
    }
    return result;
}

struct Delta {
    uint32_t idx;
    uint32_t start;
    uint32_t end;
    bool missing;
    std::string_view data;
};

std::map<uint32_t, Delta> GenerateDelta(const std::string& s, uint32_t blockSize, const std::vector<BlockSignature>& sigs) {
    std::map<uint32_t, Delta> deltas;
    std::map<uint32_t, std::vector<const BlockSignature*>> mapsigs;
    for (const auto& sig : sigs) {
        auto idx = sig.idx;
        auto start = idx * blockSize;
        mapsigs[sig.weak].push_back(&sig);
        deltas.emplace(idx, Delta{idx, start, start + blockSize, true});
    }

    KarpRabinHash khash;
    auto it = s.begin(), last_it = it;
    auto end = it + std::min<uint32_t>(s.size(), blockSize);
    khash.hashvalue = khash.hash(to_string_view(it, end));
    while(it != s.end()) {
        const BlockSignature *sig = nullptr;
        auto& sgs = mapsigs[khash.hashvalue];
        if (!sgs.empty()) {
            auto hash = MurmurHash3(seed, to_string_view(it, end));
            for (auto s : sgs)
                if (s->strong == hash) {
                    sig = s;
                    break;
                }
        }
        if (sig) {
            auto& delta = deltas[sig->idx];
            delta.missing = false;
            delta.data = to_string_view(last_it, it);
            it = end;
            last_it = it;
            if (it != s.end()) {
                end += std::min<uint32_t>(std::distance(end, s.end()), blockSize);
                khash.hashvalue = khash.hash(to_string_view(it, end));
            }
        } else {
            if (end == s.end())
                break;
            khash.update(*it++, *end++);
        }
    }
    return deltas;
}

struct CSigDelta {
    std::vector<BlockSignature> sig;
    std::map<uint32_t, Delta> delta;
};

CSigDelta calculateDiff(int blockSize, const std::string& s1, const std::string& s2) {
    // Init KarpRabinHash
    KarpRabinHash::init(blockSize);

    // Generate signature for file A
    auto sig = GenerateSignatures(s1, blockSize);

    // Generate delta for file B using the signatures of fileA
    auto delta = GenerateDelta(s2, blockSize, sig);

    return {std::move(sig), std::move(delta)};
}

int main()
{
    std::string a("When wintertime rolls in and the days get hot enough that you need to cool off from the blazing heat");
    std::string b("When summertime rolls in and the days hot enough that you need to cool off from the blazing heat");

    auto delta = calculateDiff(16, a, b).delta;

    assert(delta.size() == 7);
    assert(delta[0].missing == true);
    assert(delta[1].missing == false);
    assert(delta[2].missing == true);
    assert(delta[3].missing == false);

    assert(delta[1].data == "When summertime ");
    assert(delta[3].data == " days hot en");

    a = "When summertime rolls in and the days get hot enough that you need to cool off from the blazing heat";
    b = "When summertime rolls in and the days get hot en ..... new additionough that you need to cool off from the blazing heat";

    delta = calculateDiff(16, a, b).delta;

    assert(delta.size() == 7);
    assert(delta[3].missing == false);
    assert(delta[3].data == " ..... new addition");

    a = "When summertime rolls in and the days get hot enough that you need to cool off from the blazing heat";
    b = "When summertim   e rolls in and the days get hot enough        that you need to cool off from the blazing heat";

    delta = calculateDiff(16, a, b).delta;

    assert(delta.size() == 7);
    assert(delta[1].missing == false);
    assert(delta[4].missing == false);

    assert(delta[1].data == "When summertim   e ");
    assert(delta[4].data == "ough        that you ne");

    return 0;
}
