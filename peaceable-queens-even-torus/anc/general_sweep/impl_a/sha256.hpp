#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <sstream>
#include <string>

namespace pq {

// Small self-contained SHA-256 implementation used only for deterministic
// certificate fingerprints and manifests.  Bytes are consumed verbatim.
class Sha256 {
public:
    Sha256()
      : state_{0x6a09e667U,0xbb67ae85U,0x3c6ef372U,0xa54ff53aU,
               0x510e527fU,0x9b05688cU,0x1f83d9abU,0x5be0cd19U} {}

    void update(const void* data, std::size_t size) {
        const auto* p = static_cast<const std::uint8_t*>(data);
        total_ += size;
        while (size) {
            std::size_t take = std::min(size, block_.size() - used_);
            for (std::size_t i=0;i<take;++i) block_[used_+i]=p[i];
            used_ += take; p += take; size -= take;
            if (used_ == block_.size()) {
                transform(block_.data());
                used_ = 0;
            }
        }
    }
    void update(const std::string& s) { update(s.data(),s.size()); }

    std::array<std::uint8_t,32> finish() {
        const std::uint64_t bits = total_ * 8;
        block_[used_++] = 0x80;
        if (used_ > 56) {
            while (used_ < 64) block_[used_++] = 0;
            transform(block_.data()); used_ = 0;
        }
        while (used_ < 56) block_[used_++] = 0;
        for (int i=7;i>=0;--i) block_[used_++] = std::uint8_t(bits>>(8*i));
        transform(block_.data()); used_ = 0;
        std::array<std::uint8_t,32> out{};
        for (int i=0;i<8;++i) for (int j=0;j<4;++j)
            out[4*i+j]=std::uint8_t(state_[i]>>(24-8*j));
        return out;
    }
    std::string hex_digest() {
        auto bytes=finish();
        std::ostringstream out;
        out<<std::hex<<std::setfill('0');
        for(auto b:bytes)out<<std::setw(2)<<unsigned(b);
        return out.str();
    }

private:
    std::array<std::uint32_t,8> state_;
    std::array<std::uint8_t,64> block_{};
    std::size_t used_{};
    std::uint64_t total_{};

    static std::uint32_t rotr(std::uint32_t x,int n) {
        return (x>>n)|(x<<(32-n));
    }
    void transform(const std::uint8_t* p) {
        static constexpr std::array<std::uint32_t,64> k{{
          0x428a2f98U,0x71374491U,0xb5c0fbcfU,0xe9b5dba5U,
          0x3956c25bU,0x59f111f1U,0x923f82a4U,0xab1c5ed5U,
          0xd807aa98U,0x12835b01U,0x243185beU,0x550c7dc3U,
          0x72be5d74U,0x80deb1feU,0x9bdc06a7U,0xc19bf174U,
          0xe49b69c1U,0xefbe4786U,0x0fc19dc6U,0x240ca1ccU,
          0x2de92c6fU,0x4a7484aaU,0x5cb0a9dcU,0x76f988daU,
          0x983e5152U,0xa831c66dU,0xb00327c8U,0xbf597fc7U,
          0xc6e00bf3U,0xd5a79147U,0x06ca6351U,0x14292967U,
          0x27b70a85U,0x2e1b2138U,0x4d2c6dfcU,0x53380d13U,
          0x650a7354U,0x766a0abbU,0x81c2c92eU,0x92722c85U,
          0xa2bfe8a1U,0xa81a664bU,0xc24b8b70U,0xc76c51a3U,
          0xd192e819U,0xd6990624U,0xf40e3585U,0x106aa070U,
          0x19a4c116U,0x1e376c08U,0x2748774cU,0x34b0bcb5U,
          0x391c0cb3U,0x4ed8aa4aU,0x5b9cca4fU,0x682e6ff3U,
          0x748f82eeU,0x78a5636fU,0x84c87814U,0x8cc70208U,
          0x90befffaU,0xa4506cebU,0xbef9a3f7U,0xc67178f2U
        }};
        std::array<std::uint32_t,64> w{};
        for(int i=0;i<16;++i)
            w[i]=(std::uint32_t(p[4*i])<<24)|(std::uint32_t(p[4*i+1])<<16)|
                 (std::uint32_t(p[4*i+2])<<8)|std::uint32_t(p[4*i+3]);
        for(int i=16;i<64;++i) {
            auto s0=rotr(w[i-15],7)^rotr(w[i-15],18)^(w[i-15]>>3);
            auto s1=rotr(w[i-2],17)^rotr(w[i-2],19)^(w[i-2]>>10);
            w[i]=w[i-16]+s0+w[i-7]+s1;
        }
        auto a=state_[0],b=state_[1],c=state_[2],d=state_[3];
        auto e=state_[4],f=state_[5],g=state_[6],h=state_[7];
        for(int i=0;i<64;++i) {
            auto s1=rotr(e,6)^rotr(e,11)^rotr(e,25);
            auto ch=(e&f)^((~e)&g);
            auto t1=h+s1+ch+k[i]+w[i];
            auto s0=rotr(a,2)^rotr(a,13)^rotr(a,22);
            auto maj=(a&b)^(a&c)^(b&c);
            auto t2=s0+maj;
            h=g;g=f;f=e;e=d+t1;d=c;c=b;b=a;a=t1+t2;
        }
        state_[0]+=a;state_[1]+=b;state_[2]+=c;state_[3]+=d;
        state_[4]+=e;state_[5]+=f;state_[6]+=g;state_[7]+=h;
    }
};

} // namespace pq
