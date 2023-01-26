#include <bits/stdc++.h>

template <unsigned mod>
requires (mod % 2 == 1)
class Montgomery32 {
public:
  unsigned value_;

  static constexpr unsigned Umod() {
    return mod;
  }

  static constexpr unsigned mod_rev_ = []() {
    unsigned ret = 1;
    for (unsigned i = 0; i < 5; ++i) {
      ret *= 2 - mod * ret;
    }
    return -ret;
  }();

  [[nodiscard]]
  static constexpr unsigned Power(unsigned a, unsigned n) {
    return Montgomery32 <mod>(a).Power(n).Get();
  }

  static constexpr unsigned primitive_root_ = []() {
    unsigned divs[20];

    unsigned id = 0;
    divs[0] = (mod - 1) >> 1;

    unsigned x = (mod - 1) >> __builtin_ctz(mod - 1);
    for (unsigned i = 3; i * i <= x; ++i) {
      if (x % i == 0) {
        divs[++id] = (mod - 1) / i;
        while (x % i == 0) {
          x /= i;
        }
      }
    }

    if (x != 1) {
      divs[++id] = (mod - 1) / x;
    }

    unsigned g = 2;
    while (true) {
      bool ok = true;
      for (unsigned i = 0; i <= id && ok; ++i) {
        if (Power(g, divs[i]) == 1) {
          ok = false;
        }
      }
      if (ok) {
        return g;
      }
      g += 1;
      ok = true;
    }
  }();

  static_assert(mod * mod_rev_ + 1 == 0, "Trouble with mod inverse");

  static constexpr uint64_t r_square_ = -uint64_t(mod) % mod;

  static constexpr unsigned Reduce(uint64_t number) {
    return (number + uint64_t(unsigned(number) * mod_rev_) * mod) >> 32;
  }

  constexpr Montgomery32()
      : value_(0) {
  }

#pragma clang diagnostic push
#pragma ide diagnostic ignored "google-explicit-constructor"
  constexpr Montgomery32(unsigned number)
      : value_(number == 0 ? 0 : Reduce(r_square_ * number)) {
  }
#pragma clang diagnostic pop

#pragma clang diagnostic push
#pragma ide diagnostic ignored "google-explicit-constructor"
  template <typename U,
      typename std::enable_if_t <!std::is_same_v <U, unsigned>, bool> = true>
  constexpr Montgomery32(U number)
      : value_(number == 0 ? 0 : Reduce(r_square_ * (number % mod))) {
  }
#pragma clang diagnostic pop

  [[nodiscard]]
  constexpr unsigned Get() const {
    unsigned q = Reduce(value_);
    return (q < mod ? q : q - mod);
  }

  [[nodiscard]]
  constexpr bool IsZero() const {
    return (value_ == 0 || value_ == Umod());
  }

  [[nodiscard]]
  constexpr Montgomery32 <mod> Power(uint64_t n) const {
    Montgomery32 <mod> res = 1;
    Montgomery32 <mod> a = *this;

    while (n > 0) {
      if (n & 1) {
        res *= a;
      }
      a *= a;
      n >>= 1;
    }

    return res;
  }

  [[nodiscard]]
  static std::optional <Montgomery32 <mod>> Sqrt(const Montgomery32 <mod> m) {
    if (m.IsZero()) {
      return Montgomery32 <mod>();
    }

    if (m.Power((Umod() - 1) >> 1) != 1) {
      return std::nullopt;
    }

    auto Multiply = [&](const std::array <Montgomery32 <mod>, 2>& lhs,
        const std::array <Montgomery32 <mod>, 2>& rhs) {
      std::array <Montgomery32 <mod>, 2> res{};
      res[1] = lhs[0] * rhs[1] + lhs[1] * rhs[0];
      res[0] = lhs[0] * rhs[0] + lhs[1] * rhs[1] * m;
      return res;
    };

    auto LinePower = [&](std::array <Montgomery32 <mod>, 2> x) {
      unsigned exp = (Umod() - 1) >> 1;
      std::array <Montgomery32 <mod>, 2> res = {{1, 0}};
      while (exp > 0) {
        if (exp & 1) {
          res = Multiply(res, x);
        }
        x = Multiply(x, x);
        exp >>= 1;
      }
      return res;
    };


    static std::mt19937 rng(std::chrono::steady_clock::now().time_since_epoch().count());
    while (true) {
      std::array <Montgomery32 <mod>, 2> z =
          {{1 + (rng() % (Umod() - 1)), 1}};

      z = LinePower(z);
      --z[0];

      if (!z[1].IsZero()) {
        auto x = z[0] / z[1];
        if (x * x == m) {
          return x;
        }
      }
    }
  }

  [[nodiscard]]
  constexpr Montgomery32 <mod> Inverse() const {
    Montgomery32 <mod> res = 1;
    Montgomery32 <mod> a = *this;

#pragma GCC unroll(30)
    for (unsigned i = 0; i < 30; ++i) {
      if ((mod - 2) >> i & 1) {
        res *= a;
      }
      a *= a;
    }

    return res;
  }

  constexpr Montgomery32 <mod> operator - () const {
    return Montgomery32 <mod>() - *this;
  }

  constexpr Montgomery32 <mod>& operator += (const Montgomery32 <mod>& rhs) {
    if (int(value_ += rhs.value_ - (mod << 1)) < 0) {
      value_ += mod << 1;
    }
    return *this;
  }

  constexpr Montgomery32 <mod>& operator -= (const Montgomery32 <mod>& rhs) {
    if (int(value_ -= rhs.value_) < 0) {
      value_ += mod << 1;
    }
    return *this;
  }

  constexpr Montgomery32 <mod>& operator *= (const Montgomery32 <mod>& rhs) {
    value_ = Reduce(uint64_t(value_) * rhs.value_);
    return *this;
  }

  constexpr Montgomery32 <mod>& operator /= (const Montgomery32 <mod>& rhs) {
    value_ = Reduce(uint64_t(value_) * rhs.Inverse().value_);
    return *this;
  }

  constexpr friend Montgomery32 <mod> operator + (const Montgomery32 <mod>& lhs, const Montgomery32 <mod>& rhs) {
    Montgomery32 <mod> res;
    res.value_ = lhs.value_;
    if (int(res.value_ += rhs.value_ - (mod << 1)) < 0) {
      res.value_ += mod << 1;
    }
    return res;
  }

  constexpr friend Montgomery32 <mod> operator - (const Montgomery32 <mod>& lhs, const Montgomery32 <mod>& rhs) {
    Montgomery32 <mod> res;
    res.value_ = lhs.value_;
    if (int(res.value_ -= rhs.value_) < 0) {
      res.value_ += mod << 1;
    }
    return res;
  }

  constexpr friend Montgomery32 <mod> operator * (const Montgomery32 <mod>& lhs, const Montgomery32 <mod>& rhs) {
    Montgomery32 <mod> res;
    res.value_ = Reduce(uint64_t(lhs.value_) * rhs.value_);
    return res;
  }

  constexpr friend Montgomery32 <mod> operator / (const Montgomery32 <mod>& lhs, const Montgomery32 <mod>& rhs) {
    Montgomery32 <mod> res;
    res.value_ = Reduce(uint64_t(lhs.value_) * rhs.Inverse().value_);
    return res;
  }

  constexpr Montgomery32 <mod>& operator ++ () {
    return *this += 1;
  }

  constexpr Montgomery32 <mod>& operator -- () {
    return *this -= 1;
  }

  constexpr friend bool operator == (const Montgomery32 <mod>& lhs, const Montgomery32 <mod>& rhs) {
    return (lhs.value_ < mod ? lhs.value_ : lhs.value_ - mod) == (rhs.value_ < mod ? rhs.value_ : rhs.value_ - mod);
  }

  constexpr friend bool operator != (const Montgomery32 <mod>& lhs, const Montgomery32 <mod>& rhs) {
    return (lhs.value_ < mod ? lhs.value_ : lhs.value_ - mod) != (rhs.value_ < mod ? rhs.value_ : rhs.value_ - mod);
  }

  friend std::istream& operator >> (std::istream& stream, Montgomery32 <mod>& m) {
    unsigned number;
    stream >> number;
    m = number;
    return stream;
  }

  friend std::ostream& operator << (std::ostream& stream, const Montgomery32 <mod>& m) {
    stream << m.Get();
    return stream;
  }
};

template <unsigned mod>
class NTT {
public:
  template <unsigned md>
  using Mint = Montgomery32 <md>;
  NTT() = delete;
  NTT(const NTT& rhs) = delete;
  NTT(NTT&& rhs) noexcept = delete;
  NTT& operator = (const NTT& rhs) = delete;
  NTT& operator = (NTT&& rhs) noexcept = delete;

  void operator () (const std::vector <Mint <mod>>::iterator& first,
                    const std::vector <Mint <mod>>::iterator& last) const {
    const unsigned n = distance(first, last);
    if ((n & (n - 1)) != 0) {
      throw std::logic_error("Distance(first, last) is not a power of 2");
    }

    {
      const unsigned shift = k_ + __builtin_clz(n) - 31U;
      for (unsigned i = 0; i < n; ++i) {
        if (i < rev_[i] >> shift) {
          std::swap(first[i], first[rev_[i] >> shift]);
        }
      }
    }

    for (unsigned i = 1; i < n; i *= 2) {
      for (unsigned j = 0; j < n; j += 2 * i) {
        for (unsigned k = 0; k < i; ++k) {
          Mint <mod> z = roots_[i + k] * first[i + j + k];
          first[i + j + k] = first[j + k] - z;
          first[j + k] += z;
        }
      }
    }
  }

  std::vector <Mint <mod>> Multiply(const std::vector <Mint <mod>>& a,
                                    const std::vector <Mint <mod>>& b) {
    if (empty(a) || empty(b)) {
      return {};
    }
    const unsigned sz = std::bit_ceil(std::max(size(a), size(b))) << 1;

    std::vector <Mint <mod>> fa(sz);
    std::copy(begin(a), end(a), begin(fa));
    this->operator()(begin(fa), end(fa));

    const Mint <mod> ratio = Mint <mod>(sz).Inverse();

    if (a != b) {
      std::vector <Mint <mod>> fb(sz);
      std::copy(begin(b), end(b), begin(fb));
      this->operator()(begin(fb), end(fb));

      for (size_t i = 0; i < sz; ++i) {
        fa[i] *= fb[i] * ratio;
      }
    } else {
      for (size_t i = 0; i < sz; ++i) {
        fa[i] *= fa[i] * ratio;
      }
    }

    std::reverse(begin(fa) + 1, end(fa));
    this->operator()(begin(fa), end(fa));
    fa.resize(size(a) + size(b) - 1);
    return fa;
  }

  static NTT <mod>& GetInstance() {
    static NTT <mod> ntt(20);
    return ntt;
  }

private:
  explicit NTT(unsigned k)
      : k_(k),
        n_(1 << k),
        rev_(1 << k),
        roots_(1 << k) {
    for (unsigned i = 1; i < n_; ++i) {
      rev_[i] = (rev_[i >> 1] >> 1) + ((i & 1) << (k_ - 1));
    }

    roots_[0] = roots_[1] = 1;
    const Mint <mod> pr = Mint <mod>::primitive_root_;
    unsigned exp = (Mint <mod>::Umod() - 1) >> 1;
    for (unsigned i = 2; i < n_; i <<= 1) {
      exp >>= 1;
      const Mint <mod> z = pr.Power(exp);
      for (unsigned j = i / 2; j < i; ++j) {
        roots_[j * 2] = roots_[j];
        roots_[j * 2 + 1] = roots_[j] * z;
      }
    }
  }

  size_t n_, k_;
  std::vector <size_t> rev_;
  std::vector <Mint <mod>> roots_;
};

constexpr unsigned mod = 998244353;

void RunCase() {
  
}

int main() {
  std::ios_base::sync_with_stdio(false);
  std::cin.tie(nullptr);
  int tt = 1;
  //std::cin >> tt;
  while (tt--) {
    RunCase();
  }
  return 0;
}
