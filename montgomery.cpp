/* Fastest modulo operations I've ever seen
 * Supports base operations (except of comparison) and discrete root in O(log mod) */
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
