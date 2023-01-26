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
class CombinatoricsStuff {
public:
  template <unsigned md>
  using Mint = Montgomery32 <mod>;
  CombinatoricsStuff() = delete;
  CombinatoricsStuff(const CombinatoricsStuff& rhs) = delete;
  CombinatoricsStuff(CombinatoricsStuff&& rhs) noexcept = delete;
  CombinatoricsStuff& operator = (const CombinatoricsStuff& rhs) = delete;
  CombinatoricsStuff& operator = (CombinatoricsStuff&& rhs) = delete;

  [[nodiscard]]
  [[gnu::always_inline]]
  inline Mint <mod> Factorial(unsigned id) const {
    return facts_[id];
  }

  [[nodiscard]]
  [[gnu::always_inline]]
  inline Mint <mod> InvFactorial(unsigned id) const {
    return rfacts_[id];
  }

  [[nodiscard]]
  [[gnu::always_inline]]
  inline Mint <mod> C(int n, int k) const {
    if (n < 0 || n < k) {
      return 0;
    }
    return facts_[n] * rfacts_[k] * rfacts_[n - k];
  }

  static CombinatoricsStuff <mod>& GetInstance() {
    static CombinatoricsStuff <mod> combinatorics_stuff(20);
    return combinatorics_stuff;
  }

private:
  explicit CombinatoricsStuff(unsigned n)
      : n_(n),
        facts_(n + 1),
        rfacts_(n + 1) {
    facts_[0] = facts_[1] = rfacts_[0] = rfacts_[1] = 1;
    for (unsigned i = 2; i <= n; ++i) {
      facts_[i] = facts_[i - 1] * i;
    }
    rfacts_[n] = facts_[n].Inverse();
    for (unsigned i = n - 1; i > 1; --i) {
      rfacts_[i] = rfacts_[i + 1] * (i + 1);
    }
  }

  size_t n_;
  std::vector <Mint <mod>> facts_;
  std::vector <Mint <mod>> rfacts_;
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

/* Class for work with polynomials
 * coefficients must be in Fp (and p must be ntt-friendly)
 * Inherited from std::vector
 * Core operations:
 * 1) A(x) +- B(x), A(x)', ∫A(x)dx, A(x) * k, A(x) / k, A(k) (k = const) - O(|A(x)|);
 * 2) A(x) * B(x), A(x) / B(x) - O(n * log(n)), where n = max(|A(x)|, |B(x)|);
 * 3) ln(A(x)) mod (x^n), exp(A(x)) mod (x^n), (A(x) ^ -1) mod (x^n), sqrt(A(x)) mod (x^n) - O(n * log(n));
 * 4) Evaluation(A(x), {x[0], x[1], ..., x[n - 1]}) - O(n * log(n))
 * 5) Interpolation({(x[0], y[0]), (x[1], y[1]), ..., (x[n - 1], y[n - 1])} - O(n * log(n))
 * 6) A(x) ^ k (k >= 0) mod (x^n) - O(n * log(n) * log(k)) (BinaryPower) and O(n * log(nk)) - Power
 * note : Power has a pretty large constant...
 *
 *
 * verified on https://judge.yosupo.jp/
 * n <= 500000:
 * 1) A(x) * B(x) - https://judge.yosupo.jp/submission/121758, 219ms
 * 2) (A(x) ^ -1) mod (x^n) - https://judge.yosupo.jp/submission/121759, 239 ms
 * 3) A(x) / B(x), A(x) % B(x) - https://judge.yosupo.jp/submission/121761, 456 ms
 * 4) ln(A(x)) mod (x^n) - https://judge.yosupo.jp/submission/121762, 342 ms
 * 5) exp(A(x)) mod (x^n) - https://judge.yosupo.jp/submission/121763, 781 ms
 * 6) (A(x) ^ k) mod (x^n) (k <= 1e18) - https://judge.yosupo.jp/submission/121764, 1075 ms
 * 7) sqrt(A(x)) mod (x^n) - https://judge.yosupo.jp/submission/121765, 583 ms
 *
 * n <= 131072 (2^17)
 * 1) Multipoint Evaluation - https://judge.yosupo.jp/submission/121766, 1043 ms
 * 2) Polynomial Interpolation -https://judge.yosupo.jp/submission/121768, 1477 ms
 *
 * note: without precalculated factorials, complexity of InplaceIntegrate() is actually O(n * log(n)) because of division
 * note: all arithmetic operations(+, -, *, /) dont actually care about exact number of coefficients:
 * if leading zeroes appear, they are getting removed immediately. So, when you're asked to output exactly n first coefficients,
 * you should use SetDegree(). However, all functions which require precision as an input argument, do actually return exactly n coefficients.
 *
 * internal ValueType (Mint <mod>) just has to support all modular arithmetic operations and (optionally) sqrt,
 * for (suddenly) sqrt of FPS */

template <unsigned mod>
class FormalPowerSeries : public std::vector <Montgomery32 <mod>> {
  using ValueType = Montgomery32 <mod>;
  using FPS = FormalPowerSeries <mod>;
  static constexpr unsigned THRESHOLD_NAIVE = 256; /* Threshold to run naive algo(multiplication, division etc.)*/

public:
  FormalPowerSeries() = default;
  explicit FormalPowerSeries(std::vector <ValueType>&& v) noexcept
  : std::vector <ValueType>(v) {
  }

  explicit FormalPowerSeries(const std::vector <ValueType>& v)
  : std::vector <ValueType>(v) {
  }

  /* Same as vector <ValueType>(n + 1) : constructs a zero polynomial of degree n.
   * Might be useful for std::istream& operator >> */
  explicit FormalPowerSeries(unsigned degree)
  : std::vector <ValueType>(degree + 1) {
  }

  FormalPowerSeries(const FormalPowerSeries& rhs) = default;
  FormalPowerSeries(FormalPowerSeries&& rhs) noexcept = default;
  FormalPowerSeries& operator = (const FormalPowerSeries& rhs) = default;
  FormalPowerSeries& operator = (FormalPowerSeries&& rhs) noexcept = default;
  ~FormalPowerSeries() = default;

  [[nodiscard]]
  [[gnu::always_inline]]
  inline bool IsZero() const {
    return empty(*this);
  }

  [[nodiscard]]
  [[gnu::always_inline]]
  inline int Degree() const {
    return ssize(*this) - 1;
  }

  [[nodiscard]]
  int GetTrailingZeroes() const {
    if (IsZero()) {
      return -1;
    }
    for (int i = 0; const auto& z : *this) {
      if (!z.IsZero()) {
        return i;
      }
      i += 1;
    }
    return ssize(*this);
  }

  [[nodiscard]]
  ValueType At(unsigned index) const {
    return (index < ssize(*this) ? (*this)[index] : ValueType());
  }

  /* Yields coefficient near x ^ Deg(A(x)) */
  [[nodiscard]]
  ValueType Lead() const {
    if (IsZero()) {
      throw std::logic_error("No leading coefficient");
    }
    return this->back();
  }

  void Extend(int new_degree) {
    if (new_degree > Degree()) {
      this->resize(new_degree + 1);
    }
  }

  void Reverse() {
    reverse(begin(*this), end(*this));
    Normalize();
  }

  /* Forced resize */
  void SetDegree(int k) {
    this->resize(k + 1);
  }

  void DivideByXK(unsigned k) {
    if (k == 0) {
      return;
    }
    if (Degree() < k) {
      *this = {};
    } else {
      this->erase(begin(*this), begin(*this) + k);
    }
  }

  void MultiplyByXK(unsigned k) {
    if (k == 0) {
      return;
    }
    std::vector <ValueType> new_coefficients(k + Degree() + 1);
    copy(begin(*this), end(*this), begin(new_coefficients) + k);
    this->swap(new_coefficients);
  }

  void ModEqXK(unsigned k) {
    if (k <= Degree()) {
      this->resize(k);
    }
  }

  /* Gets rid of leading zeroes */
  void Normalize() {
    while (!empty(*this) &&
           this->back().IsZero()) {
      this->pop_back();
    }
  }

  [[nodiscard]]
  FPS DivXK(unsigned k) const {
    FPS result(*this);
    result.DivideByXK(k);
    return result;
  }

  [[nodiscard]]
  FPS MulXK(unsigned k) const {
    FPS result(*this);
    result.MultiplyByXK(k);
    return result;
  }

  [[nodiscard]]
  FPS ModXK(unsigned k) const {
    FPS result(*this);
    result.ModEqXK(k);
    return result;
  }

  /* A(x) -> A(-x) */
  [[nodiscard]]
  FPS Conjugate() const {
    FPS result = *this;
    for (int i = 1; i <= Degree(); i += 2) {
      result[i] = -result[i];
    }
    return result;
  }

  /* A(x) -> {{A(x)[0], A(x)[2], ...}, {A(x)[1], A(x)[3], ...}}*/
  [[nodiscard]]
  std::array <FPS, 2> Bisect() const {
    std::array <FPS, 2> result{};
    result[1].reserve(size(*this) / 2);
    result[0].reserve((size(*this) + 1) / 2);
    for (int i = 0; i <= Degree(); ++i) {
      result[i % 2].emplace_back((*this)[i]);
    }
    return result;
  }

  void InplaceDerive() {
    if (IsZero()) {
      return;
    }
    for (int i = 1; i <= Degree(); ++i) {
      (*this)[i - 1] = (*this)[i] * i;
    }
    this->back() = ValueType();
    this->Normalize();
  }

  [[nodiscard]]
  FPS Derivative() const {
    FPS result(*this);
    result.InplaceDerive();
    return result;
  }

  void InplaceIntegrate() {
    if (IsZero()) {
      return;
    }

    this->emplace_back();
    for (int i = Degree() - 1; i >= 0; --i) {
      (*this)[i + 1] = (*this)[i] * CombinatoricsStuff <mod>::GetInstance().Factorial(i)
          * CombinatoricsStuff <mod>::GetInstance().InvFactorial(i + 1);
    }

    this->front() = ValueType();
    Normalize();
  }

  [[nodiscard]]
  FPS Integral() const {
    FPS result(*this);
    result.InplaceIntegrate();
    return result;
  }

  FPS operator - () const {
    FPS result(*this);
    for (ValueType& z : result) {
      z = -z;
    }
    return result;
  }

  FPS operator *= (const ValueType& x) {
    for (ValueType& z : *this) {
      z *= x;
    }
    Normalize();
    return *this;
  }

  FPS operator /= (const ValueType& x) {
    const ValueType y = x.Inverse();
    for (ValueType& z : *this) {
      z *= y;
    }
    Normalize();
    return *this;
  }

  friend FPS operator * (const FPS& lhs, const ValueType& x) {
    FPS result(lhs);
    result *= x;
    return result;
  }

  friend FPS operator / (const FPS& lhs, const ValueType& x) {
    FPS result(lhs);
    result /= x;
    return result;
  }

  friend FPS operator + (const FPS& lhs, const FPS& rhs) {
    if (lhs.IsZero()) {
      return rhs;
    }
    if (rhs.IsZero()) {
      return lhs;
    }

    FPS result(lhs);
    result.Extend(rhs.Degree());

    for (int i = 0; i <= rhs.Degree(); ++i) {
      result[i] += rhs[i];
    }

    result.Normalize();
    return result;
  }

  FPS& operator += (const FPS& rhs) {
    if (rhs.IsZero()) {
      return *this;
    }
    this->Extend(rhs.Degree());
    for (int i = 0; i <= rhs.Degree(); ++i) {
      (*this)[i] += rhs[i];
    }
    Normalize();
    return *this;
  }

  FPS& operator -= (const FPS& rhs) {
    if (rhs.IsZero()) {
      return *this;
    }
    this->Extend(rhs.Degree());
    for (int i = 0; i <= rhs.Degree(); ++i) {
      (*this)[i] -= rhs[i];
    }
    Normalize();
    return *this;
  }

  friend bool operator == (const FPS& lhs, const FPS& rhs) {
    if (size(lhs) != size(rhs)) {
      return false;
    }
    for (size_t i = 0; i < size(lhs); ++i) {
      if (lhs[i] != rhs[i]) {
        return false;
      }
    }
    return true;
  }

  FPS& operator *= (const FPS& rhs) {
    return *this = *this * rhs;
  }

  FPS& operator /= (const FPS& rhs) {
    return *this = *this /= rhs;
  }

  FPS& operator %= (const FPS& rhs) {
    return *this = *this %= rhs;
  }

  friend FPS operator - (const FPS& lhs, const FPS& rhs) {
    if (lhs.IsZero()) {
      return -rhs;
    }
    if (rhs.IsZero()) {
      return lhs;
    }

    FPS result(lhs);
    result.Extend(rhs.Degree());
    for (int i = 0; i <= rhs.Degree(); ++i) {
      result[i] -= rhs[i];
    }

    result.Normalize();
    return result;
  }

  friend FPS operator * (const FPS& lhs, const FPS& rhs) {
    if (lhs.IsZero() || rhs.IsZero()) {
      return {};
    }

    if (std::max(lhs.Degree(), rhs.Degree()) < THRESHOLD_NAIVE) {
      return MultiplyNaive(lhs, rhs);
    }
    return MultiplyFFT(lhs, rhs);
  }

  friend FPS operator / (const FPS& lhs, const FPS& rhs) {
    if (max(lhs.Degree(), lhs.Degree() - rhs.Degree()) < THRESHOLD_NAIVE) {
      return DivNaive(lhs, rhs);
    }
    return DivFFT(lhs, rhs);
  }

  friend FPS operator % (const FPS& lhs, const FPS& rhs) {
    if (std::max(lhs.Degree(), lhs.Degree() - rhs.Degree()) < THRESHOLD_NAIVE) {
      return ModNaive(lhs, rhs);
    }
    return ModFFT(lhs, rhs);
  }

  friend std::array <FPS, 2> DivMod(const FPS& lhs, const FPS& rhs) {
    if (std::max(lhs.Degree(), lhs.Degree() - rhs.Degree()) < THRESHOLD_NAIVE) {
      return DivModNaive(lhs, rhs);
    }
    return DivModFFT(lhs, rhs);
  }

  [[nodiscard]]
  FPS InverseSeries(unsigned precision_need) const {
    if (IsZero() || this->front().IsZero()) {
      throw std::logic_error("Inverse series doesn't exist");
    }

    unsigned sz = std::bit_ceil(precision_need) << 1;
    std::vector <ValueType> fa(sz);
    std::vector <ValueType> fb(sz);

    ValueType ratio = ValueType(4).Inverse();
    static constexpr ValueType inv_2 = ValueType(2).Inverse();

    unsigned ntt_size = 4;
    unsigned precision = 1;
    unsigned halved_ntt_size = 2;
    fa.front() = this->front();
    fb.front() = fa.front().Inverse();
    while (precision < precision_need) {
      unsigned limit = std::min(halved_ntt_size, unsigned(size(*this)));
      fill(begin(fa) + limit, begin(fa) + halved_ntt_size, ValueType());
      copy(begin(*this), begin(*this) + limit, begin(fa));

      NTT <mod>::GetInstance()(begin(fa), begin(fa) + ntt_size);
      NTT <mod>::GetInstance()(begin(fb), begin(fb) + ntt_size);
      for (unsigned i = 0; i < ntt_size; ++i) {
        fb[i] *= (2 - fa[i] * fb[i]) * ratio;
      }
      reverse(begin(fb) + 1, begin(fb) + ntt_size);
      NTT <mod>::GetInstance()(begin(fb), begin(fb) + ntt_size);
      fill(begin(fb) + halved_ntt_size, begin(fb) + ntt_size, ValueType());

      ratio *= inv_2;
      ntt_size <<= 1;
      precision <<= 1;
      halved_ntt_size <<= 1;
    }

    fb.resize(precision_need);
    return FPS(std::move(fb));
  }

  [[nodiscard]]
  FPS Log(unsigned precision_need) const {
    if (IsZero() || this->front() != ValueType(1)) {
      throw std::logic_error("Cannot take reasonable approximation for Q(0)");
    }

    FPS result = (Derivative() * InverseSeries(precision_need)).Integral();
    result.SetDegree(precision_need - 1);
    return result;
  }

  [[nodiscard]]
  FPS Exponent(unsigned precision_need) const {
    if (IsZero()) {
      std::vector <ValueType> result(precision_need);
      result[0] = 1;
      return FPS(std::move(result));
    }

    if (!this->front().IsZero()) {
      throw std::logic_error("Cannot take reasonable approximation for Q(0)");
    }

    const unsigned sz = std::bit_ceil(precision_need) << 1;

    FPS q = FPS(std::vector <ValueType>{1});
    ValueType ratio = ValueType(4).Inverse();
    constexpr ValueType inv = ValueType(2).Inverse();
    unsigned ntt_size = 4;
    unsigned precision = 1;
    unsigned halved_ntt_size = 2;

    std::vector <ValueType> fq(sz);
    std::vector <ValueType> fa(sz);
    std::vector <ValueType> fl(sz);
    fq.front() = 1;

    while (precision < precision_need) {
      auto L = q.Log(halved_ntt_size);
      copy(begin(L), end(L), begin(fl));

      unsigned limit = std::min(unsigned(size(*this)), halved_ntt_size);
      fill(begin(fa) + limit, begin(fa) + ntt_size, ValueType());
      copy(begin(*this), begin(*this) + limit, begin(fa));

      NTT <mod>::GetInstance()(begin(fa), begin(fa) + ntt_size);
      NTT <mod>::GetInstance()(begin(fl), begin(fl) + ntt_size);
      NTT <mod>::GetInstance()(begin(fq), begin(fq) + ntt_size);
      for (int i = 0; i < ntt_size; ++i) {
        fq[i] *= (fa[i] - fl[i] + 1) * ratio;
      }
      reverse(begin(fq) + 1, begin(fq) + ntt_size);
      NTT <mod>::GetInstance()(begin(fq), begin(fq) + ntt_size);
      q.resize(halved_ntt_size);
      fill(begin(fq) + halved_ntt_size, begin(fq) + ntt_size, ValueType());
      copy(begin(fq), begin(fq) + halved_ntt_size, begin(q));

      ratio *= inv;
      ntt_size <<= 1;
      precision <<= 1;
      halved_ntt_size <<= 1;
    }

    q.SetDegree(precision_need - 1);
    return q;
  }

  [[nodiscard]]
  ValueType Evaluation(const ValueType& x) const {
    ValueType m(1);
    ValueType result(0);
    for (const auto& c : *this) {
      result += c * m;
      m *= x;
    }
    return result;
  }

  [[nodiscard]]
  std::vector <ValueType> MultiPointEvaluation(const std::vector <ValueType>& points) const {
    unsigned n = points.size();
    if (IsZero()) {
      return std::vector <ValueType>(n);
    }

    std::vector <ValueType> result(n);
    std::vector <FPS> tree(2 * n - 1);
    BuildEvaluationTree(begin(tree), begin(points), end(points));
    this->Evaluate(begin(tree), begin(points), end(points), begin(result));
    return result;
  }

  static FPS Interpolation(const std::vector <ValueType>& x,
                           const std::vector <ValueType>& y) {
    const unsigned n = size(x);
    if (size(y) != n) {
      throw std::logic_error("Some points are incomplete");
    }

    std::vector <FPS> tree(2 * n - 1);
    BuildEvaluationTree(begin(tree), begin(x), end(x));
    FPS aux = tree.front().Derivative();
    aux.emplace_back();
    auto result = aux.Interpolate(begin(tree), begin(y), end(y));
    result.SetDegree(n - 1);
    return result;
  }

  [[nodiscard]]
  FPS BinaryPower(uint64_t k, unsigned precision_need) const {
    FPS result = FPS(std::vector <ValueType>{1});
    FPS mul = *this;
    while (k > 0) {
      if (k & 1) {
        result *= mul;
        result.ModEqXK(precision_need);
      }
      mul *= mul;
      mul.ModEqXK(precision_need);
      k >>= 1;
    }
    result.SetDegree(precision_need - 1);
    return result;
  }

  [[nodiscard]]
  FPS Power(uint64_t k, unsigned precision_need) const {
    if (IsZero()) {
      std::vector <ValueType> result(precision_need);
      if (k == 0) {
        result[0] = 1;
      }
      return FPS(std::move(result));
    }

    if (k <= THRESHOLD_NAIVE) {
      return BinaryPower(k, precision_need);
    }

    int ctz = GetTrailingZeroes();
    if (ctz > 0) {
      uint64_t new_ctz = k * ctz;
      if (uint64_t(precision_need + ctz - 1) / ctz <= k) {
        return FPS(std::move(std::vector <ValueType>(precision_need)));
      }
      FPS result = this->MulXK(ctz).Power(k, precision_need - new_ctz);
      result.MultiplyByXK(new_ctz);
      return result;
    } else {
      ValueType c = this->front();
      FPS result = ((*this / c).Log(precision_need) * ValueType(k % ValueType::Umod())).Exponent(precision_need) * c.Power(k);
      result.SetDegree(precision_need - 1);
      return result;
    }
  }

  [[nodiscard]]
  std::optional <FPS> Sqrt(unsigned precision_need) const {
    if (IsZero()) {
      return FPS(std::move(std::vector <ValueType>(precision_need)));
    }

    int ctz = GetTrailingZeroes();
    if (ctz % 2 == 1) {
      return std::nullopt;
    }

    if (ctz > 0) {
      if (precision_need <= ctz) {
        return FPS(std::move(std::vector <ValueType>(precision_need)));
      }
      auto aux = this->DivXK(ctz).Sqrt(precision_need - ctz / 2);
      if (aux.has_value()) {
        aux.value().MultiplyByXK(ctz >> 1);
      }
      return aux;
    } else {
      auto sq = ValueType::Sqrt(this->front());
      if (!sq.has_value()) {
        return std::nullopt;
      }

      FPS q = FPS(std::vector <ValueType>({sq.value()}));

      unsigned ntt_size = 4;
      unsigned precision = 1;
      unsigned halved_ntt_size = 2;
      unsigned sz = std::bit_ceil(precision_need) << 1;

      std::vector <ValueType> fa(sz);
      std::vector <ValueType> fb(sz);
      ValueType ratio = ValueType(4).Inverse();
      constexpr ValueType inv_2 = ValueType(2).Inverse();

      while (precision < precision_need) {
        unsigned limit = std::min(unsigned(size(*this)), halved_ntt_size);
        fill(begin(fa) + limit, begin(fa) + halved_ntt_size, ValueType());
        fill(begin(fb) + halved_ntt_size, begin(fb) + ntt_size, ValueType());
        copy(begin(*this), begin(*this) + limit, begin(fa));

        auto Inverse = q.InverseSeries(halved_ntt_size);
        copy(begin(Inverse), end(Inverse), begin(fb));
        NTT <mod>::GetInstance()(begin(fa), begin(fa) + ntt_size);
        NTT <mod>::GetInstance()(begin(fb), begin(fb) + ntt_size);

        for (unsigned i = 0; i < ntt_size; ++i) {
          fa[i] *= fb[i] * ratio;
        }
        reverse(begin(fa) + 1, begin(fa) + ntt_size);
        NTT <mod>::GetInstance()(begin(fa), begin(fa) + ntt_size);

        for (unsigned i = 0; i < halved_ntt_size; ++i) {
          fa[i] = q.At(i) - (q.At(i) - fa[i]) * inv_2;
        }
        q.resize(halved_ntt_size);
        copy(begin(fa), begin(fa) + halved_ntt_size, begin(q));

        ratio *= inv_2;
        ntt_size <<= 1;
        precision <<= 1;
        halved_ntt_size <<= 1;
      }

      q.SetDegree(precision_need - 1);
      return q;
    }
  }

  friend std::istream& operator >> (std::istream& stream, FPS& fps) {
    for (ValueType& z : fps) {
      stream >> z;
    }
    fps.Normalize();
    return stream;
  }

  friend std::ostream& operator << (std::ostream& stream, const FPS& fps) {
    for (const ValueType& z : fps) {
      stream << z << " ";
    }
    return stream;
  }

private:
  friend FPS MultiplyNaive(const FPS& lhs, const FPS& rhs) {
    FPS result(lhs.Degree() + rhs.Degree());
    for (int i = 0; i <= lhs.Degree(); ++i) {
      for (int j = 0; j <= rhs.Degree(); ++j) {
        result[i + j] += lhs[i] * rhs[j];
      }
    }
    result.Normalize();
    return result;
  }

  friend FPS MultiplyFFT(const FPS& lhs, const FPS& rhs) {
    const unsigned mx = std::max(lhs.Degree(), rhs.Degree());
    const unsigned sz = std::bit_ceil(mx + 1) << 1;

    std::vector <ValueType> fa(sz);
    copy(begin(lhs), end(lhs), begin(fa));
    NTT <mod>::GetInstance()(begin(fa), end(fa));

    const ValueType ratio = ValueType(sz).Inverse();
    if (lhs != rhs) {
      std::vector <ValueType> fb(sz);
      copy(begin(rhs), end(rhs), begin(fb));
      NTT <mod>::GetInstance()(begin(fb), end(fb));
      for (unsigned i = 0; i < sz; ++i) {
        fa[i] *= fb[i] * ratio;
      }
    } else {
      for (unsigned i = 0; i < sz; ++i) {
        fa[i] *= fa[i] * ratio;
      }
    }

    reverse(begin(fa) + 1, end(fa));
    NTT <mod>::GetInstance()(begin(fa), end(fa));
    fa.resize(lhs.Degree() + rhs.Degree() + 1);

    return FPS(std::move(fa));
  }

  friend std::array <FPS, 2> DivModNaive(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Cannot divide by zero");
    }

    if (lhs.IsZero()) {
      return {{{}, {}}};
    }

    if (lhs.Degree() < rhs.Degree()) {
      return {{{}, lhs}};
    }

    FPS quotient;
    FPS aux(lhs);
    while (rhs.Degree() <= aux.Degree()) {
      int d = aux.Degree() - rhs.Degree();
      ValueType q = aux.Lead() / rhs.Lead();
      FPS new_rhs = rhs * q;
      new_rhs.MultiplyByXK(d);
      quotient.Extend(d);
      quotient[d] += q;
      aux -= new_rhs;
    }

    return {quotient, aux};
  }

  friend FPS DivNaive(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Cannot divide by zero");
    }

    if (lhs.Degree() < rhs.Degree()) {
      return FPS();
    }

    FPS quotient;
    FPS aux(lhs);
    while (rhs.Degree() <= aux.Degree()) {
      int d = aux.Degree() - rhs.Degree();
      ValueType q = aux.Lead() / rhs.Lead();
      FPS new_rhs = rhs * q;
      new_rhs.MultiplyByXK(d);
      quotient.Extend(d);
      quotient[d] += q;
      aux -= new_rhs;
    }

    return quotient;
  }

  friend FPS ModNaive(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Cannot divide by zero");
    }

    if (lhs.IsZero()) {
      return FPS();
    }

    if (lhs.Degree() < rhs.Degree()) {
      return lhs;
    }

    FPS aux(lhs);
    while (rhs.Degree() <= aux.Degree()) {
      int d = aux.Degree() - rhs.Degree();
      ValueType q = aux.Lead() / rhs.Lead();
      FPS new_rhs = rhs * q;
      new_rhs.MultiplyByXK(d);
      aux -= new_rhs;
    }

    return aux;
  }

  friend std::array <FPS, 2> DivModFFT(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Cannot divide by zero");
    }

    if (lhs.Degree() < rhs.Degree()) {
      return {{{}, lhs}};
    }

    FPS aux = rhs;
    FPS lhs_r = lhs;
    unsigned d = lhs.Degree() - rhs.Degree() + 1;

    aux.Reverse();
    lhs_r.Reverse();
    lhs_r.ModEqXK(d);
    aux = aux.InverseSeries(d);

    aux = aux * lhs_r;
    aux.SetDegree(d - 1);
    aux.Reverse();
    return {aux, lhs - aux * rhs};
  }

  friend FPS DivFFT(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Cannot divide by zero");
    }

    if (lhs.Degree() < rhs.Degree()) {
      return {};
    }

    FPS aux = rhs;
    FPS lhs_r = lhs;
    unsigned d = lhs.Degree() - rhs.Degree() + 1;

    aux.Reverse();
    lhs_r.Reverse();
    lhs_r.ModEqXK(d);
    aux = aux.InverseSeries(d);

    aux = aux * lhs_r;
    aux.SetDegree(d - 1);
    aux.Reverse();

    return aux;
  }

  friend FPS ModFFT(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Cannot divide by zero");
    }

    if (lhs.Degree() < rhs.Degree()) {
      return lhs;
    }

    FPS aux = rhs;
    FPS lhs_r = lhs;
    unsigned d = lhs.Degree() - rhs.Degree() + 1;

    aux.Reverse();
    lhs_r.Reverse();
    lhs_r.ModEqXK(d);
    aux = aux.InverseSeries(d);

    aux = aux * lhs_r;
    aux.SetDegree(d - 1);
    aux.Reverse();

    return lhs - aux * rhs;
  }

  /* Auxiliary procedure for evaluation and interpolation */
  static void BuildEvaluationTree(const std::vector <FPS>::iterator& x,
                                  const auto& l, const auto& r) {
    if (std::distance(l, r) == 1) {
      *x = FPS({-(*l), 1});
      return;
    }
    auto mid = l + std::distance(l, r) / 2;
    auto z = x + (std::distance(l, mid) << 1);
    BuildEvaluationTree(x + 1, l, mid);
    BuildEvaluationTree(z, mid, r);
    *x = *(x + 1) * *z;
  }

  void Evaluate(const std::vector <FPS>::iterator& x,
                const auto& l, const auto& r,
                const std::vector <ValueType>::iterator& dest) const {
    if (std::distance(l, r) == 1) {
      *dest = this->Evaluation(*l);
      return;
    }
    auto mid = l + std::distance(l, r) / 2;
    auto z = x + (std::distance(l, mid) << 1);
    (*this % *(x + 1)).Evaluate(x + 1, l, mid, dest);
    (*this % *z).Evaluate(z, mid, r, dest + std::distance(l, mid));
  }

  /* Auxiliary interpolation function.
   * l and r, except of their primary segment tree function,
   * stand for pointers to y-coordinates */
  FPS Interpolate(const std::vector <FPS>::iterator& x,
                  const auto& l, const auto& r) const {
    if (std::distance(l, r) == 1) {
      return FPS({*l / this->front()});
    }
    auto mid = l + std::distance(l, r) / 2;
    auto z = x + (std::distance(l, mid) << 1);
    auto left = (*this % *(x + 1)).Interpolate(x + 1, l, mid);
    auto right = (*this % *z).Interpolate(z, mid, r);
    return *z * left + *(x + 1) * right;
  }
};

constexpr unsigned mod = 998244353;

void RunCase() {
  size_t n, m;
  std::cin >> n >> m;

  FormalPowerSeries <mod> a(n - 1);
  FormalPowerSeries <mod> b(m - 1);
  std::cin >> a >> b;

  FormalPowerSeries <mod> c = std::move(a * b);
  c.resize(n + m - 1);
  std::cout << c;
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
