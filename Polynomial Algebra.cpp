template <unsigned mod>
using Mint = Montgomery32 <mod>;

template <unsigned mod>
class CombinatoricsStuff {
public:
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

private:
  unsigned n_;
  std::vector <Mint <mod>> facts_;
  std::vector <Mint <mod>> rfacts_;
};

template <unsigned mod>
class NTT {
public:

  unsigned k_;
  unsigned n_;
  std::vector <Mint <mod>> roots_;
  std::vector <unsigned> rev_;

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
        roots_[j << 1] = roots_[j];
        roots_[j << 1 | 1] = roots_[j] * z;
      }
    }
  }

  void operator () (const std::vector <Mint <mod>>::iterator& first,
                    const std::vector <Mint <mod>>::iterator& last) const {
    const unsigned n = distance(first, last);
    assert((n & (n - 1)) == 0);

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
 * note: all arithmetic operations(+, -, *, /) dont actually care about exact number of coefficients:
 * if leading zeroes appear, they are getting removed immediately. So, when you're asked to output exactly n first coefficients,
 * you should use SetDegree(). However, all functions which require precision as an input argument, do actually return exactly n coefficients.
 *
 * internal value_type (Mint <mod>) just has to support all modular arithmetic operations and (optionally) sqrt,
 * for (suddenly) sqrt of FPS */

template <unsigned mod>
class FormalPowerSeries : public std::vector <Mint <mod>> {
  using value_type = Mint <mod>;
  using FPS = FormalPowerSeries <mod>;
  static inline NTT <mod> ntt = std::move(NTT <mod>(20));
  static inline CombinatoricsStuff <mod> fact_stuff = std::move(CombinatoricsStuff <mod>(1 << 20));
  static constexpr unsigned THRESHOLD_NAIVE = 256; /* Threshold to run naive algo(multiplication, division etc.)*/

public:
  FormalPowerSeries() = default;
  explicit FormalPowerSeries(std::vector <value_type>&& v) noexcept
  : std::vector <value_type>(v) {
  }

  explicit FormalPowerSeries(unsigned degree)
  : std::vector <value_type>(degree + 1) {
  }

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
  value_type At(unsigned index) const {
    return (index < ssize(*this) ? (*this)[index] : value_type());
  }

  /* Yields coefficient near x ^ Deg(A(x)) */
  [[nodiscard]]
  value_type Lead() const {
    assert(!IsZero());
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
    assert(0 <= k);
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
    std::vector <value_type> new_coefficients(k + Degree() + 1);
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

  void InplaceDerivate() {
    if (IsZero()) {
      return;
    }
    for (int i = 1; i <= Degree(); ++i) {
      (*this)[i - 1] = (*this)[i] * i;
    }
    this->back() = value_type();
    this->Normalize();
  }

  [[nodiscard]]
  FPS Derivative() const {
    FPS result(*this);
    result.InplaceDerivate();
    return result;
  }

  void InplaceIntegrate() {
    if (IsZero()) {
      return;
    }

    this->emplace_back();
    for (int i = Degree() - 1; i >= 0; --i) {
      (*this)[i + 1] = (*this)[i] * fact_stuff.Factorial(i) * fact_stuff.InvFactorial(i + 1);
    }

    this->front() = value_type();
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
    for (value_type& z : result) {
      z = -z;
    }
    return result;
  }

  FPS operator *= (const value_type& x) {
    for (value_type& z : *this) {
      z *= x;
    }
    Normalize();
    return *this;
  }

  FPS operator /= (const value_type& x) {
    const value_type y = x.Inverse();
    for (value_type& z : *this) {
      z *= y;
    }
    Normalize();
    return *this;
  }

  friend FPS operator * (const FPS& lhs, const value_type& x) {
    FPS result(lhs);
    result *= x;
    return result;
  }

  friend FPS operator / (const FPS& lhs, const value_type& x) {
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

  /*https://judge.yosupo.jp/submission/121053,
   * n <= 5e5, 223 ms> */
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
  /* https://judge.yosupo.jp/submission/121057,
   * n <= 5e5, 232 ms */
  FPS InverseSeries(unsigned precision_need) const {
    if (IsZero() || this->front().IsZero()) {
      throw std::logic_error("Inverse series doesn't exist");
    }

    unsigned sz = std::bit_ceil(precision_need) << 1;
    std::vector <value_type> fa(sz);
    std::vector <value_type> fb(sz);

    value_type ratio = value_type(4).Inverse();
    static constexpr value_type inv_2 = value_type(2).Inverse();

    unsigned ntt_size = 4;
    unsigned precision = 1;
    unsigned halved_ntt_size = 2;
    fa.front() = this->front();
    fb.front() = fa.front().Inverse();
    while (precision < precision_need) {
      unsigned limit = std::min(halved_ntt_size, unsigned(size(*this)));
      fill(begin(fa) + limit, begin(fa) + halved_ntt_size, value_type());
      copy(begin(*this), begin(*this) + limit, begin(fa));

      ntt(begin(fa), begin(fa) + ntt_size);
      ntt(begin(fb), begin(fb) + ntt_size);
      for (unsigned i = 0; i < ntt_size; ++i) {
        fb[i] *= (2 - fa[i] * fb[i]) * ratio;
      }
      reverse(begin(fb) + 1, begin(fb) + ntt_size);
      ntt(begin(fb), begin(fb) + ntt_size);
      fill(begin(fb) + halved_ntt_size, begin(fb) + ntt_size, value_type());

      ratio *= inv_2;
      ntt_size <<= 1;
      precision <<= 1;
      halved_ntt_size <<= 1;
    }

    fb.resize(precision_need);
    return FPS(std::move(fb));
  }

  /* https://judge.yosupo.jp/submission/121062,
   * n <= 5e5, 364 ms*/
  [[nodiscard]]
  FPS Log(unsigned precision_need) const {
    if (IsZero() || this->front() != value_type(1)) {
      throw std::logic_error("Cannot take reasonable approximation for Q(0)");
    }

    FPS result = (Derivative() * InverseSeries(precision_need)).Integral();
    result.SetDegree(precision_need - 1);
    return result;
  }

  [[nodiscard]]
  /*https://judge.yosupo.jp/submission/121224*,
   * n <= 5e5, 849 ms*/
  FPS Exponent(unsigned precision_need) const {
    if (IsZero()) {
      std::vector <value_type> result(precision_need);
      result[0] = 1;
      return FPS(std::move(result));
    }

    if (!this->front().IsZero()) {
      throw std::logic_error("Cannot take reasonable approximation for Q(0)");
    }

    const unsigned sz = std::bit_ceil(precision_need) << 1;

    FPS q = FPS(std::vector <value_type>{1});
    value_type ratio = value_type(4).Inverse();
    constexpr value_type inv = value_type(2).Inverse();
    unsigned ntt_size = 4;
    unsigned precision = 1;
    unsigned halved_ntt_size = 2;

    std::vector <value_type> fq(sz);
    std::vector <value_type> fa(sz);
    std::vector <value_type> fl(sz);
    fq.front() = 1;

    while (precision < precision_need) {
      auto L = q.Log(halved_ntt_size);
      copy(begin(L), end(L), begin(fl));

      unsigned limit = std::min(unsigned(size(*this)), halved_ntt_size);
      fill(begin(fa) + limit, begin(fa) + ntt_size, value_type());
      copy(begin(*this), begin(*this) + limit, begin(fa));

      ntt(begin(fa), begin(fa) + ntt_size);
      ntt(begin(fl), begin(fl) + ntt_size);
      ntt(begin(fq), begin(fq) + ntt_size);
      for (int i = 0; i < ntt_size; ++i) {
        fq[i] *= (fa[i] - fl[i] + 1) * ratio;
      }
      reverse(begin(fq) + 1, begin(fq) + ntt_size);
      ntt(begin(fq), begin(fq) + ntt_size);
      q.resize(halved_ntt_size);
      fill(begin(fq) + halved_ntt_size, begin(fq) + ntt_size, value_type());
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
  value_type Evaluation(const value_type& x) const {
    value_type m(1);
    value_type result(0);
    for (const auto& c : *this) {
      result += c * m;
      m *= x;
    }
    return result;
  }

  [[nodiscard]]
  std::vector <value_type> MultiPointEvaluation(const std::vector <value_type>& points) const {
    unsigned n = points.size();
    if (IsZero()) {
      return std::vector <value_type>(n);
    }

    std::vector <value_type> result(n);
    std::vector <FPS> tree(2 * n - 1);
    BuildEvaluationTree(begin(tree), begin(points), end(points));
    this->Evaluate(begin(tree), begin(points), end(points), begin(result));
    return result;
  }

  static FPS Interpolation(const std::vector <value_type>& x,
                           const std::vector <value_type>& y) {
    const unsigned n = size(x);
    if (size(y) != n) {
      throw std::logic_error("Some points are incomplete");
    }

    std::vector <FPS> tree(2 * n - 1);
    BuildEvaluationTree(begin(tree), begin(x), end(x));
    FPS aux = tree.front().Derivative();
    aux.emplace_back();
    return aux.Interpolate(begin(tree), begin(y), end(y));
  }

  [[nodiscard]]
  /* https://judge.yosupo.jp/submission/121483.
   * n <= 5e5, 8184 ms */
  FPS BinaryPower(uint64_t k, unsigned precision_need) const {
    FPS result = FPS(std::vector <value_type>{1});
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
  /* https://judge.yosupo.jp/submission/121489,
   * n <= 5e5, 1100 ms*/
  FPS Power(uint64_t k, unsigned precision_need) const {
    if (IsZero()) {
      std::vector <value_type> result(precision_need);
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
        return FPS(std::move(std::vector <value_type>(precision_need)));
      }
      FPS result = this->MulXK(ctz).Power(k, precision_need - new_ctz);
      result.MultiplyByXK(new_ctz);
      return result;
    } else {
      value_type c = this->front();
      FPS result = ((*this / c).Log(precision_need) * value_type(k % value_type::Umod())).Exponent(precision_need) * c.Power(k);
      result.SetDegree(precision_need - 1);
      return result;
    }
  }

  [[nodiscard]]
  /* https://judge.yosupo.jp/submission/121468
   * n <= 5e5, 561 ms */
  std::optional <FPS> Sqrt(unsigned precision_need) const {
    if (IsZero()) {
      return FPS(std::move(std::vector <value_type>(precision_need)));
    }

    int ctz = GetTrailingZeroes();
    if (ctz % 2 == 1) {
      return std::nullopt;
    }

    if (ctz > 0) {
      if (precision_need <= ctz) {
        return FPS(std::move(std::vector <value_type>(precision_need)));
      }
      auto aux = this->DivXK(ctz).Sqrt(precision_need - ctz / 2);
      if (aux.has_value()) {
        aux.value().MultiplyByXK(ctz >> 1);
      }
      return aux;
    } else {
      auto sq = value_type::Sqrt(this->front());
      if (!sq.has_value()) {
        return std::nullopt;
      }

      FPS q = FPS(std::vector <value_type>({sq.value()}));

      unsigned ntt_size = 4;
      unsigned precision = 1;
      unsigned halved_ntt_size = 2;
      unsigned sz = std::bit_ceil(precision_need) << 1;

      std::vector <value_type> fa(sz);
      std::vector <value_type> fb(sz);
      value_type ratio = value_type(4).Inverse();
      constexpr value_type inv_2 = value_type(2).Inverse();

      while (precision < precision_need) {
        unsigned limit = std::min(unsigned(size(*this)), halved_ntt_size);
        fill(begin(fa) + limit, begin(fa) + halved_ntt_size, value_type());
        fill(begin(fb) + halved_ntt_size, begin(fb) + ntt_size, value_type());
        copy(begin(*this), begin(*this) + limit, begin(fa));

        auto Inverse = q.InverseSeries(halved_ntt_size);
        copy(begin(Inverse), end(Inverse), begin(fb));
        ntt(begin(fa), begin(fa) + ntt_size);
        ntt(begin(fb), begin(fb) + ntt_size);

        for (unsigned i = 0; i < ntt_size; ++i) {
          fa[i] *= fb[i] * ratio;
        }
        reverse(begin(fa) + 1, begin(fa) + ntt_size);
        ntt(begin(fa), begin(fa) + ntt_size);

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
    for (value_type& z : fps) {
      stream >> z;
    }
    fps.Normalize();
    return stream;
  }

  friend std::ostream& operator << (std::ostream& stream, const FPS& fps) {
    for (const value_type& z : fps) {
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

    std::vector <value_type> fa(sz);
    copy(begin(lhs), end(lhs), begin(fa));
    ntt(begin(fa), end(fa));

    const value_type ratio = value_type(sz).Inverse();
    if (lhs != rhs) {
      std::vector <value_type> fb(sz);
      copy(begin(rhs), end(rhs), begin(fb));
      ntt(begin(fb), end(fb));
      for (unsigned i = 0; i < sz; ++i) {
        fa[i] *= fb[i] * ratio;
      }
    } else {
      for (unsigned i = 0; i < sz; ++i) {
        fa[i] *= fa[i] * ratio;
      }
    }

    reverse(begin(fa) + 1, end(fa));
    ntt(begin(fa), end(fa));
    fa.resize(lhs.Degree() + rhs.Degree() + 1);

    return FPS(std::move(fa));
  }

  friend std::array <FPS, 2> DivModNaive(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Do you really need this?");
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
      value_type q = aux.Lead() / rhs.Lead();
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
      throw std::logic_error("Do you really need this?");
    }

    if (lhs.Degree() < rhs.Degree()) {
      return FPS();
    }

    FPS quotient;
    FPS aux(lhs);
    while (rhs.Degree() <= aux.Degree()) {
      int d = aux.Degree() - rhs.Degree();
      value_type q = aux.Lead() / rhs.Lead();
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
      throw std::logic_error("Do you really need this?");
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
      value_type q = aux.Lead() / rhs.Lead();
      FPS new_rhs = rhs * q;
      new_rhs.MultiplyByXK(d);
      aux -= new_rhs;
    }

    return aux;
  }

  friend std::array <FPS, 2> DivModFFT(const FPS& lhs, const FPS& rhs) {
    if (rhs.IsZero()) {
      throw std::logic_error("Do you really need this?");
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
      throw std::logic_error("Do you really need this?");
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
      throw std::logic_error("Do you really need this?");
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
                const std::vector <value_type>::iterator& dest) const {
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

using FPS = FormalPowerSeries <p>;

void RunCase() {
  int n;
  std::cin >> n;

  std::vector <Mint <p>> x(n);
  std::vector <Mint <p>> y(n);
  for (auto& z : x) {
    std::cin >> z;
  }
  for (auto& z : y) {
    std::cin >> z;
  }

  auto result = FPS::Interpolation(x, y);
  result.SetDegree(n - 1);
  std::cout << result << "\n";
}

int main() {
  std::ios_base::sync_with_stdio(false);
  std::cin.tie(nullptr);
  int tt = 1;
  //cin >> tt;
  while (tt--) {
    RunCase();
  }
  return 0;
}
