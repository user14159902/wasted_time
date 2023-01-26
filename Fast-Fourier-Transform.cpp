#include <bits/stdc++.h>

template <typename FloatingPointType>
class FFT {
public:
  FFT() = delete;
  FFT(const FFT& rhs) = delete;
  FFT(FFT&& rhs) noexcept = delete;
  FFT& operator = (const FFT& rhs) = delete;
  FFT& operator = (FFT&& rhs) noexcept = delete;

  class Complex {
  public:
    FloatingPointType re_;
    FloatingPointType im_;

    Complex()
    : re_(0),
      im_(0) {
    }

    Complex(FloatingPointType re, FloatingPointType im)
    : re_(re),
      im_(im) {
    }

    template <typename U, typename V>
    explicit Complex(U re, V im = 0)
    : re_(FloatingPointType(re)),
      im_(FloatingPointType(im)) {
    }

    Complex(const Complex& rhs) = default;
    Complex& operator = (const Complex& rhs)  = default;

    Complex(Complex&& rhs) noexcept = default;
    Complex& operator = (Complex&& rhs) noexcept = default;

    [[nodiscard]]
    [[gnu::always_inline]]
    inline FloatingPointType Real() const {
      return re_;
    }

    [[nodiscard]]
    [[gnu::always_inline]]
    inline FloatingPointType Imag() const {
      return im_;
    }

    [[nodiscard]]
    [[gnu::always_inline]]
    inline Complex Conj() const {
      return {re_, -im_};
    }

    Complex& operator += (const Complex& rhs) {
      re_ += rhs.re_;
      im_ += rhs.im_;
      return *this;
    }

    Complex& operator -= (const Complex& rhs) {
      re_ -= rhs.re_;
      im_ += rhs.im_;
      return *this;
    }

    Complex& operator *= (const Complex& rhs) {
      return *this = *this * rhs;
    }

    friend Complex operator + (const Complex& lhs, const Complex& rhs) {
      return {lhs.re_ + rhs.re_, lhs.im_ + rhs.im_};
    }

    friend Complex operator - (const Complex& lhs, const Complex& rhs) {
      return {lhs.re_ - rhs.re_, lhs.im_ - rhs.im_};
    }

    friend Complex operator * (const Complex& lhs, const Complex& rhs) {
      return {lhs.re_ * rhs.re_ - lhs.im_ * rhs.im_, lhs.re_ * rhs.im_ + lhs.im_ * rhs.re_};
    }
  };

  void operator ()(const std::vector <Complex>::iterator& first,
                   const std::vector <Complex>::iterator& last) {
    const unsigned n = std::distance(first, last);

    {
      const unsigned shift = k_ + __builtin_clz(n) - 31U;
      for (unsigned i = 0; i < n; ++i) {
        if (i < rev_[i] >> shift) {
          std::swap(first[i], first[rev_[i] >> shift]);
        }
      }
    }

    for (unsigned i = 1; i < n; i *= 2) {
      for (unsigned j = 0; j < n; j += i * 2) {
        for (unsigned k = 0; k < i; ++k) {
          Complex z = roots_[i + k] * first[i + j + k];
          first[i + j + k] = first[j + k] - z;
          first[j + k] += z;
        }
      }
    }
  }

  std::vector <int> Multiply(const std::vector <int>& a, const std::vector <int>& b) {
    if (a.empty() || b.empty()) {
      return {};
    }

    const unsigned sz = std::bit_ceil((unsigned)std::max(a.size(), b.size())) << 1;
    std::vector <Complex> fa(sz);

    {
      int x, y;
      for (unsigned i = 0; i < sz >> 1; ++i) {
        x = (i < size(a) ? a[i] : 0);
        y = (i < size(b) ? b[i] : 0);
        fa[i] = Complex(x, y);
      }
    }

    this->operator()(begin(fa), end(fa));
    std::vector <Complex> fb(sz);
    const Complex ratio = {0.0, -0.25 / sz};
    for (unsigned i = 0; i < sz; ++i) {
      unsigned id = (sz - i) & (sz - 1);
      Complex conjugate = fa[id].Conj();
      fb[id] = (fa[i] * fa[i] - conjugate * conjugate) * ratio;
    }

    this->operator()(begin(fb), end(fb));
    std::vector <int> result(size(a) + size(b) - 1);
    for (int i = 0; i < size(result); ++i) {
      result[i] = int(::lroundl(fb[i].Real()));
    }

    return result;
  }

  static FFT& GetInstance() {
    static FFT <FloatingPointType> fft(20);
    return fft;
  }

private:
  explicit FFT(unsigned k)
  : k_(k),
    n_(1 << k),
    rev_(1 << k),
    roots_(1 << k) {
    for (size_t i = 1; i < n_; ++i) {
      rev_[i] = (rev_[i >> 1] >> 1) + ((i & 1) << (k_ - 1));
    }

    roots_[0] = roots_[1] = Complex(1, 0);
    for (int i = 2; i < n_; i *= 2) {
      const FloatingPointType angle = std::numbers::pi_v <FloatingPointType> / i;
      const Complex root = Complex(cosl(angle), sinl(angle));
      for (int j = i >> 1; j < i; ++j) {
        roots_[j * 2] = roots_[j];
        roots_[j * 2 + 1] = roots_[j] * root;
      }
    }
  }

  size_t n_, k_;
  std::vector <size_t> rev_;
  std::vector <Complex> roots_;
};

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
