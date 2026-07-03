#include "theories/lra/rational.h"

#include <algorithm>

namespace llm2smt::lra {

static BigInt abs_big(BigInt x) {
    return x < 0 ? -x : x;
}

static BigInt gcd_big(BigInt a, BigInt b) {
    a = abs_big(std::move(a));
    b = abs_big(std::move(b));
    while (b != 0) {
        BigInt r = a % b;
        a = b;
        b = r;
    }
    return a == 0 ? BigInt(1) : a;
}

void Rational::normalize() {
    if (den == 0) throw std::runtime_error("zero denominator in rational");
    if (num == 0) {
        den = 1;
        return;
    }
    if (den < 0) {
        num = -num;
        den = -den;
    }
    if (den == 1) return;
    BigInt g = gcd_big(num, den);
    num /= g;
    den /= g;
}

Rational Rational::parse(const std::string& s) {
    auto slash = s.find('/');
    if (slash != std::string::npos) {
        return Rational(BigInt(s.substr(0, slash)), BigInt(s.substr(slash + 1)));
    }
    auto dot = s.find('.');
    if (dot != std::string::npos) {
        std::string whole = s.substr(0, dot);
        std::string frac = s.substr(dot + 1);
        bool neg = !whole.empty() && whole[0] == '-';
        if (whole.empty() || whole == "-") whole += "0";
        std::string digits = (neg ? whole.substr(1) : whole) + frac;
        BigInt n(digits.empty() ? "0" : digits);
        BigInt d = 1;
        for (size_t i = 0; i < frac.size(); ++i) d *= 10;
        if (neg) n = -n;
        return Rational(n, d);
    }
    return Rational(BigInt(s), 1);
}

std::string Rational::str() const {
    if (den == 1) return num.str();
    return "(/ " + num.str() + " " + den.str() + ")";
}

std::string DeltaRational::str() const {
    if (delta.is_zero()) return real.str();
    if (real.is_zero()) return delta.str() + "*delta";
    return real.str() + (delta > Rational(0) ? " + " : " - ") +
           (delta > Rational(0) ? delta : -delta).str() + "*delta";
}

} // namespace llm2smt::lra
