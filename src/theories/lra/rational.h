#pragma once

#include <compare>
#include <cstdio>
#include <stdio.h>
#include <numeric>
#include <ostream>
#include <stdexcept>
#include <string>

#ifndef EOF
#define EOF (-1)
#endif

#include <boost/multiprecision/cpp_int.hpp>

namespace llm2smt::lra {

using BigInt = boost::multiprecision::cpp_int;

class Rational {
public:
    BigInt num{0};
    BigInt den{1};

    Rational() = default;
    Rational(long long n) : num(n), den(1) {}
    Rational(BigInt n, BigInt d = 1) : num(std::move(n)), den(std::move(d)) {
        normalize();
    }

    static Rational parse(const std::string& s);

    bool is_zero() const { return num == 0; }
    std::string str() const;

    Rational operator-() const { return Rational(-num, den); }

    Rational& operator+=(const Rational& o) {
        num = num * o.den + o.num * den;
        den *= o.den;
        normalize();
        return *this;
    }
    Rational& operator-=(const Rational& o) { return *this += -o; }
    Rational& operator*=(const Rational& o) {
        num *= o.num;
        den *= o.den;
        normalize();
        return *this;
    }
    Rational& operator/=(const Rational& o) {
        if (o.num == 0) throw std::runtime_error("division by zero in rational constant");
        num *= o.den;
        den *= o.num;
        normalize();
        return *this;
    }

    friend Rational operator+(Rational a, const Rational& b) { return a += b; }
    friend Rational operator-(Rational a, const Rational& b) { return a -= b; }
    friend Rational operator*(Rational a, const Rational& b) { return a *= b; }
    friend Rational operator/(Rational a, const Rational& b) { return a /= b; }

    friend bool operator==(const Rational& a, const Rational& b) {
        return a.num == b.num && a.den == b.den;
    }
    friend std::strong_ordering operator<=>(const Rational& a, const Rational& b) {
        BigInt lhs = a.num * b.den;
        BigInt rhs = b.num * a.den;
        if (lhs < rhs) return std::strong_ordering::less;
        if (lhs > rhs) return std::strong_ordering::greater;
        return std::strong_ordering::equal;
    }

private:
    void normalize();
};

// Values of the form c + k*delta, ordered lexicographically with delta as a
// positive infinitesimal. This implements Dutertre/de Moura Section 3.3 for
// strict LRA bounds while keeping all arithmetic exact.
struct DeltaRational {
    Rational real{0};
    Rational delta{0};

    DeltaRational() = default;
    DeltaRational(Rational r, Rational d = Rational(0))
        : real(std::move(r)), delta(std::move(d)) {}

    bool is_zero() const { return real.is_zero() && delta.is_zero(); }
    std::string str() const;

    DeltaRational operator-() const { return DeltaRational(-real, -delta); }
    DeltaRational& operator+=(const DeltaRational& o) {
        real += o.real;
        delta += o.delta;
        return *this;
    }
    DeltaRational& operator-=(const DeltaRational& o) { return *this += -o; }
    DeltaRational& operator*=(const Rational& q) {
        real *= q;
        delta *= q;
        return *this;
    }
    DeltaRational& operator/=(const Rational& q) {
        real /= q;
        delta /= q;
        return *this;
    }

    friend DeltaRational operator+(DeltaRational a, const DeltaRational& b) { return a += b; }
    friend DeltaRational operator-(DeltaRational a, const DeltaRational& b) { return a -= b; }
    friend DeltaRational operator*(DeltaRational a, const Rational& q) { return a *= q; }
    friend DeltaRational operator*(const Rational& q, DeltaRational a) { return a *= q; }
    friend DeltaRational operator/(DeltaRational a, const Rational& q) { return a /= q; }
    friend bool operator==(const DeltaRational& a, const DeltaRational& b) {
        return a.real == b.real && a.delta == b.delta;
    }
    friend std::strong_ordering operator<=>(const DeltaRational& a, const DeltaRational& b) {
        if (auto c = a.real <=> b.real; c != 0) return c;
        return a.delta <=> b.delta;
    }
};

inline std::ostream& operator<<(std::ostream& os, const Rational& q) {
    return os << q.str();
}

inline std::ostream& operator<<(std::ostream& os, const DeltaRational& q) {
    return os << q.str();
}

} // namespace llm2smt::lra
