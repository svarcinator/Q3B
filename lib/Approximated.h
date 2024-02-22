#pragma once

#include <functional>

enum Precision { APPROXIMATED, PRECISE };

typedef std::pair<int, int> Interval;

Precision operator && (const Precision &l, const Precision &r);

template <typename T>
struct Approximated
{
    T value;
    Precision operationPrecision;
    Precision variablePrecision;

    Precision isPrecise() const
    {
	return operationPrecision && variablePrecision;
    }

    template <typename TRes>
    Approximated<TRes> Apply(const std::function<TRes(T)> &f)
    {
	return {f(value), operationPrecision, variablePrecision};
    }

    template <typename TRes>
    Approximated<TRes> Apply2(const Approximated<T> &r, const std::function<TRes(T, T)> &f)
    {
	TRes res = f(value, r.value);
	return {res, operationPrecision && r.operationPrecision, variablePrecision && r.variablePrecision};
    }

    template <typename TRes>
    Approximated<TRes> Apply2(const Approximated<T> &r, const std::function<TRes(T, T, std::vector<Interval>)> &f, const std::vector<Interval>& interv)
    {
	TRes res = f(value, r.value, interv);
	return {res, operationPrecision && r.operationPrecision, variablePrecision && r.variablePrecision};
    }
};
