// Copyright (c) 2011 Keean Schupke

#include <vector>
#include <stdint.h>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <cassert>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <boost/concept_check.hpp>
#include <boost/concept/requires.hpp>
#include <boost/function_types/function_arity.hpp>
#include <boost/function_types/result_type.hpp>
#include <boost/function_types/parameter_types.hpp>

extern "C" {
#include <sys/resource.h>
}

//----------------------------------------------------------------------------
// Benchmarking

double rtime() {
    struct rusage rusage;
    getrusage(RUSAGE_SELF, &rusage);
    return static_cast<double>(rusage.ru_utime.tv_sec) 
        + static_cast<double>(rusage.ru_utime.tv_usec) / 1000000.0L;
}

template <typename T> struct profile {
    static double t;
    static double s;

    profile() {
        s = rtime();
    }

	static void start() {
		s = rtime();
	}

    ~profile() {
        t += rtime() - s;
    }

	static void finish() {
		t += rtime() - s;
	}

    static double report() {
        return t;
    }
};

template <typename T> double profile<T>::t(0);
template <typename T> double profile<T>::s;

//----------------------------------------------------------------------------
// Values that depend on types.

template <typename T> void same_type(T const&, T const&);

template <typename F> int constexpr arity() {
    return boost::function_types::function_arity<decltype(&F::operator())>::value;
}

//----------------------------------------------------------------------------
// Types that depend on types.

template <typename T> struct value_type;
template <typename T> using ValueType = typename value_type<T>::type;
//template <typename T> struct value_type {typedef T type;};

template <typename T> struct underlying_type;
template <typename T> using UnderlyingType = typename underlying_type<T>::type;
template <typename T> struct underlying_type {typedef T type;};

template <typename T> struct iterator_type;
template <typename T> using IteratorType = typename iterator_type<T>::type;

template <typename T> struct iterator_const_type;
template <typename T> using IteratorConstType = typename iterator_const_type<T>::type;

template <typename T> struct size_type;
template <typename T> using SizeType = typename size_type<T>::type;

template <typename T> struct weight_type;
template <typename T> using WeightType = typename weight_type<T>::type;

template <typename T> struct distance_type;
template <typename T> using DistanceType = typename distance_type<T>::type;

template <typename T> struct subset_type;
template <typename T> using SubsetType = typename subset_type<T>::type;

template <typename T> struct superset_type;
template <typename T> using SupersetType = typename superset_type<T>::type;

template <typename T> struct disjoint_set_type;
template <typename T> using DisjointSetType = typename disjoint_set_type<T>::type;

template <typename T> struct actions_type;
template <typename T> using ActionsType = typename actions_type<T>::type;

template <typename T> struct regions_type;
template <typename T> using RegionsType = typename regions_type<T>::type;

template <typename F> using ResultType = typename boost::function_types::result_type<decltype(&F::operator())>::type;

template <typename F> using Domain = typename boost::mpl::at_c<boost::function_types::parameter_types<decltype(&F::operator())>,1>::type;

template <typename F, int N> using InputType = typename boost::mpl::at_c<boost::function_types::parameter_types<decltype(&F::operator())>,N>::type;

//----------------------------------------------------------------------------

template <typename T> struct fn_deref {
	ValueType<T>& operator() (T) const;
};

template <typename T> inline ValueType<T>& deref(T t) {
	return fn_deref<T>()(t);
}

//----------------------------------------------------------------------------
// Pointer to mutable data.

template <typename T> using pointer = T*;

template <typename T> struct value_type<pointer<T>> {typedef T type;};
template <typename T> struct distance_type<pointer<T>> {typedef ssize_t type;};

template <typename T> inline pointer<T> addressof(T& x) {
    return &x;
}

template <typename T> struct fn_deref<pointer<T>> {
	inline ValueType<pointer<T>>& operator() (pointer<T> i) const {
		return *i;
	}
};

template <typename T> inline ValueType<pointer<T>> const& source(pointer<T> i) {return deref(i);}
template <typename T> inline ValueType<pointer<T>>& sink(pointer<T> i) {return deref(i);}

//----------------------------------------------------------------------------
// Pointer to immutable data.

template <typename T> using pointer_const = T const*;

template <typename T> struct value_type<pointer_const<T>> {typedef T const type;};
template <typename T> struct distance_type<pointer_const<T>> {typedef ssize_t type;};

template <typename T> inline pointer_const<T> addressof(T const& x) {
    return &x;
}

template <typename T> struct fn_deref<pointer_const<T>> {
	inline ValueType<pointer_const<T>>& operator() (pointer_const<T> i) const {
		return *i;
	}
};

template <typename T> inline ValueType<pointer_const<T>> const& source(pointer_const<T> i) {return deref(i);}

//----------------------------------------------------------------------------
// Basic Concepts

template <typename T, typename S> struct SameType {
    BOOST_CONCEPT_USAGE(SameType) {
        same_type(x, y);
    }
private:
    static T const& x;
    static S const& y;
};

//----------------------------------------------------------------------------

template <typename T, int N> struct Procedure {
    BOOST_CONCEPT_USAGE(Procedure) {
        static_assert(arity<T>() - 1 == N, "incorrect arity");
    }
};

template <typename T> struct FunctionalProcedure {
    BOOST_CONCEPT_USAGE(FunctionalProcedure) {
        typedef decltype(&T::operator()) type;
    }
};

template <typename T> struct Predicate {
    BOOST_CONCEPT_USAGE(Predicate) {
        BOOST_CONCEPT_ASSERT((FunctionalProcedure<T>));
        BOOST_CONCEPT_ASSERT((SameType<ResultType<T>, bool>));
    }
};

template <typename T, int N> struct HomogeneousFunctionN {
    BOOST_CONCEPT_USAGE(HomogeneousFunctionN) {
        BOOST_CONCEPT_ASSERT((SameType<Domain<T>, InputType<T, N>>));
        BOOST_CONCEPT_ASSERT((HomogeneousFunctionN<T, N - 1>));
    }
};
template <typename T> struct HomogeneousFunctionN<T, 1> {};

template <typename T> struct HomogeneousFunction {
    BOOST_CONCEPT_USAGE(HomogeneousFunction) {
        BOOST_CONCEPT_ASSERT((HomogeneousFunctionN<T, arity<T>() - 1>));
    }
};

template <typename T> struct TotallyOrdered {
    BOOST_CONCEPT_USAGE(TotallyOrdered) {
        b = (x < y);
    }
private:
    static T const x;
    static T const y;
    static bool b;
};

template <typename T> struct Regular {
    BOOST_CONCEPT_USAGE(Regular) {
        BOOST_CONCEPT_ASSERT((TotallyOrdered<T>));
        b = (x == y);
        b = (x != y);
        y = x;
        T z;
        y = z;
        y = T();
        T w(x);
        z = w;
    }
private:
    static T const x;
    static T y;
    static bool b;
};

template <typename T> ValueType<T> const& source(T);
template <typename T> struct Readable {
    BOOST_CONCEPT_USAGE(Readable) {
        same_type(source(x), v);
    }
private:
    static T const x;
    static ValueType<T> const& v;
};

template <typename T> ValueType<T>& sink(T);
template <typename T> struct Writable {
    BOOST_CONCEPT_USAGE(Writable) {
        sink(x) = y;
    }
private:
    static T x;
    static ValueType<T> const y;
};

template <typename T> struct Mutable {
    BOOST_CONCEPT_USAGE(Mutable) {
        BOOST_CONCEPT_ASSERT((Readable<T>));
        BOOST_CONCEPT_ASSERT((Writable<T>));
        deref(x) = y;
        same_type(deref(x), y);
    }
private:
    static T x;
    static ValueType<T> const y;
};

template <typename T> struct fn_successor {
	T operator() (T);
};
template <typename T> inline T successor(T t) {
	return fn_successor<T>()(t);
}
//template <typename T> T successor(T);
template <typename T> struct Iterator {
    BOOST_CONCEPT_USAGE(Iterator) {
        same_type(successor(x), x);
    }
private:
    static T const x;
};

template <typename T> struct ForwardIterator {
    BOOST_CONCEPT_USAGE(ForwardIterator) {
        same_type(successor(x), x);
    }
private:
    static T const x;
};

template <typename T> void set_successor(T, T);
template <typename I> struct LinkedForwardIterator {
    BOOST_CONCEPT_USAGE(LinkedForwardIterator) {
        BOOST_CONCEPT_ASSERT((ForwardIterator<I>));
        set_successor(i, i);
    }
private:
    static I i;
};

template <typename I, typename P> inline BOOST_CONCEPT_REQUIRES(
    ((ForwardIterator<I>))
    ((Mutable<I>))
    ((Procedure<P, 1>))
    ((SameType<InputType<P, 1>, ValueType<I>>))
    ,(void))
foreach(I i, P proc) {
    while(i != nullptr) {
        proc(deref(i));
        i = successor(i);
    }
}

template <typename T> T predecessor(T);
template <typename T> struct BidirectionalIterator {
    BOOST_CONCEPT_USAGE(BidirectionalIterator) {
        BOOST_CONCEPT_ASSERT((ForwardIterator<T>));
        same_type(predecessor(x), x);
    }
private:
    static T const x;
};

/*
template <typename T> struct ForwardLinker {
    BOOST_CONCEPT_USAGE(ForwardLinker) {
        BOOST_CONCEPT_ASSERT((ForwardIterator<IteratorType<T>>));
        set_link(x, x);
    }
private:
    static T const set_link;
    static IteratorType<T> x;
};
*/

template <typename T> struct IndexedIterator {
    BOOST_CONCEPT_USAGE(IndexedIterator) {
        BOOST_CONCEPT_ASSERT((BidirectionalIterator<T>));
        same_type(x + s, x);
        same_type(x - s, x);
        same_type(x - x, s);
    }
private:
    static T const x;
    static DistanceType<T> const s;
};

template <typename T> struct Linearizable {
    BOOST_CONCEPT_USAGE(Linearizable) {
        BOOST_CONCEPT_ASSERT((ForwardIterator<IteratorType<T>>));
        same_type(begin(x), i);
        same_type(end(x), i);
        same_type(size(x), s);
        same_type(empty(x), b);
        same_type(x[s], v);
    }
private:
    T x;
    static IteratorType<T> const i;
    static ValueType<T> const v;
    static SizeType<T> const s;
    static bool const b;
};

template <typename T> T twice(T);
template <typename T> T half_nonnegative(T);
template <typename T> T binary_scale_down_nonnegative(T, unsigned int);
template <typename T> T binary_scale_up_nonnegative(T, unsigned int);
template <typename T> bool positive(T);
template <typename T> bool negative(T);
template <typename T> bool zero(T);
template <typename T> bool one(T);
template <typename T> bool even(T);
template <typename T> bool odd(T);
template <typename T> struct Integer {
    BOOST_CONCEPT_USAGE(Integer) {
		BOOST_CONCEPT_ASSERT((BidirectionalIterator<T>));
        n = twice(n);
        n = half_nonnegative(n);
        n = binary_scale_down_nonnegative(n, n);
        n = binary_scale_up_nonnegative(n, n);
        b = positive(n);
        b = negative(n);
        b = zero(n);
        b = one(n);
        b = even(n);
        b = odd(n);
    }
private:
    static T n;
    static bool b;
};

template <typename T> struct Relation {
    BOOST_CONCEPT_USAGE(Relation) {
        BOOST_CONCEPT_ASSERT((Predicate<T>));
        BOOST_CONCEPT_ASSERT((HomogeneousFunction<T>));
        BOOST_CONCEPT_ASSERT((Procedure<T, 2>));
    }
};

//----------------------------------------------------------------------------

template <> struct fn_successor<int> {
	inline int operator()(int n) {return n + 1;}
};
//template <> inline int successor(int n) {return n + 1;}
template <> inline int predecessor(int n) {return n - 1;}
template <> inline int twice(int n) {return n + n;}
template <> inline int half_nonnegative(int n) {return n >> 1;}
template <> inline int binary_scale_down_nonnegative(int n, unsigned int k) {return n >> k;}
template <> inline int binary_scale_up_nonnegative(int n, unsigned int k) {return n << k;}
template <> inline bool positive(int n) {return n > 0;}
template <> inline bool negative(int n) {return n < 0;}
template <> inline bool zero(int n) {return n == 0;}
template <> inline bool one(int n) {return n == 1;}
template <> inline bool even(int n) {return (n & 1) == 0;}
template <> inline bool odd(int n) {return (n & 1) != 0;} 

BOOST_CONCEPT_ASSERT((Integer<int>));

template <> struct fn_successor<unsigned int> {
	inline unsigned int operator()(unsigned int n) {return n + 1;}
};
//template <> inline unsigned int successor(unsigned int n) {return n + 1;}
template <> inline unsigned int predecessor(unsigned int n) {return n - 1;}
template <> inline unsigned int twice(unsigned int n) {return n + n;}
template <> inline unsigned int half_nonnegative(unsigned int n) {return n >> 1;}
template <> inline unsigned int binary_scale_down_nonnegative(unsigned int n, unsigned int k) {return n >> k;}
template <> inline unsigned int binary_scale_up_nonnegative(unsigned int n, unsigned int k) {return n << k;}
template <> inline bool positive(unsigned int n) {return true;}
template <> inline bool negative(unsigned int n) {return false;}
template <> inline bool zero(unsigned int n) {return n == 0;}
template <> inline bool one(unsigned int n) {return n == 1;}
template <> inline bool even(unsigned int n) {return (n & 1) == 0;}
template <> inline bool odd(unsigned int n) {return (n & 1) != 0;}

BOOST_CONCEPT_ASSERT((Integer<unsigned int>));

//----------------------------------------------------------------------------

template <typename T> struct fn_successor<pointer<T>> {
	inline pointer<T> operator()(pointer<T> i) {return i + 1;}
};
template <typename T> struct fn_successor<pointer_const<T>> {
	inline pointer_const<T> operator()(pointer_const<T> i) {return i + 1;}
};
//template <typename T> inline pointer<T> successor(pointer<T> i) {return i + 1;}
//template <typename T> inline pointer_const<T> successor(pointer_const<T> i) {return i + 1;}

template <typename T> inline pointer<T> predecessor(pointer<T> i) {return i - 1;}
template <typename T> inline pointer_const<T> predecessor(pointer_const<T> i) {return i - 1;}

BOOST_CONCEPT_ASSERT((IndexedIterator<pointer<int>>));
BOOST_CONCEPT_ASSERT((IndexedIterator<pointer_const<int>>));

//----------------------------------------------------------------------------

template <typename T> inline BOOST_CONCEPT_REQUIRES(
    ((Regular<T>)),
    (UnderlyingType<T>&))
underlying_ref(T& x) throw() {
    return reinterpret_cast<UnderlyingType<T>&>(x);
}

template <typename T> inline BOOST_CONCEPT_REQUIRES(
    ((Regular<T>)),
    (void))
swap(T& x, T& y) throw() {
    UnderlyingType<T> tmp(std::move(underlying_ref(x)));   
    underlying_ref(x) = std::move(underlying_ref(y));
    underlying_ref(y) = std::move(tmp);
}

template <typename T0, typename T1> struct pair {
    BOOST_CONCEPT_ASSERT((Regular<T0>));
    BOOST_CONCEPT_ASSERT((Regular<T1>));
    pair() {}
    pair(T0 const& m0, T1 const& m1) : m0(m0), m1(m1) {}
    T0 m0;
    T1 m1;
};

template <typename I0, typename I1, typename R> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I0>))
    ((Readable<I1>))
    ((Iterator<I0>))
    ((Iterator<I1>))
    ((Relation<R>))
    ((SameType<ValueType<I0>, ValueType<I1>>))
    ((SameType<ValueType<I0>, Domain<R>>))
    ,(pair<I0, I1>))
find_mismatch(I0 f0, I0 l0, I1 f1, I1 l1, R r) {
    // Precondition: readable_bounded_range(f0, l0)
    // Precondition: readable_bounded_range(f1, l1)
    while (f0 != l0 && f1 != l1 && r(source(f0), source(f1))) {
        f0 = successor(f0);
        f1 = successor(f1);
    } 
    return pair<I0, I1>(f0, f1);
}

template <typename I0, typename I1, typename R> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I0>))
    ((Readable<I1>))
    ((Iterator<I0>))
    ((Iterator<I1>))
    ((Relation<R>))
    ((SameType<ValueType<I0>, ValueType<I1>>))
    ((SameType<ValueType<I0>, Domain<R>>))
    ,(bool))
lexicographical_equivalent(I0 f0, I0 l0, I1 f1, I1 l1, R r) {
    // Precondition: readable_bounded_range(f0, l0)
    // Precondition: readable_bounded_range(f1, l1)
    // Precondition: equivalence(r)
    pair<I0, I1> p = find_mismatch(f0, l0, f1, l1, r);
    return p.m0 == l0 && p.m1 == l1;
}

template <typename I0, typename I1, typename R> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I0>))
    ((Readable<I1>))
    ((Iterator<I0>))
    ((Iterator<I1>))
    ((Relation<R>))
    ((SameType<ValueType<I0>, ValueType<I1>>))
    ((SameType<ValueType<I0>, Domain<R>>))
    ,(bool))
lexicographical_compare(I0 f0, I0 l0, I1 f1, I1 l1, R r) {
    // Precondition: readable_bounded_range(f0, l0)
    // Precondition: readable_bounded_range(f1, l1)
    // Precondition: weak_ordering(r)
    while (true) {
        if (f1 == l1) return false;
        if (f0 == l0) return true;
        if (r(source(f0), source(f1))) return true;
        if (r(source(f1), source(f0))) return false;
        f0 = successor(f0);
        f1 = successor(f1);
    }
}

template <typename T> struct equal {
    bool operator() (T const& x, T const& y) {
        return x == y;
    }
};

template <typename T> struct less {
    BOOST_CONCEPT_ASSERT((TotallyOrdered<T>));
    bool operator() (T const& x, T const& y) {
        return x < y;
    }
};

template <typename I0, typename I1> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I0>))
    ((Readable<I1>))
    ((Iterator<I0>))
    ((Iterator<I1>))
    ((SameType<ValueType<I0>, ValueType<I1>>))
    ,(bool))
lexicographical_equal(I0 f0, I0 l0, I1 f1, I1 l1) {
    return lexicographical_equivalent(f0, l0, f1, l1, equal<ValueType<I0>>());
};

template <typename I0, typename I1> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I0>))
    ((Readable<I1>))
    ((Iterator<I0>))
    ((Iterator<I1>))
    ((SameType<ValueType<I0>, ValueType<I1>>))
    ,(bool))
lexicographical_less(I0 f0, I0 l0, I1 f1, I1 l1) {
    return lexicographical_compare(f0, l0, f1, l1, less<ValueType<I0>>());
};


template <typename N> inline BOOST_CONCEPT_REQUIRES(
    ((Integer<N>))
    ,(bool))
count_down(N& n) {
    // Precondition: n >= 0
    if (zero(n)) return false;
    n = predecessor(n);
    return true;
}

template <typename I, typename O> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I>))
    ((Iterator<I>))
    ((Writable<O>))
    ((Iterator<O>))
    ((SameType<ValueType<I>, ValueType<O>>))
    ,(void))
copy_step(I& f_i, O& f_o) {
    // Precondition: source(f_i) && sink(f_o) are defined
    sink(f_o) = source(f_i);
    f_i = successor(f_i);
    f_o = successor(f_o);
}

template <typename I, typename O> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I>))
    ((Iterator<I>))
    ((Writable<O>))
    ((Iterator<O>))
    ((SameType<ValueType<I>, ValueType<O>>))
    ,(O))
copy(I f_i, I l_i, O f_o) {
    while (f_i != l_i) copy_step(f_i, f_o);
    return f_o;
}

template <typename I, typename O, typename N> inline BOOST_CONCEPT_REQUIRES(
    ((Readable<I>))
    ((Iterator<I>))
    ((Writable<O>))
    ((Iterator<O>))
    ((Integer<N>))
    ((SameType<ValueType<I>, ValueType<O>>))
    ,(pair<I, O>))
copy_n(I f_i, N n, O f_o) {
    // Precondition: non_overlapped_forward(f_i, f_i+n, f_o, f_o+n)
    while (count_down(n)) copy_step(f_i, f_o);
    return pair<I, O>(f_i, f_o);
}

//----------------------------------------------------------------------------
// RAII Dynamic Array

template <typename T> struct array;

template <typename T> struct underlying_array {
private:
    pointer<T> data;
    SizeType<array<T>> size;
};

template <typename T> struct array_base {
    array_base& operator= (array_base const& b) = delete;
    explicit array_base(SizeType<array<T>> n = 0) : data((n == 0) ? nullptr : new T[n]), size(n) {}
    explicit array_base(array_base const& b) throw() : data(b.data), size(b.size) {}
    ~array_base() throw() {
        delete data;
    }
    pointer<T> data;
    SizeType<array<T>> size;
};

template <typename T> struct array {
    BOOST_CONCEPT_ASSERT((Regular<ValueType<array>>));
// Regular
    explicit array(SizeType<array<T>> n = 0) : base(n) {}
    array(array const& b) : base(b.base.size) {
        std::copy_n(b.base.data, b.base.size, base.data);
        base.size = b.base.size;
    }
    array(array&& b) : base(b.base) {
        b.base.data = nullptr;
        b.base.size = 0;
    }
    array& operator= (array const& b) {
        assert(b.base.size == base.size);
        std::copy_n(b.base.data, b.base.size, base.data);
        base.size = b.base.size;
    }
// Linearizable
    friend IteratorType<array> begin(array& a) {
        return a.base.data;
    }
    friend IteratorConstType<array> begin(array const& a) {
        return a.base.data;
    }
    friend IteratorType<array> end(array& a) {
        return a.base.data + a.base.size;
    }
    friend IteratorConstType<array> end(array const& a) {
        return a.base.data + a.base.size;
    }
    friend SizeType<array> size(array const& a) {
        return a.base.size;
    }
    friend bool empty(array const& a) {
        return a.base.size == 0;
    }
    ValueType<array>& operator[] (SizeType<array> const d) {
        return base.data[d];
    }
    ValueType<array> const& operator[] (SizeType<array> const d) const {
        return base.data[d];
    }
private:
    array_base<T> base;
};

template <typename T> inline bool operator== (array<T> const& a, array<T> const& b) {
    return lexicographical_equal(begin(a), end(a), begin(b), end(b));
}
template <typename T> inline bool operator!= (array<T> const& a, array<T> const& b) {
    return !lexicographical_equal(begin(a), end(a), begin(b), end(b));
}
template <typename T> inline bool operator< (array<T> const& a, array<T> const& b) {
    return lexicographical_less(begin(a), end(a), begin(b), end(b));
}

template <typename T> struct underlying_type<array<T>> {typedef underlying_array<T> type;};
template <typename T> struct iterator_type<array<T>> {typedef pointer<T> type;};
template <typename T> struct iterator_const_type<array<T>> {typedef pointer_const<T> type;};
template <typename T> struct size_type<array<T>> {typedef unsigned int type;};
template <typename T> struct value_type<array<T>> {typedef T type;};

BOOST_CONCEPT_ASSERT((Regular<array<int>>));
BOOST_CONCEPT_ASSERT((Linearizable<array<int>>));
BOOST_CONCEPT_ASSERT((Regular<IteratorType<array<int>>>));
BOOST_CONCEPT_ASSERT((Mutable<IteratorType<array<int>>>));
BOOST_CONCEPT_ASSERT((IndexedIterator<IteratorType<array<int>>>));
BOOST_CONCEPT_ASSERT((Readable<IteratorConstType<array<int>>>));
BOOST_CONCEPT_ASSERT((IndexedIterator<IteratorConstType<array<int>>>));

template <typename T> struct underlying_sack {
private:
    array_base<T> base;
    SizeType<array<T>> size;
};

template <typename T> struct sack {
    BOOST_CONCEPT_ASSERT((Regular<T>));
// Regular
    explicit sack(SizeType<sack> s = 0) : base(s), size(0) {}
    sack(sack const& b) : base(b.base.size), size(b.size) {
        copy_n(b.base.data, b.size, base.data);
    }
    sack(sack&& b) : base(), size(0) {
        swap(b.base.data, base.data);
        swap(b.base.size, base.size);
        swap(b.size, size);

    }
    sack& operator= (sack b) {
        swap(b.base.data, base.data);
        swap(b.base.size, base.size);
        swap(b.size, size);
        return *this;
    }
// Linearizable
    friend IteratorType<sack> begin(sack& a) {
        return a.base.data;
    }
    friend IteratorConstType<sack> begin(sack const& a) {
        return a.base.data;
    }
    friend IteratorType<sack> end(sack& a) {
        return a.base.data + a.size;
    }
    friend IteratorConstType<sack> end(sack const& a) {
        return a.base.data + a.size;
    }
    friend SizeType<sack> size(sack const& a) {
        return a.size;
    }
    friend void set_size(sack& a, SizeType<sack> const d) {
        a.size = d;
    }
    friend bool empty(sack const& a) {
        return a.size == 0;
    }
    ValueType<sack>& operator[] (SizeType<sack> const d) {
        return base.data[d];
    }
    ValueType<sack> const& operator[] (SizeType<sack> const d) const {
        return base.data[d];
    }
// Sack
    friend void clear(sack& a) {
        a.size = 0;
    }
    friend void add(sack& a, ValueType<sack> const v) {
        a.base.data[a.size++] = v;
    }
    friend void remove(sack& a, IteratorConstType<sack> i) {
        *const_cast<IteratorType<sack>>(i) = a.base.data[--a.size];
    }
private:
    array_base<T> base;
    SizeType<array<T>> size;
};

template <typename T> inline bool operator== (sack<T> const& a, sack<T> const& b) {
    return lexicographical_equal(begin(a), end(a), begin(b), end(b));
}
template <typename T> inline bool operator!= (sack<T> const& a, sack<T> const& b) {
    return !lexicographical_equal(begin(a), end(a), begin(b), end(b));
}
template <typename T> inline bool operator< (sack<T> const& a, sack<T> const& b) {
    return lexicographical_less(begin(a), end(a), begin(b), end(b));
}

template <typename T> struct underlying_type<sack<T>> {typedef underlying_sack<T> type;};
template <typename T> struct iterator_type<sack<T>> {typedef IteratorType<array<T>> type;};
template <typename T> struct iterator_const_type<sack<T>> {typedef IteratorConstType<array<T>> type;};
template <typename T> struct size_type<sack<T>> {typedef SizeType<array<T>> type;};
template <typename T> struct value_type<sack<T>> {typedef ValueType<array<T>> type;};

BOOST_CONCEPT_ASSERT((Regular<sack<int>>));
BOOST_CONCEPT_ASSERT((Linearizable<sack<int>>));

//----------------------------------------------------------------------------

template <typename T> struct D2Coordinate {
    BOOST_CONCEPT_USAGE(D2Coordinate) {
        same_type(up(x), x);
        same_type(down(x), x);
        same_type(left(x), x);
        same_type(right(x), x);
    }
private:
    static T const x;
};

template <typename T> struct IndexedD2Coordinate {
    BOOST_CONCEPT_USAGE(IndexedD2Coordinate) {
        BOOST_CONCEPT_ASSERT((D2Coordinate<T>));
        same_type(add_cols(x, s), x);
        same_type(add_rows(x, t), x);
        same_type(add(x, s, t), x);
    }
private:
    static T x;
    static int const s, t;
};

template <typename T> struct NonEmptyRectangularizable {
    BOOST_CONCEPT_USAGE(NonEmptyRectangularizable) {
        same_type(topleft(x), i);
        same_type(topright(x), i);
        same_type(bottomleft(x), i);
        same_type(bottomright(x), i);
        same_type(rows(x), s);
        same_type(cols(x), s);
        same_type(x(s, s), v);
    }
private:
    static T x;
    static IteratorType<T> const i; 
    static ValueType<T> const v;
    static SizeType<T> const s;
};

template <typename T> struct NonEmptyCircularIterator {
    BOOST_CONCEPT_USAGE(NonEmptyCircularIterator) {
        same_type(successor(x), x);
    }
private:
    static T const x;
};

template <typename T> struct LinkedNonEmptyCircularIterator {
    BOOST_CONCEPT_USAGE(LinkedNonEmptyCircularIterator) {
        BOOST_CONCEPT_ASSERT((NonEmptyCircularIterator<T>));
        set_successor(x, x);
    }
private:
    static T x;
};

template <typename T> struct DisjointSet {
    BOOST_CONCEPT_USAGE(DisjointSet) {
        BOOST_CONCEPT_ASSERT((ForwardIterator<T>));
        same_type(rank(x), s);
    }
private:
    static T const x;
    static WeightType<T> const s;
};

template <typename T> struct LinkedDisjointSet {
    BOOST_CONCEPT_USAGE(LinkedDisjointSet) {
        BOOST_CONCEPT_ASSERT((LinkedForwardIterator<T>));
        BOOST_CONCEPT_ASSERT((DisjointSet<T>));
        set_rank(x, s);
    }
private:
    static T x;
    static WeightType<T> const s;
};

template <typename T> struct RegionCoordinate {
    BOOST_CONCEPT_USAGE(RegionCoordinate) {
        u = superset(t);
        v = subset(t);
        w = disjoint_set(t);
        v = subset(u);
        w = disjoint_set(u);
        u = superset(v);
        w = disjoint_set(v);
        u = superset(w);
        v = subset(w);
    }
private:
    static T t;
    static SupersetType<T> u;
    static SubsetType<T> v;
    static DisjointSetType<T> w;
};

template <typename T> struct RegionSuperset {
    BOOST_CONCEPT_USAGE(RegionSuperset) {
        u = subset(t);
        v = disjoint_set(t);
        t = superset(u);
        v = disjoint_set(u);
        t = superset(v);
        u = subset(v);
    }
private:
    static T t;
    static SubsetType<T> u;
    static DisjointSetType<T> v;
};

template <typename T> struct RegionSubset {
    BOOST_CONCEPT_USAGE(RegionSubset) {
        u = subset(t);
        v = disjoint_set(t);
        t = superset(u);
        v = disjoint_set(u);
        t = superset(v);
        u = subset(v);
    }
private:
    static SupersetType<T> t;
    static T u;
    static DisjointSetType<T> v;
};

template <typename T> struct RegionDisjointset {
    BOOST_CONCEPT_USAGE(RegionDisjointset) {
        u = subset(t);
        v = disjoint_set(t);
        t = superset(u);
        v = disjoint_set(u);
        t = superset(v);
        u = subset(v);
    }
private:
    static SupersetType<T> t;
    static SubsetType<T> u;
    static T v;
};

template <typename T> struct Showable {
    BOOST_CONCEPT_USAGE(Showable) {
        show(x);
    }
private:
    static T const x;
};

template <typename T> inline BOOST_CONCEPT_REQUIRES(
    ((Showable<T>)),
    (void))
show(T const& i) {
    std::cout << i;
}

template <typename T> struct Random {
public:
    BOOST_CONCEPT_USAGE(Random)
    {
        same_type(random(v), v);
    }
private:
    static T random;
    static uint32_t v;
};


struct xor_shift {
    xor_shift(xor_shift const&) = delete;
    xor_shift& operator= (xor_shift const&) = delete;
    xor_shift() {
        uint64_t random_seed[2];
        std::ifstream random_fs;

        random_fs.exceptions(std::ifstream::failbit | std::ifstream::badbit);
        random_fs.open("/dev/urandom", std::ifstream::binary);
        random_fs.read(reinterpret_cast<char*>(random_seed), sizeof(random_seed));
        random_fs.close();

        s0 = random_seed[0];
        s1 = random_seed[1];
    }
    explicit xor_shift(uint64_t l0, uint64_t l1)
        : s0(l0)
        , s1(l1)
        {}
    uint32_t operator() (uint32_t const scale) {
        uint64_t const l0 = s1;
        uint64_t l1 = s0;
        l1 ^= l1 << 23;
        s0 = l0;
        l1 ^= l0 ^ (l1 >> 17) ^ (l0 >> 26);
        s1 = l1;
        return static_cast<uint32_t>((((l0 + l1) & 0xffffffff) * scale) >> 32);
    }
private:
    uint64_t s0;
    uint64_t s1;
};

BOOST_CONCEPT_ASSERT((Random<xor_shift>));

//----------------------------------------------------------------------------
// disjoint set container and iterators.

template <typename T> struct region {
    pointer<region> canonical;
    pointer<region> successor;
    unsigned int rank;
    T value;
};

template <typename T> inline bool operator== (region<T> const& a, region<T> const& b) {
    return &a == &b;
}
template <typename T> inline bool operator!= (region<T> const& a, region<T> const& b) {
    return &a != &b;
}
template <typename T> inline bool operator<  (region<T> const& a, region<T> const& b) {
    return &a < &b;
}

BOOST_CONCEPT_ASSERT((Regular<region<int>>));



template <typename T> struct region_superset : region<T> {};
template <typename T> struct region_subset : region<T> {};
template <typename T> struct region_canonical : region<T> {};

template <typename T> inline pointer<region_superset<T>> superset(pointer<region<T>> i) {
    return reinterpret_cast<pointer<region_superset<T>>>(i);
}

template <typename T> inline pointer_const<region_superset<T>> superset(pointer_const<region<T>> i) {
    return reinterpret_cast<pointer_const<region_superset<T>>>(i);
}

template <typename T> inline pointer<region_subset<T>> subset(pointer<region<T>>i) {
    return reinterpret_cast<pointer<region_subset<T>>>(i);
}

template <typename T> inline pointer_const<region_subset<T>> subset(pointer_const<region<T>> i) {
    return reinterpret_cast<pointer_const<region_subset<T>>>(i);
}

template <typename T> inline pointer<region_canonical<T>> disjoint_set(pointer<region<T>> i) {
    return reinterpret_cast<pointer<region_canonical<T>>>(i);
}

template <typename T> inline pointer_const<region_canonical<T>> disjoint_set(pointer_const<region<T>> i) {
    return reinterpret_cast<pointer_const<region_canonical<T>>>(i);
}

template <typename T> struct fn_deref<pointer<region_superset<T>>> {
	inline T& operator() (pointer<region_superset<T>> i) const {
    	return i->value;
	}
};

template <typename T> struct fn_deref<pointer<region_canonical<T>>> {
	inline T& operator() (pointer<region_canonical<T>> i) const {
    	return i->value;
	}
};

//template <typename T> inline T& deref(pointer<region_subset<T>> i) {
//    return i->value;
//}

//template <typename T> inline T& deref(pointer<region_canonical<T>> i) {
//    return i->value;
//}

template <typename T> inline T const& source(pointer_const<region_superset<T>> i) {
    return i->value;
}

template <typename T> inline T const& source(pointer_const<region_subset<T>> i) {
    return i->value;
}

template <typename T> inline T const& source(pointer_const<region_canonical<T>> i) {
    return i->value;
}

template <typename T> struct fn_successor<pointer<region_subset<T>>> {
	inline pointer<region_subset<T>> operator() (pointer<region_subset<T>> i) {
		return reinterpret_cast<pointer<region_subset<T>>>(i->successor);
	}
};

template <typename T> struct fn_successor<pointer_const<region_subset<T>>> {
	inline pointer_const<region_subset<T>> operator() (pointer_const<region_subset<T>> i) {
		return reinterpret_cast<pointer_const<region_subset<T>>>(i->successor);
	}
};

//template <typename T> inline pointer<region_subset<T>> successor(pointer<region_subset<T>> i) {
//    return reinterpret_cast<pointer<region_subset<T>>>(i->successor);
//}

template <typename T> struct fn_successor<pointer<region_canonical<T>>> {
	inline pointer<region_canonical<T>> operator() (pointer<region_canonical<T>> i) {
		return reinterpret_cast<pointer<region_canonical<T>>>(i->canonical);
	}
};

template <typename T> struct fn_successor<pointer_const<region_canonical<T>>> {
	inline pointer_const<region_canonical<T>> operator() (pointer_const<region_canonical<T>> i) {
		return reinterpret_cast<pointer_const<region_canonical<T>>>(i->canonical);
	}
};

//template <typename T> inline pointer<region_canonical<T>> successor(pointer<region_canonical<T>> i) {
//    return reinterpret_cast<pointer<region_canonical<T>>>(i->canonical);
//}

//template <typename T> inline pointer_const<region_subset<T>> successor(pointer_const<region_subset<T>> i) {
//    return reinterpret_cast<pointer_const<region_subset<T>>>(i->successor);
//}

//template <typename T> inline pointer_const<region_canonical<T>> successor(pointer_const<region_canonical<T>> i) {
//    return reinterpret_cast<pointer_const<region_canonical<T>>>(i->canonical);
//}

template <typename T> inline void set_successor(pointer<region_subset<T>> i, pointer<region_subset<T>> j) {
    i->successor = j;
}

template <typename T> inline void set_successor(pointer<region_canonical<T>> i, pointer<region_canonical<T>> j) {
    i->canonical = j;
}

template <typename T> inline unsigned int rank(pointer_const<region_canonical<T>> i) {
    return i->rank;
}

template <typename T> inline void set_rank(pointer<region_canonical<T>> i, unsigned int rank) {
    i->rank = rank;
}

template <typename T> struct weight_type<pointer<region_canonical<T>>> {typedef unsigned int type;};

template <typename T> struct value_type<pointer<region_superset<T>>> {typedef T type;};
template <typename T> struct value_type<pointer<region_subset<T>>> {typedef T type;};
template <typename T> struct value_type<pointer<region_canonical<T>>> {typedef T type;};

template <typename T> struct value_type<pointer_const<region_superset<T>>> {typedef T type;};
template <typename T> struct value_type<pointer_const<region_subset<T>>> {typedef T type;};
template <typename T> struct value_type<pointer_const<region_canonical<T>>> {typedef T type;};

template <typename T> struct superset_type<pointer<region<T>>> {typedef pointer<region_superset<T>> type;};
template <typename T> struct superset_type<pointer<region_subset<T>>> {typedef pointer<region_superset<T>> type;};
template <typename T> struct superset_type<pointer<region_canonical<T>>> {typedef pointer<region_superset<T>> type;};

template <typename T> struct superset_type<pointer_const<region<T>>> {typedef pointer_const<region_superset<T>> type;};
template <typename T> struct superset_type<pointer_const<region_subset<T>>> {typedef pointer_const<region_superset<T>> type;};
template <typename T> struct superset_type<pointer_const<region_canonical<T>>> {typedef pointer_const<region_superset<T>> type;};

template <typename T> struct subset_type<pointer<region<T>>> {typedef pointer<region_subset<T>> type;};
template <typename T> struct subset_type<pointer<region_superset<T>>> {typedef pointer<region_subset<T>> type;};
template <typename T> struct subset_type<pointer<region_canonical<T>>> {typedef pointer<region_subset<T>> type;};

template <typename T> struct subset_type<pointer_const<region<T>>> {typedef pointer_const<region_subset<T>> type;};
template <typename T> struct subset_type<pointer_const<region_superset<T>>> {typedef pointer_const<region_subset<T>> type;};
template <typename T> struct subset_type<pointer_const<region_canonical<T>>> {typedef pointer_const<region_subset<T>> type;};

template <typename T> struct disjoint_set_type<pointer<region<T>>> {typedef pointer<region_canonical<T>> type;};
template <typename T> struct disjoint_set_type<pointer<region_superset<T>>> {typedef pointer<region_canonical<T>> type;};
template <typename T> struct disjoint_set_type<pointer<region_subset<T>>> {typedef pointer<region_canonical<T>> type;};

template <typename T> struct disjoint_set_type<pointer_const<region<T>>> {typedef pointer_const<region_canonical<T>> type;};
template <typename T> struct disjoint_set_type<pointer_const<region_superset<T>>> {typedef pointer_const<region_canonical<T>> type;};
template <typename T> struct disjoint_set_type<pointer_const<region_subset<T>>> {typedef pointer_const<region_canonical<T>> type;};

BOOST_CONCEPT_ASSERT((Linearizable<array<region<int>>>));
BOOST_CONCEPT_ASSERT((Regular<array<region<int>>>));
BOOST_CONCEPT_ASSERT((RegionSuperset<SupersetType<IteratorType<array<region<int>>>>>));
BOOST_CONCEPT_ASSERT((RegionSubset<SubsetType<IteratorType<array<region<int>>>>>));
BOOST_CONCEPT_ASSERT((RegionDisjointset<DisjointSetType<IteratorType<array<region<int>>>>>));
BOOST_CONCEPT_ASSERT((RegionSuperset<SupersetType<IteratorConstType<array<region<int>>>>>));
BOOST_CONCEPT_ASSERT((RegionSubset<SubsetType<IteratorConstType<array<region<int>>>>>));
BOOST_CONCEPT_ASSERT((RegionDisjointset<DisjointSetType<IteratorConstType<array<region<int>>>>>));



//----------------------------------------------------------------------------
// join two non-empty circular iterators

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((LinkedNonEmptyCircularIterator<I>))
    ,(void))
link_circular(I i, I j) {
    I const tmp(successor(j));
    set_successor(j, successor(i));
    set_successor(i, tmp);
}

//----------------------------------------------------------------------------
// Disjoint set operations
// i == root_successor(i) && j == root_successor(j) => find(i, j) == (i == j)

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((LinkedDisjointSet<I>))
    ,(void))
makeset_wqupc(I i) {
    set_successor(i, i);
    set_rank(i, 0);
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((LinkedForwardIterator<I>))
    ,(I))
find_wqupc(I i) {
    while (successor(successor(i)) != successor(i)) {
        set_successor(i, successor(successor(i)));
        i = successor(i);
    }
    return successor(i);
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((LinkedDisjointSet<I>))
    ,(I))
link_wqupc(I h, I f) {
    // Precondition: i == canonical(i) && j == canonical(j)
    if (rank(h) < rank(f)) {
        set_successor(h, f);
        return f;
    } else if (rank(h) == rank(f)) {
        set_rank(h, rank(h) + 1);
    }
    set_successor(f, h);
    return h;
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((LinkedDisjointSet<I>))
    ,(void))
makeset_eager(I i) {
    set_successor(i, i);
    set_rank(i, 1);
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((ForwardIterator<I>))
    ,(I))
find_eager(I i) {
    return successor(i);
}

namespace {
    template <typename I> inline BOOST_CONCEPT_REQUIRES(
        ((LinkedDisjointSet<I>))
        ,(void))
    link_eager_head(I h, I f) {
        SubsetType<I> k(subset(f));
        do {
            set_successor(disjoint_set(k), h);
            k = successor(k);
        } while (k != subset(f));
        set_rank(h, rank(h) + rank(f));
    }
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((LinkedDisjointSet<I>))
    ,(I))
link_eager(I h, I f) {
    if (rank(h) < rank(f)) {
        link_eager_head(f, h);
        return f;
    } else {
        link_eager_head(h, f);
        return h;
    }
}

//----------------------------------------------------------------------------

struct colour {
    typedef unsigned int type;

    static type const black = 0;
    static type const white = 1;
    static type const empty = 2;
    static type const none = 2;
    static type const out_of_bounds = 3;
    static type const red = 3;

    static type opposite(type const c) {
        return 1 - c;
    }
} colour;

struct node {
    unsigned int pseudo_liberties;
    ::colour::type colour;
    uint8_t neighbours[4];
};

inline void show(node const& n) {
    std::cout << "node{" << n.pseudo_liberties << '}';
}

inline bool operator== (node const& a, node const& b) {
    return addressof(a) == addressof(b);
}
inline bool operator!= (node const& a, node const& b) {
    return addressof(a) != addressof(b);
}
inline bool operator< (node const& a, node const& b) {
    return addressof(a) < addressof(b);
}

BOOST_CONCEPT_ASSERT((Regular<node>));
BOOST_CONCEPT_ASSERT((Showable<node>));

//-----------------------------------------------------------------------------

template <colour::type C, unsigned int N, typename I> inline BOOST_CONCEPT_REQUIRES(
    ((Mutable<I>))
    ((RegionSuperset<I>))
    ((SameType<ValueType<I>, node>))
    ,(void))
clear_node(I const i) {
    set_successor(subset(i), subset(i));
    makeset_eager(disjoint_set(i));
    sink(i).pseudo_liberties = N;
    sink(i).colour = C;
    sink(i).neighbours[colour::black] = sink(i).neighbours[colour::white] = sink(i).neighbours[colour::red] = 4 - N;
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((ForwardIterator<I>))
    ((Mutable<I>))
    ((RegionSuperset<I>))
    ((SameType<ValueType<I>, node>))
    ,(void))
clear_board(I i, DistanceType<I> const w, DistanceType<I> const h, sack<I>& moves) {
    clear(moves);
    // row 0
    clear_node<colour::red, 0>(i);
    i = successor(i);
    for (DistanceType<I> x(1); x < w - 1; ++x) {
        clear_node<colour::red, 1>(i);
        i = successor(i);
    }
    clear_node<colour::red, 0>(i);
    i = successor(i);

    // row 1
    clear_node<colour::red, 1>(i);
    i = successor(i);
    clear_node<colour::none, 2>(i);
    add(moves, i);
    i = successor(i);
    for (DistanceType<I> x(2); x < w - 2; ++x) {
        clear_node<colour::none, 3>(i);
        add(moves, i);
        i = successor(i);
    }
    clear_node<colour::none, 2>(i);
    add(moves, i);
    i = successor(i);
    clear_node<colour::red, 1>(i);
    i = successor(i);

    // rows 2 to h - 3
    for (DistanceType<I> y(2); y < h - 2; ++y) {
        clear_node<colour::red, 1>(i);
        i = successor(i);
        clear_node<colour::none, 3>(i);
        add(moves, i);
        i = successor(i);
        for (DistanceType<I> x(2); x < w - 2; ++x) {
            clear_node<colour::none, 4>(i);
            add(moves, i);
            i = successor(i);
        }
        clear_node<colour::none, 3>(i);
        add(moves, i);
        i = successor(i);
        clear_node<colour::red, 1>(i);
        i = successor(i);
    }

    // row h - 2
    clear_node<colour::red, 1>(i);
    i = successor(i);
    clear_node<colour::none, 2>(i);
    add(moves, i);
    i = successor(i);
    for (DistanceType<I> x(2); x < w - 2; ++x) {
        clear_node<colour::none, 3>(i);
        add(moves, i);
        i = successor(i);
    }
    clear_node<colour::none, 2>(i);
    add(moves, i);
    i = successor(i);
    clear_node<colour::red, 1>(i);
    i = successor(i);

    // row h - 1
    clear_node<colour::red, 0>(i);
    i = successor(i);
    for (DistanceType<I> x(1); x < w - 1; ++x) {
        clear_node<colour::red, 1>(i);
        i = successor(i);
    }
    clear_node<colour::red, 0>(i);
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((ForwardIterator<I>))
    ((Mutable<I>))
    //((RegionSuperset<I>))
    ((SameType<ValueType<I>, node>))
    ,(void))
board_remove(I const i, colour::type const colour) {
    ++(deref(find_eager(disjoint_set(i))).pseudo_liberties);
    --(deref(i).neighbours[colour]);
}

template <typename I> inline BOOST_CONCEPT_REQUIRES(
    ((ForwardIterator<I>))
    ((Mutable<I>))
    ((DisjointSet<I>))
    ((SameType<ValueType<I>, node>))
    ,(bool))
check_suicide(I const i, colour::type const my_colour) {
    return (source(i).colour == colour::red) || ((source(i).colour == my_colour) == (source(i).pseudo_liberties == 0));
}

//----------------------------------------------------------------------------
// Board

struct board {
    typedef array<region<node>> regions;
    typedef sack<SupersetType<IteratorType<regions>>> actions;

    BOOST_CONCEPT_ASSERT((Readable<IteratorConstType<regions>>));
    BOOST_CONCEPT_ASSERT((Mutable<IteratorType<regions>>));
    BOOST_CONCEPT_ASSERT((IndexedIterator<IteratorConstType<regions>>));
    BOOST_CONCEPT_ASSERT((RegionCoordinate<IteratorConstType<regions>>));
    BOOST_CONCEPT_ASSERT((SameType<ValueType<SupersetType<IteratorConstType<regions>>>, node>));

    board(SizeType<regions> const w, SizeType<regions> const h)
        : max_moves(3 * w * h)
        , cols(w)
        , rows(h)
        , r(w * h)
        , moves((w - 1) * (h - 1))
        , ko(nullptr)
        , points {0, 0}
        , passes(0)
        , plies(0)
        , my_colour(colour::black)
        {
            clear_board(superset(begin(r)), w, h, moves);
        }
    friend std::string to_string(board const& b, IteratorConstType<regions> i) {
        static char const* const c("_ABCDEFGHJKLMNOPQRSTUVWXYZ_");
        std::stringstream ss;
        ss << c[(i - begin(b.r)) % b.cols] << ((i - begin(b.r)) / b.cols);
        return ss.str();
    }
    friend bool is_ko(board const& b, SupersetType<IteratorConstType<regions>> const i) {
        return i == b.ko;
    }
    friend bool is_suicide(board const& b, SupersetType<IteratorType<regions>> const i) {
        if (source(i).pseudo_liberties != 0) {
            return false;
        }

        DisjointSetType<IteratorType<regions>> const n(find_eager(disjoint_set(i - b.cols)));
        DisjointSetType<IteratorType<regions>> const w(find_eager(disjoint_set(i - 1)));
        DisjointSetType<IteratorType<regions>> const e(find_eager(disjoint_set(i + 1)));
        DisjointSetType<IteratorType<regions>> const s(find_eager(disjoint_set(i + b.cols)));

        unsigned int const np(source(n).pseudo_liberties);
        unsigned int const wp(source(w).pseudo_liberties);
        unsigned int const ep(source(e).pseudo_liberties);
        unsigned int const sp(source(s).pseudo_liberties);

        --(deref(n).pseudo_liberties);
        --(deref(w).pseudo_liberties);
        --(deref(e).pseudo_liberties);
        --(deref(s).pseudo_liberties);

        bool const suicide = check_suicide(n, b.my_colour)
            && check_suicide(w, b.my_colour)
            && check_suicide(e, b.my_colour)
            && check_suicide(s, b.my_colour);

        sink(n).pseudo_liberties = np;
        sink(w).pseudo_liberties = wp;
        sink(e).pseudo_liberties = ep;
        sink(s).pseudo_liberties = sp;

        return suicide;
    }
    friend bool is_eyelike(board const& b, SupersetType<IteratorConstType<regions>> const i) {
        if (source(i).pseudo_liberties != 0 || source(i).neighbours[b.my_colour] != 4) {
            return false;
        }

        colour::type const op_colour = colour::opposite(b.my_colour);
        int const nwse(b.cols + 1);
        int const nesw(b.cols - 1);

        return (source(i - nwse).colour == op_colour)
            + (source(i - nesw).colour == op_colour)
            + (source(i + nesw).colour == op_colour)
            + (source(i + nwse).colour == op_colour)
            < 1 + (source(i).neighbours[colour::red] < 1);
    }

	friend bool is_legal(board const& b, SupersetType<IteratorType<regions>> const j) {
		return !(is_eyelike(b, j) || is_suicide(b, j) || is_ko(b, j));
	}

    friend void show_board(board const& b) {
        static char const* const cstr("ABCDEFGHJKLMNOPQRSTUVWXYZ");
        SupersetType<IteratorConstType<regions>> i(superset(begin(b.r)));
        std::cout << "    ";
        for (SizeType<regions> x(0); x < b.cols - 2; ++x) {
            std::cout << ' ' << cstr[x];
        }
        std::cout << "\n";
        for (SizeType<regions> y(b.rows); y--;) {
            if (y > 0 && y < b.rows - 1) {
                std::cout << std::setw(2) << (b.cols - 1 - y);
            } else {
                std::cout << "  ";
            }
            for (SizeType<regions> x(0); x < b.cols; ++x) {
                DisjointSetType<IteratorConstType<regions>> j(find_eager(disjoint_set(i)));
                switch(source(j).colour) {
                    case colour::white:
                        //std::cout << "\e[107m";
                        break;
                    case colour::black:
                        std::cout << "\e[7m";
                        break;
                    case colour::red:
                        std::cout << "\e[41;31;2m";
                        break;
                    default:
                        std::cout << "\e[47;2m";
                        break;
                }
                std::cout << std::setw(2) << std::hex << source(j).pseudo_liberties << std::dec << "\e[0m";
                //std::cout << std::setw(2) << std::hex << static_cast<int>(source(j).neighbours[b.my_colour]) << std::dec << "\e[0m";
                i = successor(i);
            }
            std::cout << "\n";
        }
        std::cout << "\n";
    }
    friend void capture(board& b, SupersetType<IteratorType<regions>> const i) {
		colour::type const colour = source(i).colour;
        SupersetType<IteratorType<regions>> j(i);

        do {
            sink(j).colour = colour::none;
            sink(j).pseudo_liberties = 0;
            makeset_eager(disjoint_set(j));
            add(b.moves, j);
            --(b.points[colour]);
            j = superset(successor(subset(j)));
        } while (j != i);

        do {
            board_remove(j - b.cols, colour);
            board_remove(j - 1, colour);
            board_remove(j + 1, colour);
            board_remove(j + b.cols, colour);

            SupersetType<IteratorType<regions>> const k(superset(successor(subset(j))));
            set_successor(subset(j), subset(j));
            j = k;
        } while (j != i);
    }

    template <typename R> friend void benchmark_mc(R& random, unsigned int reps);

    // Game
    friend colour::type player(board const& b) {return b.my_colour;}
    friend actions& actions(board& b) {return b.moves;}
    friend actions const& actions(board const& b) {return b.moves;}
    friend void place_neighbour_ko(board& b, DisjointSetType<IteratorType<regions>> const i, colour::type const my_colour, DisjointSetType<IteratorConstType<regions>>& ko) {
        DisjointSetType<IteratorType<regions>> const j(find_eager(i));
        ++(deref(i).neighbours[my_colour]);
        --(deref(j).pseudo_liberties);
        if (source(j).colour != colour::red && source(j).pseudo_liberties == 0) {
            capture(b, superset(j));
            ko = j;
        }
    }

    friend void place_neighbour(board& b, DisjointSetType<IteratorType<regions>> const i, colour::type const my_colour, colour::type const op_colour, DisjointSetType<IteratorType<regions>>& h) {
        DisjointSetType<IteratorType<regions>> const j(find_eager(i));
        ++(deref(i).neighbours[my_colour]);
        --(deref(j).pseudo_liberties);
        if (source(j).colour == my_colour) {
            if (j != h) {
                DisjointSetType<IteratorType<regions>> const k(link_eager(j, h));
                link_circular(subset(h), subset(j));
                sink(k).pseudo_liberties = source(h).pseudo_liberties + source(j).pseudo_liberties;
                h = k;
            }
        } else if (source(j).colour == op_colour && source(j).pseudo_liberties == 0) {
            capture(b, superset(j));
        }
    }
    friend void result(board& b, IteratorConstType<actions> const j) {
        if (j == nullptr) {
            b.my_colour = colour::opposite(b.my_colour);
            ++(b.passes);
            ++(b.plies);
            return;
        }

        SupersetType<IteratorType<regions>> const i(source(j));
        colour::type const my_colour(b.my_colour);
        colour::type const op_colour(colour::opposite(my_colour));

        remove(b.moves, j);
        DisjointSetType<IteratorType<regions>> const n = disjoint_set(i - b.cols);
        DisjointSetType<IteratorType<regions>> const w = disjoint_set(i - 1);
        DisjointSetType<IteratorType<regions>> const e = disjoint_set(i + 1);
        DisjointSetType<IteratorType<regions>> const s = disjoint_set(i + b.cols);
        sink(i).colour = my_colour;
        ++(b.points[my_colour]);

        if (source(i).neighbours[op_colour] == 4) {
            DisjointSetType<IteratorConstType<regions>> ko(nullptr);
            unsigned int const a(size(b.moves) + 1);

            place_neighbour_ko(b, n, my_colour, ko);
            place_neighbour_ko(b, w, my_colour, ko);
            place_neighbour_ko(b, e, my_colour, ko);
            place_neighbour_ko(b, s, my_colour, ko);
            b.ko = (size(b.moves) == a) ? superset(ko) : nullptr;
        } else {
            DisjointSetType<IteratorType<regions>> h(disjoint_set(i));

            place_neighbour(b, n, my_colour, op_colour, h);
            place_neighbour(b, w, my_colour, op_colour, h);
            place_neighbour(b, e, my_colour, op_colour, h);
            place_neighbour(b, s, my_colour, op_colour, h);
            b.ko = nullptr;
        }

        b.my_colour = op_colour;
        b.passes = 0;
        ++(b.plies);
    }
    friend bool not_terminal(board const& b) {
        return b.passes < 2 && b.plies < b.max_moves;
    }
    friend int utility(board const& b, colour::type const my_colour) {
        colour::type const op_colour = colour::opposite(my_colour);
        int s(b.points[my_colour] - b.points[op_colour]);
        for (SupersetType<IteratorConstType<regions>> const i : b.moves) {
            s += (source(i).neighbours[my_colour] == 4);
            s -= (source(i).neighbours[op_colour] == 4);
        }
        return s;
    }

    void clear() {
        clear_board(superset(begin(r)), cols, rows, moves);
        ko = nullptr;
        points[colour::black] = 0;
        points[colour::white] = 0;
        passes = 0;
        plies = 0;
        my_colour = colour::black;
    }

    /*
    board& operator= (board const& b) {
        copy_n(begin(b.r), size(b.r), begin(r));
        copy_n(begin(b.moves), size(b.moves), begin(moves));
        set_size(moves, size(b.moves));
        ko = b.ko;
        points[0] = b.points[0];
        points[1] = b.points[1];
        passes = b.passes;
        plies = b.plies;
        my_colour = b.my_colour;
        return *this;
    }
    */

    board& operator= (board const& b) = delete;

    void push() {
        stack.emplace_back(r, moves, ko, points, passes, plies, my_colour);
    }

    void copy(unsigned int i = 0) {
        board_save const& s(stack[stack.size() - (i + 1)]);
        r = s.r;
        moves = s.moves;
        ko = s.ko;
        points[0] = s.points[0];
        points[1] = s.points[1];
        passes = s.passes;
        plies = s.plies;
        my_colour = s.my_colour;
    }

    void pop() {
        stack.pop_back();
    }
        
private:
    unsigned int const max_moves;
    unsigned int const cols;
    unsigned int const rows;

    regions r;
    actions moves;
    IteratorConstType<regions> ko;
    unsigned int points[2];
    unsigned int passes;
    unsigned int plies;
    colour::type my_colour;

    struct board_save {
        regions r;
        actions moves;
        IteratorConstType<regions> ko;
        unsigned int points[2];
        unsigned int passes;
        unsigned int plies;
        colour::type my_colour;

        board_save(
            regions const& r, 
            actions const& moves,
            IteratorConstType<regions> const& ko,
            unsigned int const* points,
            unsigned int const& passes,
            unsigned int const& plies,
            colour::type const& my_colour
        )
        : r(r)
        , moves(moves)
        , ko(ko)
        , points{points[0], points[1]}
        , passes(passes)
        , plies(plies)
        , my_colour(my_colour)
        {}
    };

    std::vector<board_save> stack {};
};

template<> struct regions_type<board>{typedef typename board::regions type;};
template<> struct actions_type<board>{typedef typename board::actions type;};

//----------------------------------------------------------------------------

template <typename Random, typename Board> struct genmove {
    genmove(Random& r) : random(r) {}

    IteratorConstType<ActionsType<Board>> operator() (Board& b) {
        ActionsType<Board> const& as(actions(b));
        IteratorConstType<ActionsType<Board>> const k(begin(as) + random(size(as)));
        IteratorConstType<ActionsType<Board>> j(k);

        while (is_eyelike(b, source(j)) || is_suicide(b, source(j)) || is_ko(b, source(j))) {
            j = successor(j);
            if (j == end(as)) j = begin(as);
            if (j == k) return nullptr;
        }
        return j;
    }

private:
	Random& random;
};

template <typename Board, typename Genmove> inline void playout(Board& b, Genmove& g) {
    while (not_terminal(b)) result(b, g(b));
}

//----------------------------------------------------------------------------

template <typename Random> void benchmark_mc(Random& random, unsigned int reps) {
    board b(11, 11);
    unsigned int plies(0);
    unsigned int games(0);
    unsigned int black_wins(0);
    unsigned int white_wins(0);
    genmove<Random, board> g(random);

    result(b, g(b)); // play one move
    b.push(); // save board state.
    show_board(b);

    double const t1(rtime());
    while (games < reps) {
        b.copy(); // copy board at top of stack
        show_board(b);
        playout(b, g);
        if (b.plies < b.max_moves) {
            show_board(b);
            plies += b.plies;
            float const s(static_cast<float>(utility(b, colour::black)) - 6.5f);
			//std::cout << s << ' ';
            black_wins += (s > 0.0f);
            white_wins += (s < 0.0f);
            ++games;
        } else {
            std::cout << "MAX MOVES EXCEEDED\n";
        }
    }
    double const t2(rtime());

    std::cout << plies << " plies over " << games << " in " << t2 - t1 << " seconds.\n" << std::setprecision(16)
        << static_cast<double>(plies) / static_cast<double>(reps) << " plies per game, "
        << static_cast<double>(reps) / (1000.0L * (t2 - t1)) << "k games per second.\n"
        << static_cast<double>(black_wins) * 100.0 / static_cast<double>(reps) << "% black / "
        << static_cast<double>(white_wins) * 100.0 / static_cast<double>(reps) << "% white wins\n";

    std::cout << "profile: " << std::setprecision(16) << profile<int>::report() << "\n";
}

template <typename R> inline BOOST_CONCEPT_REQUIRES(
    ((Random<R>))
    ,(void))
benchmark_prng(R& random, unsigned int reps) {
    uint32_t x(0);

    double const t1(rtime());
    for (unsigned int i = reps; i--;) {
        x += random(400);
    }
    double const t2(rtime());

    std::cout << x << " " << ((reps / 1000000.0) / (t2 - t1)) << "M random numbers per second\n";
}

//----------------------------------------------------------------------------

int main() {
    xor_shift x {123456789362436069, 52128862988675123};

    std::cout << "region size: " << sizeof(region<node>) << "B\n";
    std::cout << "board size: " << sizeof(board) << "B\n";

    //benchmark_prng(x, 1000000000);
    benchmark_mc(x, 1000000);
}

