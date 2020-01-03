#include <iostream>
#include <boost/lexical_cast.hpp>
#include <boost/tokenizer.hpp>
#include <boost/iterator/indirect_iterator.hpp>
#include <boost/iterator/zip_iterator.hpp>
#include <boost/core/null_deleter.hpp>
#include <boost/range/algorithm/set_algorithm.hpp>
#include <boost/range/adaptor/map.hpp>
#include <boost/function_output_iterator.hpp>
#include <boost/iterator/function_input_iterator.hpp>
#include <boost/iterator/counting_iterator.hpp>
#include <map>
#include <algorithm>
#include <numeric>
#include <stdexcept>
#include <set>
#include <type_traits>
#include <valarray>
#include <sstream>
#include <unordered_set>
#include "combinations.h"
#include "hash_map.hpp"

template<typename T>
const std::string& getLine(T&& writeIfNeeded) {
    static std::string tmp;
    std::cout << writeIfNeeded;
    std::getline(std::cin, tmp);
    return tmp;
}

template<typename To, typename T>
To getLineAndValidate(T&& writeIfNeeded) {
    while(true) {
        try {
            return boost::lexical_cast<To>(getLine(writeIfNeeded));
        } catch (const boost::bad_lexical_cast&) {}
    }
}

template <typename T>
T count_each_repetable_permutation(T elements, T place) {
    if (!elements && place)
        throw std::invalid_argument("Empty set repeated not zero times");
    if (elements > 0 && place * std::log2l(elements) > std::log2l(std::numeric_limits<T>::max()))
        throw std::overflow_error("count_each_repetable_permutation is bigger than T size");
    
    T res = 1;
    while (place) {
        if (place & 1)
            res *= elements;
        place >>= 1;
        elements *= elements;
    }
    return res;
}

template<typename T, typename U>
auto count_each_repetable_permutation(T begin, T end, U place_count) {
    if constexpr (std::is_signed_v<U>)
        if (place_count < 0)
            throw std::invalid_argument("Count can not be negative");

    return count_each_repetable_permutation<std::uintmax_t>(std::distance(begin, end), place_count);
}

template<typename T, typename U>
auto count_each_repetable_permutation(T begin, T end, U place_begin, U place_end) {
    return count_each_repetable_permutation(begin, end, std::distance(place_begin, place_end));
}

template<typename T, typename U, typename L>
auto for_each_repetable_permutation_impl(T begin, T end, U place_begin, U place_end, L&& lambda) {
    std::fill(place_begin, place_end, begin);

    bool nEnd;
    do {
        if (lambda())
            break;

        nEnd = false;
        for (auto curr = place_end; curr != place_begin;)
            if (++*--curr == end)
                *curr = begin;
            else {
                nEnd = true;
                break;
            }
            
    } while (nEnd);
    
    return std::forward<L>(lambda);
}

template<typename T, typename U, typename L>
auto for_each_repetable_permutation(T begin, T end, U place_begin, U place_end, L&& lambda) {
    if (begin == end && place_begin != place_end)
        throw std::invalid_argument("Empty set repeated not zero times");

    for_each_repetable_permutation_impl(begin, end, place_begin, place_end, [&lambda,
        indirect_begin = boost::make_indirect_iterator(place_begin),
        indirect_end = boost::make_indirect_iterator(place_end)] {
        if constexpr (std::is_same_v<std::invoke_result_t<L,decltype(indirect_begin), decltype(indirect_end)>, void>) {
            lambda(indirect_begin, indirect_end);
            return false;
        } else
            return lambda(indirect_begin, indirect_end);
    });

    return std::forward<L>(lambda);
}

template<typename T, typename U, typename L>
auto for_each_repetable_permutation(T begin, T end, U place_count, L&& lambda) {
    if constexpr (std::is_signed_v<U>)
        if (place_count < 0)
            throw std::invalid_argument("Count can not be negative");

    std::vector<T> place(place_count);
    return for_each_repetable_permutation(begin, end, std::begin(place), std::end(place), std::forward<L>(lambda));
}


template <typename T>
T count_each_repetable_combination(T elements, T place) {
    if (!elements && place)
        throw std::invalid_argument("Empty set repeated not zero times");
    
    return count_each_combination(elements - 1, place);
}

template<typename T, typename U>
auto count_each_repetable_combination(T begin, T end, U place_count) {
    if constexpr (std::is_signed_v<U>)
        if (place_count < 0)
            throw std::invalid_argument("Count can not be negative");

    return count_each_repetable_combination<std::uintmax_t>(std::distance(begin, end), place_count);
}

template<typename T, typename U>
auto count_each_repetable_combination(T begin, T end, U place_begin, U place_end) {
    return count_each_repetable_combination(begin, end, std::distance(place_begin, place_end));
}

template<typename T, typename U, typename L>
auto for_each_repetable_combination_impl(T begin, T end, U place_begin, U place_end, L&& lambda) {
    std::fill(place_begin, place_end, begin);

    auto step = [&] {
        for (auto curr = place_end; curr != place_begin;)
            if (++*--curr != end) {
                std::fill(std::next(curr), place_end, *curr);
                return true;
            }
        return false;
    };

    do {
        if (lambda())
            break;
    } while (step());
    
    return std::forward<L>(lambda);
}

template<typename T, typename U, typename L>
auto for_each_repetable_combination(T begin, T end, U place_begin, U place_end, L&& lambda) {
    if (begin == end && place_begin != place_end)
        throw std::invalid_argument("Empty set repeated not zero times");

    for_each_repetable_combination_impl(begin, end, place_begin, place_end, [&lambda,
        indirect_begin = boost::make_indirect_iterator(place_begin),
        indirect_end = boost::make_indirect_iterator(place_end)] {
        if constexpr (std::is_same_v<std::invoke_result_t<L,decltype(indirect_begin), decltype(indirect_end)>, void>) {
            lambda(indirect_begin, indirect_end);
            return false;
        } else
            return lambda(indirect_begin, indirect_end);
    });

    return std::forward<L>(lambda);
}


template<typename T, typename U, typename L>
auto for_each_repetable_combination(T begin, T end, U place_count, L&& lambda) {
    if constexpr (std::is_signed_v<U>)
        if (place_count < 0)
            throw std::invalid_argument("Count can not be negative");

    std::vector<T> place(place_count);
    return for_each_repetable_combination(begin, end, std::begin(place), std::end(place), std::forward<L>(lambda));
}


template<typename T, typename U, typename L>
auto for_each_repetable_combination_least_one_impl(T begin, T end, U place_begin, U place_end, L&& lambda) {
    std::fill(place_begin, place_end, begin);

    auto step = [&] {
        for (auto curr = place_end; curr != place_begin;)
            if (auto next = std::next(*--curr); next != end && curr != place_begin && *std::prev(curr) == *curr) {
                std::fill(curr, place_end, next);
                return true;
            }
        return false;
    };

    do {
        if (lambda())
            break;
    } while (step());
    
    return std::forward<L>(lambda);
}

template<typename T, typename U, typename L>
auto for_each_repetable_combination_least_one(T begin, T end, U place_begin, U place_end, L&& lambda) {
    if (begin == end && place_begin != place_end)
        throw std::invalid_argument("Empty set repeated not zero times");

    for_each_repetable_combination_least_one_impl(begin, end, place_begin, place_end, [&lambda,
        indirect_begin = boost::make_indirect_iterator(place_begin),
        indirect_end = boost::make_indirect_iterator(place_end)] {
        if constexpr (std::is_same_v<std::invoke_result_t<L,decltype(indirect_begin), decltype(indirect_end)>, void>) {
            lambda(indirect_begin, indirect_end);
            return false;
        } else
            return lambda(indirect_begin, indirect_end);
    });

    return std::forward<L>(lambda);
}


template<typename T, typename U, typename L>
auto for_each_repetable_combination_least_one(T begin, T end, U place_count, L&& lambda) {
    if constexpr (std::is_signed_v<U>)
        if (place_count < 0)
            throw std::invalid_argument("Count can not be negative");

    std::vector<T> place(place_count);
    return for_each_repetable_combination_least_one(begin, end, std::begin(place), std::end(place), std::forward<L>(lambda));
}


namespace impl {
    template<bool partitioning, class ResultTypeX = void, class BidirIter, class Equality>
    auto getPartitions(BidirIter first, BidirIter last, Equality&& eq) {
        using ResultType = std::conditional_t<std::is_same_v<ResultTypeX, void>, std::pair<BidirIter, BidirIter>, ResultTypeX>;
        using DiffType = decltype(std::distance(first, last));

        std::vector<ResultType> groupPtrs;
        auto emplace = [&groupPtrs] ([[maybe_unused]] BidirIter from, BidirIter to) {
            if constexpr (std::is_constructible_v<ResultType, BidirIter, BidirIter>)
                groupPtrs.emplace_back(from, to);
            else if constexpr (std::is_constructible_v<ResultType, BidirIter, DiffType>)
                groupPtrs.emplace_back(from, std::distance(from, to));
            else if constexpr (std::is_constructible_v<ResultType, DiffType, BidirIter>)
                groupPtrs.emplace_back(std::distance(from, to), to);
            else if constexpr (std::is_constructible_v<ResultType, BidirIter>)
                groupPtrs.emplace_back(to);
            else if constexpr (std::is_constructible_v<ResultType, DiffType>)
                groupPtrs.emplace_back(std::distance(from, to));
            else static_assert(!std::is_same_v<ResultType, ResultType>, "And now what?");
        };

        if constexpr (partitioning) { // O(n * group), O(n) swap 
            for(auto curr{first}, next{curr}; curr != last; curr = next)
                emplace(curr, next = std::partition(std::next(curr), last, std::bind(eq, std::placeholders::_1, *curr)));
        } else {  // O(n)
            auto findFirstDiff = [last, neq = [&eq](auto&& l, auto&& r) { return !eq(l, r); }](auto from) {
                return std::adjacent_find(from, last, neq);    
            };

            auto prev = first;
            for (auto element = findFirstDiff(prev); element != last; element = findFirstDiff(prev = element))
                emplace(prev, ++element);
            emplace(prev, last);
        }
        return groupPtrs;
    }
    
    template<bool partitioning, class ItType, class ... Types>
    auto getPartitionEnds(ItType&& first, Types&& ... fwd) {
        return getPartitions<partitioning, std::decay_t<ItType>>(std::forward<ItType>(first), std::forward<Types>(fwd)...); 
    }
    
    template<bool partitioning, class ... Types>
    auto getPartitionSizes(Types&& ... fwd) {
        return getPartitions<partitioning, std::size_t>(std::forward<Types>(fwd)...); 
    }
}

template <class K, class InputIter>
std::common_type_t<K, typename std::iterator_traits<InputIter>::value_type>
count_each_multi_permutation(K k, InputIter begin, InputIter end);

template<bool partitioning = false, class BidirIter,
    class Equality = std::equal_to<typename std::iterator_traits<BidirIter>::value_type>>
std::uintmax_t
count_each_multi_permutation(BidirIter first, BidirIter mid, BidirIter last, Equality&& eq = {}) {
    auto&& sizes = impl::getPartitionSizes<partitioning>(first, last, std::forward<Equality>(eq));
    return count_each_multi_permutation<std::uintmax_t>(std::distance(first, mid), sizes.begin(), sizes.end());
}


template<bool partitioning = false, class BidirIter, class Function, 
    class Equality = std::equal_to<typename std::iterator_traits<BidirIter>::value_type>>
Function for_each_multi_permutation(BidirIter first, BidirIter mid, BidirIter last, Function&& f, Equality&& eq = {}) {
    std::vector<BidirIter>&& groupPtrs = impl::getPartitionEnds<partitioning>(first, last, std::forward<Equality>(eq));
    auto kGroupIndices = std::make_unique<std::size_t[]>(std::distance(first, mid));
    for(auto&& [m, groupIt] = std::tuple(first, kGroupIndices.get()); !f(first, mid);) {
        for (std::size_t group{}; m != mid; ++m, *groupIt++ = group)  // O(k + group)
            while (groupPtrs[group] == m)
                groupPtrs[group++] = mid;
        
        while (m != first) { // O(k * group), O(k * group) swap
            --m, --groupIt;
            if (auto itit = groupPtrs.begin() + *groupIt; *itit != last) {
                std::iter_swap(*itit, m);
                for (auto it = (*itit)++; ++*groupIt, *++itit == it; ++*itit);
                ++m, ++groupIt;
                break;
            } else
                for (auto prev = m; itit != groupPtrs.begin();)
                    if (auto it = --*--itit; it != prev)
                        std::iter_swap(prev = it, m);
        }
        if (m == first)
            break;
    }
    
    return std::forward<Function>(f);
}


template <class K, class InputIter>
std::common_type_t<K, typename std::iterator_traits<InputIter>::value_type>
count_each_multi_combination(K k, InputIter begin, InputIter end);

template<bool partitioning = false, class BidirIter,
    class Equality = std::equal_to<typename std::iterator_traits<BidirIter>::value_type>>
std::uintmax_t
count_each_multi_combination(BidirIter first, BidirIter mid, BidirIter last, Equality&& eq = {}) {
    auto&& sizes = impl::getPartitionSizes<partitioning>(first, last, std::forward<Equality>(eq));
    return count_each_multi_combination<std::uintmax_t>(std::distance(first, mid), sizes.begin(), sizes.end());
}

[[maybe_unused]]
auto identity = [](auto&& vs) -> decltype(vs) { return vs; };
template<typename T, typename UIt = decltype(identity) >
void dump(T it, std::size_t n, UIt tr = identity) {
    std::cout << "[";
    if (n) std::cout << tr(*it);
    while (--n > 0) std::cout << " " << tr(*++it);
    std::cout << "]\n";
}

template<bool partitioning = false, class BidirIter, class Function, 
    class Equality = std::equal_to<typename std::iterator_traits<BidirIter>::value_type>>
Function for_each_multi_combination(const BidirIter first, const BidirIter mid, const BidirIter last, Function&& f, Equality&& eq = {}) {
    constexpr bool is_random_access_iterator_v = std::is_base_of_v<std::random_access_iterator_tag, 
        typename std::iterator_traits<BidirIter>::iterator_category>;
    auto&& groupPtrs = impl::getPartitions<partitioning, std::pair<std::ptrdiff_t, BidirIter>>(first, last, std::forward<Equality>(eq));
    const auto k = std::distance(first, mid);

    const auto kGroupIndices = std::make_unique<std::size_t[]>(k);
    const auto kGroupIndicesBegin = kGroupIndices.get(), kGroupIndicesEnd = kGroupIndicesBegin + k;
    
    for (auto&& [groupIndex, place, placeGroup] = std::make_tuple(std::size_t{}, first, kGroupIndicesBegin); 
            place != mid; ++place, *placeGroup++ = groupIndex, --groupPtrs[groupIndex].first)
        while (groupPtrs[groupIndex].second == place)
            groupPtrs[groupIndex++].second = mid;

    while (!f(first, mid)) {
        bool notEnd{};
        for (auto&& [place, placeGrIndex] = std::make_tuple(mid, kGroupIndicesEnd); place != first;) {
            --place, --placeGrIndex;
            if (auto placeGroupPtrIt = groupPtrs.begin() + *placeGrIndex; placeGroupPtrIt->second != last) {
                notEnd = true;

                std::iter_swap(place, placeGroupPtrIt->second++);
                ++placeGroupPtrIt->first;
                
                --(++placeGroupPtrIt)->first;
                ++*placeGrIndex;

                ++place, ++placeGrIndex;
                
                if (place == mid)
                    break;

                const auto kSize = kGroupIndicesEnd - placeGrIndex;
                const auto othFrom = kSize < placeGroupPtrIt->first ? 
                    std::prev(placeGroupPtrIt->second, kSize) : std::prev(placeGroupPtrIt)->second;
                std::ptrdiff_t othDistance;
                
                if constexpr (is_random_access_iterator_v)
                    othDistance = last - othFrom;
                else {
                    othDistance = std::min(kSize, placeGroupPtrIt->first);
                    for (auto it = std::next(placeGroupPtrIt); it != groupPtrs.end(); ++it)
                        othDistance += it->first;
                }
                
                detail::rotate_discontinuous(place, mid, kSize,
                     othFrom, last, othDistance); // O(n), but it can be O(group) - rewrite it
                     
                // the next 2 'for' can be merged somehow?
                std::vector<std::size_t> groupAdd(groupPtrs.size());
                for (auto placeGrIndex2 = placeGrIndex; placeGrIndex2 != kGroupIndicesEnd;) // O(k)
                    for (std::size_t groupIndex = *placeGrIndex2++, &gr = ++groupAdd[groupIndex]; 
                        placeGrIndex2 != kGroupIndicesEnd && groupIndex == *placeGrIndex2; ++placeGrIndex2, ++gr);
                
                for (std::ptrdiff_t diff{}; placeGroupPtrIt != groupPtrs.end(); ++placeGroupPtrIt) { // O(k + group)
                    auto& [count, it] = *placeGroupPtrIt;
                    auto add = groupAdd[placeGroupPtrIt - groupPtrs.begin()];
                    count += add;
                    diff += add;
                    if (placeGrIndex != kGroupIndicesEnd) {
                        auto fill = std::min(kGroupIndicesEnd - placeGrIndex, count);
                        
                        placeGrIndex = std::fill_n(placeGrIndex, fill, placeGroupPtrIt - groupPtrs.begin());
                        count -= fill;
                        diff -= fill;
                    }
                    std::advance(it, diff);
                }
                
                break;
            };
        }
        if (!notEnd) break;
    }
    std::rotate(first, mid, last); // O(n)
    
    return std::forward<Function>(f);
}

template<typename Lambda, typename PlaceIt, typename ElementIt>
auto merged(ElementIt eBegin, ElementIt eMiddle, ElementIt eEnd, PlaceIt pBegin, PlaceIt pEnd, Lambda&& l) {
    std::vector<std::size_t> index_vec(std::distance(pBegin, pEnd));
    std::vector<ElementIt> elements(index_vec.size());
    
    return for_each_repetable_permutation(eBegin, eMiddle == eEnd ? eMiddle : std::next(eMiddle), pBegin, pEnd, [&](auto from, auto to) {
        std::size_t count{};
        for (auto&& [i, bases] = std::tuple{std::size_t{}, from.base()}; bases != to.base(); ++i, ++bases)
            if (*bases == eMiddle) index_vec[i] = count++;

        auto transform = [&](auto it) -> auto& {
            return *it == eMiddle ? elements[index_vec[it - pBegin]] : *it;
        };

        bool end{};
        return for_each_repetable_combination_least_one(eMiddle, eEnd, elements.begin(), elements.begin() + count, [&end, &l, &eMiddle,
            _from = boost::make_indirect_iterator(boost::make_transform_iterator(boost::make_counting_iterator(from.base()), transform)),
            _to =  boost::make_indirect_iterator(boost::make_transform_iterator(boost::make_counting_iterator(to.base()), transform))
        ](auto&& repBegin, auto&& repEnd) {
            return end = l(_from, _to, repBegin == repEnd ? eMiddle : std::next(*std::prev(repEnd.base())));
        }), end;
    }), std::forward<Lambda>(l);
}

template<typename Lambda, typename U, typename ElementIt>
auto merged(ElementIt eBegin, ElementIt eMiddle, ElementIt eEnd, U placeCount, Lambda&& l) {
    std::vector<ElementIt> place(placeCount);
    return merged(eBegin, eMiddle, eEnd, place.begin(), place.end(), std::forward<Lambda>(l));
}

bool test() {
    return true;
}



struct GuessStrategy1 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::size_t minCount{}, minI = static_cast<std::size_t>(-1);
        std::pair<int, int> minPair{};
        bool isPossible{};

        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            std::size_t max = 0;
            std::pair<int, int> maxPair{};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j; ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > max) {
                        maxPair = p;
                        max = c;
                    }
                }
            }
            if (minI == static_cast<std::size_t>(-1) || minCount > max || (minCount == max && !isPossible && possibleIndArray[i])) {
                minCount = max;
                minI = i;
                isPossible = possibleIndArray[i];
                minPair = maxPair;
            }
        }
        dump(minI, minCount, minPair);
        
        return minI;
    }
    
    void dump(std::size_t minI, std::size_t minCount, std::pair<int, int> minPair) const {
        std::cout << "minI: " << minI <<", minCount: " << minCount << " if result is: " << minPair.first << "," << minPair.second << std::endl;
        for (auto from = possibles.begin() + minI*placesToGuess, to = possibles.begin() + (minI+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
    }
};

struct GuessStrategy2 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::tuple<std::size_t, bool, long double> maxX;
        std::optional<std::size_t> max;
        
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            std::tuple<std::size_t, bool, long double> currX{0, possibleIndArray[i], 1};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j - (j == 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > 0) {
                        ++std::get<0>(currX);
                        std::get<2>(currX) *= std::pow(c, 1/14.0);
                    }
                }
            }
            if (!max || maxX < currX) {
                maxX = currX;
                max = i;
                std::cout << *max << " reached: " << std::get<2>(maxX) << std::endl;
            }
        }
        std::cout << "Max is: " << std::get<0>(maxX) << " & " << std::get<1>(maxX) << " & " << std::get<2>(maxX) << std::endl;
        for (auto from = possibles.begin() + *max*placesToGuess, to = possibles.begin() + (*max+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
        return max;
    }
};

struct GuessStrategy3 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::tuple<std::size_t, std::size_t, long double, bool> maxX;
        std::optional<std::size_t> max;
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            decltype(maxX) currX{~0UL, 0, 1, possibleIndArray[i]};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j - (j == 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > 0) {
                        std::get<0>(currX) = std::min(std::get<0>(currX), ~c);
                        ++std::get<1>(currX);
                        std::get<2>(currX) *= std::pow(c, 1/14.0);
                    }
                }
            }
            if (!max || maxX < currX) {
                maxX = currX;
                max = i;
            }
        }
        std::cout << "Max is: " << std::get<0>(maxX) << " & " << std::get<1>(maxX) << " & " << std::get<2>(maxX) << std::endl;
        for (auto from = possibles.begin() + *max*placesToGuess, to = possibles.begin() + (*max+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
        
        return max;
    }
};


struct GuessStrategy4 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::tuple<std::size_t, std::size_t, long double, bool> maxX;
        std::optional<std::size_t> max;
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            decltype(maxX) currX{0, ~0UL, 1, possibleIndArray[i]};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j - (j == 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > 0) {
                        std::get<1>(currX) = std::min(std::get<1>(currX), ~c);
                        ++std::get<0>(currX);
                        std::get<2>(currX) *= std::pow(c, 1/14.0);
                    }
                }
            }
            if (!max || maxX < currX) {
                maxX = currX;
                max = i;
            }
        }
        std::cout << "Max is: " << std::get<0>(maxX) << " & " << std::get<1>(maxX) << " & " << std::get<2>(maxX) << std::endl;
        for (auto from = possibles.begin() + *max*placesToGuess, to = possibles.begin() + (*max+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
        
        return max;
    }
};

struct GuessStrategy5 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::tuple<std::size_t, std::size_t, bool, long double> maxX;
        std::optional<std::size_t> max;
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            decltype(maxX) currX{0, ~0UL, possibleIndArray[i], 1};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j - (j == 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > 0) {
                        std::get<1>(currX) = std::min(std::get<1>(currX), ~c);
                        ++std::get<0>(currX);
                        std::get<3>(currX) *= std::pow(c, 1/14.0);
                    }
                }
            }
            if (!max || maxX < currX) {
                maxX = currX;
                max = i;
            }
        }
        std::cout << "Max is: " << std::get<0>(maxX) << " & " << std::get<1>(maxX) << " & " << std::get<2>(maxX) << std::endl;
        for (auto from = possibles.begin() + *max*placesToGuess, to = possibles.begin() + (*max+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
        
        return max;
    }
};


struct GuessStrategy6 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::tuple<std::size_t, bool, std::size_t, long double> maxX;
        std::optional<std::size_t> max;
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            decltype(maxX) currX{0, possibleIndArray[i], ~0UL, 1};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j - (j == 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > 0) {
                        std::get<2>(currX) = std::min(std::get<2>(currX), ~c);
                        ++std::get<0>(currX);
                        std::get<3>(currX) *= std::pow(c, 1/14.0);
                    }
                }
            }
            if (!max || maxX < currX) {
                maxX = currX;
                max = i;
            }
        }
        std::cout << "Max is: " << std::get<0>(maxX) << " & " << std::get<1>(maxX) << " & " << std::get<2>(maxX) << std::endl;
        for (auto from = possibles.begin() + *max*placesToGuess, to = possibles.begin() + (*max+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
        
        return max;
    }
};


struct GuessStrategy7 {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (!possibleSetCount) return {};
        std::tuple<bool, std::size_t, std::size_t, long double> maxX;
        std::optional<std::size_t> max;
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            decltype(maxX) currX{possibleIndArray[i], 0, ~0UL, 1};
            for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j - (j == 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                    if (c > 0) {
                        std::get<2>(currX) = std::min(std::get<2>(currX), ~c);
                        ++std::get<1>(currX);
                        std::get<3>(currX) *= std::pow(c, 1/14.0);
                    }
                }
            }
            if (!max || maxX < currX) {
                maxX = currX;
                max = i;
            }
        }
        std::cout << "Max is: " << std::get<0>(maxX) << " & " << std::get<1>(maxX) << " & " << std::get<2>(maxX) << std::endl;
        for (auto from = possibles.begin() + *max*placesToGuess, to = possibles.begin() + (*max+1)*placesToGuess; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;
        
        return max;
    }
};

struct GuessStrategy8 {
    GuessStrategy4 gs;
    std::unique_ptr<bool> first = std::make_unique<bool>(true);
    
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray) const {
        if (*first) { *first = false; return 10; }
        return gs(possibleIndArray);
    }
};


struct GuessRecursive {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& possibles;
    const std::valarray<std::pair<int, int>>& results;
    inline std::optional<std::size_t> operator() (const std::valarray<bool>& possibleIndArray, std::size_t level = 3, std::optional<std::size_t> maxLevel = {}) const {
        
        auto size = possibleIndArray[possibleIndArray].size();
        if (level == 0 || size < 2)
            return size;

        if (!maxLevel) maxLevel = level;
        
        std::optional<std::size_t> best;
        std::size_t gMin{};
        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            if (level == *maxLevel) {
                if (i != 0 && i != 1 && i != 10 && i != 11 && i != 102)
                    continue;
                std::cout << std::string((*maxLevel-level)*2, ' ') << "At level " << (*maxLevel-level) << ": " << "Started index: " << i << ": ";
                for (auto from = possibles.begin() + i*placesToGuess, to = possibles.begin() + (i+1)*placesToGuess; from != to; ++from) {
                    std::cout << *from << " ";
                }
                std::cout << std::endl;
            
            }



            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            
            std::optional<std::size_t> max;
            bool skip = false;
            std::stringstream ss;
            for (std::decay_t<decltype(placesToGuess)> j = 0; !skip && j <= placesToGuess; ++j) {
                for (std::decay_t<decltype(placesToGuess)> l = 0; !skip && l <= placesToGuess - j - (j <= 1); ++l) {
                    auto p = std::pair{int(j), int(l)};
                    if (auto childBest = (*this)(possibleIndArray && arr == p, level - 1, maxLevel)) {
                        if (!max || *max < *childBest) {
                            max = childBest;
                        }
                        ss << std::string((*maxLevel-level)*2, ' ') << "At level " << (*maxLevel-level) << ": " << "current max:" << *max << " bests: " << *childBest << " at " << p.first << "," << p.second << std::endl;
                    }
                    if (max && best && *max >= gMin)
                        skip = true;
                }
            }
            if (!skip && max && (!best || gMin > *max)) {
                best = i;
                gMin = *max;
                if (level > 1) {
                    std::cout << ss.str();
                    std::cout << std::string((*maxLevel-level)*2, ' ') << "At level " << (*maxLevel-level) << ": " << "The current winner is with " << gMin << " AKA index: " << i << ": ";
                    for (auto from = possibles.begin() + i*placesToGuess, to = possibles.begin() + (i+1)*placesToGuess; from != to; ++from) {
                        std::cout << *from << " ";
                    }
                    std::cout << std::endl;
                }
            }
        }
        if (*best) {
            std::cout << std::string((*maxLevel-level)*2, ' ') << "At level " << (*maxLevel-level) << ": " << "The best with " << gMin << " AKA index: " << *best << ": ";
            for (auto from = possibles.begin() + *best*placesToGuess, to = possibles.begin() + (*best+1)*placesToGuess; from != to; ++from) {
                std::cout << *from << " ";
            }
            std::cout << std::endl;
        }
        
        return gMin;
    }

};



template<typename DoItType>
struct GuessStrategyIn {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::vector<const char*>& names;
    const std::vector<const char*>& possibles;
    const DoItType& doIt;
    std::string namesS{};
    
    inline std::optional<std::size_t> operator()(const std::valarray<bool>&) {
        if (namesS.empty()) {
            std::stringstream nss;
            for (std::size_t i = 0; i < names.size(); ++i)
                nss << "(" << i << "): " << names[i] << std::endl;
            namesS = nss.str();
        }
        std::istringstream ss{getLine(namesS + "GuessedLine indices: ")};
        std::vector<const char*> res(placesToGuess);
        std::transform(std::istream_iterator<std::size_t>(ss), std::istream_iterator<std::size_t>(), res.begin(), [&](auto&& i) -> const char* {
            if (i >= names.size()) {
                return nullptr;
            } 
            return names.at(i);
        });

        auto findByVector = [](auto& counter, const auto& vec) {
            return [&counter, b = vec.begin(), e = vec.end()](auto&& lhs, auto&& rhs) {
                if (std::equal(lhs, rhs, b, e))
                    return true;
                ++counter;
                return false;
            };
        };

        // stupid search...
        std::size_t counter{};
        doIt(findByVector(counter, res));
        if (counter == possibleSetCount) {
            std::cout << "Can not find this guess :(\n";
            return {};
        }

        std::cout << counter << " [";
        std::copy(possibles.begin() + counter*placesToGuess, possibles.begin() + (counter+1)*placesToGuess, std::ostream_iterator<decltype(*possibles.begin())>(std::cout, " "));
        std::cout << "]\n";
        
        return counter;
    }
};

struct ResultIn {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::valarray<std::pair<int, int>>& results;
    
    inline std::optional<std::pair<int, int>> operator()(const std::valarray<bool>& possibleIndArray, std::size_t guess) const {
        // calculate worst result: 
        auto arr = std::valarray(results[std::slice(guess*possibleSetCount, possibleSetCount, 1)]);
        std::size_t max = 0;
        std::pair<int, int> maxPair{};
        for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
            for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j; ++l) {
                auto p = std::pair{int(j), int(l)};
                auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                std::cout << "At result " << j << " " << l << " the size is: " << c << std::endl;
                if (c > max) {
                    maxPair = p;
                    max = c;
                }
            }
        }
        std::stringstream ss;
        ss << "Worst thing to do is: " << max << " aka: " << maxPair.first << "," << maxPair.second << std::endl;

        std::pair<int, int> result;
        std::istringstream ss2{getLine(ss.str() + "Result: ")};
        ss2 >> result.first >> result.second;

        if (!static_cast<bool>(ss2) || static_cast<std::size_t>(result.first + result.second) > placesToGuess) {
            std::cout << "INVALID result :(\n";
            return {};
        }
        return result;
    }
};

struct ResultWorst {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    const std::valarray<std::pair<int, int>>& results;
    
    inline std::optional<std::pair<int, int>> operator()(const std::valarray<bool>& possibleIndArray, std::size_t guess) const {
        // calculate worst result: 
        auto arr = std::valarray(results[std::slice(guess*possibleSetCount, possibleSetCount, 1)]);
        std::size_t max = 0;
        std::pair<int, int> maxPair{};
        for (std::decay_t<decltype(placesToGuess)> j = 0; j <= placesToGuess; ++j) {
            for (std::decay_t<decltype(placesToGuess)> l = 0; l <= placesToGuess - j; ++l) {
                auto p = std::pair{int(j), int(l)};
                auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                if (c > max || (c > 0 && c == max && (p.second < maxPair.second || (p.second == maxPair.second && p.first < maxPair.first)))) {
                    maxPair = p;
                    max = c;
                }
            }
        }
        return maxPair;
    }

};

struct FinalNo {
    inline std::optional<std::size_t> operator()() const {
        return {};
    }
    
    bool hasNext() const {
        return false;
    }

};

struct FinalIn {
    std::size_t possibleSetCount;
    inline std::optional<std::size_t> operator()() const {
        std::stringstream ss(getLine("Final index is: "));
        std::size_t res;
        if (ss >> res) return res;
        return {};
    }
    
    bool hasNext() const {
        return false;
    }
};

struct FinalAll {
    std::valarray<std::size_t> valarr;
    std::size_t* curr{std::begin(valarr)};
    inline std::optional<std::size_t> operator()() {
        return *curr++;
    }
    
    bool hasNext() const {
        return curr != std::end(valarr);
    }
};

template<typename GuessStrategy, typename ResultStrategy, typename FinalStrategy>
struct Game {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    
    const std::valarray<std::pair<int, int>>& results;
    const std::valarray<bool>& possibleIndArrayOrig;
    const std::valarray<std::size_t>& indArray;
    const std::vector<const char*>& possibles;
    
    GuessStrategy& guess;
    ResultStrategy& result;
    FinalStrategy& finale;
    inline std::optional<std::size_t> operator()() {
        std::optional<std::size_t> index{finale()};
        std::valarray<bool> possibleIndArray = possibleIndArrayOrig;
        std::size_t nTh{1};
        if (index)
            std::cout << "Try to guess: " << *index << std::endl;
        
        while (true) {
            // some advice
            std::optional<std::size_t> guessing;
            std::pair<int, int> resultPair{};
            do {
                while (!guessing) {
                    guessing = guess(possibleIndArray);
                }
                
                
                if (index) {
                    resultPair = results[(*guessing) * possibleSetCount + *index];
                } else if (auto res = result(possibleIndArray, *guessing)) {
                    resultPair = *res;
                } else {
                    guessing.reset();
                }
            } while(!guessing);
            std::cout << "Result is: " << resultPair.first << " " << resultPair.second << std::endl;

            possibleIndArray &= std::valarray(results[std::slice((*guessing) * possibleSetCount, possibleSetCount, 1)]) == resultPair;
            
            std::valarray<std::size_t> currPoss = indArray[possibleIndArray];
            std::size_t currentCount = currPoss.size();
            for (auto & guessIndex : std::valarray(currPoss[std::slice(0, std::min(10ul, currentCount), 1)])) {
                for (auto from = possibles.begin() + guessIndex * placesToGuess, to = possibles.begin() + (guessIndex + 1) * placesToGuess; from != to; ++from) {
                    std::cout << *from << " ";
                }
                std::cout << std::endl;
            }
            if (currentCount > 10)
                std::cout << "..." << std::endl;
            
            if (currentCount == 1) {
                std::cout << "FOUND SOLUTION" << std::endl;
                if (*std::begin(currPoss) != *guessing)
                    ++nTh;
                return nTh;
            } else if (currentCount == 0) {
                std::cout << "NO SOLUTION" << std::endl;
                return {};
            }
            ++nTh;
            std::cout << nTh << ". try. Current possible solution count: " << currentCount << std::endl;
        }
    }
};


template<typename GuessStrategy>
struct Tree {
    std::size_t placesToGuess;
    std::size_t possibleSetCount;
    
    const std::valarray<std::pair<int, int>>& results;
    const std::valarray<bool>& possibleIndArrayOrig;
    const std::valarray<std::size_t>& indArray;
    const std::vector<const char*>& possibles;
    
    GuessStrategy& guess;
    
    struct TreeNode {
        const TreeNode* parent;
        std::valarray<bool> possibleIndArray;
        std::size_t guessed;
        bool valid;
        std::size_t others;

        std::vector<std::pair<std::pair<int, int>, TreeNode>> childs;
        template<typename IndArray>
        TreeNode(const Tree& t, IndArray&& possibleIndArray, const TreeNode* parent = nullptr, int level = 0, const std::pair<int, int>* f = nullptr) 
            : parent(parent)
            , possibleIndArray(std::forward<IndArray>(possibleIndArray))
            // , guessed(t.guess(this->possibleIndArray).value())
            // , valid(this->possibleIndArray[guessed])
        {
            std::valarray<std::size_t> validIndices(t.indArray[this->possibleIndArray]);
            if (validIndices.size() == 1) {
                guessed = validIndices[0];
                others = 0;
                valid = true;
            } else {
                guessed = t.guess(this->possibleIndArray).value();
                valid = this->possibleIndArray[guessed];
                others = validIndices.size() - valid;
            }
            if (f) {
                std::cerr << std::string(level*2, ' ') << level << "|";
                std::cerr << f->first << " " << f->second << "|";
            }
            for (auto from = t.possibles.begin() + guessed*t.placesToGuess, to = t.possibles.begin() + (guessed+1)*t.placesToGuess; from != to; ++from) {
                std::cerr << *from << " ";
            }
            std::cerr << (valid ? " OK" : "NOK");
            if (others)
                std::cerr << " -- And other " << others;
            std::cerr << std::endl;
            
            if (others) {
                childs.reserve((t.placesToGuess+1) * (t.placesToGuess+2) / 2 - 2);
                // foreach result, if has child...
                for (std::decay_t<decltype(placesToGuess)> j = 0; j <= t.placesToGuess; ++j) {
                    for (std::decay_t<decltype(placesToGuess)> l = 0; l <= t.placesToGuess - j - (j <= 1); ++l) {
                        std::pair<int, int> res{j, l};
                        
                        std::valarray<bool> thisResult = this->possibleIndArray && std::valarray(t.results[std::slice(guessed*t.possibleSetCount, t.possibleSetCount, 1)]) == res;
                        if (thisResult.max()) {
                            childs.emplace_back(std::piecewise_construct, std::forward_as_tuple(res), std::forward_as_tuple(t, std::move(thisResult), this, level+1, &res));
                        }
                    }
                }
            }
        }
        
        void operator()(const Tree& t, int level = 0) {
            if (others)
                for (auto& node : boost::adaptors::values(childs))
                    node(t, level+1);
        }
    };
    
    inline auto operator()() {
        return std::make_unique<TreeNode>(*this, possibleIndArrayOrig);
    }
};
int main() {
    if (test())
        return 0;

    std::string names_string_container;
    std::vector<const char*> names;
    do {
        names_string_container = getLine("The colors name (separated by spaces): ");

        for (auto pch = std::strtok(names_string_container.data(), " "); pch; pch = std::strtok(nullptr, " "))
            names.emplace_back(pch);
    } while (names.empty());

    std::cout << "-> n = " << names.size() << std::endl;

    const auto k = getLineAndValidate<std::size_t>("Places to guess: ");
    const auto has_repeat = k > names.size() || getLineAndValidate<bool>("Enabled duplicate (0/1): "),
         can_repeat_guess = has_repeat || getLineAndValidate<bool>("But can we guess with duplicate (0/1): ");
    
    const auto doIt = [&](auto&& what) {
        if (has_repeat || can_repeat_guess) {
            for_each_repetable_permutation(names.begin(), names.end(), k, what);
        } else {
            for_each_permutation(names.begin(), names.begin() + k, names.end(), what);
        }
    };

    std::vector<const char*> possibles;
    if (has_repeat || can_repeat_guess) {
        possibles.resize(count_each_repetable_permutation<std::uintmax_t>(names.size(), k) * k);
    } else {
        possibles.resize(count_each_permutation(k, names.size() - k) * k);
    }
    doIt([ptr = possibles.begin()](auto&& lhs, auto&& rhs) mutable {
        ptr = std::copy(lhs, rhs, ptr);
        return false;
    });
    auto possibleSetCount = possibles.size() / k;
    
    auto calc = [myHash = [mh = std::hash<std::uintptr_t>{}](const char* lhs) {
        return mh(reinterpret_cast<std::uintptr_t>(lhs));
    }](auto& result, auto b1, auto e1, auto b2, auto e2) {
        emilib::HashMap<const char*, int, decltype(myHash)> uoms{b1, e1, myHash};

        for (; b2 != e2; ++b2,++b1) {
            if (*b1 == *b2)
                --result.first, ++result.second;
            if (auto&& it = uoms.find(*b2); it != std::end(uoms) && --it->second>=0)
                ++result.first;
        }
        return (result);
    };

    std::valarray<std::pair<int, int>> results(possibleSetCount*possibleSetCount);
    std::valarray<bool> possibleIndArrayOrig (true, possibleSetCount);
    for (auto i = 0ull; i < possibles.size(); i += k) {
        results[i/k + i/k*possibleSetCount] = {0, k};
        for (auto j = i+k; j < possibles.size(); j += k) {
            results[i/k + j/k*possibleSetCount] = calc(results[j/k + i/k*possibleSetCount],
                possibles.begin() + i,
                possibles.begin() + i + k,
                possibles.begin() + j,
                possibles.begin() + j + k);
        }
        if (!has_repeat && can_repeat_guess && std::unordered_set<const char*>(possibles.begin() + i, possibles.begin() + i + k).size() < k)
            possibleIndArrayOrig[i/k] = false;
    }
    std::cout << "Results generated: " << results.size() << std::endl;
    std::valarray<std::size_t> indArray (possibleSetCount);
    std::iota(std::begin(indArray), std::end(indArray), std::size_t{0});
    
    std::cout << "Start possible count: " << std::valarray(possibleIndArrayOrig[possibleIndArrayOrig]).size() << std::endl;
    
    //GuessStrategy1 guessStr{k, possibleSetCount, possibles, results};
    //GuessStrategy2 guessStr{k, possibleSetCount, possibles, results};
    //GuessStrategy3 guessStr{k, possibleSetCount, possibles, results};
    GuessStrategy4 guessStr{k, possibleSetCount, possibles, results};
    //GuessStrategy5 guessStr{k, possibleSetCount, possibles, results};
    //GuessStrategy6 guessStr{k, possibleSetCount, possibles, results};
    //GuessStrategy7 guessStr{k, possibleSetCount, possibles, results};
    //GuessStrategy8 guessStr{{k, possibleSetCount, possibles, results}};
    std::map<int, int> countOfGuess;
    
    if (false) {
        Tree<decltype(guessStr)> tree{k, possibleSetCount, results, 
            possibleIndArrayOrig, indArray, possibles, guessStr};
            
        [[maybe_unused]]
        auto nodePtr = tree();
        (*nodePtr)(tree);
        
        auto walker = [&](auto& walk, auto& node, int level = 1) -> void {
            if (node.valid) ++countOfGuess[level];
            for (auto& chNode : boost::adaptors::values(node.childs))
                walk(walk, chNode, level+1);
        };
        walker(walker, *nodePtr);
    } else if (true) {
        //GuessStrategyIn<decltype(doIt)> guessStr{k, possibleSetCount, names, possibles, doIt};
    
        FinalNo finalStr;
        // FinalIn finalStr{possibleSetCount};
        // FinalAll finalStr{std::valarray(indArray[possibleIndArrayOrig])};
        
        //ResultIn resultStr{k, possibleSetCount, results};
        ResultWorst resultStr{k, possibleSetCount, results};

        auto game = Game<decltype(guessStr), decltype(resultStr), decltype(finalStr)>{k, possibleSetCount, results, possibleIndArrayOrig, indArray, possibles, guessStr, resultStr, finalStr};
        
        do {
            if (auto opt = game()) {
                std::cout << *opt << std::endl;
                ++countOfGuess[*opt];
            }
        } while (finalStr.hasNext());
    } else {
        //GuessRecursive guessStr{k, possibleSetCount, possibles, results};
        if (auto bestlevel2 = guessStr(possibleIndArrayOrig/*, 2*/)) {
            std::cout << *bestlevel2 << std::endl;
        }
    }

    std::cout << "\nGuessing rate:\n";
    for (auto&& [n, count] : countOfGuess) {
        std::cout << n << " guess count: " << count << std::endl;
    }
}
