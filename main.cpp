#include <iostream>
#include <boost/lexical_cast.hpp>
#include <boost/tokenizer.hpp>
#include <boost/iterator/indirect_iterator.hpp>
#include <boost/iterator/zip_iterator.hpp>
#include <boost/core/null_deleter.hpp>
#include <boost/range/algorithm/set_algorithm.hpp>
#include <boost/function_output_iterator.hpp>
#include <map>
#include <algorithm>
#include <numeric>
#include <stdexcept>
#include <set>
#include <type_traits>
#include <valarray>
#include <sstream>
#include "combinations.h"

template<typename T>
const std::string& getLine(T&& writeIfNeeded) {
    static std::string tmp;
    std::cout << writeIfNeeded;
    std::getline(std::cin, tmp);
    return tmp;
}

template <typename T>
T count_each_repetable_combination(T elements, T place) {
    if (elements > 0 && place * std::log2l(elements) >= sizeof(T) * 8 - std::is_signed_v<T>)
        throw std::overflow_error("count_each_repetable_combination is bigger than T size");
    
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
auto count_each_repetable_combination(T begin, T end, U place_count) {
    return count_each_repetable_combination<std::uintmax_t>(std::distance(begin, end), place_count);
}

template<typename T, typename U>
auto count_each_repetable_combination(T begin, T end, U place_begin, U place_end) {
    return count_each_repetable_combination(begin, end, std::distance(place_begin, place_end));
}

template<typename T, typename U, typename L>
auto for_each_repetable_combination_impl(T begin, T end, U place_begin, U place_end, L&& lambda) {
    std::fill(place_begin, place_end, begin);

    auto step = [rBeginPlace = std::make_reverse_iterator(place_end),
        rEndPlace = std::make_reverse_iterator(place_begin), &begin, &end] {
        for (auto rCurr = rBeginPlace; rCurr != rEndPlace; ++rCurr)
            if (++*rCurr == end)
                *rCurr = begin;
            else return true;
        return false;
    };    

    do {
        if (lambda(boost::indirect_iterator{place_begin}, boost::indirect_iterator{place_end}))
            break;
    } while (step());
}


template<typename T, typename U, typename L>
auto for_each_repetable_combination(T begin, T end, U place_begin, U place_end, L&& lambda) {
    if (begin == end && place_begin != place_end)
        throw std::invalid_argument("Empty set repeated not zero times");
    return for_each_repetable_combination_impl(begin, end, place_begin, place_end, lambda);
}

template<typename T, typename U, typename L>
auto for_each_repetable_combination(T begin, T end, U count, L&& lambda) {
    std::vector<T> place(count);
    return for_each_repetable_combination(begin, end, std::begin(place), std::end(place), std::forward<L>(lambda));
}


template<typename T>
std::pair<int, int> calc(T b1, T e1, T b2, T e2) {
    std::pair<int, int> result{};
    boost::range::set_intersection(std::multiset(b1, e1), std::multiset(b2, e2), boost::make_function_output_iterator([&](auto&&) { ++result.first; }));

    result.second = (int)std::count_if(boost::make_zip_iterator(boost::make_tuple(b1, b2)),
        boost::make_zip_iterator(boost::make_tuple(e1, e2)), [](auto&& tup) { return boost::get<0>(tup) == boost::get<1>(tup); });
result.first -= result.second;
    return result;
}


int main() {
    auto names_string_container = getLine("A színek neve space-el elválasztva: ");

    std::vector<const char*> names;
    for (auto pch = std::strtok(names_string_container.data(), " "); pch; pch = std::strtok(nullptr, " "))
        names.emplace_back(pch);

    std::cerr << "Tehát n = " << names.size() << std::endl;
    const auto k = boost::lexical_cast<std::size_t>(getLine("Kitalálandó helyek száma: "));
    const auto has_repeat = boost::lexical_cast<bool>(getLine("Lehet duplikált (0/1): ")),
         can_repeat_guess = has_repeat || boost::lexical_cast<bool>(getLine("Lehet duplikált találás (0/1): "));
    
    const auto doIt = [&](auto&& what) {
        if (has_repeat || can_repeat_guess) {
            for_each_repetable_combination(names.begin(), names.end(), k, what);
        } else {
            for_each_permutation(names.begin(), names.begin() + k, names.end(), what);
        }
    };

    std::vector<const char*> possibles;
    if (has_repeat || can_repeat_guess) {
        possibles.resize(count_each_repetable_combination<std::uintmax_t>(names.size(), k) * k);
    } else {
        possibles.resize(count_each_permutation(k, names.size() - k) * k);
    }
    doIt([ptr = possibles.begin()](auto&& lhs, auto&& rhs) mutable {
        ptr = std::copy(lhs, rhs, ptr);
        return false;
    });

    std::valarray<std::pair<int, int>> results(possibles.size()/k*possibles.size()/k);
    std::valarray<bool> possibleIndArray (true, possibles.size()/k);
    for (auto i = 0ull; i < possibles.size(); i += k) {
        for (auto j = 0ull; j < possibles.size(); j += k) {
            results[j/k + i*possibles.size()/k/k] = calc(possibles.begin() + i, possibles.begin() + i + k, possibles.begin() + j, possibles.begin() + j + k);
        }
        if (!has_repeat && can_repeat_guess && std::set(possibles.begin() + i, possibles.begin() + i + k).size() < k)
            possibleIndArray[i/k] = false;
    }
    std::cout << "Results generated: " << results.size() << std::endl;
    std::valarray<std::size_t> indArray (possibles.size()/k);
    std::iota(std::begin(indArray), std::end(indArray), std::size_t{0});
    while (true) {
        for (std::size_t i = 0; i < names.size(); ++i)
            std::cout << "(" << i << "): " << names[i] << std::endl;
        std::istringstream ss{getLine("GuessedLine indices: ")};
        auto ii = std::istream_iterator<std::size_t>(ss);
        std::vector<const char*> res(k);
        std::transform(ii, std::istream_iterator<std::size_t>(), res.begin(), [&](auto&& i) -> const char* {
            if (i >= names.size()) {
                return nullptr;
            } 
            return names.at(i);
        });
        // buta módon kikeressük...
        std::size_t counter{};
        doIt([&counter, &res](auto&& lhs, auto&& rhs) {
            if (std::equal(lhs, rhs, res.begin(), res.end()))
                return true;
            ++counter;
            return false;
        });
        if (counter == possibles.size()/k) {
            std::cout << "Nem találtam meg :(\n";
            continue;
        }
        std::cout << counter << " [";
        std::copy(possibles.begin() + counter*k, possibles.begin() + counter*k+k, std::ostream_iterator<decltype(*possibles.begin())>(std::cout, " "));
        std::cout << "]\n";


        ss = std::istringstream{getLine("Result: ")};
        auto ii2 = std::istream_iterator<int>(ss);
        std::pair<int, int> p{*ii2, 0}; p.second = *++ii2;
        if (!static_cast<bool>(ss) || static_cast<std::size_t>(p.first + p.second) > k) {
            std::cout << "INVALID result :(\n";
            continue;
        }

        possibleIndArray &= std::valarray(results[std::slice(counter*possibles.size()/k, possibles.size()/k, 1)]) == p;
        
        std::valarray<std::size_t> currPoss = indArray[possibleIndArray];
        for (auto & index : currPoss) {
            for (auto from = possibles.begin() + index*k, to = possibles.begin() + index*k + k; from != to; ++from) {
                std::cout << *from << " ";
            }
            std::cout << std::endl;
        }
        
        if (currPoss.size() == 1) {
            std::cout << "FOUND SOLUTION" << std::endl;
            break;
        } else if (currPoss.size() == 0) {
            std::cout << "NO SOLUTION" << std::endl;
            break;
        }
        
        // some advice
        
    }
}
