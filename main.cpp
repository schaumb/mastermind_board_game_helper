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


int main() {
    std::vector<const char*> names;
    std::string names_string_container;
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

    auto findByVector = [](auto& counter, const auto& vec) {
        return [&counter, b = vec.begin(), e = vec.end()](auto&& lhs, auto&& rhs) {
            if (std::equal(lhs, rhs, b, e))
                return true;
            ++counter;
            return false;
        };
    };
    
    std::cout << "Start possible count: " << std::valarray(possibleIndArrayOrig[possibleIndArrayOrig]).size() << std::endl;

    std::valarray<bool> possibleIndArray = possibleIndArrayOrig;
    std::optional<std::size_t> index{};
    while (true) {
        // some advice

        std::size_t minCount{}, minI = static_cast<std::size_t>(-1);
        std::pair<int, int> minPair{};
        bool isPossible{};

        for (auto i = static_cast<decltype(possibleSetCount)>(0); i < possibleSetCount; ++i) {
            auto arr = std::valarray(results[std::slice(i*possibleSetCount, possibleSetCount, 1)]);
            std::size_t max = 0;
            std::pair<int, int> maxPair{};
            for (std::decay_t<decltype(k)> j = 0; j <= k; ++j) {
                for (std::decay_t<decltype(k)> l = 0; l <= k - j; ++l) {
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
        std::cout << "minI: " << minI <<", minCount: " << minCount << " if result is: " << minPair.first << "," << minPair.second << std::endl;
        for (auto from = possibles.begin() + minI*k, to = possibles.begin() + minI*k + k; from != to; ++from) {
            std::cout << *from << " ";
        }
        std::cout << std::endl;

        std::optional<std::size_t> guess {minI};
        std::pair<int, int> result{};
        do {
            if (!guess) {
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
                // stupid search...
                std::size_t counter{};
                doIt(findByVector(counter, res));
                if (counter == possibleSetCount) {
                    std::cout << "Can not find this guess :(\n";
                    continue;
                }

                std::cout << counter << " [";
                std::copy(possibles.begin() + counter*k, possibles.begin() + counter*k+k, std::ostream_iterator<decltype(*possibles.begin())>(std::cout, " "));
                std::cout << "]\n";
                
                guess = counter;
            }
            
            // calculate worst result: 
            {
                auto arr = std::valarray(results[std::slice((*guess)*possibleSetCount, possibleSetCount, 1)]);
                std::size_t max = 0;
                std::pair<int, int> maxPair{};
                for (std::decay_t<decltype(k)> j = 0; j <= k; ++j) {
                    for (std::decay_t<decltype(k)> l = 0; l <= k - j; ++l) {
                        auto p = std::pair{int(j), int(l)};
                        auto c = std::valarray(arr[possibleIndArray && arr == p]).size();
                        if (c > max) {
                            maxPair = p;
                            max = c;
                        }
                    }
                }
                std::cout << "Worst thing to do is: " << max << " aka: " << maxPair.first << "," << maxPair.second << std::endl;
            }

            std::istringstream ss2 = std::istringstream{getLine("Result: ")};
            ss2 >> result.first >> result.second;

            if (!static_cast<bool>(ss2) || static_cast<std::size_t>(result.first + result.second) > k) {
                std::cout << "INVALID result :(\n";
                guess.reset();
                continue;
            }
        } while(!guess);

        possibleIndArray &= std::valarray(results[std::slice((*guess)*possibleSetCount, possibleSetCount, 1)]) == result;
        
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
        std::cout << "Current possible solution count: " << currPoss.size() << std::endl;
    }
}
