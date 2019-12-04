cmake_minimum_required(VERSION 3.10)


project(mastermind)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DBOOST_THREAD_VERSION=4 -D_GLIBCXX_USE_CXX11_ABI=1 -DBOOST_ERROR_CODE_HEADER_ONLY -DBOOST_NO_CXX14_CONSTEXPR -Wall -Werror -Wextra -O3 -Wpedantic -pedantic-errors")

# set(Boost_INCLUDE_DIR "")
find_package(Boost MODULE REQUIRED)

add_executable(mastermind
        main.cpp)
target_link_libraries(mastermind
        Boost::boost)