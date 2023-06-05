#include <iostream>
#include <iomanip>
#include <vector>
#include <array>
#include "bct_entry.hpp"
#include <catch2/catch_test_macros.hpp>

using std::cout;
using std::endl;

int main()
{

    const auto entry = ubct_entry(
        0b00000000100000000000000000000000,
        0b10000000000000000000000000000100,
        0b00000010000000000000000000010010,
        0b00000000000000000000000000000010,
        0b00000000100000000000000000000100,
        32
    );
    cout << entry << endl;
    return 0;
}
