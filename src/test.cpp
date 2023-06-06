#include <iostream>
#include <iomanip>
#include <vector>
#include <array>
#include "bct_entry.hpp"
#include <catch2/catch_test_macros.hpp>
#include "ortools_extend_sat.h"

using namespace operations_research;
using namespace operations_research::sat;
using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;

#include "speck_boomerang2.h"
#include "window_size_util.h"
#include "nlohmann/json.hpp"
#include <tuple>
#include <algorithm>

using std::cout;
using std::endl;

TEST_CASE( "Factorials are computed", "[factorial]" ) {
    int preRound = 4;
    int postRound = 4;
    const int branchSize = 16;
    CpModelBuilder cp_model;
    std::vector< BoolVec > intermediate;
    constexpr int blockSize = 2 * branchSize;
    auto totalProb = cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
    std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };
    std::vector< std::array<BoolVec, 2> > allState;
    std::vector<IntVar> probs; // apparently they model the probabilities as pr = \neg x; this is why it is necessary to do branch_size - 1 - x
    IntVar e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
    create_model<32 / 2>(4, 4, 0, 16, -1, inputDiff, allState, intermediate, probs, totalProb, e1Prob, cp_model);
//search<32 / 2>(cp_model, 4, 4, 0, 16, -1, inputDiff, allState, intermediate, probs, totalProb, e1Prob);
}






//int main()
//{
//
//    const auto entry = ubct_entry(
//        0b00000000100000000000000000000000,
//        0b10000000000000000000000000000100,
//        0b00000010000000000000000000010010,
//        0b00000000000000000000000000000010,
//        0b00000000100000000000000000000100,
//        32
//    );
//    cout << entry << endl;
//    return 0;
//}
