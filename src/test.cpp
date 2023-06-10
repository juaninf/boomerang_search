
#define CATCH_CONFIG_MAIN
#include "bct_entry.hpp"
#include "ortools_extend_sat.h"
#include "window_size_util.h"
#include "speck_boomerang2.h"
#include <catch2/catch_all.hpp>
#include <catch2/catch_test_macros.hpp>

#include <iostream>
#include <iomanip>
#include <vector>
#include <array>
#include <string.h>


using namespace speck_boomerang2;

using namespace operations_research;
using namespace operations_research::sat;
using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;


#include "nlohmann/json.hpp"
#include <tuple>
#include <algorithm>

using std::cout;
using std::endl;

TEST_CASE( "Factorials are computedd", "[create_model1]") {
constexpr int branchSize = 16;
const int preRound = 4;
const int postRound = 4;
const int mNum = 0;
const int halfNum = 16;
const int window_size = -1;

std::vector<std::array<BoolVec, 2>> allState;
std::vector<BoolVec> intermediate;
std::vector<IntVar> probs;
CpModelBuilder cp_model;
IntVar totalProb =  cp_model.NewIntVar(Domain(0, (branchSize - 1) * (preRound + postRound)));
IntVar e1Prob = cp_model.NewIntVar(Domain(0, preRound * (branchSize - 1)));
std::array<BoolVec, 2> inputDiff = { NewBoolVec(cp_model, branchSize), NewBoolVec(cp_model, branchSize) };

// Perform any necessary setup before calling the method
// ...

// Call the method being tested
create_model<16>(preRound, postRound, mNum, halfNum, window_size, inputDiff, allState, intermediate,
        probs, totalProb, e1Prob, cp_model);


//int window_size = -1;
//searchT<16>(4, 4, 0, 16, 2, 2, window_size);
BoolVec left_5_round = allState[5][0];
BoolVec right_5_round = allState[5][1];
std::vector<int> binary_left_5 = {0, 0, 0, 0, 1,0,1,0,0,0,0,0,0,1,0,0};
std::vector<int> binary_right_5 = {0, 0, 0, 0, 1,0,0,0,0,0,0,0,0,1,0,0};
mapBoolVecToBinary(left_5_round, binary_left_5, cp_model);
mapBoolVecToBinary(right_5_round, binary_right_5, cp_model);
json result = search<16>(cp_model, 4, 4, 0, 16, -1, inputDiff, allState, intermediate, probs, totalProb, e1Prob);
printf("%s", result["E1"]["inputDiff"].dump().c_str());


REQUIRE ( strcmp(result["E1"]["inputDiff"].dump().c_str(), "\"00101000000000000000000000010000\"") == 0);
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
