
#define CATCH_CONFIG_MAIN
#include "bct_entry.hpp"
#include "ortools_extend_sat.h"
#include "window_size_util.h"
#include "util.h"
#include "speck_boomerang.h"
#include <catch2/catch_all.hpp>
#include <catch2/catch_test_macros.hpp>

#include <iostream>
#include <iomanip>
#include <vector>
#include <array>
#include <string.h>

using namespace util;
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

TEST_CASE( "Table 6", "[speck32/64]") {

const int preRound = 4;
const int postRound = 4;
const int mNum = 0;
const int halfNum = 16;
const int window_size = -1;

std::vector<std::array<BoolVec, 2>> allState;
std::vector<BoolVec> intermediate;
std::vector<IntVar> probs;
CpModelBuilder cp_model;
create_model<16>(preRound, postRound, mNum, halfNum, window_size,  allState, intermediate,
        probs, cp_model);


BoolVec left_0_round = allState[0][0];
BoolVec right_0_round = allState[0][1];
std::vector<int> binary_left_0= {0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0};
std::vector<int> binary_right_0 = {0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0};
mapBoolVecToBinary(left_0_round, binary_left_0, cp_model);
mapBoolVecToBinary(right_0_round, binary_right_0, cp_model);

BoolVec left_5_round = allState[5][0];
BoolVec right_5_round = allState[5][1];
std::vector<int> binary_left_5 = {0, 0, 0, 0, 1,0,1,0,0,0,0,0,0,1,0,0};
std::vector<int> binary_right_5 = {0, 0, 0, 0, 1,0,0,0,0,0,0,0,0,1,0,0};
mapBoolVecToBinary(left_5_round, binary_left_5, cp_model);
mapBoolVecToBinary(right_5_round, binary_right_5, cp_model);
json result = search<16>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs);
printf("%s", result["E1"]["inputDiff"].dump().c_str());
REQUIRE ( strcmp(result["E1"]["inputDiff"].dump().c_str(), "\"00101000000000000000000000010000\"") == 0);
}


TEST_CASE( "Table 7", "[speck48/72]") {
const int preRound = 5;
const int postRound = 5;
const int mNum = 0;
const int halfNum = 24;
const int window_size = -1;

std::vector<std::array<BoolVec, 2>> allState;
std::vector<BoolVec> intermediate;
std::vector<IntVar> probs;
CpModelBuilder cp_model;
create_model<24>(preRound, postRound, mNum, halfNum, window_size,  allState, intermediate,
        probs, cp_model);


BoolVec left_0_round = allState[0][0];
BoolVec right_0_round = allState[0][1];
std::vector<int> binary_left_0= {0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0};
std::vector<int> binary_right_0 = {0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(left_0_round, binary_left_0, cp_model);
mapBoolVecToBinary(right_0_round, binary_right_0, cp_model);

BoolVec left_5_round = allState[5][0];
BoolVec right_5_round = allState[5][1];
std::vector<int> binary_left_5 = {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_5 = {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0};
mapBoolVecToBinary(left_5_round, binary_left_5, cp_model);
mapBoolVecToBinary(right_5_round, binary_right_5, cp_model);

BoolVec left_6_round = allState[6][0];
BoolVec right_6_round = allState[6][1];
std::vector<int> binary_left_6 =  {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
mapBoolVecToBinary(left_6_round, binary_left_6, cp_model);
mapBoolVecToBinary(right_6_round, binary_right_6, cp_model);

BoolVec left_7_round = allState[7][0];
BoolVec right_7_round = allState[7][1];
std::vector<int> binary_left_7 =  {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(left_7_round, binary_left_7, cp_model);
mapBoolVecToBinary(right_7_round, binary_right_7, cp_model);

json result = search<24>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs);
REQUIRE ( strcmp(result["E2"]["outputDiff"].dump().c_str(), "\"000000001000000010100000001000001000010110100100\"") == 0);
}



