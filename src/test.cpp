
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


TEST_CASE( "Table 6", "Single_Key[speck32/64]") { // To run this specific test you can run bin/testrun -t "Table 6"
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
    REQUIRE ( strcmp(result["E1"]["inputDiff"].dump().c_str(), "\"00101000000000000000000000010000\"") == 0);
    std::string intermediate_values_as_string = result["intermediate_values"].dump().c_str();
    std::string expected_intermediate_values = "[\"0100\",\"840a\",\"4205\",\"50a1\",\"850a\",\"150a\",\"9520\",\"0a04\",\"0080\",\"0a84\"]";
    REQUIRE ( intermediate_values_as_string.compare(expected_intermediate_values ) == 0);
    cout << result.dump().c_str();
}




TEST_CASE( "Table 7 test", "[speck48/72]") {
    const int preRound = 3;
    const int postRound = 3;
    const int mNum = 0;
    const int halfNum = 64;
    const int window_size = -1;

    std::vector<std::array<BoolVec, 2>> allState;
    std::vector<BoolVec> intermediate;
    std::vector<IntVar> probs;
    CpModelBuilder cp_model;
    create_model<64>(preRound, postRound, mNum, halfNum, window_size,  allState, intermediate,
            probs, cp_model);




    json result = search<64>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs);
    cout << result.dump().c_str() << endl;
    //REQUIRE ( strcmp(result["E2"]["outputDiff"].dump().c_str(), "\"000000001000000010100000001000001000010110100100\"") == 0);
}

// TODO:: change this because it is a not valid differential trail
TEST_CASE( "Checking Trail in the Related Key Model speck32/64", "Related_key[speck32/64]") {
    const int preRound = 4;
    const int postRound = 5;
    const int mNum = 0;
    const int halfNum = 16;
    const int window_size = -1;
    int key_size = 64;

    std::vector<std::array<BoolVec, 3>> allState;
    std::vector<BoolVec> intermediate;
    std::vector<BoolVec> key_state_top;
    std::vector<BoolVec> key_state_bottom;
    std::vector <std::array<IntVar, 2>> probs;
    CpModelBuilder cp_model;
    create_model_related_key<16>(preRound, postRound, mNum, halfNum, window_size,  allState, key_state_top, key_state_bottom, intermediate,
            probs, key_size, cp_model, false);

    std::vector<int> key_values_0 = { 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1 }; // 1a80
    std::vector<int> key_values_1 = { 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0 }; // 0880
    std::vector<int> key_values_2 = { 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; // 0028
    std::vector<int> key_values_3 = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0 }; // 1000
    mapBoolVecToBinary(key_state_top[0], key_values_3, cp_model);
    mapBoolVecToBinary(key_state_top[1], key_values_2, cp_model);
    mapBoolVecToBinary(key_state_top[2], key_values_1, cp_model);
    mapBoolVecToBinary(key_state_top[3], key_values_0, cp_model);


    BoolVec left_0_round = allState[0][1];
    BoolVec right_0_round = allState[0][2];
    std::vector<int> binary_left_0 = {0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_0 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0};
    mapBoolVecToBinary(left_0_round, binary_left_0, cp_model);
    mapBoolVecToBinary(right_0_round, binary_right_0, cp_model);

    BoolVec left_1_round = allState[1][1];
    BoolVec right_1_round = allState[1][2];
    std::vector<int> binary_left_1 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0};
    std::vector<int> binary_right_1 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_1_round, binary_left_1, cp_model);
    mapBoolVecToBinary(right_1_round, binary_right_1, cp_model);

    BoolVec left_2_round = allState[2][1];
    BoolVec right_2_round = allState[2][2];
    std::vector<int> binary_left_2 = {1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_2 = {1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0};
    mapBoolVecToBinary(left_2_round, binary_left_2, cp_model);
    mapBoolVecToBinary(right_2_round, binary_right_2, cp_model);

    BoolVec left_3_round = allState[3][1];
    BoolVec right_3_round = allState[3][2];
    std::vector<int> binary_left_3 = {1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_3 = {1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0};
    mapBoolVecToBinary(left_3_round, binary_left_3, cp_model);
    mapBoolVecToBinary(right_3_round, binary_right_3, cp_model);

    BoolVec left_4_round = allState[4][1];
    BoolVec right_4_round = allState[4][2];
    std::vector<int> binary_left_4 = {0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1};
    std::vector<int> binary_right_4 = {0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0};
    mapBoolVecToBinary(left_4_round, binary_left_4, cp_model);
    mapBoolVecToBinary(right_4_round, binary_right_4, cp_model);


    // Post rounds

    BoolVec key_5_round = allState[5][0];
    BoolVec left_5_round = allState[5][1];
    BoolVec right_5_round = allState[5][2];
    std::vector<int> binary_key_5 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0};
    std::vector<int> binary_left_5 = {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_5 = {0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1};
    mapBoolVecToBinary(key_5_round, binary_key_5, cp_model);
    mapBoolVecToBinary(left_5_round, binary_left_5, cp_model);
    mapBoolVecToBinary(right_5_round, binary_right_5, cp_model);

    BoolVec left_6_round = allState[6][1];
    BoolVec right_6_round = allState[6][2];
    std::vector<int> binary_left_6 = {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0};
    mapBoolVecToBinary(left_6_round, binary_left_6, cp_model);
    mapBoolVecToBinary(right_6_round, binary_right_6, cp_model);

    BoolVec left_7_round = allState[7][1];
    BoolVec right_7_round = allState[7][2];
    std::vector<int> binary_left_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
    std::vector<int> binary_right_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_7_round, binary_left_7, cp_model);
    mapBoolVecToBinary(right_7_round, binary_right_7, cp_model);


    BoolVec left_7_round_key = allState[7][0];
    std::vector<int> binary_left_7_key = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_7_round_key, binary_left_7_key, cp_model);


    BoolVec left_8_round = allState[8][1];
    BoolVec right_8_round = allState[8][2];
    std::vector<int> binary_left_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_8_round, binary_left_8, cp_model);
    mapBoolVecToBinary(right_8_round, binary_right_8, cp_model);


    BoolVec left_8_round_key = allState[8][0];
    std::vector<int> binary_left_8_key = {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_8_round_key, binary_left_8_key, cp_model);

    /*BoolVec left_9_round = allState[9][1];
    BoolVec right_9_round = allState[9][2];
    std::vector<int> binary_left_9 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_9 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_9_round, binary_left_9, cp_model);
    mapBoolVecToBinary(right_9_round, binary_right_9, cp_model);*/


    json result = search_related_key<16>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs, key_state_top, key_state_bottom);
    //cout << result["key_state_bottom"].dump().c_str() << endl;
    //cout << result["states"].dump().c_str() << endl;

    REQUIRE ( strcmp(result["states"][4].dump().c_str(), "\"400044a95602\"") == 0);
}

TEST_CASE( "Checking Boomerang Trail in the Related Key Model speck32/64", "Related_key[speck32/64]") {
    const int preRound = 5;
    const int postRound = 5;
    const int mNum = 0;
    const int halfNum = 16;
    const int window_size = -1;
    int key_size = 64;

    std::vector<std::array<BoolVec, 3>> allState;
    std::vector<BoolVec> intermediate;
    std::vector<BoolVec> key_state_top;
    std::vector<BoolVec> key_state_bottom;
    std::vector <std::array<IntVar, 2>> probs;
    CpModelBuilder cp_model;
    create_model_related_key<16>(preRound, postRound, mNum, halfNum, window_size,  allState, key_state_top, key_state_bottom, intermediate,
                                 probs, key_size, cp_model, false);

    BoolVec key_state_top_0 = key_state_top[0];
    std::vector<int> binary_top_0 = {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_0, binary_top_0, cp_model);

    BoolVec key_state_top_1 = key_state_top[1];
    std::vector<int> binary_top_1 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_1, binary_top_1, cp_model);

    BoolVec key_state_top_2 = key_state_top[2];
    std::vector<int> binary_top_2 = {0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_2, binary_top_2, cp_model);

    BoolVec key_state_top_3 = key_state_top[3];
    std::vector<int> binary_top_3 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_3, binary_top_3, cp_model);

    BoolVec key_state_top_4 = key_state_top[4];
    std::vector<int> binary_top_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_4, binary_top_4, cp_model);

    BoolVec key_state_top_5 = key_state_top[5];
    std::vector<int> binary_top_5 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0};
    mapBoolVecToBinary(key_state_top_5, binary_top_5, cp_model);

    // To ensure non-overlaping
    BoolVec key_state_top_6 = key_state_top[6];
    std::vector<int> binary_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_6, binary_6, cp_model);

    BoolVec key_state_top_7 = key_state_top[7];
    std::vector<int> binary_top_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_top_7, binary_top_7, cp_model);

    BoolVec key_state_bottom_0 = key_state_bottom[0];
    std::vector<int> binary_bottom_0 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_0, binary_bottom_0, cp_model);

    BoolVec key_state_bottom_1 = key_state_bottom[1];
    std::vector<int> binary_bottom_1 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_1, binary_bottom_1, cp_model);

    BoolVec key_state_bottom_2 = key_state_bottom[2];
    std::vector<int> binary_bottom_2 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_2, binary_bottom_2, cp_model);

    BoolVec key_state_bottom_3 = key_state_bottom[3];
    std::vector<int> binary_bottom_3 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_3, binary_bottom_3, cp_model);

    BoolVec key_state_bottom_4 = key_state_bottom[4];
    std::vector<int> binary_bottom_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_4, binary_bottom_4, cp_model);

    BoolVec key_state_bottom_5 = key_state_bottom[5];
    std::vector<int> binary_bottom_5 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_5, binary_bottom_5, cp_model);

    BoolVec key_state_bottom_6 = key_state_bottom[6];
    std::vector<int> binary_bottom_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_6, binary_bottom_6, cp_model);

    BoolVec key_state_bottom_7 = key_state_bottom[7];
    std::vector<int> binary_bottom_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_state_bottom_3, binary_bottom_7, cp_model);


    /*BoolVec key_0_round = allState[0][0];
    BoolVec left_0_round = allState[0][1];
    BoolVec right_0_round = allState[0][2];
    std::vector<int> binary_key_0 = {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_0= {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
    std::vector<int> binary_right_0 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
    mapBoolVecToBinary(key_0_round, binary_key_0, cp_model);
    mapBoolVecToBinary(left_0_round, binary_left_0, cp_model);
    mapBoolVecToBinary(right_0_round, binary_right_0, cp_model);


    BoolVec key_1_round = allState[1][0];
    BoolVec left_1_round = allState[1][1];
    BoolVec right_1_round = allState[1][2];
    std::vector<int> binary_key_1 = {0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_1= {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_1 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_1_round, binary_key_1, cp_model);
    mapBoolVecToBinary(left_1_round, binary_left_1, cp_model);
    mapBoolVecToBinary(right_1_round, binary_right_1, cp_model);


    BoolVec key_2_round = allState[2][0];
    BoolVec left_2_round = allState[2][1];
    BoolVec right_2_round = allState[2][2];
    std::vector<int> binary_key_2 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_2= {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_2 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_2_round, binary_key_2, cp_model);
    mapBoolVecToBinary(left_2_round, binary_left_2, cp_model);
    mapBoolVecToBinary(right_2_round, binary_right_2, cp_model);


    BoolVec key_3_round = allState[3][0];
    BoolVec left_3_round = allState[3][1];
    BoolVec right_3_round = allState[3][2];
    std::vector<int> binary_key_3 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_3= {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_3 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_3_round, binary_key_3, cp_model);
    mapBoolVecToBinary(left_3_round, binary_left_3, cp_model);
    mapBoolVecToBinary(right_3_round, binary_right_3, cp_model);


    BoolVec key_4_round = allState[4][0];
    BoolVec left_4_round = allState[4][1];
    BoolVec right_4_round = allState[4][2];
    std::vector<int> binary_key_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_4= {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_4_round, binary_key_4, cp_model);
    mapBoolVecToBinary(left_4_round, binary_left_4, cp_model);
    mapBoolVecToBinary(right_4_round, binary_right_4, cp_model);


    BoolVec key_5_round = allState[5][0];
    BoolVec left_5_round = allState[5][1];
    BoolVec right_5_round = allState[5][2];
    std::vector<int> binary_key_5 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_5= {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_5 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_5_round, binary_key_5, cp_model);
    mapBoolVecToBinary(left_5_round, binary_left_5, cp_model);
    mapBoolVecToBinary(right_5_round, binary_right_5, cp_model);


    BoolVec key_6_round = allState[6][0];
    BoolVec left_6_round = allState[6][1];
    BoolVec right_6_round = allState[6][2];
    std::vector<int> binary_key_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_6= {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_6 = {0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0};
    mapBoolVecToBinary(key_6_round, binary_key_6, cp_model);
    mapBoolVecToBinary(left_6_round, binary_left_6, cp_model);
    mapBoolVecToBinary(right_6_round, binary_right_6, cp_model);


    BoolVec key_7_round = allState[7][0];
    BoolVec left_7_round = allState[7][1];
    BoolVec right_7_round = allState[7][2];
    std::vector<int> binary_key_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_7= {0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
    mapBoolVecToBinary(key_7_round, binary_key_7, cp_model);
    mapBoolVecToBinary(left_7_round, binary_left_7, cp_model);
    mapBoolVecToBinary(right_7_round, binary_right_7, cp_model);


    BoolVec key_8_round = allState[8][0];
    BoolVec left_8_round = allState[8][1];
    BoolVec right_8_round = allState[8][2];
    std::vector<int> binary_key_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_8= {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_8_round, binary_key_8, cp_model);
    mapBoolVecToBinary(left_8_round, binary_left_8, cp_model);
    mapBoolVecToBinary(right_8_round, binary_right_8, cp_model);


    BoolVec key_9_round = allState[9][0];
    BoolVec left_9_round = allState[9][1];
    BoolVec right_9_round = allState[9][2];
    std::vector<int> binary_key_9 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_9= {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_9 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_9_round, binary_key_9, cp_model);
    mapBoolVecToBinary(left_9_round, binary_left_9, cp_model);
    mapBoolVecToBinary(right_9_round, binary_right_9, cp_model);


    BoolVec key_10_round = allState[10][0];
    BoolVec left_10_round = allState[10][1];
    BoolVec right_10_round = allState[10][2];
    std::vector<int> binary_key_10 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_10= {1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_10 = {1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0};
    mapBoolVecToBinary(key_10_round, binary_key_10, cp_model);
    mapBoolVecToBinary(left_10_round, binary_left_10, cp_model);
    mapBoolVecToBinary(right_10_round, binary_right_10, cp_model);


    BoolVec key_11_round = allState[11][0];
    BoolVec left_11_round = allState[11][1];
    BoolVec right_11_round = allState[11][2];
    std::vector<int> binary_key_11 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_11= {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_11 = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0};
    mapBoolVecToBinary(key_11_round, binary_key_11, cp_model);
    mapBoolVecToBinary(left_11_round, binary_left_11, cp_model);
    mapBoolVecToBinary(right_11_round, binary_right_11, cp_model);*/

    json result = search_related_key<16>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs, key_state_top, key_state_bottom);
    cout << result["key_state_top"].dump().c_str() << endl;
    cout << result["key_state_bottom"].dump().c_str() << endl;
    cout << result["states"].dump().c_str() << endl;
    cout << result["probabilities"].dump().c_str() << endl;

    //REQUIRE ( strcmp(result["states"][4].dump().c_str(), "\"400044a95602\"") == 0);
}

TEST_CASE( "Checking Trail in Related Key Scenario speck48/96 66010b32-46d2-4b16-bc99-ad0969c2f2ef", "[speck48/96]") {
    const int preRound = 4;
    const int postRound = 5;
    const int mNum = 0;
    const int halfNum = 24;
    const int window_size = -1;
    int key_size = 96;

    std::vector<std::array<BoolVec, 3>> allState;
    std::vector<BoolVec> intermediate;
    std::vector<BoolVec> key_state_top;
    std::vector<BoolVec> key_state_bottom;
    std::vector <std::array<IntVar, 2>> probs;
    CpModelBuilder cp_model;
    bool withMiddlePart = false;
    create_model_related_key<24>(preRound, postRound, mNum, halfNum, window_size,  allState, key_state_top, key_state_bottom, intermediate,
            probs, key_size, cp_model, withMiddlePart);
    std::vector<int> key_values_0 = { 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0 }; //
    std::vector<int> key_values_1 = { 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0 }; //
    std::vector<int> key_values_2 = { 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; //
    std::vector<int> key_values_3 = { 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 }; //
    mapBoolVecToBinary(key_state_top[0], key_values_3, cp_model);
    mapBoolVecToBinary(key_state_top[1], key_values_2, cp_model);
    mapBoolVecToBinary(key_state_top[2], key_values_1, cp_model);
    mapBoolVecToBinary(key_state_top[3], key_values_0, cp_model);


    BoolVec left_0_round = allState[0][1];
    BoolVec right_0_round = allState[0][2];
    std::vector<int> binary_left_0 = {0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0};
    std::vector<int> binary_right_0 = {0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_0_round, binary_left_0, cp_model);
    mapBoolVecToBinary(right_0_round, binary_right_0, cp_model);

    BoolVec left_1_round = allState[1][1];
    BoolVec right_1_round = allState[1][2];
    std::vector<int> binary_left_1 = {1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_1 = {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_1_round, binary_left_1, cp_model);
    mapBoolVecToBinary(right_1_round, binary_right_1, cp_model);

    BoolVec left_2_round = allState[2][1];
    BoolVec right_2_round = allState[2][2];
    std::vector<int> binary_left_2 = {0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1};
    std::vector<int> binary_right_2 = {0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1};
    mapBoolVecToBinary(left_2_round, binary_left_2, cp_model);
    mapBoolVecToBinary(right_2_round, binary_right_2, cp_model);

    BoolVec left_3_round = allState[3][1];
    BoolVec right_3_round = allState[3][2];
    std::vector<int> binary_left_3 = {0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_3 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0};
    mapBoolVecToBinary(left_3_round, binary_left_3, cp_model);
    mapBoolVecToBinary(right_3_round, binary_right_3, cp_model);

    BoolVec left_4_round = allState[4][1];
    BoolVec right_4_round = allState[4][2];
    std::vector<int> binary_left_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1};
    std::vector<int> binary_right_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1};
    mapBoolVecToBinary(left_4_round, binary_left_4, cp_model);
    mapBoolVecToBinary(right_4_round, binary_right_4, cp_model);

    // Post Round
    BoolVec key_6_round = allState[6][0];
    BoolVec left_6_round = allState[6][1];
    BoolVec right_6_round = allState[6][2];
    std::vector<int> binary_key_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_6_round, binary_key_6, cp_model);
    mapBoolVecToBinary(left_6_round, binary_left_6, cp_model);
    mapBoolVecToBinary(right_6_round, binary_right_6, cp_model);

    BoolVec left_7_round = allState[7][1];
    BoolVec right_7_round = allState[7][2];
    std::vector<int> binary_left_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(left_7_round, binary_left_7, cp_model);
    mapBoolVecToBinary(right_7_round, binary_right_7, cp_model);

    BoolVec key_8_round = allState[8][0];
    BoolVec left_8_round = allState[8][1];
    BoolVec right_8_round = allState[8][2];
    std::vector<int> binary_key_8 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_8_round, binary_key_8, cp_model);
    mapBoolVecToBinary(left_8_round, binary_left_8, cp_model);
    mapBoolVecToBinary(right_8_round, binary_right_8, cp_model);

    BoolVec key_9_round = allState[9][0];
    BoolVec left_9_round = allState[9][1];
    BoolVec right_9_round = allState[9][2];
    std::vector<int> binary_key_9 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0};
    std::vector<int> binary_left_9 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_9 = {1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(key_9_round, binary_key_9, cp_model);
    mapBoolVecToBinary(left_9_round, binary_left_9, cp_model);
    mapBoolVecToBinary(right_9_round, binary_right_9, cp_model);

    BoolVec key_10_round = allState[10][0];
    BoolVec left_10_round = allState[10][1];
    BoolVec right_10_round = allState[10][2];
    std::vector<int> binary_key_10 = {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0};
    std::vector<int> binary_left_10 = {0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    std::vector<int> binary_right_10 = {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0};
    mapBoolVecToBinary(key_10_round, binary_key_10, cp_model);
    mapBoolVecToBinary(left_10_round, binary_left_10, cp_model);
    mapBoolVecToBinary(right_10_round, binary_right_10, cp_model);

    BoolVec after_addition = key_state_bottom[3];
    std::vector<int> binary_after_addition = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
    mapBoolVecToBinary(after_addition, binary_after_addition, cp_model);



    json result = search_related_key<24>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs, key_state_top, key_state_bottom);
    REQUIRE ( strcmp(result["states"][4].dump().c_str(), "\"002048001949005809\"") == 0);
}


TEST_CASE( "Checking Trail in Related Key Scenario speck48/96 66010b32-46d2-4b16-bc99-ad0969c2f2ef with Middle Part in the internal procedure", "[speck48/96]") {
const int preRound = 6;
const int postRound = 5;
const int mNum = 0;
const int halfNum = 24;
const int window_size = -1;
int key_size = 96;

std::vector<std::array<BoolVec, 3>> allState;
std::vector<BoolVec> intermediate;
std::vector<BoolVec> key_state_top;
std::vector<BoolVec> key_state_bottom;
std::vector <std::array<IntVar, 2>> probs;
CpModelBuilder cp_model;
bool withMiddlePart = true;
create_model_related_key<24>(preRound, postRound, mNum, halfNum, window_size,  allState, key_state_top, key_state_bottom, intermediate,
        probs, key_size, cp_model, withMiddlePart);
/*std::vector<int> key_values_0 = { 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0 }; //
std::vector<int> key_values_1 = { 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0 }; //
std::vector<int> key_values_2 = { 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; //
std::vector<int> key_values_3 = { 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 }; //
mapBoolVecToBinary(key_state_top[0], key_values_3, cp_model);
mapBoolVecToBinary(key_state_top[1], key_values_2, cp_model);
mapBoolVecToBinary(key_state_top[2], key_values_1, cp_model);
mapBoolVecToBinary(key_state_top[3], key_values_0, cp_model);


BoolVec left_0_round = allState[0][1];
BoolVec right_0_round = allState[0][2];
std::vector<int> binary_left_0 = {0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0};
std::vector<int> binary_right_0 = {0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0};
mapBoolVecToBinary(left_0_round, binary_left_0, cp_model);
mapBoolVecToBinary(right_0_round, binary_right_0, cp_model);

BoolVec left_1_round = allState[1][1];
BoolVec right_1_round = allState[1][2];
std::vector<int> binary_left_1 = {1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0};
std::vector<int> binary_right_1 = {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0};
mapBoolVecToBinary(left_1_round, binary_left_1, cp_model);
mapBoolVecToBinary(right_1_round, binary_right_1, cp_model);

BoolVec left_2_round = allState[2][1];
BoolVec right_2_round = allState[2][2];
std::vector<int> binary_left_2 = {0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1};
std::vector<int> binary_right_2 = {0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1};
mapBoolVecToBinary(left_2_round, binary_left_2, cp_model);
mapBoolVecToBinary(right_2_round, binary_right_2, cp_model);

BoolVec left_3_round = allState[3][1];
BoolVec right_3_round = allState[3][2];
std::vector<int> binary_left_3 = {0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_3 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0};
mapBoolVecToBinary(left_3_round, binary_left_3, cp_model);
mapBoolVecToBinary(right_3_round, binary_right_3, cp_model);

BoolVec left_4_round = allState[4][1];
BoolVec right_4_round = allState[4][2];
std::vector<int> binary_left_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1};
std::vector<int> binary_right_4 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1};
mapBoolVecToBinary(left_4_round, binary_left_4, cp_model);
mapBoolVecToBinary(right_4_round, binary_right_4, cp_model);

// Post Round
BoolVec key_6_round = allState[6][0];
BoolVec left_6_round = allState[6][1];
BoolVec right_6_round = allState[6][2];
std::vector<int> binary_key_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_left_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_6 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(key_6_round, binary_key_6, cp_model);
mapBoolVecToBinary(left_6_round, binary_left_6, cp_model);
mapBoolVecToBinary(right_6_round, binary_right_6, cp_model);

BoolVec left_7_round = allState[7][1];
BoolVec right_7_round = allState[7][2];
std::vector<int> binary_left_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_7 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(left_7_round, binary_left_7, cp_model);
mapBoolVecToBinary(right_7_round, binary_right_7, cp_model);

BoolVec key_8_round = allState[8][0];
BoolVec left_8_round = allState[8][1];
BoolVec right_8_round = allState[8][2];
std::vector<int> binary_key_8 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_left_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_8 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(key_8_round, binary_key_8, cp_model);
mapBoolVecToBinary(left_8_round, binary_left_8, cp_model);
mapBoolVecToBinary(right_8_round, binary_right_8, cp_model);

BoolVec key_9_round = allState[9][0];
BoolVec left_9_round = allState[9][1];
BoolVec right_9_round = allState[9][2];
std::vector<int> binary_key_9 = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0};
std::vector<int> binary_left_9 = {1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_9 = {1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(key_9_round, binary_key_9, cp_model);
mapBoolVecToBinary(left_9_round, binary_left_9, cp_model);
mapBoolVecToBinary(right_9_round, binary_right_9, cp_model);

BoolVec key_10_round = allState[10][0];
BoolVec left_10_round = allState[10][1];
BoolVec right_10_round = allState[10][2];
std::vector<int> binary_key_10 = {0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0};
std::vector<int> binary_left_10 = {0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
std::vector<int> binary_right_10 = {0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0};
mapBoolVecToBinary(key_10_round, binary_key_10, cp_model);
mapBoolVecToBinary(left_10_round, binary_left_10, cp_model);
mapBoolVecToBinary(right_10_round, binary_right_10, cp_model);

BoolVec after_addition = key_state_bottom[3];
std::vector<int> binary_after_addition = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0};
mapBoolVecToBinary(after_addition, binary_after_addition, cp_model);*/



json result = search_related_key<24>(cp_model, preRound, postRound, 0, halfNum, window_size,  allState, intermediate, probs, key_state_top, key_state_bottom);
cout << result["probabilities"].dump().c_str() << endl;
cout << "key_state_top: " << result["key_state_top"].dump().c_str() << endl;
cout << "key_state_bottom: " << result["key_state_bottom"].dump().c_str() << endl;
cout << result["states"].dump().c_str() << endl;
//REQUIRE ( strcmp(result["states"][4].dump().c_str(), "\"002048001949005809\"") == 0);
}


