//
// Created by Juan del Carmen Grados Vasquez on 04/06/2023.
//

#ifndef SPECK_BOOMERANG2_H
#define SPECK_BOOMERANG2_H

#include <sstream>
#include <random>
#include <fstream>
#include "nlohmann/json.hpp"
#include "ortools_extend_sat.h"

using json = nlohmann::json;
using namespace operations_research;
using namespace operations_research::sat;

using std::cout;
using std::endl;



namespace speck_boomerang2 {


    void write_string_to_file(std::string string_to_write, std::string experiment_id);

    std::string vectorToString(const std::vector<int> &vec);

    std::string binaryToHex(const std::string &binaryString, int bit_size);

    void print_states(std::vector <std::array<BoolVec, 2>> allState, int branch_size,
                      operations_research::sat::CpSolverResponse response);


    void mapBoolVecToBinary(const BoolVec &boolvec, const std::vector<int> &binary,
                            operations_research::sat::CpModelBuilder &cp_model);


    template<int branchSize>
    json search(CpModelBuilder &cp_model, const int preRound, const int postRound, const int mNum, const int halfNum,
                int window_size, std::vector <std::array<BoolVec, 2>> &allState,
                std::vector <BoolVec> &intermediate,
                std::vector <IntVar> &probs);

    template<int branchSize>
    CpModelBuilder
    create_model(const int preRound, const int postRound, const int mNum, const int halfNum, int window_size,
                 std::vector <std::array<BoolVec, 2>> &allState,
                 std::vector <BoolVec> &intermediate,
                 std::vector <IntVar> &probs,  CpModelBuilder &cp_model);


    template<int branchSize>
    int searchT(const int preRound, const int postRound, const int mNum, const int halfNum, const int first0, const int second0, int &window_size);
}


#endif //SEARCH_SPECK_BOOMERANG2_CPP_H
