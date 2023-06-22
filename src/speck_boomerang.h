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

    template<int branchSize>
    json search(CpModelBuilder &cp_model, const int preRound, const int postRound, const int mNum, const int halfNum,
                int window_size, std::vector <std::array<BoolVec, 2>> &allState,
                std::vector <BoolVec> &intermediate,
                std::vector <IntVar> &probs);

    template<int branchSize>
    json search_related_key(CpModelBuilder &cp_model, const int preRound, const int postRound, const int mNum, const int halfNum,
                int window_size, std::vector <std::array<BoolVec, 3>> &allState,
                std::vector <BoolVec> &intermediate, std::vector <std::array<IntVar, 2>> &probs, std::vector<BoolVec> &key_state_top, std::vector<BoolVec> &key_state_bottom);

    template<int branchSize>
    CpModelBuilder
    create_model(const int preRound, const int postRound, const int mNum, const int halfNum, int window_size,
                 std::vector <std::array<BoolVec, 2>> &allState,
                 std::vector <BoolVec> &intermediate,
                 std::vector <IntVar> &probs,  CpModelBuilder &cp_model);

    template<int branchSize>
    CpModelBuilder
    create_model_related_key(const int preRound, const int postRound, const int mNum, const int halfNum, int window_size,
                                               std::vector <std::array<BoolVec, 3>> &allState, std::vector<BoolVec> &key_state, std::vector<BoolVec> &key_state_bottom,
                                               std::vector <BoolVec> &intermediate,
                                               std::vector <std::array<IntVar, 2>> &probs, int key_size, CpModelBuilder &cp_model, bool withMiddlePart);


    template<int branchSize>
    int searchT(const int preRound, const int postRound, const int mNum, const int halfNum, const int first0, const int second0, int &window_size);
}


#endif //SEARCH_SPECK_BOOMERANG2_CPP_H
