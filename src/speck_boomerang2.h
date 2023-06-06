//
// Created by Juan del Carmen Grados Vasquez on 04/06/2023.
//
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

#ifndef SEARCH_SPECK_BOOMERANG2_CPP_H
#define SEARCH_SPECK_BOOMERANG2_CPP_H




void write_string_to_file(std::string string_to_write, std::string experiment_id);
std::string vectorToString(const std::vector<int>& vec);

std::string binaryToHex(const std::string& binaryString, int bit_size);

void print_states(std::vector< std::array<BoolVec, 2> > allState, int branch_size, operations_research::sat::CpSolverResponse response);


void mapBoolVecToBinary(const BoolVec& boolvec, const std::vector<int>& binary, operations_research::sat::CpModelBuilder& cp_model);

template<int branchSize>
void search(CpModelBuilder &cp_model, const int preRound, const int postRound, const int mNum, const int halfNum, int window_size,
        std::array<BoolVec, 2> &inputDiff, std::vector< std::array<BoolVec, 2> > &allState, std::vector< BoolVec > &intermediate,
std::vector<IntVar> &probs, IntVar &totalProb, IntVar &e1Prob);

template<int branchSize>
CpModelBuilder create_model(const int preRound, const int postRound, const int mNum, const int halfNum, int window_size,
                            std::array<BoolVec, 2> &inputDiff, std::vector< std::array<BoolVec, 2> > &allState, std::vector< BoolVec > &intermediate,
                            std::vector<IntVar> &probs, IntVar &totalProb, IntVar &e1Prob, CpModelBuilder &cp_model);

#endif //SEARCH_SPECK_BOOMERANG2_CPP_H
