
#ifndef UTIL
#define UTIL
#include "ortools_extend_sat.h"
#include <iostream>
#include <vector>
#include <array>
#include <tuple>
#include <algorithm>
#include <sstream>
#include <random>
#include <fstream>

using std::cout;
using std::endl;


using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;

namespace util {
    std::string vectorToString(const std::vector<int> &vec);

    void write_string_to_file(std::string string_to_write, std::string experiment_id);

    std::string binaryToHex(const std::string &binaryString, int bit_size);

    void print_states(std::vector<std::array < BoolVec, 2>
    > allState,
    int branch_size, operations_research::sat::CpSolverResponse
    response);

    void mapBoolVecToBinary(const BoolVec &boolvec, const std::vector<int> &binary,
                                              operations_research::sat::CpModelBuilder &cp_model);
    std::string generate_uuid_v4();
}

#endif