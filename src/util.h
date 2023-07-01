
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
    std::string vectorToString(const std::vector<int> &vec, int m);

    void write_string_to_file(std::string string_to_write, std::string experiment_id);

    std::string binaryToHex(const std::string &binaryString, int bit_size);

    void print_states(std::vector<std::array < BoolVec, 2>
    > allState,
    int branch_size, operations_research::sat::CpSolverResponse
    response, int m);

    void print_states(std::vector<std::array < BoolVec, 3>
                      > allState,
                      int branch_size, operations_research::sat::CpSolverResponse
                      response, int m);

    void print_states(std::vector<std::array < BoolVec, 4>
                      > allState,
                      int branch_size, operations_research::sat::CpSolverResponse
                      response, int m);


    std::vector<std::string> states_to_vector_hex_string(std::vector< std::array<BoolVec, 3> > allState, int branch_size, operations_research::sat::CpSolverResponse response);

        void mapBoolVecToBinary(const BoolVec &boolvec, const std::vector<int> &binary,
                                              operations_research::sat::CpModelBuilder &cp_model);
    std::string generate_uuid_v4();

    template <typename T>
    std::vector<T> flatten2DArray(const std::vector<std::vector<T>>& arr2D) {
        std::vector<T> flattened;

        for (const auto& row : arr2D) {
            flattened.insert(flattened.end(), row.begin(), row.end());
        }

        return flattened;
    }

    template <typename T, size_t N>
    std::vector<T> flatten2DArray(const std::vector<std::array<T, N>>& arr2D) {
        std::vector<T> flattened;

        for (const auto& row : arr2D) {
            flattened.insert(flattened.end(), row.begin(), row.end());
        }

        return flattened;
    }

    template <typename T>
    std::vector<T> flatten3DArray(const std::vector<std::vector<std::vector<T>>>& arr3D) {
    std::vector<T> flattened;

    for (const auto& outer : arr3D) {
    for (const auto& middle : outer) {
    flattened.insert(flattened.end(), middle.begin(), middle.end());
    }
    }
    return flattened;
    }

template <int state_number_of_words>
void  print_states(std::vector< std::array<BoolVec, state_number_of_words> > allState, int branch_size, operations_research::sat::CpSolverResponse response) {

    for (int k = 0; k < allState.size(); k++) {
        std::vector<int> tmp;
        for (int i = 0; i < state_number_of_words; i++)
            for (int j = 0; j < branch_size; j++)
                tmp.push_back(SolutionIntegerValue(response, allState[k][i][j]));
        cout<<binaryToHex(vectorToString(tmp, state_number_of_words), state_number_of_words*branch_size)<<endl;
    }
}
template <int state_number_of_words>
std::vector<std::string> states_to_vector_hex_string(std::vector< std::array<BoolVec, state_number_of_words> > allState, int branch_size, operations_research::sat::CpSolverResponse response) {
    std::vector<std::string> vector_hex_string;

    for (int k = 0; k < allState.size(); k++) {
        std::vector<int> tmp;
        for (int i = 0; i < state_number_of_words; i++)
            for (int j = 0; j < branch_size; j++)
                tmp.push_back(SolutionIntegerValue(response, allState[k][i][j]));
        vector_hex_string.push_back(binaryToHex(vectorToString(tmp, state_number_of_words), state_number_of_words*branch_size));
    }
    return vector_hex_string;
}

    std::vector<std::string> states_to_vector_hex_string(std::vector< BoolVec > allState, int branch_size, operations_research::sat::CpSolverResponse response);
    unsigned long long int state_to_ull(BoolVec word, operations_research::sat::CpSolverResponse response, int branchSize);

}

#endif