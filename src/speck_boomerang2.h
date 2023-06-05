//
// Created by Juan del Carmen Grados Vasquez on 04/06/2023.
//
#include <sstream>
#include <random>
#include<fstream>
#include "ortools_extend_sat.h"

using std::cout;
using std::endl;

#ifndef SEARCH_SPECK_BOOMERANG2_CPP_H
#define SEARCH_SPECK_BOOMERANG2_CPP_H


namespace uuid {
    static std::random_device              rd;
    static std::mt19937                    gen(rd());
    static std::uniform_int_distribution<> dis(0, 15);
    static std::uniform_int_distribution<> dis2(8, 11);

    std::string generate_uuid_v4() {
        std::stringstream ss;
        int i;
        ss << std::hex;
        for (i = 0; i < 8; i++) {
            ss << dis(gen);
        }
        ss << "-";
        for (i = 0; i < 4; i++) {
            ss << dis(gen);
        }
        ss << "-4";
        for (i = 0; i < 3; i++) {
            ss << dis(gen);
        }
        ss << "-";
        ss << dis2(gen);
        for (i = 0; i < 3; i++) {
            ss << dis(gen);
        }
        ss << "-";
        for (i = 0; i < 12; i++) {
            ss << dis(gen);
        };
        return ss.str();
    }
}

void write_string_to_file(std::string string_to_write, std::string experiment_id) {
    std::fstream file;
    file.open(experiment_id+".txt", std::ios_base::app);

    if (!file.is_open()) {
        cout << "Unable to open the file.\n";
        return;
    }

    file << string_to_write + "\n";

    file.close();
}
std::string vectorToString(const std::vector<int>& vec) {
    std::string result;
    result.reserve(vec.size());

    int halfSize = vec.size() / 2;

    // Reverse the first half
    for (int i = halfSize - 1; i >= 0; i--) {
        result.push_back(static_cast<char>('0' + vec[i]));
    }

    // Reverse the second half
    for (int i = vec.size() - 1; i >= halfSize; i--) {
        result.push_back(static_cast<char>('0' + vec[i]));
    }

    return result;
}

std::string binaryToHex(const std::string& binaryString, int bit_size) {
    std::bitset<256> bits(binaryString);  // Assuming 256-bit binary string, adjust the size as needed
    std::stringstream hexStream;
    hexStream << std::hex << std::setw((bit_size + 3) / 4) << std::setfill('0') << bits.to_ulong();
    return hexStream.str();
}

void print_states(std::vector< std::array<BoolVec, 2> > allState, int branch_size, operations_research::sat::CpSolverResponse response) {

    for (int k = 0; k < allState.size(); k++) {
        std::vector<int> tmp;
        for (int i = 0; i < 2; i++)
            for (int j = 0; j < branch_size; j++)
                tmp.push_back(SolutionIntegerValue(response, allState[k][i][j]));
        cout<<binaryToHex(vectorToString(tmp), 2*branch_size)<<endl;
    }
}



#endif //SEARCH_SPECK_BOOMERANG2_CPP_H
