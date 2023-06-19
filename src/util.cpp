#include "util.h"


using namespace util;
/*std::string util::vectorToString(const std::vector<int>& vec) {
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
}*/
/*
using namespace util;
std::string util::vectorToString(const std::vector<int>& vec, int m) {
    std::string result;
    result.reserve(vec.size());
    cout << "m is:" << m << endl;
    int halfSize = vec.size() / m;

    // Reverse the first half
    for (int i = halfSize - 1; i >= 0; i--) {
        result.push_back(static_cast<char>('0' + vec[i]));
    }

    // Reverse the second half
    for (int i = vec.size() - 1; i >= halfSize; i--) {
        result.push_back(static_cast<char>('0' + vec[i]));
    }

    return result;
}*/

using namespace util;
std::string util::vectorToString(const std::vector<int>& vec, int m) {
    std::string result;
    result.reserve(vec.size());

    int wordSize = vec.size() / m;

    // Reverse the first half
    for (int j = 1; j <= m; j++)
        for (int i = j*wordSize - 1; i >= (j-1)*wordSize; i--) {
            result.push_back(static_cast<char>('0' + vec[i]));
        }

    return result;
}

void util::write_string_to_file(std::string string_to_write, std::string experiment_id) {
    std::fstream file;
    file.open(experiment_id+".json", std::ios_base::app);

    if (!file.is_open()) {
        cout << "Unable to open the file.\n";
        return;
    }

    file << string_to_write + "\n";

    file.close();
}

std::string util::binaryToHex(const std::string& binaryString, int bit_size) {
    int num_bits = (bit_size + 3) / 4 * 4;  // Round up to the nearest multiple of 4 bits
    int num_bytes = (num_bits + 7) / 8;  // Calculate the number of bytes required

    std::vector<unsigned char> bytes(num_bytes, 0);  // Create a vector to hold the bytes

    // Convert each byte from the binary string to an unsigned char
    for (int i = 0; i < num_bytes; ++i) {
        for (int j = 0; j < 8 && (i * 8 + j) < bit_size; ++j) {
            if (binaryString[i * 8 + j] == '1') {
                bytes[i] |= (1 << (7 - j));
            }
        }
    }

    std::stringstream hexStream;
    hexStream << std::hex << std::setw((num_bits + 3) / 4) << std::setfill('0');

    // Convert each byte to its hex representation and append to the hex string
    for (int i = 0; i < num_bytes; ++i) {
        hexStream << std::setw(2) << static_cast<int>(bytes[i]);
    }

    return hexStream.str();
}


void util::mapBoolVecToBinary(const BoolVec& boolvec, const std::vector<int>& binary, operations_research::sat::CpModelBuilder& cp_model) {
    int n = boolvec.size();

    for (int i = 0; i < n; i++) {
        cp_model.AddEquality(boolvec[n - i - 1], binary[i]);
    }
}


    std::string util::generate_uuid_v4() {
        static std::random_device              rd;
        static std::mt19937                    gen(rd());
        static std::uniform_int_distribution<> dis(0, 15);
        static std::uniform_int_distribution<> dis2(8, 11);
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

std::vector<std::string> util::states_to_vector_hex_string(std::vector< BoolVec > allState, int branch_size, operations_research::sat::CpSolverResponse response) {
    std::vector<std::string> vector_hex_string;
    std::vector<int> tmp;

    for (int k = 0; k < allState.size(); k++) {
        for (int j = 0; j < branch_size; j++)
            tmp.push_back(SolutionIntegerValue(response, allState[k][j]));
        vector_hex_string.push_back(binaryToHex(vectorToString(tmp, 1), branch_size));
    }
    return vector_hex_string;
}

