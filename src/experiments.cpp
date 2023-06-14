#include "bct_entry.hpp"
#include "ortools_extend_sat.h"
#include "window_size_util.h"
#include "speck_boomerang.h"
#include "util.h"

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

template<int branchSize>
void run_one_experiment(int half_block_size, int window_size, int top_number_of_rounds, int bottom_number_of_rounds) {
    const int mNum = 0;
    std::vector<std::array<BoolVec, 2>> allState;
    std::vector<BoolVec> intermediate;
    std::vector<IntVar> probs;
    CpModelBuilder cp_model;
    create_model<branchSize>(top_number_of_rounds, bottom_number_of_rounds, mNum, half_block_size, window_size,  allState, intermediate,
                             probs, cp_model);
    json result = search<branchSize>(cp_model, top_number_of_rounds, bottom_number_of_rounds, 0, half_block_size, window_size,  allState, intermediate, probs);
    std::cout << result.dump() << std::endl;
    write_string_to_file(result.dump(), result["experiment_id"]);
}

void running_time_single_key_scenario(){
    int speck_versions[5] = {32, 48, 64, 96, 128};
    int number_rounds_per_speck_version[5][10] = {
            {1, 2, 3, 4, 5, 6, 0, 0, 0, 0 },
            {1, 2, 3, 4, 5, 6, 7, 0, 0, 0 },
            {1, 2, 3, 4, 5, 6, 7, 8, 0, 0 },
            {1, 2, 3, 4, 5, 6, 7, 8, 9, 0 },
            {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    };
    int number_of_speck_versions = 5;
    int max_number_of_rounds = 8;
    for (int i = 3; i < number_of_speck_versions; i++) {
        for (int j = 1; j < max_number_of_rounds; j++) {
            for (int window_size = -1; window_size < 4; window_size++) {
                if (number_rounds_per_speck_version[i][j] != 0) {
                    int block_size = speck_versions[i];
                    int half_block_size = block_size/2;
                    const int top_number_of_rounds = number_rounds_per_speck_version[i][j];
                    const int bottom_number_of_rounds = top_number_of_rounds;

                    switch (half_block_size) {
                        case 16: {
                            run_one_experiment<16>(half_block_size, window_size, top_number_of_rounds, bottom_number_of_rounds);
                        } break;
                        case 24: {
                            run_one_experiment<24>(half_block_size, window_size, top_number_of_rounds, bottom_number_of_rounds);
                        } break;
                        case 32: {
                            run_one_experiment<32>(half_block_size, window_size, top_number_of_rounds, bottom_number_of_rounds);
                        } break;
                        case 48: {
                            run_one_experiment<48>(half_block_size, window_size, top_number_of_rounds, bottom_number_of_rounds);
                        } break;
                        case 64:{
                            run_one_experiment<64>(half_block_size, window_size, top_number_of_rounds, bottom_number_of_rounds);
                        } break;
                        default:
                            printf("Speck version does not exists");
                            exit(-1);

                    }
                }
            }
        }
    }
}

int main()
{
    printf("Main speck_boomerang2\n");
    running_time_single_key_scenario();
    //search<48 / 2>(5, 5, 0, 24, 0);
    return 0;
}