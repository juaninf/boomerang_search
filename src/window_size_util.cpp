//
// Created by Juan del Carmen Grados Vasquez on 30/05/2023.
//

#include "ortools/sat/cp_model.h"
#include "ortools_extend_sat.h"
#include "window_size_util.h"





void window_size_0_cnf(sat::CpModelBuilder &model, BoolVec &x) {
    model.AddBoolOr({x[0], x[1], Not(x[2])});
    model.AddBoolOr({x[0], x[2], Not(x[1])});
    model.AddBoolOr({x[1], x[2], Not(x[0])});
    model.AddBoolOr({Not(x[0]), Not(x[1]), Not(x[2])});
}

void window_size_1_cnf(sat::CpModelBuilder &model, BoolVec &x) {
    model.AddBoolOr({x[0], x[1], x[3], x[4], Not(x[2]), Not(x[5])});
    model.AddBoolOr({x[0], x[1], x[3], x[5], Not(x[2]), Not(x[4])});
    model.AddBoolOr({x[0], x[1], x[4], x[5], Not(x[2]), Not(x[3])});
    model.AddBoolOr({x[0], x[2], x[3], x[4], Not(x[1]), Not(x[5])});
    model.AddBoolOr({x[0], x[2], x[3], x[5], Not(x[1]), Not(x[4])});
    model.AddBoolOr({x[0], x[2], x[4], x[5], Not(x[1]), Not(x[3])});
    model.AddBoolOr({x[1], x[2], x[3], x[4], Not(x[0]), Not(x[5])});
    model.AddBoolOr({x[1], x[2], x[3], x[5], Not(x[0]), Not(x[4])});
    model.AddBoolOr({x[1], x[2], x[4], x[5], Not(x[0]), Not(x[3])});
    model.AddBoolOr({x[0], x[1], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5])});
    model.AddBoolOr({x[0], x[2], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5])});
    model.AddBoolOr({x[1], x[2], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5])});
    model.AddBoolOr({x[3], x[4], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5])});
    model.AddBoolOr({x[3], x[5], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4])});
    model.AddBoolOr({x[4], x[5], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3])});
    model.AddBoolOr({Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5])});
}


void window_size_2_cnf(sat::CpModelBuilder &model, BoolVec &x) {
    model.AddBoolOr({x[0], x[1], x[3], x[4], x[6], x[7], Not(x[2]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[3], x[4], x[6], x[8], Not(x[2]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[3], x[4], x[7], x[8], Not(x[2]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[3], x[5], x[6], x[7], Not(x[2]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[3], x[5], x[6], x[8], Not(x[2]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[3], x[5], x[7], x[8], Not(x[2]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[4], x[5], x[6], x[7], Not(x[2]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[4], x[5], x[6], x[8], Not(x[2]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[4], x[5], x[7], x[8], Not(x[2]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[0], x[2], x[3], x[4], x[6], x[7], Not(x[1]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[3], x[4], x[6], x[8], Not(x[1]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[2], x[3], x[4], x[7], x[8], Not(x[1]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[2], x[3], x[5], x[6], x[7], Not(x[1]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[3], x[5], x[6], x[8], Not(x[1]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[0], x[2], x[3], x[5], x[7], x[8], Not(x[1]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[0], x[2], x[4], x[5], x[6], x[7], Not(x[1]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[4], x[5], x[6], x[8], Not(x[1]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[0], x[2], x[4], x[5], x[7], x[8], Not(x[1]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[1], x[2], x[3], x[4], x[6], x[7], Not(x[0]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[3], x[4], x[6], x[8], Not(x[0]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[1], x[2], x[3], x[4], x[7], x[8], Not(x[0]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[1], x[2], x[3], x[5], x[6], x[7], Not(x[0]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[3], x[5], x[6], x[8], Not(x[0]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[1], x[2], x[3], x[5], x[7], x[8], Not(x[0]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[1], x[2], x[4], x[5], x[6], x[7], Not(x[0]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[4], x[5], x[6], x[8], Not(x[0]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[1], x[2], x[4], x[5], x[7], x[8], Not(x[0]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[3], x[4], Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[3], x[5], Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[4], x[5], Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[6], x[7], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[6], x[8], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[7], x[8], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[2], x[3], x[4], Not(x[1]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[3], x[5], Not(x[1]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[4], x[5], Not(x[1]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[6], x[7], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], x[6], x[8], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[2], x[7], x[8], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[1], x[2], x[3], x[4], Not(x[0]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[3], x[5], Not(x[0]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[4], x[5], Not(x[0]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[6], x[7], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], x[6], x[8], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[1], x[2], x[7], x[8], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[3], x[4], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[3], x[4], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[3], x[4], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[3], x[5], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[3], x[5], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[3], x[5], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[4], x[5], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[4], x[5], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[4], x[5], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[0], x[2], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[1], x[2], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[3], x[4], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[3], x[5], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[4], x[5], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr({x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
}


void window_size_3_cnf(sat::CpModelBuilder &model, BoolVec &x) {
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[3], x[4], x[6], x[7], Not(x[2]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[3], x[4], x[6], x[8], Not(x[2]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[3], x[4], x[7], x[8], Not(x[2]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[3], x[5], x[6], x[7], Not(x[2]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[3], x[5], x[6], x[8], Not(x[2]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[3], x[5], x[7], x[8], Not(x[2]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[4], x[5], x[6], x[7], Not(x[2]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[4], x[5], x[6], x[8], Not(x[2]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[11], x[4], x[5], x[7], x[8], Not(x[2]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[0], x[1], x[10], x[3], x[4], x[6], x[7], x[9], Not(x[11]), Not(x[2]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[10], x[3], x[4], x[6], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[10], x[3], x[4], x[7], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[10], x[3], x[5], x[6], x[7], x[9], Not(x[11]), Not(x[2]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[10], x[3], x[5], x[6], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[10], x[3], x[5], x[7], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[10], x[4], x[5], x[6], x[7], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[10], x[4], x[5], x[6], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[10], x[4], x[5], x[7], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[11], x[3], x[4], x[6], x[7], x[9], Not(x[10]), Not(x[2]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[11], x[3], x[4], x[6], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[11], x[3], x[4], x[7], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[11], x[3], x[5], x[6], x[7], x[9], Not(x[10]), Not(x[2]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[11], x[3], x[5], x[6], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[11], x[3], x[5], x[7], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[0], x[1], x[11], x[4], x[5], x[6], x[7], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[0], x[1], x[11], x[4], x[5], x[6], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[0], x[1], x[11], x[4], x[5], x[7], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[3], x[4], x[6], x[7], Not(x[1]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[3], x[4], x[6], x[8], Not(x[1]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[3], x[4], x[7], x[8], Not(x[1]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[3], x[5], x[6], x[7], Not(x[1]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[3], x[5], x[6], x[8], Not(x[1]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[3], x[5], x[7], x[8], Not(x[1]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[4], x[5], x[6], x[7], Not(x[1]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[4], x[5], x[6], x[8], Not(x[1]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[11], x[2], x[4], x[5], x[7], x[8], Not(x[1]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[0], x[10], x[2], x[3], x[4], x[6], x[7], x[9], Not(x[1]), Not(x[11]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[10], x[2], x[3], x[4], x[6], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[10], x[2], x[3], x[4], x[7], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[10], x[2], x[3], x[5], x[6], x[7], x[9], Not(x[1]), Not(x[11]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[0], x[10], x[2], x[3], x[5], x[6], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[0], x[10], x[2], x[3], x[5], x[7], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[0], x[10], x[2], x[4], x[5], x[6], x[7], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[0], x[10], x[2], x[4], x[5], x[6], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[0], x[10], x[2], x[4], x[5], x[7], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[0], x[11], x[2], x[3], x[4], x[6], x[7], x[9], Not(x[1]), Not(x[10]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[0], x[11], x[2], x[3], x[4], x[6], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[0], x[11], x[2], x[3], x[4], x[7], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[0], x[11], x[2], x[3], x[5], x[6], x[7], x[9], Not(x[1]), Not(x[10]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[0], x[11], x[2], x[3], x[5], x[6], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[0], x[11], x[2], x[3], x[5], x[7], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[0], x[11], x[2], x[4], x[5], x[6], x[7], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[0], x[11], x[2], x[4], x[5], x[6], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[0], x[11], x[2], x[4], x[5], x[7], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[3], x[4], x[6], x[7], Not(x[0]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[3], x[4], x[6], x[8], Not(x[0]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[3], x[4], x[7], x[8], Not(x[0]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[3], x[5], x[6], x[7], Not(x[0]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[3], x[5], x[6], x[8], Not(x[0]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[3], x[5], x[7], x[8], Not(x[0]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[4], x[5], x[6], x[7], Not(x[0]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[4], x[5], x[6], x[8], Not(x[0]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[11], x[2], x[4], x[5], x[7], x[8], Not(x[0]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr({x[1], x[10], x[2], x[3], x[4], x[6], x[7], x[9], Not(x[0]), Not(x[11]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[1], x[10], x[2], x[3], x[4], x[6], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[1], x[10], x[2], x[3], x[4], x[7], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[1], x[10], x[2], x[3], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[11]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[1], x[10], x[2], x[3], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[1], x[10], x[2], x[3], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[1], x[10], x[2], x[4], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[1], x[10], x[2], x[4], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[1], x[10], x[2], x[4], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[6])});
    model.AddBoolOr({x[1], x[11], x[2], x[3], x[4], x[6], x[7], x[9], Not(x[0]), Not(x[10]), Not(x[5]), Not(x[8])});
    model.AddBoolOr({x[1], x[11], x[2], x[3], x[4], x[6], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[5]), Not(x[7])});
    model.AddBoolOr({x[1], x[11], x[2], x[3], x[4], x[7], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[5]), Not(x[6])});
    model.AddBoolOr({x[1], x[11], x[2], x[3], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[10]), Not(x[4]), Not(x[8])});
    model.AddBoolOr({x[1], x[11], x[2], x[3], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[4]), Not(x[7])});
    model.AddBoolOr({x[1], x[11], x[2], x[3], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[4]), Not(x[6])});
    model.AddBoolOr({x[1], x[11], x[2], x[4], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[8])});
    model.AddBoolOr({x[1], x[11], x[2], x[4], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[7])});
    model.AddBoolOr({x[1], x[11], x[2], x[4], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[6])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], x[3], x[4], Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], x[3], x[5], Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], x[4], x[5], Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], x[6], x[7], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], x[6], x[8], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], x[7], x[8], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[3], x[4], x[9], Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[3], x[5], x[9], Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[4], x[5], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[6], x[7], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[6], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[7], x[8], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[3], x[4], x[9], Not(x[10]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[3], x[5], x[9], Not(x[10]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[4], x[5], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[6], x[7], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[6], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[7], x[8], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[4], x[6], x[7], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[4], x[6], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[4], x[7], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[5], x[6], x[7], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[5], x[6], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[5], x[7], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[4], x[5], x[6], x[7], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[4], x[5], x[6], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[4], x[5], x[7], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], x[3], x[4], Not(x[1]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], x[3], x[5], Not(x[1]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], x[4], x[5], Not(x[1]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], x[6], x[7], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], x[6], x[8], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], x[7], x[8], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[3], x[4], x[9], Not(x[1]), Not(x[11]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[3], x[5], x[9], Not(x[1]), Not(x[11]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[4], x[5], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[6], x[7], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[6], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[7], x[8], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[3], x[4], x[9], Not(x[1]), Not(x[10]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[3], x[5], x[9], Not(x[1]), Not(x[10]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[4], x[5], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[6], x[7], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[6], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[7], x[8], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[4], x[6], x[7], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[4], x[6], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[4], x[7], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[5], x[6], x[7], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[5], x[6], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[5], x[7], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[4], x[5], x[6], x[7], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[4], x[5], x[6], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[4], x[5], x[7], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], x[3], x[4], Not(x[0]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], x[3], x[5], Not(x[0]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], x[4], x[5], Not(x[0]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], x[6], x[7], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], x[6], x[8], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], x[7], x[8], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[3], x[4], x[9], Not(x[0]), Not(x[11]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[3], x[5], x[9], Not(x[0]), Not(x[11]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[4], x[5], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[6], x[7], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[6], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[7], x[8], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[3], x[4], x[9], Not(x[0]), Not(x[10]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[3], x[5], x[9], Not(x[0]), Not(x[10]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[4], x[5], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[6], x[7], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[6], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[7], x[8], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[4], x[6], x[7], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[4], x[6], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[4], x[7], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[5], x[6], x[7], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[5], x[6], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[5], x[7], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[4], x[5], x[6], x[7], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[4], x[5], x[6], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[4], x[5], x[7], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[4], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[4], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[4], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[5], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[5], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[5], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[4], x[5], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[4], x[5], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[4], x[5], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[3], x[4], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[10], x[3], x[4], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[10], x[3], x[4], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[10], x[3], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[8])});
    model.AddBoolOr(
            {x[10], x[3], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[7])});
    model.AddBoolOr(
            {x[10], x[3], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6])});
    model.AddBoolOr(
            {x[10], x[4], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[8])});
    model.AddBoolOr(
            {x[10], x[4], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[7])});
    model.AddBoolOr(
            {x[10], x[4], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6])});
    model.AddBoolOr(
            {x[11], x[3], x[4], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[5]), Not(x[8])});
    model.AddBoolOr(
            {x[11], x[3], x[4], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[5]), Not(x[7])});
    model.AddBoolOr(
            {x[11], x[3], x[4], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[5]), Not(x[6])});
    model.AddBoolOr(
            {x[11], x[3], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[4]), Not(x[8])});
    model.AddBoolOr(
            {x[11], x[3], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[4]), Not(x[7])});
    model.AddBoolOr(
            {x[11], x[3], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[4]), Not(x[6])});
    model.AddBoolOr(
            {x[11], x[4], x[5], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[8])});
    model.AddBoolOr(
            {x[11], x[4], x[5], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[7])});
    model.AddBoolOr(
            {x[11], x[4], x[5], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[6])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[11], Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[10], x[9], Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[11], x[9], Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[4], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[3], x[5], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[4], x[5], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[6], x[7], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[6], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], x[7], x[8], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[11], x[2], Not(x[1]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[10], x[2], x[9], Not(x[1]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[0], x[11], x[2], x[9], Not(x[1]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[4], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[3], x[5], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[4], x[5], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[6], x[7], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[6], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], x[7], x[8], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[11], x[2], Not(x[0]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[10], x[2], x[9], Not(x[0]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[1], x[11], x[2], x[9], Not(x[0]), Not(x[10]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[4], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[3], x[5], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[4], x[5], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[6], x[7], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[6], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], x[7], x[8], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[4], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[3], x[5], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[4], x[5], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[10], x[3], x[4], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[10], x[3], x[5], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[10], x[4], x[5], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[10], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[8])});
    model.AddBoolOr(
            {x[10], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[7])});
    model.AddBoolOr(
            {x[10], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[6])});
    model.AddBoolOr(
            {x[11], x[3], x[4], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[11], x[3], x[5], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[11], x[4], x[5], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]),
             Not(x[8])});
    model.AddBoolOr(
            {x[11], x[6], x[7], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[8])});
    model.AddBoolOr(
            {x[11], x[6], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[7])});
    model.AddBoolOr(
            {x[11], x[7], x[8], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[6])});
    model.AddBoolOr(
            {x[3], x[4], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[3], x[4], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[3], x[4], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[3], x[5], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[3], x[5], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[3], x[5], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[4], x[5], x[6], x[7], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[8]),
             Not(x[9])});
    model.AddBoolOr(
            {x[4], x[5], x[6], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[7]),
             Not(x[9])});
    model.AddBoolOr(
            {x[4], x[5], x[7], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6]),
             Not(x[9])});
    model.AddBoolOr(
            {x[0], x[1], Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[0], x[2], Not(x[1]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[1], x[2], Not(x[0]), Not(x[10]), Not(x[11]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[11], Not(x[0]), Not(x[1]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[10], x[9], Not(x[0]), Not(x[1]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[11], x[9], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[7]), Not(x[8])});
    model.AddBoolOr(
            {x[3], x[4], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[5]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[3], x[5], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[4]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[4], x[5], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[6]), Not(x[7]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[6], x[7], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[8]), Not(x[9])});
    model.AddBoolOr(
            {x[6], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[7]), Not(x[9])});
    model.AddBoolOr(
            {x[7], x[8], Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]),
             Not(x[6]), Not(x[9])});
    model.AddBoolOr(
            {Not(x[0]), Not(x[1]), Not(x[10]), Not(x[11]), Not(x[2]), Not(x[3]), Not(x[4]), Not(x[5]), Not(x[6]),
             Not(x[7]), Not(x[8]), Not(x[9])});
}

void add_window_size(sat::CpModelBuilder &model, int window_size, int branchSize, BoolVec &a, BoolVec &b, BoolVec &output) {
    for (int i=0; i < branchSize - window_size; i++) {
        auto n_window_vars = NewBoolVec(model, ((window_size + 1) * 3));
        for (int j=0; j < window_size + 1; j++) {
            n_window_vars[3 * j + 0] = a[branchSize - 1 - (i + j)];
            n_window_vars[3 * j + 1] = b[branchSize - 1 - (i + j)];
            n_window_vars[3 * j + 2] = output[branchSize - 1 - (i + j)];
        }
        switch(window_size) {
            case 0:
                window_size_0_cnf(model, n_window_vars);
                break;
            case 1:
                window_size_1_cnf(model, n_window_vars);
                break;
            case 2:
                window_size_2_cnf(model, n_window_vars);
                break;
            case 3:
                window_size_3_cnf(model, n_window_vars);
                break;
            default:
                printf("Window Size not Implemented yet \n");
                exit(-1);
        }
    }
}
