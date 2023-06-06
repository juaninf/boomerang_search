//
// Created by Juan del Carmen Grados Vasquez on 30/05/2023.
//



using namespace operations_research;
using namespace operations_research::sat;

using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;



void window_size_0_cnf(sat::CpModelBuilder &model, BoolVec &x);

void window_size_1_cnf(sat::CpModelBuilder &model, BoolVec &x);


void window_size_2_cnf(sat::CpModelBuilder &model, BoolVec &x);


void window_size_3_cnf(sat::CpModelBuilder &model, BoolVec &x);

void add_window_size(sat::CpModelBuilder &model, int window_size, int branchSize, BoolVec &a, BoolVec &b, BoolVec &output);
