#pragma once

#include <vector>
#include <string>
#include <cassert>

#include "ortools/sat/cp_model.h"
#include "ortools/linear_solver/linear_solver.h"

using namespace operations_research;

using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;

using MPBoolVec = std::vector<MPVariable*>;

BoolVec NewBoolVec(sat::CpModelBuilder &model, const int size = 4);

MPBoolVec NewBoolVec(MPSolver &solver, const int size, const std::string name);


IntVec BV2IV(BoolVec &bv);

void BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1, BoolVec &bv2);

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::IntVar b);

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::BoolVar b);

void BVAssign(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values);

BoolVec BVRor(const BoolVec &bv, const int rotation);

MPBoolVec BVRor(const MPBoolVec &bv, const int rotation);

BoolVec BVRol(BoolVec &bv, const int rotation);

MPBoolVec BVRol(MPBoolVec &bv, const int rotation);

BoolVec BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1);

//
// return b0 ^ b1 with specific name
//
MPVariable *MPBoolXor(MPSolver &model, MPVariable *b0, MPVariable *b1, const std::string name);

//
// b2 = b0 ^ b1
//
void MPBoolXor(MPSolver &model, MPVariable *b0, MPVariable *b1, MPVariable *b2);

//
// return bv0 ^ bv1 with specific name
//
MPBoolVec BVXor(MPSolver &model, MPBoolVec &bv0, MPBoolVec &bv1, const std::string name);

//
// bv2 = bv0 ^ bv1
//
MPBoolVec BVXor(MPSolver &model, MPBoolVec &bv0, MPBoolVec &bv1, MPBoolVec &bv2);

