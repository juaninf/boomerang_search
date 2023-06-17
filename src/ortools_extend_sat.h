#pragma once

#include <vector>
#include <string>
#include <cassert>

#include "ortools/sat/cp_model.h"

using namespace operations_research;

using BoolVec = std::vector<sat::BoolVar>;
using IntVec = std::vector<sat::IntVar>;


BoolVec NewBoolVec(sat::CpModelBuilder &model, const int size);

IntVec BV2IV(BoolVec &bv);

void BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1, BoolVec &bv2);

void BVAddEqualConstraint(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1);

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::IntVar b);

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::BoolVar b);

void BVAssign(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values);

BoolVec BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1);

void BVRor(sat::CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation);

void BVRol(sat::CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation);
