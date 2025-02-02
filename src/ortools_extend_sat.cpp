#include "ortools_extend_sat.h"

BoolVec NewBoolVec(sat::CpModelBuilder &model, const int size = 4)
{
    // bv[0] is the lsb
    BoolVec bv;
    for (int i = 0; i < size; ++i) bv.push_back(model.NewBoolVar());
    return bv;
}

IntVec BV2IV(BoolVec &bv)
{
    const int len = bv.size();

    IntVec iv;
    for (int i = 0; i < len; ++i) iv.push_back(sat::IntVar(bv[i]));
    return iv;
}

void BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1, BoolVec &bv2)
{
    /*
     * bv0 ^ bv1 = bv2
     */
    const int len = bv0.size();

    for (int i = 0; i < len; ++i) {
        model.AddBoolXor({bv0[i], bv1[i], bv2[i], model.TrueVar()});
    }

    return;
}

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::IntVar b)
{
    auto iv = BV2IV(bv);
    iv.push_back(b);
    auto table = model.AddAllowedAssignments(iv);

    for (auto &value : values) {
        table.AddTuple(value);
    }

    return;
}

void BVAssignIf(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values, sat::BoolVar b)
{
    BVAssignIf(model, bv, values, sat::IntVar(b));
    return;
}

void BVAssign(sat::CpModelBuilder &model, BoolVec &bv, const std::vector<std::vector<int64_t>> &values)
{
    auto iv = BV2IV(bv);
    auto table = model.AddAllowedAssignments(iv);

    for (auto &value : values) {
        table.AddTuple(value);
    }

    return;
}

void BVAddEqualConstraint(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1)
{
    /*
     * bv0 = bv1
     */
    const int len = bv0.size();

    for (int i = 0; i < len; ++i) {
        model.AddEquality(bv0[i], bv1[i]);
    }

    return;
}

BoolVec BVXor(sat::CpModelBuilder &model, BoolVec &bv0, BoolVec &bv1)
{
    const int len = bv0.size();
    BoolVec bv2 = NewBoolVec(model, len);

    for (int i = 0; i < len; ++i) {
        model.AddBoolXor({bv0[i], bv1[i], bv2[i], model.TrueVar()});
    }

    return bv2;
}

void BVRor(sat::CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation)
{
    const int len = bv0.size();
    const int rn = rotation % len;

    for (int i = rn; i < len; ++i) {
        model.AddEquality(output[i - rn], bv0[i]);
    }
    for (int i = 0; i < rn; ++i) {
        model.AddEquality(output[i + (len - rn)], bv0[i]);
    }

    return;
}

void BVRol(sat::CpModelBuilder &model, BoolVec &output, BoolVec &bv0, const int rotation)
{
    const int len = bv0.size();
    const int rn = rotation % len;
    BVRor(model, output, bv0, len - rn);

    return;
}