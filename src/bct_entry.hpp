#pragma once

#include "absl/numeric/int128.h"

#include <array>
#include <vector>
#include <cstdint>

#include <iostream>
using std::cout;
using std::endl;


static inline bool carry(const bool a, const bool b, const bool c)
{
    return (a & b) ^ (a & c) ^ (b & c);
}

static inline bool borrow(const bool a, const bool b, const bool c)
{
    const bool na = a ^ 1;
    return (na & b) | (na & c) | (a & b & c);
}

static inline unsigned char bct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR);

unsigned long long int bct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, const int nbit);

long double bct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, const int nbit);

static inline unsigned char lbct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR, const bool nLL);

unsigned long long int lbct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, unsigned int nLL, const int nbit);

long double lbct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, uint64_t nLL, const int nbit);

static inline unsigned char ubct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR, const bool dLL);

unsigned long long int ubct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, unsigned int dLL, const int nbit);

long double ubct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, uint64_t dLL, const int nbit);

static inline unsigned char ebct_transfer(const unsigned char state, const bool l, const bool r, const bool dL, const bool dR, const bool nL, const bool nR, const bool dLL, const bool nLL);

unsigned long long int ebct_entry(unsigned int dL, unsigned int dR, unsigned int nL, unsigned int nR, unsigned int dLL, unsigned int nLL, const int nbit);

long double ebct_entry128(uint64_t dL, uint64_t dR, uint64_t nL, uint64_t nR, uint64_t dLL, uint64_t nLL, const int nbit);