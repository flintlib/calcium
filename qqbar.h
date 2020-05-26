/*
    Copyright (C) 2020 Fredrik Johansson

    This file is part of Calcium.

    Calcium is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#ifndef QQBAR_H
#define QQBAR_H

#ifdef QQBAR_INLINES_C
#define QQBAR_INLINE
#else
#define QQBAR_INLINE static __inline__
#endif

#ifdef __cplusplus
extern "C" {
#endif

#include "flint/fmpz_poly.h"
#include "flint/fmpq_poly.h"
#include "flint/fmpz_mat.h"
#include "flint/fmpq_mat.h"
#include "acb.h"

#include "calcium.h"

typedef struct
{
    fmpz_poly_struct poly;
    acb_struct enclosure;
}
qqbar_struct;

typedef qqbar_struct qqbar_t[1];
typedef qqbar_struct * qqbar_ptr;
typedef const qqbar_struct * qqbar_srcptr;

#define QQBAR_POLY(x) (&((x)->poly))
#define QQBAR_COEFFS(x) ((&((x)->poly))->coeffs)
#define QQBAR_ENCLOSURE(x) (&((x)->enclosure))

#define QQBAR_DEFAULT_PREC 128

/* Memory management */

void qqbar_init(qqbar_t res);

void qqbar_clear(qqbar_t res);

QQBAR_INLINE qqbar_ptr
qqbar_vec_init(slong len)
{
    slong i;
    qqbar_ptr vec = flint_malloc(len * sizeof(qqbar_struct));
    for (i = 0; i < len; i++)
        qqbar_init(vec + i);
    return vec;
}

QQBAR_INLINE void
qqbar_vec_clear(qqbar_ptr vec, slong len)
{
    slong i;
    for (i = 0; i < len; i++)
        qqbar_clear(vec + i);
    flint_free(vec);
}

/* Assignment */

void qqbar_swap(qqbar_t x, qqbar_t y);

void qqbar_set(qqbar_t res, const qqbar_t x);

void qqbar_set_si(qqbar_t res, slong x);

void qqbar_set_ui(qqbar_t res, ulong x);

void qqbar_set_fmpz(qqbar_t res, const fmpz_t x);

void qqbar_set_fmpq(qqbar_t res, const fmpq_t x);

void qqbar_set_re_im(qqbar_t res, const qqbar_t x, const qqbar_t y);

int qqbar_set_d(qqbar_t res, double x);

int qqbar_set_re_im_d(qqbar_t res, double x, double y);

/* Properties */

QQBAR_INLINE slong
qqbar_degree(const qqbar_t x)
{
    return fmpz_poly_degree(QQBAR_POLY(x));
}

QQBAR_INLINE int
qqbar_is_rational(const qqbar_t x)
{
    return (qqbar_degree(x) == 1);
}

QQBAR_INLINE int
qqbar_is_integer(const qqbar_t x)
{
    return qqbar_is_rational(x) && fmpz_is_one(QQBAR_COEFFS(x) + 1);
}

QQBAR_INLINE int
qqbar_is_algebraic_integer(const qqbar_t x)
{
    return fmpz_is_one(QQBAR_COEFFS(x) + qqbar_degree(x));
}

QQBAR_INLINE int
qqbar_is_zero(const qqbar_t x)
{
    return qqbar_is_integer(x) && fmpz_is_zero(QQBAR_COEFFS(x));
}

QQBAR_INLINE int
qqbar_is_one(const qqbar_t x)
{
    return qqbar_is_integer(x) && (fmpz_equal_si(QQBAR_COEFFS(x), -1));
}

QQBAR_INLINE int
qqbar_is_neg_one(const qqbar_t x)
{
    return qqbar_is_integer(x) && fmpz_is_one(QQBAR_COEFFS(x));
}

int qqbar_sgn_re(const qqbar_t x);

int qqbar_sgn_im(const qqbar_t x);

QQBAR_INLINE int
qqbar_is_real(const qqbar_t x)
{
    return qqbar_sgn_im(x) == 0;
}

slong qqbar_height_bits(const qqbar_t x);

void qqbar_height(fmpz_t res, const qqbar_t x);

/* Special values */

QQBAR_INLINE void
qqbar_zero(qqbar_t res)
{
    qqbar_set_ui(res, 0);
}

QQBAR_INLINE void
qqbar_one(qqbar_t res)
{
    qqbar_set_ui(res, 1);
}

void qqbar_i(qqbar_t res);

void qqbar_phi(qqbar_t res);

/* Random generation */

void qqbar_randtest(qqbar_t res, flint_rand_t state, slong deg, slong bits);

void qqbar_randtest_real(qqbar_t res, flint_rand_t state, slong deg, slong bits);

void qqbar_randtest_nonreal(qqbar_t res, flint_rand_t state, slong deg, slong bits);

/* Input and output */

void qqbar_print(const qqbar_t x);

void qqbar_printn(const qqbar_t x, slong n);

void qqbar_printnd(const qqbar_t x, slong n);

/* Comparisons */

int qqbar_equal(const qqbar_t x, const qqbar_t y);

int qqbar_cmp_re(const qqbar_t x, const qqbar_t y);

int qqbar_cmp_im(const qqbar_t x, const qqbar_t y);

int qqbar_cmpabs_re(const qqbar_t x, const qqbar_t y);

int qqbar_cmpabs_im(const qqbar_t x, const qqbar_t y);

int qqbar_cmpabs(const qqbar_t x, const qqbar_t y);

/* Complex parts */

void qqbar_conj(qqbar_t res, const qqbar_t x);

void qqbar_re(qqbar_t res, const qqbar_t x);

void qqbar_im(qqbar_t res, const qqbar_t x);

void qqbar_re_im(qqbar_t res1, qqbar_t res2, const qqbar_t x);

void qqbar_abs(qqbar_t res, const qqbar_t x);

void qqbar_abs2(qqbar_t res, const qqbar_t x);

void qqbar_sgn(qqbar_t res, const qqbar_t x);

int qqbar_csgn(const qqbar_t x);

/* Integer parts */

void qqbar_floor(fmpz_t res, const qqbar_t x);

void qqbar_ceil(fmpz_t res, const qqbar_t x);

/* Arithmetic */

void qqbar_neg(qqbar_t res, const qqbar_t x);

void qqbar_add(qqbar_t res, const qqbar_t x, const qqbar_t y);
void qqbar_add_fmpq(qqbar_t res, const qqbar_t x, const fmpq_t y);
void qqbar_add_fmpz(qqbar_t res, const qqbar_t x, const fmpz_t y);
void qqbar_add_ui(qqbar_t res, const qqbar_t x, ulong y);
void qqbar_add_si(qqbar_t res, const qqbar_t x, slong y);

void qqbar_sub(qqbar_t res, const qqbar_t x, const qqbar_t y);
void qqbar_sub_fmpq(qqbar_t res, const qqbar_t x, const fmpq_t y);
void qqbar_sub_fmpz(qqbar_t res, const qqbar_t x, const fmpz_t y);
void qqbar_sub_ui(qqbar_t res, const qqbar_t x, ulong y);
void qqbar_sub_si(qqbar_t res, const qqbar_t x, slong y);

void qqbar_mul(qqbar_t res, const qqbar_t x, const qqbar_t y);
void qqbar_mul_fmpq(qqbar_t res, const qqbar_t x, const fmpq_t y);
void qqbar_mul_fmpz(qqbar_t res, const qqbar_t x, const fmpz_t y);
void qqbar_mul_ui(qqbar_t res, const qqbar_t x, ulong y);
void qqbar_mul_si(qqbar_t res, const qqbar_t x, slong y);

void qqbar_div(qqbar_t res, const qqbar_t x, const qqbar_t y);
void qqbar_div_fmpq(qqbar_t res, const qqbar_t x, const fmpq_t y);
void qqbar_div_fmpz(qqbar_t res, const qqbar_t x, const fmpz_t y);
void qqbar_div_ui(qqbar_t res, const qqbar_t x, ulong y);
void qqbar_div_si(qqbar_t res, const qqbar_t x, slong y);
void qqbar_fmpq_div(qqbar_t res, const fmpq_t x, const qqbar_t y);
void qqbar_fmpz_div(qqbar_t res, const fmpz_t x, const qqbar_t y);
void qqbar_ui_div(qqbar_t res, ulong x, const qqbar_t y);
void qqbar_si_div(qqbar_t res, slong x, const qqbar_t y);


QQBAR_INLINE void
qqbar_sqr(qqbar_t res, const qqbar_t x)
{
    qqbar_mul(res, x, x);
}

void qqbar_inv(qqbar_t res, const qqbar_t x);

void qqbar_mul_2exp_si(qqbar_t res, const qqbar_t x, slong exp);

void qqbar_pow_ui(qqbar_t res, const qqbar_t x, ulong n);

void qqbar_root_ui(qqbar_t res, const qqbar_t x, ulong n);

QQBAR_INLINE void
qqbar_sqrt(qqbar_t res, const qqbar_t x)
{
    qqbar_root_ui(res, x, 2);
}

QQBAR_INLINE void
qqbar_rsqrt(qqbar_t res, const qqbar_t x)
{
    qqbar_sqrt(res, x);
    qqbar_inv(res, res);
}

/* Numerical enclosure */

void qqbar_cache_enclosure(qqbar_t res, slong prec);

void qqbar_get_acb(acb_t res, const qqbar_t x, slong prec);

void qqbar_get_arb(arb_t res, const qqbar_t x, slong prec);

void qqbar_get_arb_re(arb_t res, const qqbar_t x, slong prec);

void qqbar_get_arb_im(arb_t res, const qqbar_t x, slong prec);

/* Conjugates */

void qqbar_conjugates(qqbar_ptr res, const qqbar_t x);

/* Polynomial operations */

void _qqbar_evaluate_fmpq_poly(qqbar_t res, const fmpz * poly, const fmpz_t den, slong len, const qqbar_t x);

void qqbar_evaluate_fmpq_poly(qqbar_t res, const fmpq_poly_t poly, const qqbar_t x);

void _qqbar_evaluate_fmpz_poly(qqbar_t res, const fmpz * poly, slong len, const qqbar_t x);

void qqbar_evaluate_fmpz_poly(qqbar_t res, const fmpz_poly_t poly, const qqbar_t x);

#define QQBAR_ROOTS_IRREDUCIBLE 1

void qqbar_roots_fmpz_poly(qqbar_ptr res, const fmpz_poly_t poly, int flags);

void qqbar_roots_fmpq_poly(qqbar_ptr res, const fmpq_poly_t poly, int flags);

void qqbar_eigenvalues_fmpz_mat(qqbar_ptr res, const fmpz_mat_t mat, int flags);

void qqbar_eigenvalues_fmpq_mat(qqbar_ptr res, const fmpq_mat_t mat, int flags);

/* Roots of unity and trigonometric functions */

void qqbar_root_of_unity(qqbar_t res, slong p, ulong q);

int qqbar_is_root_of_unity(slong * p, ulong * q, const qqbar_t x);

void qqbar_exp_pi_i(qqbar_t res, slong p, ulong q);

void qqbar_cos_pi(qqbar_t res, slong p, ulong q);

void qqbar_sin_pi(qqbar_t res, slong p, ulong q);

void qqbar_tan_pi(qqbar_t res, slong p, ulong q);

void qqbar_cot_pi(qqbar_t res, slong p, ulong q);

void qqbar_sec_pi(qqbar_t res, slong p, ulong q);

void qqbar_csc_pi(qqbar_t res, slong p, ulong q);

int qqbar_log_pi_i(slong * p, ulong * q, const qqbar_t x);

int qqbar_atan_pi(slong * p, ulong * q, const qqbar_t x);

int qqbar_asin_pi(slong * p, ulong * q, const qqbar_t x);

int qqbar_acos_pi(slong * p, ulong * q, const qqbar_t x);

int qqbar_acot_pi(slong * p, ulong * q, const qqbar_t x);

int qqbar_asec_pi(slong * p, ulong * q, const qqbar_t x);

int qqbar_acsc_pi(slong * p, ulong * q, const qqbar_t x);

/* Guessing and simplification */

int qqbar_guess(qqbar_t res, const acb_t z, slong max_deg, slong max_bits, int flags, slong prec);

int qqbar_express_in_field(fmpq_poly_t res, const qqbar_t alpha, const qqbar_t x, slong max_bits, int flags, slong prec);

/* Internal functions */

void qqbar_scalar_op(qqbar_t res, const qqbar_t x, const fmpz_t a, const fmpz_t b, const fmpz_t c);

void qqbar_fmpz_poly_composed_op(fmpz_poly_t res, const fmpz_poly_t A, const fmpz_poly_t B, int op);

void qqbar_binary_op(qqbar_t res, const qqbar_t x, const qqbar_t y, int op);

int _qqbar_validate_uniqueness(acb_t res, const fmpz_poly_t poly, const acb_t z, slong max_prec);

int _qqbar_validate_existence_uniqueness(acb_t res, const fmpz_poly_t poly, const acb_t z, slong prec);

void _qqbar_enclosure_raw(acb_t res, const fmpz_poly_t poly, const acb_t zin, slong prec);

void qqbar_enclosure_raw(acb_t res, const qqbar_t x, slong prec);

int _qqbar_acb_lindep(fmpz * rel, acb_srcptr vec, slong len, int check, slong prec);

#ifdef __cplusplus
}
#endif

#endif
