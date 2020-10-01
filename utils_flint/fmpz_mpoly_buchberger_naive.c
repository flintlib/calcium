/*
    Copyright (C) 2020 Fredrik Johansson

    This file is part of Calcium.

    Calcium is free software: you can redistribute it and/or modify it under
    the terms of the GNU Lesser General Public License (LGPL) as published
    by the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.  See <http://www.gnu.org/licenses/>.
*/

#include "utils_flint.h"

static int
within_limits(const fmpz_mpoly_t poly, slong poly_len_limit, slong poly_bits_limit, const fmpz_mpoly_ctx_t ctx)
{
    slong bits;

    if (fmpz_mpoly_length(poly, ctx) > poly_len_limit)
        return 0;

    bits = fmpz_mpoly_max_bits(poly);
    bits = FLINT_ABS(bits);

    if (bits > poly_bits_limit)
        return 0;

    return 1;
}

#if 0

int
fmpz_mpoly_buchberger_naive_with_limits(fmpz_mpoly_vec_t G, const fmpz_mpoly_vec_t F,
    slong ideal_len_limit, slong poly_len_limit, slong poly_bits_limit, const fmpz_mpoly_ctx_t ctx)
{
    pairs_t B;
    fmpz_mpoly_t h;
    slong i, j, index_h;
    pair_t pair;
    int success;

    fmpz_mpoly_vec_set_primitive_unique(G, F, ctx);

    if (G->length <= 1)
        return 1;

    if (G->length >= ideal_len_limit)
        return 0;

    for (i = 0; i < G->length; i++)
        if (!within_limits(fmpz_mpoly_vec_entry(G, i), poly_len_limit, poly_bits_limit, ctx))
            return 0;

    pairs_init(B);
    fmpz_mpoly_init(h, ctx);

    for (i = 0; i < G->length; i++)
        for (j = i + 1; j < G->length; j++)
            pairs_append(B, i, j);

    success = 1;
    while (B->length != 0)
    {
        pair = fmpz_mpoly_select_pop_pair(B, G, ctx);

        fmpz_mpoly_spoly(h, fmpz_mpoly_vec_entry(G, pair.a), fmpz_mpoly_vec_entry(G, pair.b), ctx);
        fmpz_mpoly_reduction_primitive_part(h, h, G, ctx);

        if (!fmpz_mpoly_is_zero(h, ctx))
        {
            /* printf("h stats %ld, %ld, %ld\n", h->length, h->bits, G->length); */

            if (G->length >= ideal_len_limit || !within_limits(h, poly_len_limit, poly_bits_limit, ctx))
            {
                success = 0;
                break;
            }

            index_h = G->length;
            fmpz_mpoly_vec_append(G, h, ctx);

            for (i = 0; i < index_h; i++)
                pairs_append(B, i, index_h);
        }
    }

    fmpz_mpoly_clear(h, ctx);
    pairs_clear(B);

    return success;
}

#else

void
fmpz_mpoly_reduction_primitive_part2(fmpz_mpoly_t res, const fmpz_mpoly_t f, const fmpz_mpoly_vec_t Ipoly, const pairs_t I, const fmpz_mpoly_ctx_t ctx)
{
    fmpz_t scale;
    fmpz_mpoly_struct ** Q, ** B;
    slong i, len;

    len = I->length;

    fmpz_init(scale);
    Q = flint_malloc(sizeof(fmpz_mpoly_struct *) * len);
    B = flint_malloc(sizeof(fmpz_mpoly_struct *) * len);

    for (i = 0; i < len; i++)
    {
        Q[i] = flint_malloc(sizeof(fmpz_mpoly_struct));
        fmpz_mpoly_init(Q[i], ctx);
        B[i] = Ipoly->p + I->pairs[i].a;
    }

    fmpz_mpoly_quasidivrem_ideal(scale, Q, res, f, B, len, ctx);

    for (i = 0; i < len; i++)
    {
        fmpz_mpoly_clear(Q[i], ctx);
        flint_free(Q[i]);
    }

    flint_free(Q);
    flint_free(B);
    fmpz_clear(scale);
}

static void
monomial_lcm(ulong * lcm, const ulong * exp1, const ulong * exp2, slong nvars)
{
    slong i;
    for (i = 0; i < nvars; i++)
        lcm[i] = FLINT_MAX(exp1[i], exp2[i]);
}

static int
monomials_are_disjoint(const ulong * exp1, const ulong * exp2, slong nvars)
{
    slong i;
    for (i = 0; i < nvars; i++)
        if (FLINT_MAX(exp1[i], exp2[i]) != 0)
            return 0;
    return 1;
}

static int
monomial_equal(const ulong * exp1, const ulong * exp2, slong nvars)
{
    slong i;
    for (i = 0; i < nvars; i++)
        if (exp1[i] != exp2[i])
            return 0;
    return 1;
}

static int
monomial_divides(const ulong * exp1, const ulong * exp2, slong nvars)
{
    slong i;
    for (i = 0; i < nvars; i++)
        if (exp1[i] > exp2[i])
            return 0;
    return 1;
}


#define VERBOSE 0

void
fmpz_mpoly_buchberger_update(pairs_t G, pairs_t B, fmpz_mpoly_vec_t G_all, const fmpz_mpoly_t h, const fmpz_mpoly_ctx_t ctx)
{
    pairs_t C, D, E, Bnew;
    slong i, j, h_index, nvars;
    ulong * HTh, * HTga, * HTgb, *lcm1, *lcm2;
    int disjoint;

    nvars = ctx->minfo->nvars;

    HTh = flint_malloc(nvars * sizeof(ulong));
    HTga = flint_malloc(nvars * sizeof(ulong));
    HTgb = flint_malloc(nvars * sizeof(ulong));
    lcm1 = flint_malloc(nvars * sizeof(ulong));
    lcm2 = flint_malloc(nvars * sizeof(ulong));

    pairs_init(C);
    pairs_init(D);
    pairs_init(E);
    pairs_init(Bnew);

    fmpz_mpoly_get_term_exp_ui(HTh, h, 0, ctx);

    /* Store the polynomial h in G_all so that it has an index */


#if 1
    h_index = fmpz_mpoly_vec_insert_unique(G_all, h, ctx);
#else
    h_index = G_all->length;
    fmpz_mpoly_vec_append(G_all, h, ctx);
#endif

    /* Step 1: build C */
    for (i = 0; i < G->length; i++)
        pairs_append(C, h_index, G->pairs[i].a);

    /* Step 2: build D */
    while (C->length != 0)
    {
        j = C->pairs[C->length - 1].b;             /* Pop from C. */
        C->length--;

        /* HT(h) and HT(g) are disjoint? */
        fmpz_mpoly_get_term_exp_ui(HTgb, G_all->p + j, 0, ctx);

        if (monomials_are_disjoint(HTh, HTgb, nvars))
        {
            pairs_append(D, h_index, j);
        }
        else
        {
            monomial_lcm(lcm2, HTh, HTgb, nvars);

            disjoint = 1;
            for (i = 0; i < C->length && disjoint; i++)
            {
                fmpz_mpoly_get_term_exp_ui(HTga, G_all->p + C->pairs[i].b, 0, ctx);
                monomial_lcm(lcm1, HTh, HTga, nvars);

                if (monomial_divides(lcm1, lcm2, nvars))
                    disjoint = 0;
            }

            for (i = 0; i < D->length && disjoint; i++)
            {
                fmpz_mpoly_get_term_exp_ui(HTga, G_all->p + D->pairs[i].b, 0, ctx);
                monomial_lcm(lcm1, HTh, HTga, nvars);

                if (monomial_divides(lcm1, lcm2, nvars))
                    disjoint = 0;
            }

            if (disjoint)
                pairs_append(D, h_index, j);
        }
    }

    /* Step 3: build E */
    while (D->length != 0)
    {
        /* pop from D */
        i = D->pairs[D->length - 1].a;
        j = D->pairs[D->length - 1].b;
        D->length--;

        if (i != h_index)
            flint_abort();

        fmpz_mpoly_get_term_exp_ui(HTgb, G_all->p + j, 0, ctx);

        if (!monomials_are_disjoint(HTh, HTgb, nvars))
            pairs_append(E, h_index, j);
    }

    /* Step 4: build B_new (todo: inplace) */
    while (B->length != 0)
    {
        /* pop from B */
        i = B->pairs[B->length - 1].a;
        j = B->pairs[B->length - 1].b;
        B->length--;

        fmpz_mpoly_get_term_exp_ui(HTga, G_all->p + i, 0, ctx);
        fmpz_mpoly_get_term_exp_ui(HTgb, G_all->p + j, 0, ctx);
        monomial_lcm(lcm1, HTga, HTgb, nvars);

        if (!monomial_divides(HTh, lcm1, nvars))
        {
            pairs_append(Bnew, i, j);
            continue;
        }

        monomial_lcm(lcm1, HTga, HTh, nvars);
        monomial_lcm(lcm2, HTga, HTgb, nvars);
        if (monomial_equal(lcm1, lcm2, nvars))
        {
            pairs_append(Bnew, i, j);
            continue;
        }

        monomial_lcm(lcm1, HTgb, HTh, nvars);
        if (monomial_equal(lcm1, lcm2, nvars))
        {
            pairs_append(Bnew, i, j);
            continue;
        }
    }

    /* B = Bnew union E */
    B->length = 0;
    for (i = 0; i < Bnew->length; i++)
    {
        slong a, b;
        a = FLINT_MIN(Bnew->pairs[i].a, Bnew->pairs[i].b);
        b = FLINT_MAX(Bnew->pairs[i].a, Bnew->pairs[i].b);
        pairs_insert_unique(B, a, b);  /* append? */
    }

    for (i = 0; i < E->length; i++)
    {
        slong a, b;
        a = FLINT_MIN(E->pairs[i].a, E->pairs[i].b);
        b = FLINT_MAX(E->pairs[i].a, E->pairs[i].b);
        pairs_insert_unique(B, a, b);
    }

    /* Step 5: update G */

    for (i = 0; i < G->length; i++)
    {
        fmpz_mpoly_get_term_exp_ui(HTga, G_all->p + G->pairs[i].a, 0, ctx);

        /* remove from G */

        if (monomial_divides(HTh, HTga, nvars))
        {
            G->pairs[i] = G->pairs[G->length - 1];
            G->length--;
        }
    }

    pairs_insert_unique(G, h_index, h_index);

    pairs_clear(C);
    pairs_clear(D);
    pairs_clear(E);
    pairs_clear(Bnew);

    flint_free(HTh);
    flint_free(HTga);
    flint_free(HTgb);
    flint_free(lcm1);
    flint_free(lcm2);
}

int
fmpz_mpoly_buchberger_naive_with_limits(fmpz_mpoly_vec_t G_out, const fmpz_mpoly_vec_t F,
    slong ideal_len_limit, slong poly_len_limit, slong poly_bits_limit, const fmpz_mpoly_ctx_t ctx)
{
    pairs_t B, G;
    fmpz_mpoly_vec_t G_all;
    fmpz_mpoly_t h;
    slong i;
    pair_t pair;
    pairs_t FF;
    int success;

    fmpz_mpoly_vec_set_primitive_unique(G_out, F, ctx);

    if (G_out->length <= 1)
        return 1;

    for (i = 0; i < G_out->length; i++)
        if (!within_limits(fmpz_mpoly_vec_entry(G_out, i), poly_len_limit, poly_bits_limit, ctx))
            return 0;

    success = 1;

    fmpz_mpoly_vec_init(G_all, ctx);

    pairs_init(B);
    pairs_init(G);   /* not actually pairs, but we will use it for convenience */

    fmpz_mpoly_init(h, ctx);

    pairs_init(FF);
    for (i = 0; i < G_out->length; i++)
        pairs_append(FF, i, i);

    for (i = 0; i < G_out->length; i++)
    {
        pair = fmpz_mpoly_select_pop_pair(FF, G_out, ctx);
        fmpz_mpoly_set(h, F->p + pair.a, ctx);
        fmpz_mpoly_buchberger_update(G, B, G_all, h, ctx);
    }

    pairs_clear(FF);

    while (B->length != 0)
    {
        pair = fmpz_mpoly_select_pop_pair(B, G_all, ctx);
        fmpz_mpoly_spoly(h, G_all->p + pair.a, G_all->p + pair.b, ctx);
        fmpz_mpoly_reduction_primitive_part2(h, h, G_all, G, ctx);

        if (!fmpz_mpoly_is_zero(h, ctx))
        {
            if (G->length >= ideal_len_limit || !within_limits(h, poly_len_limit, poly_bits_limit, ctx))
            {
                success = 0;
                break;
            }

            fmpz_mpoly_buchberger_update(G, B, G_all, h, ctx);
        }
    }

    G_out->length = 0;
    for (i = 0; i < G->length; i++)
        fmpz_mpoly_vec_append(G_out, G_all->p + G->pairs[i].a, ctx);

    fmpz_mpoly_vec_clear(G_all, ctx);

    pairs_clear(B);
    pairs_clear(G);

    return success;
}

#endif

void
fmpz_mpoly_buchberger_naive(fmpz_mpoly_vec_t G, const fmpz_mpoly_vec_t F, const fmpz_mpoly_ctx_t ctx)
{
    pairs_t B;
    fmpz_mpoly_t h;
    slong i, j, index_h;
    pair_t pair;

    fmpz_mpoly_vec_set_primitive_unique(G, F, ctx);

    if (G->length <= 1)
        return;

    pairs_init(B);
    fmpz_mpoly_init(h, ctx);

    for (i = 0; i < G->length; i++)
        for (j = i + 1; j < G->length; j++)
            pairs_append(B, i, j);

    while (B->length != 0)
    {
        pair = fmpz_mpoly_select_pop_pair(B, G, ctx);
        fmpz_mpoly_spoly(h, fmpz_mpoly_vec_entry(G, pair.a), fmpz_mpoly_vec_entry(G, pair.b), ctx);
        fmpz_mpoly_reduction_primitive_part(h, h, G, ctx);

        if (!fmpz_mpoly_is_zero(h, ctx))
        {
            index_h = G->length;
            fmpz_mpoly_vec_append(G, h, ctx);

            for (i = 0; i < index_h; i++)
                pairs_append(B, i, index_h);
        }
    }

    fmpz_mpoly_clear(h, ctx);
    pairs_clear(B);
}
