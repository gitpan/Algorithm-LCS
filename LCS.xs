#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

struct LK {
        IV i;
        IV j;
};
struct LA {
    struct LK *arr;
    IV max;
    IV alloc;
};
struct TA {
    IV *arr;
    IV max;
    IV alloc;
};
struct CTX {
    struct TA thresh;
    struct LA links;
};

inline
static IV *ta_push(struct TA *a)
{
    a->max++;
    if (a->max == a->alloc) {
        IV *new = malloc(2 * a->alloc * sizeof *new);
        memcpy(new, a->arr, a->max * sizeof *new);
        free(a->arr);
        a->arr = new;
        a->alloc *= 2;
    }
    return &a->arr[a->max];
}

inline
static struct LK *la_push(struct LA *a)
{
    a->max++;
    if (a->max == a->alloc) {
        struct LK *new = malloc(2 * a->alloc * sizeof *new);
        memcpy(new, a->arr, a->max * sizeof *new);
        free(a->arr);
        a->arr = new;
        a->alloc *= 2;
    }
    return &a->arr[a->max];
}

inline
static IV lcs_DESTROY(SV *sv) 
{
        struct CTX *ctx = (struct CTX *)SvIVX(SvRV(sv));
        if (ctx == NULL)
            return 0;
        if (ctx->thresh.alloc)
            free(ctx->thresh.arr);
        if (ctx->links.alloc)
            free(ctx->links.arr);
        free(ctx);
        return 1;
}

inline
static SV *lcs_new(char *class)
{
        struct CTX *ctx = malloc(sizeof *ctx);

        ctx->thresh.arr = malloc(100 * sizeof *ctx->thresh.arr);
        ctx->thresh.alloc = 100;
        ctx->thresh.max = -1;

        ctx->links.arr = malloc(100 * sizeof *ctx->links.arr);
        ctx->links.alloc = 100;
        ctx->links.max = -1;

        return sv_setref_pv(newSV(0),class,ctx);
}

inline
static int rnlw(struct TA *a, const IV aValue, IV high)
{
/* literal C translation of Algorithm::Diff::_replaceNextLargestWith */
    IV low = 0;
    if (high <= 0)
        high = a->max;
    if (high == -1 || aValue > a->arr[a->max]) {
        *ta_push(a) = aValue;
        return high + 1;
    }
    while (low <= high) {
        IV idx = (low + high) / 2;
        IV found = a->arr[idx];
        if (aValue == found)
            return -1;
        else if (aValue > found)
            low = idx + 1;
        else
            high = idx - 1;
    }
    a->arr[low] = aValue;
    return low;
}


MODULE = Algorithm::LCS  PACKAGE = Algorithm::LCS  PREFIX = lcs_
PROTOTYPES: DISABLED

SV *lcs_new(char *class)

IV lcs_DESTROY(SV *sv) 

void lcs__core_loop(obj, a, a_min, a_max, h)
    SV *obj
    AV *a
    IV a_min
    IV a_max
    HV *h

    PREINIT:
        struct CTX *ctx = (struct CTX *)SvIVX(SvRV(obj));
        IV i, j, max_line, min_line;

    PPCODE:
        min_line = -1;
        max_line = 0;
        ctx->links.max = ctx->thresh.max = -1;

        for (i = a_min; i <= a_max; ++i) {
            SV *line = *av_fetch(a, i, 0);
            STRLEN klen;
            char *key = SvPVbyte(line, klen);
            SV **lines = hv_fetch(h, key, klen, 0);

            if (lines != NULL) {
                register IV k = 0, idx;
                AV *matches = (AV *)SvRV(*lines); /* line_map() value */

                if (min_line == -1)
                    min_line = i;
                max_line = i;

                for (idx = av_len(matches); idx >= 0; --idx) {
                    /* We know (via sub line_map) "matches" holds
                     * valid SvIV's, in increasing order, so we can use
                     * (quicker) SvIVX instead of (safer) SvIV here.
                     */
                    j = SvIVX(*av_fetch(matches, idx, 0));

                    if (k > 0 && ctx->thresh.arr[k] > j && 
                                 ctx->thresh.arr[k-1] < j) {
                        ctx->thresh.arr[k] = j;
                    }
                    else
                        k = rnlw(&ctx->thresh, j, k);

                    if (k >= 0) {
                        struct LK lk = {i, j};
                        if (ctx->links.max < k) {
                            *la_push(&ctx->links) = lk;
                        }
                        else
                            ctx->links.arr[k] = lk;
                    }
                }
            }
        }

        if (min_line >= 0) {
            IV *e, *start, *end;
            ++max_line;
            if (ctx->thresh.alloc <= max_line) {
                    IV *new = malloc(2 * max_line * sizeof *new);
                    free(ctx->thresh.arr);
                    ctx->thresh.alloc = 2 * max_line;
                    ctx->thresh.arr = new;
            }
            start = &ctx->thresh.arr[min_line];
            memset(start, -1, (max_line - min_line) * sizeof *ctx->thresh.arr);
            end = &ctx->thresh.arr[--max_line];
            do {
                struct LK *link = &ctx->links.arr[ctx->thresh.max--];
                ctx->thresh.arr[link->i] = link->j;
            } while (ctx->thresh.max >= 0);

            if (GIMME_V == G_ARRAY) {
                for (e = start; e <= end; ++e) {
                    if (*e >= 0) {
                         AV *arr = newAV();
                         av_push(arr, newSViv(e - ctx->thresh.arr));
                         av_push(arr, newSViv(*e));
                         XPUSHs(sv_2mortal(newRV_noinc((SV *)arr)));
                    }
                }
            }
            else {
                j = 0;
                for (e = start; e <= end; ++e)
                    if (*e >= 0)
                        ++j;
                XSRETURN_IV(j);
            }
        }
        else if (GIMME_V == G_SCALAR)
            XSRETURN_IV(0);
