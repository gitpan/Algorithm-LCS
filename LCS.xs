#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

#include "ppport.h"

struct LK {
 struct LK *link;
        IV i;
        IV j;
 struct LK *next;
};
struct LA {
    struct LK **arr;
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
    struct LA avail;
    struct LK *current;
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
static struct LK **la_push(struct LA *a)
{
    a->max++;
    if (a->max == a->alloc) {
        struct LK **new = malloc(2 * a->alloc * sizeof *new);
        memcpy(new, a->arr, a->max * sizeof *new);
        free(a->arr);
        a->arr = new;
        a->alloc *= 2;
    }
    return &a->arr[a->max];
}


#define PREP_LINKS(cur,N) do {                          \
    struct LK *e = (cur), *end = (cur) + ((N)-1);       \
    while (e < end) {                                   \
        e->next = e + 1;                                \
        ++e;                                            \
   }                                                    \
   end->next = NULL;                                    \
} while(0)


inline
static struct LK *make_link(struct CTX *ctx, struct LK *lk, IV i, IV j)
{
    struct LK *new = ctx->current;
    new->link = lk;
    new->i = i;
    new->j = j;
    if (new->next) {
        ctx->current = new->next;
        return new;
    }
    ctx->current = malloc(100 * sizeof *ctx->current);
    PREP_LINKS(ctx->current, 100);
    *la_push(&ctx->avail) = ctx->current;
    new->next = ctx->current;
    return new;
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
        if (ctx->avail.alloc) {
            while (ctx->avail.max >= 0)
                free(ctx->avail.arr[ctx->avail.max--]);
            free(ctx->avail.arr);
        }

        free(ctx);
        return 1;
}

inline
static SV *lcs_new(char *class)
{
        struct CTX *ctx = malloc(sizeof *ctx);
        struct LK *end;

        ctx->thresh.arr = malloc(100 * sizeof *ctx->thresh.arr);
        ctx->thresh.alloc = 100;
        ctx->thresh.max = -1;

        ctx->links.arr = malloc(100 * sizeof *ctx->links.arr);
        ctx->links.alloc = 100;
        ctx->links.max = -1;

        ctx->avail.arr = malloc(100 * sizeof *ctx->links.arr);
        ctx->avail.alloc = 100;
        ctx->avail.max = -1;

        ctx->current = malloc(100 * sizeof *ctx->current);
        PREP_LINKS(ctx->current, 100);
        *la_push(&ctx->avail) = ctx->current;

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
        ctx->current = *ctx->avail.arr;

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
                        struct LK *lk = make_link(ctx, (k>0) ? 
                                                  ctx->links.arr[k-1] :
                                                  NULL, i, j);
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
            struct LK *lk;
            if (ctx->thresh.alloc <= max_line) {
                    IV *new = malloc(2 * max_line * sizeof *new);
                    free(ctx->thresh.arr);
                    ctx->thresh.alloc = 2 * max_line;
                    ctx->thresh.arr = new;
            }
            start = &ctx->thresh.arr[min_line];
            memset(start, -1, (max_line - min_line) * sizeof *ctx->thresh.arr);
            end = &ctx->thresh.arr[--max_line];

            for (lk = ctx->links.arr[ctx->thresh.max]; lk; lk = lk->link)
                ctx->thresh.arr[lk->i] = lk->j;

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
