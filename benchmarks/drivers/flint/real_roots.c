/* Benchmark driver: FLINT real root isolation, refinement, and counting.

   Arguments: input, answer, result, mode, min_seconds, min_reps.
   The input holds a coefficient count and then one ascending integer
   coefficient per line. Modes:

     isolate      squarefree part, then arb_fmpz_poly_complex_roots at a low
                  target; real roots come first and are certified real
     refine53     the same with every root enclosed to width 2^-53
     refine1000   the same with width 2^-1000
     count        fmpz_poly_num_real_roots (distinct real roots)
     sturm        fmpz_poly_num_real_roots_sturm
     bitsN        refinement to width 2^-N (the harness reference)

   FLINT has no fmpz_poly_isolate_real_roots, arb_fmpz_poly_real_roots,
   or arb_fmpz_poly_refine_root_arb; complex_roots is its certified real
   root solver (it finds every complex root, so the time covers them all).
   The answer lists the count and then, per real root, `m e m e` for the
   lower and upper endpoints m * 2^e. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <flint/fmpz_poly.h>
#include <flint/arb_fmpz_poly.h>
#include <flint/acb.h>

static long now_ns(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1000000000L + t.tv_nsec;
}

static long status_kb(const char * field)
{
    FILE * f = fopen("/proc/self/status", "r");
    char line[256];
    long value = 0;
    size_t n = strlen(field);
    while (fgets(line, sizeof line, f))
        if (!strncmp(line, field, n) && line[n] == ':')
            value = atol(line + n + 1);
    fclose(f);
    return value;
}

static void reset_peak(void)
{
    FILE * f = fopen("/proc/self/clear_refs", "w");
    if (f) { fputs("5", f); fclose(f); }
}

static void read_poly(fmpz_poly_t p, const char * path)
{
    FILE * f = fopen(path, "r");
    long count;
    if (!f || fscanf(f, "%ld", &count) != 1) { fprintf(stderr, "bad input\n"); exit(2); }
    char * buf = malloc(1 << 20);
    fmpz_t c;
    fmpz_init(c);
    for (long i = 0; i < count; i++)
    {
        if (fscanf(f, "%1048575s", buf) != 1) { fprintf(stderr, "bad coefficient\n"); exit(2); }
        fmpz_set_str(c, buf, 10);
        fmpz_poly_set_coeff_fmpz(p, i, c);
    }
    fmpz_clear(c);
    free(buf);
    fclose(f);
}

/* Real roots of the squarefree part, each enclosed to width below 2^-bits
   (bits <= 0: the solver's first certified isolation). Returns the count. */
static slong solve(acb_ptr * out, const fmpz_poly_t p, slong bits)
{
    fmpz_poly_t g, d, q;
    fmpz_poly_init(g); fmpz_poly_init(d); fmpz_poly_init(q);
    fmpz_poly_derivative(d, p);
    fmpz_poly_gcd(g, p, d);
    fmpz_poly_div(q, p, g);
    slong deg = fmpz_poly_degree(q);
    acb_ptr roots = _acb_vec_init(deg > 0 ? deg : 1);
    slong nreal = 0;
    if (deg > 0)
    {
        slong target = bits > 0 ? bits + 16 : 2;
        for (;;)
        {
            arb_fmpz_poly_complex_roots(roots, q, 0, target);
            int ok = 1;
            nreal = 0;
            for (slong i = 0; i < deg; i++)
            {
                if (!arb_is_zero(acb_imagref(roots + i)))
                    break;
                nreal++;
                if (bits > 0)
                {
                    arf_t w;
                    arf_init(w);
                    arf_set_mag(w, arb_radref(acb_realref(roots + i)));
                    if (arf_cmp_2exp_si(w, -bits - 1) >= 0)
                        ok = 0;
                    arf_clear(w);
                }
            }
            if (ok)
                break;
            target += target / 2 + 32;
        }
    }
    *out = roots;
    fmpz_poly_clear(g); fmpz_poly_clear(d); fmpz_poly_clear(q);
    return nreal;
}

int main(int argc, char ** argv)
{
    if (argc == 2 && strcmp(argv[1], "--version") == 0) { puts(flint_version); return 0; }
    if (argc != 7) { fprintf(stderr, "usage: real_roots INPUT ANSWER RESULT MODE MIN_SECONDS MIN_REPS\n"); return 2; }
    const char * mode = argv[4];
    double limit = atof(argv[5]) * 1e9;
    long min_reps = atol(argv[6]);
    fmpz_poly_t p;
    fmpz_poly_init(p);
    read_poly(p, argv[1]);
    slong bits = !strcmp(mode, "isolate") ? 0 : !strcmp(mode, "refine53") ? 53 : !strcmp(mode, "refine1000") ? 1000
               : !strncmp(mode, "bits", 4) ? atol(mode + 4) : -1;
    int counting = !strcmp(mode, "count") || !strcmp(mode, "sturm");
    if (bits < 0 && !counting) { fprintf(stderr, "unknown mode %s\n", mode); return 2; }

    long times[100000];
    long reps = 0, total = 0, peak = 0;
    long rss_before = status_kb("VmRSS");
    acb_ptr roots = NULL;
    slong nreal = 0;
    reset_peak();
    while (reps == 0 || reps < min_reps || total < limit)
    {
        long start = now_ns();
        acb_ptr r = NULL;
        slong n;
        if (counting)
            n = !strcmp(mode, "count") ? fmpz_poly_num_real_roots(p) : fmpz_poly_num_real_roots_sturm(p);
        else
            n = solve(&r, p, bits);
        long lap = now_ns() - start;
        if (reps == 0)
        {
            peak = status_kb("VmHWM");
            roots = r;
            nreal = n;
        }
        else if (r)
            _acb_vec_clear(r, fmpz_poly_degree(p) > 0 ? fmpz_poly_degree(p) : 1);
        times[reps++] = lap;
        total += lap;
        if (lap >= limit || reps >= 100000)
            break;
    }

    FILE * f = fopen(argv[2], "w");
    fprintf(f, "%ld\n", (long) nreal);
    if (roots)
    {
        arf_t lo, hi;
        fmpz_t m, e;
        arf_init(lo); arf_init(hi); fmpz_init(m); fmpz_init(e);
        for (slong i = 0; i < nreal; i++)
        {
            arb_get_lbound_arf(lo, acb_realref(roots + i), ARF_PREC_EXACT);
            arb_get_ubound_arf(hi, acb_realref(roots + i), ARF_PREC_EXACT);
            arf_get_fmpz_2exp(m, e, lo);
            fmpz_fprint(f, m); fputc(' ', f); fmpz_fprint(f, e); fputc(' ', f);
            arf_get_fmpz_2exp(m, e, hi);
            fmpz_fprint(f, m); fputc(' ', f); fmpz_fprint(f, e); fputc('\n', f);
        }
    }
    fclose(f);
    f = fopen(argv[3], "w");
    fprintf(f, "{\"times_ns\": [");
    for (long i = 0; i < reps; i++)
        fprintf(f, "%s%ld", i ? ", " : "", times[i]);
    fprintf(f, "], \"rss_before_kb\": %ld, \"peak_kb\": %ld}\n", rss_before, peak);
    fclose(f);
    return 0;
}
