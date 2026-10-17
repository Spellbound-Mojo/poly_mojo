/* Benchmark driver: FLINT truncated series, multipoint evaluation,
   interpolation, and evaluation at a rational.

   Arguments: input, answer, result, min_seconds, min_reps. The input format is
   described in harness/series.py. Operands are converted to FLINT types before
   the timer starts. The answer lists one value per line: a hexadecimal
   integer, or `numerator/denominator` in hexadecimal.

   series over QQ     fmpq_poly_{mullow, inv_series, sqrt_series, log_series,
                      exp_series, pow_trunc, compose_series, revert_series}
   series over GF(p)  the nmod_poly functions of the same names
   multipoint         fmpz_poly_evaluate_fmpz_vec, nmod_poly_evaluate_nmod_vec
   interp             fmpq_poly_interpolate_fmpz_vec, nmod_poly_interpolate_nmod_vec
   evalq              fmpz_poly_evaluate_fmpq */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpq.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpq_poly.h>
#include <flint/nmod_poly.h>

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

/* ------------------------------------------------------------------ input */

static char kind[32], op[32];
static ulong modulus;
static slong n, exponent;
static int operand_count;
static slong lengths[4];
static fmpz * operands[4];

static void read_input(const char * path)
{
    FILE * f = fopen(path, "r");
    if (!f) { fprintf(stderr, "cannot open input\n"); exit(2); }
    int c;
    while ((c = fgetc(f)) != '\n' && c != EOF)
        ;  /* the JSON header */
    if (fscanf(f, "%31s %31s %lu %ld %ld", kind, op, &modulus, &n, &exponent) != 5) { fprintf(stderr, "bad header\n"); exit(2); }
    char * buf = malloc(1 << 16);
    slong count;
    while (operand_count < 4 && fscanf(f, "%ld", &count) == 1)
    {
        lengths[operand_count] = count;
        operands[operand_count] = _fmpz_vec_init(count);
        for (slong i = 0; i < count; i++)
        {
            if (fscanf(f, "%65535s", buf) != 1) { fprintf(stderr, "bad value\n"); exit(2); }
            fmpz_set_str(operands[operand_count] + i, buf, 16);
        }
        operand_count++;
    }
    free(buf);
    fclose(f);
}

/* ----------------------------------------------------------------- output */

static FILE * answer;

static void put_fmpz(const fmpz_t x)
{
    char * s = fmpz_get_str(NULL, 16, x);
    fputs(s, answer);
    flint_free(s);
}

static void put_fmpq(const fmpq_t x)
{
    put_fmpz(fmpq_numref(x));
    if (!fmpz_is_one(fmpq_denref(x)))
    {
        fputc('/', answer);
        put_fmpz(fmpq_denref(x));
    }
    fputc('\n', answer);
}

static void put_fmpq_poly(const fmpq_poly_t p, slong len)
{
    fmpq_t c;
    fmpq_init(c);
    fprintf(answer, "%ld\n", len);
    for (slong i = 0; i < len; i++)
    {
        fmpq_poly_get_coeff_fmpq(c, p, i);
        put_fmpq(c);
    }
    fmpq_clear(c);
}

static void put_nmod_poly(const nmod_poly_t p, slong len)
{
    fprintf(answer, "%ld\n", len);
    for (slong i = 0; i < len; i++)
        fprintf(answer, "%lx\n", nmod_poly_get_coeff_ui(p, i));
}

/* ------------------------------------------------------------------ timing */

static long times[1 << 20];
static int reps;
static long total, rss_before, peak;

/* Run `body` once, then repeat while the first run was under min_seconds and
   either fewer than min_reps runs or less than min_seconds have elapsed. */
#define TIMED(body) do { \
        rss_before = status_kb("VmRSS"); reset_peak(); \
        for (;;) { \
            long start = now_ns(); \
            body; \
            long elapsed = now_ns() - start; \
            if (!reps) peak = status_kb("VmHWM"); \
            times[reps++] = elapsed; total += elapsed; \
            if (times[0] >= limit || (reps >= min_reps && total >= limit) || reps == (1 << 20)) break; \
        } \
    } while (0)

static void write_result(const char * path)
{
    FILE * f = fopen(path, "w");
    fputs("{\"times_ns\": [", f);
    for (int i = 0; i < reps; i++)
        fprintf(f, "%s%ld", i ? ", " : "", times[i]);
    fprintf(f, "], \"rss_before_kb\": %ld, \"peak_kb\": %ld}\n", rss_before, peak);
    fclose(f);
}

/* ------------------------------------------------------------------ cases */

static void set_fmpq_poly(fmpq_poly_t p, const fmpz * v, slong len)
{
    fmpq_poly_fit_length(p, len);
    _fmpz_vec_set(p->coeffs, v, len);
    fmpz_one(p->den);
    _fmpq_poly_set_length(p, len);
    fmpq_poly_canonicalise(p);
}

static void set_nmod_poly(nmod_poly_t p, const fmpz * v, slong len)
{
    for (slong i = len - 1; i >= 0; i--)
        nmod_poly_set_coeff_ui(p, i, fmpz_fdiv_ui(v + i, modulus));
}

static void series_qq(double limit, int min_reps)
{
    fmpq_poly_t a, b, r;
    fmpq_poly_init(a); fmpq_poly_init(b); fmpq_poly_init(r);
    set_fmpq_poly(a, operands[0], lengths[0]);
    if (operand_count > 1)
        set_fmpq_poly(b, operands[1], lengths[1]);
    if (!strcmp(op, "mul")) TIMED(fmpq_poly_mullow(r, a, b, n));
    else if (!strcmp(op, "inv")) TIMED(fmpq_poly_inv_series(r, a, n));
    else if (!strcmp(op, "sqrt")) TIMED(fmpq_poly_sqrt_series(r, a, n));
    else if (!strcmp(op, "log")) TIMED(fmpq_poly_log_series(r, a, n));
    else if (!strcmp(op, "exp")) TIMED(fmpq_poly_exp_series(r, a, n));
    else if (!strcmp(op, "pow")) TIMED(fmpq_poly_pow_trunc(r, a, exponent, n));
    else if (!strcmp(op, "compose")) TIMED(fmpq_poly_compose_series(r, a, b, n));
    else if (!strcmp(op, "revert")) TIMED(fmpq_poly_revert_series(r, a, n));
    else { fprintf(stderr, "unknown op %s\n", op); exit(2); }
    put_fmpq_poly(r, n);
    fmpq_poly_clear(a); fmpq_poly_clear(b); fmpq_poly_clear(r);
}

static void series_gf(double limit, int min_reps)
{
    nmod_poly_t a, b, r;
    nmod_poly_init(a, modulus); nmod_poly_init(b, modulus); nmod_poly_init(r, modulus);
    set_nmod_poly(a, operands[0], lengths[0]);
    if (operand_count > 1)
        set_nmod_poly(b, operands[1], lengths[1]);
    if (!strcmp(op, "mul")) TIMED(nmod_poly_mullow(r, a, b, n));
    else if (!strcmp(op, "inv")) TIMED(nmod_poly_inv_series(r, a, n));
    else if (!strcmp(op, "sqrt")) TIMED(nmod_poly_sqrt_series(r, a, n));
    else if (!strcmp(op, "log")) TIMED(nmod_poly_log_series(r, a, n));
    else if (!strcmp(op, "exp")) TIMED(nmod_poly_exp_series(r, a, n));
    else if (!strcmp(op, "pow")) TIMED(nmod_poly_pow_trunc(r, a, exponent, n));
    else if (!strcmp(op, "compose")) TIMED(nmod_poly_compose_series(r, a, b, n));
    else if (!strcmp(op, "revert")) TIMED(nmod_poly_revert_series(r, a, n));
    else { fprintf(stderr, "unknown op %s\n", op); exit(2); }
    put_nmod_poly(r, n);
    nmod_poly_clear(a); nmod_poly_clear(b); nmod_poly_clear(r);
}

static void multipoint(double limit, int min_reps)
{
    slong count = lengths[1];
    if (modulus)
    {
        nmod_poly_t f;
        nmod_poly_init(f, modulus);
        set_nmod_poly(f, operands[0], lengths[0]);
        ulong * xs = flint_malloc(count * sizeof(ulong));
        ulong * ys = flint_malloc(count * sizeof(ulong));
        for (slong i = 0; i < count; i++)
            xs[i] = fmpz_fdiv_ui(operands[1] + i, modulus);
        TIMED(nmod_poly_evaluate_nmod_vec(ys, f, xs, count));
        fprintf(answer, "%ld\n", count);
        for (slong i = 0; i < count; i++)
            fprintf(answer, "%lx\n", ys[i]);
        flint_free(xs); flint_free(ys);
        nmod_poly_clear(f);
    }
    else
    {
        fmpz_poly_t f;
        fmpz_poly_init(f);
        for (slong i = lengths[0] - 1; i >= 0; i--)
            fmpz_poly_set_coeff_fmpz(f, i, operands[0] + i);
        fmpz * ys = _fmpz_vec_init(count);
        TIMED(fmpz_poly_evaluate_fmpz_vec(ys, f, operands[1], count));
        fprintf(answer, "%ld\n", count);
        for (slong i = 0; i < count; i++)
        {
            put_fmpz(ys + i);
            fputc('\n', answer);
        }
        _fmpz_vec_clear(ys, count);
        fmpz_poly_clear(f);
    }
}

static void interp(double limit, int min_reps)
{
    slong count = lengths[0];
    if (modulus)
    {
        nmod_poly_t f;
        nmod_poly_init(f, modulus);
        ulong * xs = flint_malloc(count * sizeof(ulong));
        ulong * ys = flint_malloc(count * sizeof(ulong));
        for (slong i = 0; i < count; i++)
        {
            xs[i] = fmpz_fdiv_ui(operands[0] + i, modulus);
            ys[i] = fmpz_fdiv_ui(operands[1] + i, modulus);
        }
        TIMED(nmod_poly_interpolate_nmod_vec(f, xs, ys, count));
        put_nmod_poly(f, count);
        flint_free(xs); flint_free(ys);
        nmod_poly_clear(f);
    }
    else
    {
        fmpq_poly_t f;
        fmpq_poly_init(f);
        TIMED(fmpq_poly_interpolate_fmpz_vec(f, operands[0], operands[1], count));
        put_fmpq_poly(f, count);
        fmpq_poly_clear(f);
    }
}

static void evalq(double limit, int min_reps)
{
    fmpz_poly_t f;
    fmpq_t x, r;
    fmpz_poly_init(f); fmpq_init(x); fmpq_init(r);
    for (slong i = lengths[0] - 1; i >= 0; i--)
        fmpz_poly_set_coeff_fmpz(f, i, operands[0] + i);
    fmpq_set_fmpz_frac(x, operands[1], operands[1] + 1);
    TIMED(fmpz_poly_evaluate_fmpq(r, f, x));
    fputs("1\n", answer);
    put_fmpq(r);
    fmpz_poly_clear(f); fmpq_clear(x); fmpq_clear(r);
}

int main(int argc, char ** argv)
{
    if (argc != 6) { fprintf(stderr, "usage: series INPUT ANSWER RESULT MIN_SECONDS MIN_REPS\n"); return 2; }
    read_input(argv[1]);
    double limit = atof(argv[4]) * 1e9;
    int min_reps = atoi(argv[5]);
    answer = fopen(argv[2], "w");
    if (!strcmp(kind, "series")) { if (modulus) series_gf(limit, min_reps); else series_qq(limit, min_reps); }
    else if (!strcmp(kind, "multipoint")) multipoint(limit, min_reps);
    else if (!strcmp(kind, "interp")) interp(limit, min_reps);
    else if (!strcmp(kind, "evalq")) evalq(limit, min_reps);
    else { fprintf(stderr, "unknown kind %s\n", kind); return 2; }
    fclose(answer);
    write_result(argv[3]);
    return 0;
}
