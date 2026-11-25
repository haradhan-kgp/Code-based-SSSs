/*
 * Reference implementation of the code-based ramp secret sharing schemes
 *   Scheme I   : K_n-based (t,n) scheme from an [m,k] MDS (Reed-Solomon) code
 *   Scheme II  : generator-matrix-based (t,n) scheme from an [n,t] MDS code
 *   Scheme III : perfect-code-based (t+1,2t+1) scheme (binary Hamming / Golay)
 *   Scheme IV  : Tompa-Woll-resistant variant of Scheme I
 *
 * MDS codes are Reed-Solomon codes over GF(P): G[r][e] = (e+1)^r, so any k
 * columns form an invertible Vandermonde matrix as long as m < P.
 * Perfect codes are cyclic codes with generator polynomial g(x); decoding is
 * syndrome (remainder mod g) lookup over all error patterns of weight <= t.
 *
 * Build:  gcc -O2 -Wall -o ramp_sss ramp_sss.c -lm
 * Run:    ./ramp_sss          (correctness tests, incl. tampering experiments)
 *         ./ramp_sss bench    (timing benchmarks)
 *         ./ramp_sss latex    (timing benchmarks as LaTeX table rows)
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef long long ll;
typedef unsigned __int128 vec;
#define P 1000003LL
#define MAXN 128
#define MAXM 1000
#define MAXK 400
#define MAXT 64
#define MAXL 128

/* ---------- helpers ---------- */
static ll mpow(ll b, ll e) {
    ll r = 1; b %= P; if (b < 0) b += P;
    while (e) { if (e & 1) r = r * b % P; b = b * b % P; e >>= 1; }
    return r;
}
static ll minv(ll a) { return mpow(a, P - 2); }
static ll rnd_fe(void) { return (((ll)rand() << 15) ^ rand()) % P; }
static double now_us(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3;
}
/* average microseconds per execution (runs for at least 50 ms) */
#define BENCH(us, ...) do { int _r = 0; double _t0 = now_us(), _t; \
    do { __VA_ARGS__; _r++; _t = now_us() - _t0; } while (_t < 50000.0); \
    (us) = _t / _r; } while (0)

/* Solve A x = b, A is n x n augmented with b in column n. 0 ok, -1 singular. */
static int solve(int n, ll A[][MAXK + 1], ll *x) {
    for (int c = 0; c < n; c++) {
        int piv = -1;
        for (int r = c; r < n; r++) if (A[r][c] % P) { piv = r; break; }
        if (piv < 0) return -1;
        if (piv != c) for (int j = 0; j <= n; j++) { ll t = A[c][j]; A[c][j] = A[piv][j]; A[piv][j] = t; }
        ll iv = minv(A[c][c]);
        for (int j = c; j <= n; j++) A[c][j] = A[c][j] * iv % P;
        for (int r = 0; r < n; r++) if (r != c && A[r][c]) {
            ll f = A[r][c];
            for (int j = c; j <= n; j++) A[r][j] = ((A[r][j] - f * A[c][j]) % P + P) % P;
        }
    }
    for (int i = 0; i < n; i++) x[i] = A[i][n];
    return 0;
}

/* =====================================================================
 * Schemes I and IV  (K_n based)
 * ===================================================================== */
static ll G[MAXK][MAXM];
static ll share[MAXN][MAXN];          /* share[i][j] = coordinate c_{ij} held by P_i */
static ll Asys[MAXK][MAXK + 1];

static int edge_idx(int n, int i, int j) { return i * n - i * (i + 1) / 2 + (j - i - 1); } /* i<j */
static int N_t(int n, int t) { return t * n - t * (t + 1) / 2; }
static int C2(int t) { return t * (t - 1) / 2; }

static void build_G(int k, int m) {
    for (int e = 0; e < m; e++) G[0][e] = 1;
    for (int r = 1; r < k; r++) for (int e = 0; e < m; e++) G[r][e] = G[r - 1][e] * (e + 1) % P;
}
static void encode(int k, int m, const ll *lam, ll *c) {
    for (int e = 0; e < m; e++) { ll s = 0; for (int r = 0; r < k; r++) s = (s + lam[r] * G[r][e]) % P; c[e] = s; }
}
static void fill_shares(int n, const ll *c) {
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) share[i][j] = share[j][i] = c[edge_idx(n, i, j)];
}
static int recover(int k, const int *edges, const ll *vals, ll *lam) {
    for (int q = 0; q < k; q++) { for (int r = 0; r < k; r++) Asys[q][r] = G[r][edges[q]]; Asys[q][k] = vals[q]; }
    return solve(k, Asys, lam);
}
/* Coalition P_0..P_{cnt-1}.  iv=0: Scheme I (each member submits its whole share);
 * iv=1: Scheme IV (members submit only edges whose other endpoint is also in the coalition).
 * Counts pairwise mismatches on edges seen twice.  Returns 0 ok, -1 too few coordinates. */
static int coalition_recover(int n, int cnt, int k, int iv, int *mismatch, ll *lam) {
    static int edges[MAXM]; static ll vals[MAXM], vbe[MAXM]; static char seen[MAXM];
    int m = n * (n - 1) / 2, c = 0; memset(seen, 0, m); *mismatch = 0;
    for (int i = 0; i < cnt; i++) for (int j = 0; j < n; j++) {
        if (j == i || (iv && j >= cnt)) continue;
        int e = edge_idx(n, i < j ? i : j, i < j ? j : i);
        if (seen[e]) { if (vbe[e] != share[i][j]) (*mismatch)++; continue; }
        seen[e] = 1; vbe[e] = share[i][j]; edges[c] = e; vals[c] = share[i][j]; c++;
    }
    if (c < k) return -1;
    return recover(k, edges, vals, lam) ? -2 : 0;
}

static int test_scheme1(int n, int t) {
    int m = n * (n - 1) / 2, k = N_t(n, t - 1) + 1;
    printf("[Scheme I]   n=%d t=%d  [m=%d,k=%d] MDS, N_{t-1}=%d N_t=%d, rho=%.3f\n",
           n, t, m, k, N_t(n, t - 1), N_t(n, t), (double)k / (n - 1));
    build_G(k, m);
    ll lam[MAXK], c[MAXM], rec[MAXK]; int mm;
    for (int r = 0; r < k; r++) lam[r] = rnd_fe();
    encode(k, m, lam, c); fill_shares(n, c);
    int rc = coalition_recover(n, t, k, 0, &mm, rec), ok = (rc == 0);
    for (int r = 0; ok && r < k; r++) if (rec[r] != lam[r]) ok = 0;
    printf("    %d participants (%d coords)   -> recovery %s\n", t, N_t(n, t), ok ? "OK" : "FAILED");
    int rc2 = coalition_recover(n, t - 1, k, 0, &mm, rec);
    printf("    %d participants (%d coords<k) -> %s\n", t - 1, N_t(n, t - 1), rc2 == -1 ? "cannot recover (expected)" : "UNEXPECTED");
    return ok && rc2 == -1;
}

/* Tompa-Woll style tampering experiment, Scheme I (iv=0) vs Scheme IV (iv=1) */
static int test_tamper(int n, int t, int iv) {
    int m = n * (n - 1) / 2, k = iv ? C2(t - 1) + 1 : N_t(n, t - 1) + 1;
    printf("[Scheme %s]  n=%d t=%d  [m=%d,k=%d], rho=%.3f\n", iv ? "IV" : "I ", n, t, m, k, (double)k / (n - 1));
    build_G(k, m);
    ll lam[MAXK], c[MAXM], rec[MAXK]; int mm, ok = 1;
    for (int r = 0; r < k; r++) lam[r] = rnd_fe();
    encode(k, m, lam, c);
    int rc2; fill_shares(n, c);
    rc2 = coalition_recover(n, t - 1, k, iv, &mm, rec);
    printf("    %d participants -> %s\n", t - 1, rc2 == -1 ? "cannot recover (expected)" : "UNEXPECTED");
    ok &= (rc2 == -1);
    const char *nm[3] = {"honest coalition", "P_0 tampers edge to OUTSIDER P_t", "P_0 tampers edge to INSIDER P_1"};
    int want[2][3] = {{1, 2, 0}, {1, 1, 0}};   /* 0 detected, 1 correct, 2 wrong secret accepted */
    for (int sc = 0; sc < 3; sc++) {
        fill_shares(n, c);
        if (sc == 1) share[0][t] = (share[0][t] + 1) % P;
        if (sc == 2) share[0][1] = (share[0][1] + 1) % P;
        int rc = coalition_recover(n, t, k, iv, &mm, rec), good = (rc == 0);
        for (int r = 0; good && r < k; r++) if (rec[r] != lam[r]) good = 0;
        int res = mm > 0 ? 0 : (good ? 1 : 2);
        printf("    %-34s -> %s\n", nm[sc], res == 0 ? "tampering DETECTED" : res == 1 ? "secret recovered correctly" : "WRONG SECRET ACCEPTED (undetected)");
        ok &= (res == want[iv][sc]);
    }
    return ok;
}

/* =====================================================================
 * Scheme II  (generator-matrix based)
 * ===================================================================== */
static ll A2[MAXN][MAXT], M2[MAXT][MAXL], Q2[MAXN][MAXL], W2[MAXT][2 * MAXT], R2[MAXT][MAXL];
static void s2_share(int n, int t, int l) {
    for (int i = 0; i < n; i++) { A2[i][0] = 1; for (int j = 1; j < t; j++) A2[i][j] = A2[i][j - 1] * (i + 1) % P; }
    for (int i = 0; i < t; i++) for (int j = 0; j < l; j++) M2[i][j] = rnd_fe();
    for (int i = 0; i < n; i++) for (int j = 0; j < l; j++) {
        ll s = 0; for (int q = 0; q < t; q++) s = (s + A2[i][q] * M2[q][j]) % P; Q2[i][j] = s;
    }
}
static int s2_recon(int n, int t, int l, const int *rows) {      /* M = (A_bar)^{-1} Q_bar */
    for (int r = 0; r < t; r++) for (int c = 0; c < 2 * t; c++) W2[r][c] = c < t ? A2[rows[r]][c] : (c - t == r);
    for (int c = 0; c < t; c++) {
        int piv = -1; for (int r = c; r < t; r++) if (W2[r][c]) { piv = r; break; }
        if (piv < 0) return 0;
        if (piv != c) for (int j = 0; j < 2 * t; j++) { ll x = W2[c][j]; W2[c][j] = W2[piv][j]; W2[piv][j] = x; }
        ll iv = minv(W2[c][c]); for (int j = 0; j < 2 * t; j++) W2[c][j] = W2[c][j] * iv % P;
        for (int r = 0; r < t; r++) if (r != c && W2[r][c]) {
            ll f = W2[r][c]; for (int j = 0; j < 2 * t; j++) W2[r][j] = ((W2[r][j] - f * W2[c][j]) % P + P) % P;
        }
    }
    int ok = 1;
    for (int i = 0; i < t; i++) for (int j = 0; j < l; j++) {
        ll s = 0; for (int q = 0; q < t; q++) s = (s + W2[i][t + q] * Q2[rows[q]][j]) % P;
        R2[i][j] = s; if (s != M2[i][j]) ok = 0;
    }
    return ok;
}
static int test_scheme2(int n, int t, int l) {
    printf("[Scheme II]  n=%d t=%d l=%d  secret = %dx%d matrix, rho=t=%d\n", n, t, l, t, l, t);
    s2_share(n, t, l);
    int rows[MAXT]; for (int r = 0; r < t; r++) rows[r] = n - t + r;
    int ok = s2_recon(n, t, l, rows);
    printf("    %d participants -> recovery %s\n", t, ok ? "OK" : "FAILED");
    return ok;
}

/* =====================================================================
 * Scheme III  (perfect cyclic code: binary Hamming or Golay)
 * ===================================================================== */
typedef struct { const char *name; int M, r, t; vec g; vec *tab; } Code;
static int popc(vec v) { return __builtin_popcountll((unsigned long long)v) + __builtin_popcountll((unsigned long long)(v >> 64)); }
static int getb(vec v, int i) { return (int)((v >> i) & 1); }
static vec rem_g(const Code *C, vec v) {
    for (int i = C->M - 1; i >= C->r; i--) if ((v >> i) & 1) v ^= C->g << (i - C->r);
    return v;
}
static int fill_rec(Code *C, char *used, int start, int left, vec e) {
    vec s = rem_g(C, e);
    if (used[s]) return -1;                         /* collision => code is not perfect */
    used[s] = 1; C->tab[s] = e;
    if (!left) return 0;
    for (int i = start; i < C->M; i++) if (fill_rec(C, used, i + 1, left - 1, e | ((vec)1 << i)) < 0) return -1;
    return 0;
}
static int code_init(Code *C, const char *name, int M, int r, int t, vec g) {
    C->name = name; C->M = M; C->r = r; C->t = t; C->g = g;
    C->tab = calloc((size_t)1 << r, sizeof(vec));
    char *used = calloc((size_t)1 << r, 1);
    int rc = fill_rec(C, used, 0, t, 0), full = 1;
    for (size_t s = 0; s < ((size_t)1 << r); s++) if (!used[s]) full = 0;
    free(used);
    return rc == 0 && full;                         /* perfect: every syndrome has a unique coset leader of weight <= t */
}
static vec decode(const Code *C, vec v) { return v ^ C->tab[rem_g(C, v)]; }   /* unique bounded-distance decoding */
static vec rnd_bits(int nb) { vec v = 0; for (int i = 0; i < nb; i += 15) v = (v << 15) | (rand() & 0x7fff); return nb < 128 ? v & (((vec)1 << nb) - 1) : v; }
static vec cl_mul(const Code *C, vec msg) { vec c = 0; for (int i = 0; i < C->M - C->r; i++) if ((msg >> i) & 1) c ^= C->g << i; return c; }
static vec gen_secret(const Code *C) {                  /* nonzero codeword with wt <= M-2t-1 */
    for (;;) { vec c = cl_mul(C, rnd_bits(C->M - C->r)); if (c && popc(c) <= C->M - 2 * C->t - 1) return c; }
}
static vec make_helper(const Code *C, vec S, int *Zpos) {
    int t = C->t, M = C->M;
    for (;;) {
        int a = rand() % (t + 1), c = 0; vec Z = 0;
        while (c < a) { int i = rand() % M; if (getb(S, i) && !getb(Z, i)) { Z |= (vec)1 << i; c++; } }
        c = 0; while (c < 2 * t + 1 - a) { int i = rand() % M; if (!getb(S, i) && !getb(Z, i)) { Z |= (vec)1 << i; c++; } }
        vec h = S ^ Z;
        if (popc(S ^ h) == 2 * t + 1 && popc((S ^ h) & S) <= t) {
            int nz = 0; for (int i = 0; i < M; i++) if (getb(Z, i)) Zpos[nz++] = i;
            for (int i = nz - 1; i > 0; i--) { int j = rand() % (i + 1), x = Zpos[i]; Zpos[i] = Zpos[j]; Zpos[j] = x; } /* random bijection */
            return h;
        }
    }
}
static int test_scheme3(Code *C, vec g, const char *name, int M, int r, int t) {
    int perfect = code_init(C, name, M, r, t, g), k = M - r, np = 2 * t + 1, ok = perfect;
    printf("[Scheme III] %s [%d,%d,%d] t=%d -> (%d,%d)-threshold, perfect=%s, rho=k/log2(m)=%.2f\n",
           name, M, k, 2 * t + 1, t, t + 1, np, perfect ? "yes" : "NO", k / (__builtin_log2((double)M)));
    if (!perfect) return 0;
    if (k <= 20) {
        long cnt = 0; for (long msg = 1; msg < (1L << k); msg++) if (popc(cl_mul(C, (vec)msg)) <= M - 2 * t - 1) cnt++;
        printf("    |secret space| = %ld of %ld codewords (eta = %.4f)\n", cnt, 1L << k, (double)cnt / (double)(1L << k));
    }
    vec S = gen_secret(C); int Z[8]; vec h = make_helper(C, S, Z);
    for (int mask = 0; mask < (1 << np); mask++) {
        vec zt = 0; int sz = __builtin_popcount(mask);
        for (int p = 0; p < np; p++) if (mask >> p & 1) zt |= (vec)1 << Z[p];
        int right = (decode(C, h ^ zt) == S);
        if (sz >= t + 1 && !right) ok = 0;
        if (sz <= t && right) ok = 0;
    }
    printf("    all %d participant subsets behave as (%d,%d)-threshold: %s\n", 1 << np, t + 1, np, ok ? "OK" : "FAILED");
    return ok;
}

/* =====================================================================
 * Benchmarks
 * ===================================================================== */
static void row(int latex, const char *sch, const char *par, double g, double r, const char *sh) {
    if (latex) printf("%s & %s & %.1f & %.1f & %s \\\\\n", sch, par, g, r, sh);
    else printf("%-11s %-22s gen %11.1f us   recon %11.1f us   share %s\n", sch, par, g, r, sh);
}
static void bench_s1(int latex, int n, int t) {
    int m = n * (n - 1) / 2, k = N_t(n, t - 1) + 1, mm; static ll lam[MAXK], c[MAXM], c2[MAXM], rec[MAXK];
    char par[64], sh[32]; double g, r;
    build_G(k, m); for (int i = 0; i < k; i++) lam[i] = rnd_fe();
    BENCH(g, encode(k, m, lam, c)); fill_shares(n, c);
    BENCH(r, coalition_recover(n, t, k, 0, &mm, rec); encode(k, m, rec, c2));
    snprintf(par, 64, "n=%d,t=%d,k=%d", n, t, k); snprintf(sh, 32, "%d sym", n - 1);
    row(latex, "I / IV", par, g, r, sh);
}
static void bench_s2(int latex, int n, int t, int l) {
    int rows[MAXT]; char par[64], sh[32]; double g, r;
    BENCH(g, s2_share(n, t, l));
    for (int i = 0; i < t; i++) rows[i] = n - t + i;
    BENCH(r, s2_recon(n, t, l, rows));
    snprintf(par, 64, "n=%d,t=%d,l=%d", n, t, l); snprintf(sh, 32, "%d sym", l);
    row(latex, "II", par, g, r, sh);
}
static volatile unsigned long long sink;
static void bench_s3(int latex, const char *name, vec g, int M, int r, int t) {
    Code C; char par[64], sh[32]; double gt, rt; int Z[8]; vec S = 0, h = 0, zt = 0;
    if (!code_init(&C, name, M, r, t, g)) { printf("code %s not perfect\n", name); return; }
    BENCH(gt, S = gen_secret(&C); h = make_helper(&C, S, Z));
    for (int i = 0; i <= t; i++) zt |= (vec)1 << Z[i];
    BENCH(rt, sink ^= (unsigned long long)decode(&C, h ^ zt));
    snprintf(par, 64, "%s,t=%d", name, t); snprintf(sh, 32, "%d bits", (int)__builtin_ceil(__builtin_log2((double)M)));
    row(latex, "III", par, gt, rt, sh);
}
static void bench_all(int latex) {
    if (!latex) printf("Timing benchmarks (average per operation)\n");
    int s1[4][2] = {{10, 3}, {20, 5}, {30, 8}, {40, 10}}; for (int i = 0; i < 4; i++) bench_s1(latex, s1[i][0], s1[i][1]);
    int s2[4][3] = {{10, 4, 16}, {30, 10, 64}, {60, 20, 64}, {120, 40, 128}}; for (int i = 0; i < 4; i++) bench_s2(latex, s2[i][0], s2[i][1], s2[i][2]);
    bench_s3(latex, "Hamming[7,4]", 0xB, 7, 3, 1);
    bench_s3(latex, "Hamming[31,26]", 0x25, 31, 5, 1);
    bench_s3(latex, "Hamming[127,120]", 0x89, 127, 7, 1);
    bench_s3(latex, "Golay[23,12]", 0xC75, 23, 11, 3);
}

int main(int argc, char **argv) {
    srand((unsigned)time(NULL) ^ (unsigned)clock());
    if (argc > 1) { bench_all(strcmp(argv[1], "latex") == 0); return 0; }
    int ok = 1; Code C;
    ok &= test_scheme1(8, 2);
    ok &= test_scheme1(10, 3);
    ok &= test_scheme2(10, 4, 5);
    ok &= test_scheme3(&C, 0xB, "Hamming", 7, 3, 1);
    ok &= test_scheme3(&C, 0x25, "Hamming", 31, 5, 1);
    ok &= test_scheme3(&C, 0x89, "Hamming", 127, 7, 1);
    ok &= test_scheme3(&C, 0xC75, "Golay", 23, 11, 3);
    printf("\n--- Tompa-Woll tampering experiment (coalition of t participants) ---\n");
    ok &= test_tamper(8, 4, 0);
    ok &= test_tamper(8, 4, 1);
    printf("\n%s\n", ok ? "ALL TESTS PASSED" : "SOME TESTS FAILED");
    return !ok;
}
