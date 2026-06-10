/* test_runner.c — lightweight unit checks for core arithmetic.
 * Run with `make -C tests run` (or `make test` from the project root). */
#include "modarith.h"
#include "orbit_scan.h"
#include "sparse_matrix.h"
#include <stdio.h>
#include <math.h>

static int fails = 0;
#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL: %s\n", msg); fails++; } \
} while (0)

static void test_modarith(void) {
    CHECK(ma_gcd(12, 18) == 6, "gcd(12,18)=6");
    CHECK(ma_ipow(3, 6) == 729, "3^6=729");
    /* 2 is a unit mod 3^r; check inverse and powmod round-trip */
    for (int r = 1; r <= 10; r++) {
        uint64_t m = ma_ipow(3, (uint64_t)r);
        uint64_t inv = ma_inv(2, m);
        CHECK(ma_mulmod(2, inv, m) == 1, "2 * 2^{-1} == 1 mod 3^r");
        /* 2 is a primitive root mod 3^r: order is 2*3^{r-1} (= phi) */
        uint64_t phi = 2 * ma_ipow(3, (uint64_t)(r - 1));
        CHECK(ma_powmod(2, phi, m) == 1, "2^phi == 1 mod 3^r");
        if (r >= 1) CHECK(ma_powmod(2, phi / 2, m) != 1 || r == 0,
                          "order of 2 is exactly phi (primitive root)");
    }
}

static void test_orbit(void) {
    /* The accelerated Syracuse orbit of every tested odd seed reaches 1. */
    uint64_t seeds[] = {1, 3, 7, 27, 97, 703, 9999};
    for (size_t i = 0; i < sizeof seeds/sizeof seeds[0]; i++) {
        orbit_t o; orbit_init(&o, seeds[i]);
        uint64_t guard = 0;
        while (o.status == ORBIT_RUNNING && guard < 100000) { orbit_step(&o); guard++; }
        CHECK(o.status == ORBIT_REACHED_ONE, "orbit reaches 1");
        orbit_clear(&o);
    }
}

/* Arnoldi spectral radius vs known spectra. */
static ldbl approx(ldbl a, ldbl b) { return fabsl(a-b); }

static void test_arnoldi(void) {
    ldbl res; int mu;

    /* 1. real diagonal: rho = max|diag| = 0.9 */
    { triplets_t t; tri_init(&t, 4);
      ldbl d[] = {0.3L, 0.9L, 0.5L, 0.7L};
      for (int i=0;i<4;i++) tri_add(&t,i,i,d[i]+0.0L*I);
      csr_t A = csr_from_triplets(&t); tri_free(&t);
      ldbl r = csr_spectral_radius_arnoldi(&A, 40, 240, 1e-12L, &res, &mu);
      CHECK(approx(r,0.9L) < 1e-9L, "arnoldi: real diagonal rho=0.9");
      csr_free(&A); }

    /* 2. complex diagonal: rho = |0.8 i| = 0.8 */
    { triplets_t t; tri_init(&t, 3);
      tri_add(&t,0,0,0.6L+0.0L*I); tri_add(&t,1,1,0.0L+0.8L*I); tri_add(&t,2,2,-0.5L+0.0L*I);
      csr_t A = csr_from_triplets(&t); tri_free(&t);
      ldbl r = csr_spectral_radius_arnoldi(&A, 40, 240, 1e-12L, &res, &mu);
      CHECK(approx(r,0.8L) < 1e-9L, "arnoldi: complex diagonal rho=0.8");
      csr_free(&A); }

    /* 3. cyclic permutation (5x5): eigenvalues are 5th roots of unity, rho=1 */
    { triplets_t t; tri_init(&t, 5);
      for (int i=0;i<5;i++) tri_add(&t,(i+1)%5,i,1.0L+0.0L*I);
      csr_t A = csr_from_triplets(&t); tri_free(&t);
      ldbl r = csr_spectral_radius_arnoldi(&A, 40, 240, 1e-12L, &res, &mu);
      CHECK(approx(r,1.0L) < 1e-9L, "arnoldi: cyclic permutation rho=1");
      csr_free(&A); }

    /* 4. agreement with power iteration on a well-separated nonnegative matrix */
    { triplets_t t; tri_init(&t, 6);
      for (int i=0;i<6;i++){ tri_add(&t,i,i,0.2L+0.1L*i); if(i+1<6) tri_add(&t,i,i+1,0.05L); }
      csr_t A = csr_from_triplets(&t); tri_free(&t);
      ldbl ra = csr_spectral_radius_arnoldi(&A, 40, 240, 1e-12L, &res, &mu);
      ldbl rp = csr_spectral_radius(&A, 5000, 1e-13L, 2, NULL, NULL);
      CHECK(approx(ra,rp) < 1e-7L, "arnoldi matches power iteration (separated spectrum)");
      csr_free(&A); }
}

int main(void) {
    test_modarith();
    test_orbit();
    test_arnoldi();
    if (fails == 0) { printf("all unit checks passed\n"); return 0; }
    fprintf(stderr, "%d unit check(s) failed\n", fails);
    return 1;
}
