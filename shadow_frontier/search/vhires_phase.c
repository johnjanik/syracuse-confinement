/* vhires_phase.c — very-high-resolution (D, eps) phase diagram engine.
 *
 * Computes ln lambda(D, omega, t) for the tilted strip transfer, using the
 * EXACT quantized state space: D-confinement forces B_j into the integer
 * window [ceil(j*log2(3) - D), floor(j*log2(3) + D)] of size <= floor(2D)+1,
 * so the tilted count is a rotation-driven product of small matrices.
 * No delta-grid discretization of the state variable at all; the growth
 * rate is the Birkhoff/Lyapunov average of per-step max-norm growth along
 * the (uniquely ergodic) rotation orbit.
 *
 * Tilt weight on letter b: w_b = exp(t * phi_omega(b)),
 *   phi_omega(b) = Re( omega * (z^{-b} - G) ),  z = e^{2 pi i / 3},
 *   G = sum_{b>=1} 2^{-b} z^{-b}.
 *
 * Output: row-major double array lnlam[ND][NW][NT] -> results/vhires_lnlam.bin
 *
 * Build: gcc -O3 -march=native -fopenmp -o vhires_phase vhires_phase.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <omp.h>

#define ND   2000          /* D grid points in [0.6, 6.0] */
#define NW   24            /* directions omega = e^{2 pi i k / NW} */
#define NT   400           /* tilts: t_0 = 0, then geomspace(0.2, 20, NT-1) */
#define P    2800          /* rotation-orbit length (steps) */
#define BURN 400           /* burn-in steps excluded from the average */
#define BCAP 24            /* letter cap (max possible b is ~ 2D + 2 <= 15) */
#define MMAX 16            /* max window size: floor(2*6)+1 = 13 */

static const double DLO = 0.6, DHI = 6.0;

int main(void)
{
    const double L = log(3.0) / log(2.0);

    /* G = sum_{b>=1} 2^{-b} z^{-b} */
    double Gr = 0.0, Gi = 0.0;
    for (int b = 1; b <= 300; b++) {
        double ang = -2.0 * M_PI * b / 3.0;
        Gr += pow(0.5, b) * cos(ang);
        Gi += pow(0.5, b) * sin(ang);
    }

    /* phi[wi][b] for b = 1..BCAP */
    static double phi[NW][BCAP + 1];
    for (int wi = 0; wi < NW; wi++) {
        double th = 2.0 * M_PI * wi / NW;
        double c = cos(th), s = sin(th);
        for (int b = 1; b <= BCAP; b++) {
            double ang = -2.0 * M_PI * b / 3.0;
            double cr = cos(ang) - Gr, ci = sin(ang) - Gi;
            phi[wi][b] = c * cr - s * ci;
        }
    }

    /* tilt grid */
    static double ts[NT];
    ts[0] = 0.0;
    for (int i = 1; i < NT; i++)
        ts[i] = 0.2 * pow(20.0 / 0.2, (double)(i - 1) / (double)(NT - 2));

    double *out = malloc((size_t)ND * NW * NT * sizeof(double));
    if (!out) { fprintf(stderr, "alloc failed\n"); return 1; }

    int done = 0;

#pragma omp parallel
    {
        /* per-thread window tables (depend on D only) */
        long  *lo = malloc((P + 1) * sizeof(long));
        int   *mm = malloc((P + 1) * sizeof(int));
        double v[MMAX], v2[MMAX], w[BCAP + 1];

#pragma omp for schedule(dynamic) collapse(2)
        for (int di = 0; di < ND; di++) {
            for (int wi = 0; wi < NW; wi++) {
                double D = DLO + (DHI - DLO) * di / (double)(ND - 1);

                for (int j = 0; j <= P; j++) {
                    double c = j * L;
                    long l = (long)ceil(c - D - 1e-12);
                    long h = (long)floor(c + D + 1e-12);
                    lo[j] = l;
                    mm[j] = (int)(h - l + 1);
                    if (mm[j] > MMAX) { fprintf(stderr, "MMAX overflow\n"); exit(1); }
                }

                for (int ti = 0; ti < NT; ti++) {
                    double t = ts[ti];
                    for (int b = 1; b <= BCAP; b++)
                        w[b] = exp(t * phi[wi][b]);

                    /* init: B_0 = 0 sits at index -lo[0] in window 0 */
                    for (int k = 0; k < MMAX; k++) v[k] = 0.0;
                    v[(int)(-lo[0])] = 1.0;

                    double logsum = 0.0;
                    for (int j = 0; j < P; j++) {
                        long d = lo[j + 1] - lo[j];
                        int m0 = mm[j], m1 = mm[j + 1];
                        double vmax = 0.0;
                        for (int k2 = 0; k2 < m1; k2++) {
                            double s = 0.0;
                            for (int k = 0; k < m0; k++) {
                                long b = d + k2 - k;
                                if (b >= 1 && b <= BCAP) s += v[k] * w[b];
                            }
                            v2[k2] = s;
                            if (s > vmax) vmax = s;
                        }
                        if (vmax <= 0.0) { logsum = -1e9; break; } /* cannot happen: L > 1 */
                        double inv = 1.0 / vmax;
                        for (int k2 = 0; k2 < m1; k2++) v[k2] = v2[k2] * inv;
                        for (int k2 = m1; k2 < MMAX; k2++) v[k2] = 0.0;
                        if (j >= BURN) logsum += log(vmax);
                    }
                    out[((size_t)di * NW + wi) * NT + ti] =
                        logsum > -1e8 ? logsum / (double)(P - BURN) : -1e9;
                }

#pragma omp atomic
                done++;
                if (done % 4800 == 0)
                    fprintf(stderr, "  %d / %d tasks\n", done, ND * NW);
            }
        }
        free(lo); free(mm);
    }

    FILE *f = fopen("results/vhires_lnlam.bin", "wb");
    if (!f) { fprintf(stderr, "cannot open output\n"); return 1; }
    fwrite(out, sizeof(double), (size_t)ND * NW * NT, f);
    fclose(f);

    /* meta sidecar */
    f = fopen("results/vhires_lnlam.meta", "w");
    fprintf(f, "ND %d\nNW %d\nNT %d\nP %d\nBURN %d\nDLO %g\nDHI %g\n"
               "tilts t0=0 then geomspace(0.2,20,%d)\n",
            ND, NW, NT, P, BURN, DLO, DHI, NT - 1);
    fclose(f);

    fprintf(stderr, "wrote results/vhires_lnlam.bin (%zu MB)\n",
            (size_t)ND * NW * NT * 8 / (1024 * 1024));
    free(out);
    return 0;
}
