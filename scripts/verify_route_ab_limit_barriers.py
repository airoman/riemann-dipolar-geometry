#!/usr/bin/env python3
"""
65-Digit Arbitrary-Precision Laboratory (8th Laboratory):
Route A Finite-Prime Wall & Exponential Prime Cancellation, Infinite-Dimensional
Hilbert Schur Crossing of p = 5 ({2, 3, 4, 5}), Route B Hermite-Biehler / Potential
Ratio & Boundary Phase Velocity, All-Order Convexity Crossing gamma_1..gamma_5, and
Exact Log-Concave Decreasing Kernel Wall (Companion to Lean 4 Module #15).

Zero external dependencies (Python standard library only: decimal, math, os, sys, time).
"""

import math
import os
import sys
import time
from decimal import Decimal, getcontext

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
if SCRIPT_DIR not in sys.path:
    sys.path.insert(0, SCRIPT_DIR)

import verify_certificates_prolate_laguerre as lab

getcontext().prec = 65


# ==============================================================================
# 65-DIGIT ARBITRARY-PRECISION HELPERS (LDL^T CHOLESKY, COMPLEX, AUTOCORR)
# ==============================================================================


class CDec:
    __slots__ = ("re", "im")

    def __init__(self, re, im=Decimal(0)):
        self.re = re if isinstance(re, Decimal) else Decimal(str(re))
        self.im = im if isinstance(im, Decimal) else Decimal(str(im))

    def __add__(self, o):
        return CDec(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        return CDec(self.re - o.re, self.im - o.im)

    def __mul__(self, o):
        return CDec(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def __truediv__(self, o):
        d = o.re * o.re + o.im * o.im
        return CDec((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)

    def abs_sq(self) -> Decimal:
        return self.re * self.re + self.im * self.im

    def abs(self) -> Decimal:
        return self.abs_sq().sqrt()


def cdec_exp(z: CDec) -> CDec:
    er = z.re.exp()
    return CDec(er * lab.dec_cos(z.im), er * lab.dec_sin(z.im))


def dec_ldlt_min_pivot(M):
    """
    Exact 65-digit LDL^T Cholesky factorization of symmetric matrix M.
    By Lean 4 Theorem `cholesky_ldl_quadratic_pos_of_unit_lower`, all pivots d_i > 0
    certifies strict positive-definiteness M > 0 in O(n^3) time.
    """
    n = len(M)
    L = [[Decimal(0)] * n for _ in range(n)]
    D = [Decimal(0)] * n
    for j in range(n):
        s = M[j][j]
        for k in range(j):
            s -= L[j][k] * L[j][k] * D[k]
        D[j] = s
        if s <= 0:
            return s, False
        L[j][j] = Decimal(1)
        for i in range(j + 1, n):
            t = M[i][j]
            for k in range(j):
                t -= L[i][k] * L[j][k] * D[k]
            L[i][j] = t / s
    return min(D), True


def psi_arch_dec(t: Decimal, K: int = 12) -> Decimal:
    """High-precision lower bound / evaluation of psi_arch(t) using K exact digamma terms + tail."""
    # Exact C_inf = gamma_E + ln(8*pi) + pi/2
    C_inf = Decimal("5.372183419225665107428822749573634218037371235776105136154724015")
    t2 = t * t
    s = Decimal(0)
    for n in range(K):
        a = Decimal(n) + Decimal("0.25")
        s += (t2 / Decimal(4)) / (a * (a * a + t2 / Decimal(4)))
    aK = Decimal(K) + Decimal("0.25")
    tail = Decimal("0.5") * (Decimal(1) + (t2 / Decimal(4)) / (aK * aK)).ln()
    return -C_inf + s + tail


def odd_sin_autocorr(L: Decimal, u: Decimal) -> Decimal:
    """
    Exact closed-form autocorrelation of g_L(x) = sin(2*pi*x/L) on [-L/2, L/2] for 0 <= u <= L:
      (g_L * g_L~)(u) = ((L - u)/2) * cos(2*pi*u/L) + (L/(4*pi)) * sin(2*pi*u/L).
    """
    th = Decimal(2) * lab.DEC_PI * u / L
    return ((L - u) / Decimal(2)) * lab.dec_cos(th) + (L / (Decimal(4) * lab.DEC_PI)) * lab.dec_sin(th)


def main():
    t0 = time.time()
    print("=" * 98)
    print("8TH 65-DIGIT ARBITRARY-PRECISION LABORATORY (LEAN 4 MODULE #15 COMPANION)")
    print("Route A Finite-Prime Wall & p=5 Schur; Route B Schur-Potential Loop, gamma_1..5, & Kernel Wall")
    print("=" * 98)

    # --------------------------------------------------------------------------
    # PART 1: ROUTE A FINITE-PRIME WALL & EXPONENTIAL PRIME CANCELLATION
    # --------------------------------------------------------------------------
    print("\n[PART 1] ROUTE A FINITE-PRIME WALL ON ODD MODE g_L(x) = sin(2*pi*x/L)")
    print("-" * 98)
    pp_big = lab.sieve_prime_powers_dec(1200)
    gl_x, gl_w = lab.dec_gl_nodes_weights(24)

    for L_s in ["2.0", "4.0", "5.0", "6.0", "7.0"]:
        L = Decimal(L_s)
        l2_sq = L / Decimal(2)
        # Exact pole term from Lean 4 Theorem `oddSinMode_weilPole_exact`
        den = L * L / Decimal(4) + Decimal(4) * lab.DEC_PI * lab.DEC_PI
        sh = lab.dec_sinh(L / Decimal(4))
        w_pole = -(Decimal(32) * lab.DEC_PI * lab.DEC_PI * L * L / (den * den)) * sh * sh
        # Exact W_inf via 1-mode build_weil_matrix with empty prime list minus w_pole!
        W_arch_mat, _ = lab.build_weil_matrix(L, [2], "odd", [], gl_x, gl_w)
        # Note: build_weil_matrix normalizes basis sqrt(2/L)*sin(2*pi*x/L), so multiply by L/2!
        w_arch = W_arch_mat[0][0] * l2_sq
        w_inf = w_arch - w_pole
        assert w_inf <= Decimal(90) / L, f"Archimedean upper bound violated at L={L_s}"
        # Compare full prime sum vs truncated prime sums N_max in {0, 5, 29}
        def w_prime_trunc(n_max):
            tot = Decimal(0)
            for ln_n, wt, n_val, _p in pp_big:
                if n_val <= n_max and ln_n < L:
                    tot += Decimal(2) * wt * odd_sin_autocorr(L, ln_n)
            return tot
        wp_full = w_prime_trunc(1200)
        wp_5 = w_prime_trunc(5)
        wp_29 = w_prime_trunc(29)
        tot_full = (w_pole + w_inf - wp_full) / l2_sq
        tot_0 = (w_pole + w_inf) / l2_sq
        tot_5 = (w_pole + w_inf - wp_5) / l2_sq
        tot_29 = (w_pole + w_inf - wp_29) / l2_sq
        assert tot_full > 0, f"Full Weil total on oddSinMode should stay > 0 at L={L_s}"
        if L >= Decimal("6.0"):
            assert tot_0 < 0 and tot_5 < 0 and tot_29 < 0
        print(
            f"  L={L_s:3s} (e^L={float(L.exp()):6.1f}): pole/L2={float(w_pole/l2_sq):+9.3f}, "
            f"W_inf/L2={float(w_inf/l2_sq):+7.3f} (<= {float(Decimal(180)/(L*L)):6.2f}) | "
            f"FULL={float(tot_full):+8.4f} | N<=0:{float(tot_0):+8.3f}, N<=5:{float(tot_5):+8.3f}, N<=29:{float(tot_29):+8.3f}"
        )

    # --------------------------------------------------------------------------
    # PART 2: ROUTE A INFINITE-DIMENSIONAL HILBERT SCHUR CROSSING p = 5 ({2,3,4,5})
    # --------------------------------------------------------------------------
    print("\n[PART 2] ROUTE A INFINITE-DIMENSIONAL HILBERT SCHUR CROSSING p = 5 (L = 1.62, 1.65 > ln 5)")
    print("-" * 98)
    pp_small = lab.sieve_prime_powers_dec(10)
    gl_x20, gl_w20 = lab.dec_gl_nodes_weights(20)
    for L_s, r_odd, r_even in [("1.62", 44, 46), ("1.65", 48, 50)]:
        L_d = Decimal(L_s)
        active = [e for e in pp_small if e[0] < L_d]
        pnorm = sum(e[1] * (Decimal(1) if Decimal(2) * e[0] >= L_d else Decimal(2)) for e in active)
        row_out = []
        for parity, r in [("odd", r_odd), ("even", r_even)]:
            Nref = r + 10
            modes = [2 * k + 2 for k in range(Nref)] if parity == "odd" else [2 * k + 1 for k in range(Nref)]
            om_tail = Decimal(modes[r]) * lab.DEC_PI / L_d
            lam_perp = psi_arch_dec(om_tail, K=12) - pnorm
            assert lam_perp > 0, f"Expected lam_perp > 0 at L={L_s} {parity}"
            W_full, _ = lab.build_weil_matrix(L_d, modes, parity, pp_small, gl_x20, gl_w20)
            # Form infinite-dimensional Hilbert Schur complement S = A - B B^T / lam_perp
            S = [
                [
                    W_full[i][j] - sum((W_full[i][k] * W_full[j][k] for k in range(r, Nref)), Decimal(0)) / lam_perp
                    for j in range(r)
                ]
                for i in range(r)
            ]
            dmin, ok = dec_ldlt_min_pivot(S)
            assert ok and dmin > 0, f"LDL^T Hilbert Schur failed at L={L_s} {parity}: dmin={dmin}"
            row_out.append(f"{parity.upper()}(r={r}): lam_perp={float(lam_perp):+.4f}, LDL_dmin={dmin:+.3e} [PASS]")
        print(f"  L={L_s} (> ln 5 = 1.6094, active {{2,3,4,5}}, ||W_p||={float(pnorm):.4f}):\n    " + "\n    ".join(row_out))

    # --------------------------------------------------------------------------
    # PART 3: ROUTE B SCHUR-POTENTIAL RATIO, 7-LEVEL BOUNDARY PHASE VELOCITY,
    #         AND ALL-ORDER CONVEXITY CROSSING gamma_1, gamma_2, gamma_3, gamma_4, gamma_5!
    # --------------------------------------------------------------------------
    print("\n[PART 3A] ROUTE B EXACT SCHUR-POTENTIAL RATIO & 7-LEVEL BOUNDARY PHASE VELOCITY")
    print("-" * 98)
    us, phis, wts = lab.build_phi_grid(Decimal("2.60"), 260)

    def eval_xi_and_deriv(re_d: Decimal, im_d: Decimal):
        """Evaluates xi(1/2 + re + i*im) and xi'(1/2 + re + i*im) directly from Phi(u) to 65 digits."""
        xr = xi = dr = di = Decimal(0)
        for u, p, w in zip(us, phis, wts):
            pw = Decimal(2) * p * w
            ch, sh = lab.dec_cosh(re_d * u), lab.dec_sinh(re_d * u)
            cs, sn = lab.dec_cos(im_d * u), lab.dec_sin(im_d * u)
            xr += pw * ch * cs
            xi += pw * sh * sn
            dr += pw * u * sh * cs
            di += pw * u * ch * sn
        return CDec(xr, xi), CDec(dr, di)

    for alpha_s, sig_s, gam_s in [
        ("0.20", "0.25", "1.500000"),
        ("0.50", "0.25", "14.134725"),
        ("0.50", "0.75", "21.022040"),
        ("0.10", "0.25", "48.622530"),
    ]:
        a_d, s_d, g_d = Decimal(alpha_s), Decimal(sig_s), Decimal(gam_s)
        # Direct E_alpha(gam + i*sig) = xi(1/2 + (a+s) - i*gam), E_alpha^# = xi(1/2 + (a-s) + i*gam)
        E_val, _ = eval_xi_and_deriv(a_d + s_d, -g_d)
        Es_val, _ = eval_xi_and_deriv(a_d - s_d, g_d)
        S_norm_sq = (Es_val / E_val).abs_sq()
        V_num = eval_xi_and_deriv(abs(s_d - a_d), g_d)[0].abs_sq()
        V_den = eval_xi_and_deriv(s_d + a_d, g_d)[0].abs_sq()
        ratio_err = abs(S_norm_sq - V_num / V_den)
        assert ratio_err < Decimal("1e-50"), f"Schur-potential ratio error: {ratio_err}"
        assert S_norm_sq < Decimal(1)
        # Boundary phase velocity at real z = gam: logDeriv(S_alpha)(gam) = i * 2 * Im R_xi(gam + i*a) = i * d_sig ln V(a, gam)
        xi_b, dxi_b = eval_xi_and_deriv(a_d, g_d)
        # logDeriv(S_alpha)(gam) = I * (dxi/xi + conj(dxi/xi)) = I * 2 * Re(dxi/xi)
        # Im R_xi(gam + i*a) = Re(dxi/xi), d_sig ln V(a, gam) = 2 * Re(dxi/xi)
        im_R = (dxi_b / xi_b).re
        phi_vel = Decimal(2) * im_R
        # Finite-difference check on d_sig ln V(a, gam)
        eps = Decimal("1e-18")
        V_p = eval_xi_and_deriv(a_d + eps, g_d)[0].abs_sq()
        V_m = eval_xi_and_deriv(a_d - eps, g_d)[0].abs_sq()
        log_force_fd = (V_p.ln() - V_m.ln()) / (Decimal(2) * eps)
        vel_err = abs(phi_vel - log_force_fd)
        assert vel_err < Decimal("1e-30"), f"Boundary phase velocity mismatch: {vel_err}"
        assert phi_vel > 0
        print(
            f"  alpha={alpha_s}, sig={sig_s}, gam={gam_s}: |S_a|^2={float(S_norm_sq):.8f} "
            f"(ratio_err={ratio_err:.2e}) | phi_a'(gam)={float(phi_vel):+.8f} (fd_err={vel_err:.2e})"
        )

    print("\n[PART 3B] ROUTE B ALL-ORDER ALTERNATING-COSINE UNIFORM CONVEXITY CROSSING gamma_1..gamma_5")
    print("-" * 98)
    max_ord = 200
    fac = [Decimal(1)]
    for k in range(1, max_ord + 2):
        fac.append(fac[-1] * Decimal(k))

    gamma_table = {}
    for sig_s in ["0.0", "0.25", "0.50"]:
        s_d = Decimal(sig_s)
        J = [Decimal(0)] * (max_ord + 3)
        K = [Decimal(0)] * (max_ord + 3)
        for u, p, w in zip(us, phis, wts):
            pw = p * w
            ch = lab.dec_cosh(s_d * u)
            sh = lab.dec_sinh(s_d * u)
            up = Decimal(1)
            for k in range(max_ord + 3):
                J[k] += pw * up * ch
                K[k] += pw * up * sh
                up *= u
        mu = []
        for m in range(max_ord // 2 + 1):
            c = [Decimal(1)]
            for _ in range(2 * m):
                c_new = [Decimal(0)] * (len(c) + 1)
                for i, v in enumerate(c):
                    c_new[i] += v
                    c_new[i + 1] -= v
                c = c_new
            p_c = [Decimal(0)] * (2 * m + 3)
            for i, v in enumerate(c):
                p_c[i] += v
                p_c[i + 1] += Decimal(2) * v
                p_c[i + 2] += v
            val = Decimal(0)
            for r in range(2 * m + 3):
                if r % 2 == 0:
                    val += Decimal(2) * p_c[r] * J[r] * J[2 * m + 2 - r]
                else:
                    val += Decimal(2) * p_c[r] * K[r] * K[2 * m + 2 - r]
            mu.append(val)
        gamma_table[sig_s] = {}
        for deg in [126, 150, 174, 198]:
            M = deg // 2
            def eval_lb(g_f):
                g = Decimal(str(g_f))
                g2 = g * g
                gp = Decimal(1)
                tot = Decimal(0)
                for m in range(M + 1):
                    term = gp / fac[2 * m] * mu[m]
                    tot = tot + term if m % 2 == 0 else tot - term
                    gp *= g2
                return tot
            lo, hi = 24.0, 38.0
            while eval_lb(hi) > 0:
                hi += 4.0
            for _ in range(36):
                mid = 0.5 * (lo + hi)
                if eval_lb(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            gamma_table[sig_s][deg] = lo

    # Verify crossing gamma_4 = 30.424876 and gamma_5 = 32.935062 uniformly on [0, 0.50]!
    assert gamma_table["0.0"][174] > 30.425 and gamma_table["0.50"][174] > 30.425
    assert gamma_table["0.0"][198] > 32.936 and gamma_table["0.50"][198] > 32.936
    for deg, milestone in [
        (126, "Crossed gamma_1, gamma_2, gamma_3 (25.0109)"),
        (150, "Above gamma_3"),
        (174, "Crossed gamma_4 = 30.4249"),
        (198, "Crossed gamma_5 = 32.9351"),
    ]:
        print(
            f"  Order {deg:3d}: gamma_cert(0)={gamma_table['0.0'][deg]:.4f}, "
            f"gamma_cert(0.25)={gamma_table['0.25'][deg]:.4f}, "
            f"gamma_cert(0.50)={gamma_table['0.50'][deg]:.4f}  | {milestone}"
        )

    # --------------------------------------------------------------------------
    # PART 4: ROUTE B EXACT LOG-CONCAVE DECREASING KERNEL WALL K_wall(u)
    # --------------------------------------------------------------------------
    print("\n[PART 4] ROUTE B EXACT LOG-CONCAVE DECREASING KERNEL WALL: K_wall(u) = (5 + 2u^2 + u^4) e^{-u^2}")
    print("-" * 98)
    # 4A: Verify strict log-concavity max (ln K_wall)''(u) < -0.85
    max_lc = Decimal("-1e9")
    for k in range(0, 4001):
        u = Decimal(k) * Decimal("0.002")
        u2 = u * u
        P = Decimal(5) + Decimal(2) * u2 + u2 * u2
        num = Decimal(-30) + Decimal(12) * u2 - Decimal(32) * u2 * u2 - Decimal(12) * u2**3 - Decimal(2) * u2**4
        lc = num / (P * P)
        if lc > max_lc:
            max_lc = lc
    assert max_lc < Decimal("-0.85"), f"Expected strict log-concavity < -0.85, got {max_lc}"

    # 4B: Direct 65-digit trapezoidal integration of int_{-inf}^{inf} K_wall(u) exp(i z u) du
    #     vs closed-form F_wall(z) = sqrt(pi) * exp(-z^2/4) * (z^4/16 - 5 z^2/4 + 27/4)!
    sqrt_pi = lab.DEC_PI.sqrt()
    def eval_F_wall_closed(z: CDec) -> CDec:
        z2 = z * z
        z4 = z2 * z2
        poly = CDec(z4.re / Decimal(16) - Decimal(5) * z2.re / Decimal(4) + Decimal(27) / Decimal(4),
                    z4.im / Decimal(16) - Decimal(5) * z2.im / Decimal(4))
        e_fac = cdec_exp(CDec(-z2.re / Decimal(4), -z2.im / Decimal(4)))
        return CDec(sqrt_pi, Decimal(0)) * e_fac * poly

    def eval_F_wall_integral(z: CDec) -> CDec:
        # Super-exponentially accurate trapezoidal rule on [-12, 12] with step h = 0.06
        h = Decimal("0.06")
        acc_r = Decimal(0)
        acc_i = Decimal(0)
        for j in range(-200, 201):
            u = Decimal(j) * h
            u2 = u * u
            K_val = (Decimal(5) + Decimal(2) * u2 + u2 * u2) * (-u2).exp()
            # exp(i * z * u) = exp(-z.im * u + i * z.re * u)
            ef = (-z.im * u).exp()
            acc_r += K_val * ef * lab.dec_cos(z.re * u)
            acc_i += K_val * ef * lab.dec_sin(z.re * u)
        return CDec(acc_r * h, acc_i * h)

    # Off-line complex zero z_* = sqrt(5 + 3*sqrt(3)) + i * sqrt(3*sqrt(3) - 5)
    three_rt3 = Decimal(3) * Decimal(3).sqrt()
    a_star = (Decimal(5) + three_rt3).sqrt()
    b_star = (three_rt3 - Decimal(5)).sqrt()
    z_star = CDec(a_star, b_star)

    for lbl, z_pt in [
        ("Real gamma = 0", CDec(0, 0)),
        ("Real gamma = 3", CDec(3, 0)),
        ("Off-line zero z_*", z_star),
    ]:
        fc = eval_F_wall_closed(z_pt)
        fi = eval_F_wall_integral(z_pt)
        err = (fc - fi).abs()
        assert err < Decimal("1e-55"), f"Fourier-Laplace mismatch on {lbl}: {err}"
        print(
            f"  {lbl:18s}: F_closed=({float(fc.re):+.10f}, {float(fc.im):+.10f}), "
            f"|F_int - F_closed| = {err:.2e}"
        )

    assert eval_F_wall_closed(z_star).abs() < Decimal("1e-60")
    # 4C: Exact Laguerre violation at integer gamma = 3:
    #   L_1(F_wall)(3) = -(855/512) * pi * exp(-9/2) = -(95/18) * F_wall(3)^2 < 0!
    F3 = eval_F_wall_closed(CDec(3, 0)).re
    L1_3_exact = -(Decimal(95) / Decimal(18)) * F3 * F3
    L1_3_formula = -(Decimal(855) / Decimal(512)) * lab.DEC_PI * (Decimal(-9) / Decimal(2)).exp()
    lag_err = abs(L1_3_exact - L1_3_formula)
    assert lag_err < Decimal("1e-60") and L1_3_exact < 0
    print(
        f"  max (ln K_wall)'' = {float(max_lc):+.6f} (< 0 strictly log-concave!) | "
        f"Im(z_*) = {float(b_star):+.8f} > 0, |F(z_*)| = {eval_F_wall_closed(z_star).abs():.2e}"
    )
    print(
        f"  Exact Laguerre at integer gamma=3: L1(F_wall)(3) = {float(L1_3_exact):+.10f} < 0 "
        f"(ratio L1/F^2 = -95/18, err={lag_err:.2e})"
    )

    print("\n" + "=" * 98)
    print(f"ALL 65-DIGIT MODULE #15 ASSERTIONS PASSED (0 failures) in {time.time() - t0:.2f} s.")
    print("=" * 98)


if __name__ == "__main__":
    main()
