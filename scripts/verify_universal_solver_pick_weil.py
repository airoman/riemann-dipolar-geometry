#!/usr/bin/env python3
"""
65-Digit Arbitrary-Precision Laboratory (7th Laboratory):
Universal Hopfield-Boltzmann Solver Lyapunov Descent, Adaptive Resolvent-Universal
Preconditioner, Remote Lifted Pick Detection, and Exact All-Primes von Mangoldt
Resolvent Identity (Companion to Lean 4 Module #14).

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
# 65-DIGIT ARBITRARY-PRECISION HELPERS (COMPLEX, DIGAMMA, LINEAR ALGEBRA)
# ==============================================================================


def dec_ln(x: Decimal) -> Decimal:
    return x.ln()


def dec_tanh(y: Decimal) -> Decimal:
    e2 = (Decimal(2) * y).exp()
    return (e2 - Decimal(1)) / (e2 + Decimal(1))


def dec_phi_ent(x: Decimal) -> Decimal:
    """Binary entropy barrier Phi_ent(x) = ((1+x)/2) ln(1+x) + ((1-x)/2) ln(1-x)."""
    half = Decimal("0.5")
    one = Decimal(1)
    if abs(x) >= one - Decimal("1e-55"):
        return Decimal(2).ln()
    return half * (one + x) * (one + x).ln() + half * (one - x) * (one - x).ln()


def dec_quad(M, v) -> Decimal:
    n = len(v)
    total = Decimal(0)
    for i in range(n):
        row_dot = Decimal(0)
        Mi = M[i]
        for j in range(n):
            row_dot += Mi[j] * v[j]
        total += v[i] * row_dot
    return total


def dec_matvec(M, v):
    n = len(v)
    out = [Decimal(0)] * n
    for i in range(n):
        s = Decimal(0)
        Mi = M[i]
        for j in range(n):
            s += Mi[j] * v[j]
        out[i] = s
    return out


def dec_free_energy_Q(Q, s) -> Decimal:
    """Boltzmann-Hopfield free energy L_Q(s) = -(1/2) s^T Q s + sum_i Phi_ent(s_i)."""
    return -Decimal("0.5") * dec_quad(Q, s) + sum((dec_phi_ent(x) for x in s), Decimal(0))


def dec_solve_linear(A, b):
    """65-digit Gaussian elimination with partial pivoting."""
    n = len(b)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(M[r][col]))
        M[col], M[piv] = M[piv], M[col]
        piv_val = M[col][col]
        for r in range(col + 1, n):
            fac = M[r][col] / piv_val
            for c in range(col, n + 1):
                M[r][c] -= fac * M[col][c]
    x = [Decimal(0)] * n
    for i in range(n - 1, -1, -1):
        s = M[i][n]
        for j in range(i + 1, n):
            s -= M[i][j] * x[j]
        x[i] = s / M[i][i]
    return x


def dec_matrix_inverse(A):
    """65-digit inverse of n x n real matrix A."""
    n = len(A)
    cols = []
    for k in range(n):
        e = [Decimal(1) if i == k else Decimal(0) for i in range(n)]
        cols.append(dec_solve_linear(A, e))
    return [[cols[j][i] for j in range(n)] for i in range(n)]


def run_universal_solver_dec(W, mu: Decimal, steps: int = 800, s0=None):
    """
    Runs synchronous Universal Formula iteration:
      s^{(t+1)} = tanh(Q s^{(t)}),   Q = I - (1/mu) W
    and verifies the exact Lean 4 Module #14 discrete Lyapunov descent inequality at EVERY step:
      L_Q(s') + (1/2) (s' - s)^T Q (s' - s) + (1/2) ||s' - s||_2^2 <= L_Q(s).
    """
    n = len(W)
    Q = [[(Decimal(1) if i == j else Decimal(0)) - W[i][j] / mu for j in range(n)] for i in range(n)]
    if s0 is None:
        s = [Decimal("0.05") * (Decimal(1) if i % 2 == 0 else Decimal("-0.7")) for i in range(n)]
    else:
        s = list(s0)
    L_prev = dec_free_energy_Q(Q, s)
    lyap_slack_min = Decimal("1e100")
    monotone_ok = True
    for _ in range(steps):
        h = dec_matvec(Q, s)
        s_new = [dec_tanh(v) for v in h]
        L_new = dec_free_energy_Q(Q, s_new)
        ds = [s_new[i] - s[i] for i in range(n)]
        ds_sq = sum((d * d for d in ds), Decimal(0))
        dQ = dec_quad(Q, ds)
        # Exact Lean 4 bound: L_prev - (L_new + 0.5*dQ + 0.5*ds_sq) >= 0
        slack = L_prev - (L_new + Decimal("0.5") * dQ + Decimal("0.5") * ds_sq)
        if slack < lyap_slack_min:
            lyap_slack_min = slack
        if slack < Decimal("-1e-50"):
            monotone_ok = False
        L_prev = L_new
        s = s_new
    quad_W = dec_quad(W, s)
    norm2 = sum((x * x for x in s), Decimal(0)).sqrt()
    sum4 = sum((x ** 4 for x in s), Decimal(0))
    Qs = dec_matvec(Q, s)
    res_fp = max(abs(s[i] - dec_tanh(Qs[i])) for i in range(n))
    return {
        "s": s,
        "norm2": norm2,
        "quad_W": quad_W,
        "L_final": L_prev,
        "quartic_upper_neg": -(mu / Decimal(3)) * sum4,
        "quartic_lower_L": sum4 / Decimal(12),
        "res_fp": res_fp,
        "monotone_ok": monotone_ok,
        "lyap_slack_min": lyap_slack_min,
    }


def run_adaptive_resolvent_universal_dec(W, delta: Decimal, steps: int = 120, s0=None):
    """
    Runs Adaptive Resolvent-Universal Solver:
      s^{(t+1)} = tanh(delta * (W + delta I)^{-1} s^{(t)})
    with Q_res = delta * (W + delta I)^{-1}.
    When delta > max(0, -lambda_min(W)), Q_res is symmetric positive definite,
    so L_{Q_res} obeys exact discrete Lyapunov descent at every step AND every
    fixed point s = tanh(delta u) with u = (W + delta I)^{-1} s satisfies
      u^T W u <= -(1/delta) ||W u||_2^2 - (1/(3*delta)) sum_i s_i^4.
    """
    n = len(W)
    A = [[W[i][j] + (delta if i == j else Decimal(0)) for j in range(n)] for i in range(n)]
    A_inv = dec_matrix_inverse(A)
    Q_res = [[delta * A_inv[i][j] for j in range(n)] for i in range(n)]
    if s0 is None:
        s = [Decimal("0.02") * (Decimal(1) if i % 2 == 0 else Decimal("-0.6")) for i in range(n)]
    else:
        s = list(s0)
    L_prev = dec_free_energy_Q(Q_res, s)
    monotone_ok = True
    lyap_slack_min = Decimal("1e100")
    for _ in range(steps):
        h = dec_matvec(Q_res, s)
        s_new = [dec_tanh(v) for v in h]
        L_new = dec_free_energy_Q(Q_res, s_new)
        ds = [s_new[i] - s[i] for i in range(n)]
        ds_sq = sum((d * d for d in ds), Decimal(0))
        dQ = dec_quad(Q_res, ds)
        slack = L_prev - (L_new + Decimal("0.5") * dQ + Decimal("0.5") * ds_sq)
        if slack < lyap_slack_min:
            lyap_slack_min = slack
        if slack < Decimal("-1e-50"):
            monotone_ok = False
        L_prev = L_new
        s = s_new
    # Resolvent-mapped witness u = (W + delta I)^{-1} s
    u = dec_matvec(A_inv, s)
    Wu = dec_matvec(W, u)
    uWu = sum((u[i] * Wu[i] for i in range(n)), Decimal(0))
    Wu_sq = sum((w * w for w in Wu), Decimal(0))
    sum4 = sum((x ** 4 for x in s), Decimal(0))
    norm2 = sum((x * x for x in s), Decimal(0)).sqrt()
    res_fp = max(abs(s[i] - dec_tanh(delta * u[i])) for i in range(n))
    rhs_bound = -(Wu_sq / delta) - sum4 / (Decimal(3) * delta)
    return {
        "s": s,
        "u": u,
        "norm2": norm2,
        "uWu": uWu,
        "rhs_bound": rhs_bound,
        "L_final": L_prev,
        "res_fp": res_fp,
        "monotone_ok": monotone_ok,
        "lyap_slack_min": lyap_slack_min,
    }


# ==============================================================================
# 65-DIGIT COMPLEX ARITHMETIC & COMPLEX DIGAMMA FOR ALL-PRIMES IDENTITY
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

    def __neg__(self):
        return CDec(-self.re, -self.im)

    def __mul__(self, o):
        return CDec(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def __truediv__(self, o):
        d = o.re * o.re + o.im * o.im
        return CDec((self.re * o.re + self.im * o.im) / d, (self.im * o.re - self.re * o.im) / d)

    def conj(self):
        return CDec(self.re, -self.im)

    def abs(self) -> Decimal:
        return (self.re * self.re + self.im * self.im).sqrt()


def cdec_log(z: CDec) -> CDec:
    """Principal complex logarithm in 65-digit arithmetic (Re(z) > 0)."""
    r = z.abs()
    # atan2(im, re) via Newton refinement on tan(theta) = im/re for Re(z) > 0
    theta = Decimal(str(math.atan2(float(z.im), float(z.re))))
    # Refine theta via sin/cos Newton: f(t) = z.re * sin(t) - z.im * cos(t) = 0
    for _ in range(5):
        st = lab.dec_sin(theta)
        ct = lab.dec_cos(theta)
        f = z.re * st - z.im * ct
        df = z.re * ct + z.im * st
        theta -= f / df
    return CDec(r.ln(), theta)


def cdec_digamma(w: CDec) -> CDec:
    """
    High-precision complex digamma psi(w) = Gamma'(w)/Gamma(w) for Re(w) > 0
    using shift recurrence psi(w) = psi(w + M) - sum_{k=0}^{M-1} 1/(w + k)
    and Stirling-Bernoulli asymptotic expansion through B_16.
    """
    M = 28
    shift_sum = CDec(0, 0)
    for k in range(M):
        shift_sum = shift_sum + (CDec(1, 0) / (w + CDec(k, 0)))
    z = w + CDec(M, 0)
    inv_z = CDec(1, 0) / z
    inv_z2 = inv_z * inv_z
    # psi(z) ~ ln(z) - 1/(2z) - sum_{k=1}^8 B_{2k} / (2k * z^{2k})
    # B_2=1/6, B_4=-1/30, B_6=1/42, B_8=-1/30, B_10=5/66, B_12=-691/2730, B_14=7/6, B_16=-3617/510
    bernoulli_2k = [
        (2, Decimal(1) / Decimal(6)),
        (4, -Decimal(1) / Decimal(30)),
        (6, Decimal(1) / Decimal(42)),
        (8, -Decimal(1) / Decimal(30)),
        (10, Decimal(5) / Decimal(66)),
        (12, -Decimal(691) / Decimal(2730)),
        (14, Decimal(7) / Decimal(6)),
        (16, -Decimal(3617) / Decimal(510)),
    ]
    asym = cdec_log(z) - (CDec(Decimal("0.5"), 0) * inv_z)
    p = inv_z2
    for two_k, b2k in bernoulli_2k:
        coeff = b2k / Decimal(two_k)
        asym = asym - (CDec(coeff, 0) * p)
        p = p * inv_z2
    return asym - shift_sum


def sieve_von_mangoldt(N: int):
    """Returns list of (n, log(p)) for all prime powers p^k <= N."""
    is_prime = [True] * (N + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(N ** 0.5) + 1):
        if is_prime[p]:
            for m in range(p * p, N + 1, p):
                is_prime[m] = False
    entries = []
    for p in range(2, N + 1):
        if is_prime[p]:
            lp = Decimal(p).ln()
            pk = p
            while pk <= N:
                entries.append((pk, lp))
                pk *= p
    return entries


def cdec_lseries_von_mangoldt(s: CDec, vm_entries) -> CDec:
    """Computes truncated L(Lambda, s) = sum_{n <= N} Lambda(n) n^{-s} in 65-digit arithmetic."""
    re_sum = Decimal(0)
    im_sum = Decimal(0)
    for n, lp in vm_entries:
        ln_n = Decimal(n).ln()
        mag = lp * (-s.re * ln_n).exp()
        ang = -s.im * ln_n
        re_sum += mag * lab.dec_cos(ang)
        im_sum += mag * lab.dec_sin(ang)
    return CDec(re_sum, im_sum)


# ==============================================================================
# MAIN VERIFICATION SUITE
# ==============================================================================


def main():
    t0 = time.time()
    print("=" * 98)
    print("7TH 65-DIGIT ARBITRARY-PRECISION LABORATORY (LEAN 4 MODULE #14 COMPANION)")
    print("Universal Hopfield-Boltzmann Solver, Adaptive Resolvent Preconditioner, & All-Primes Bridge")
    print("=" * 98)

    # --------------------------------------------------------------------------
    # PART 1 & 2A: ROUTE A (EXACT vs. PERTURBED WEIL MATRICES W^{(1.60)})
    # --------------------------------------------------------------------------
    print("\n[PART 1 & 2A] ROUTE A: 8x8 EVEN WEIL MATRIX W^{(1.60)} (EXACT eta=1.00 vs PERTURBED)")
    print("-" * 98)
    pp_dec = lab.sieve_prime_powers_dec(30)
    gl_x, gl_w = lab.dec_gl_nodes_weights(20)
    modes = [2 * k + 1 for k in range(8)]
    L_val = Decimal("1.60")
    W_exact, _ = lab.build_weil_matrix(L_val, modes, "even", pp_dec, gl_x, gl_w)
    W_arch, _ = lab.build_weil_matrix(L_val, modes, "even", [], gl_x, gl_w)
    W_prime = [[W_arch[i][j] - W_exact[i][j] for j in range(8)] for i in range(8)]

    def scaled_W(eta_str: str):
        eta = Decimal(eta_str)
        return [[W_arch[i][j] - eta * W_prime[i][j] for j in range(8)] for i in range(8)]

    cases_A = [
        ("EXACT PRIMES  (eta = 1.00)", scaled_W("1.00"), True),
        ("NO PRIMES     (eta = 0.00)", scaled_W("0.00"), False),
        ("PERTURBED +1% (eta = 1.01)", scaled_W("1.01"), False),
        ("PERTURBED -1% (eta = 0.99)", scaled_W("0.99"), False),
    ]

    for label, M, expect_psd in cases_A:
        ev, _ = lab.jacobi_dec_eig(M)
        lmin, lmax = ev[0], ev[-1]
        mu = lmax * Decimal("1.05")
        # Plain Universal Formula
        res_u = run_universal_solver_dec(M, mu, steps=800)
        assert res_u["monotone_ok"], f"Lyapunov descent violated on {label}"
        if expect_psd:
            assert lmin > 0, f"Expected PSD on {label}"
            assert res_u["L_final"] >= res_u["quartic_lower_L"] - Decimal("1e-50")
            assert res_u["quad_W"] > 0
        # Adaptive Resolvent-Universal Solver (delta > max(0, -lmin) ensures Q_res > 0 and monotone Lyapunov!)
        delta = Decimal("1.8") * abs(lmin)
        res_a = run_adaptive_resolvent_universal_dec(M, delta, steps=120)
        assert res_a["monotone_ok"], f"Adaptive Resolvent Lyapunov descent violated on {label}"
        if expect_psd:
            assert res_a["norm2"] < Decimal("1e-18"), f"Expected decay to 0 on {label}, got {res_a['norm2']}"
            assert res_a["uWu"] >= 0
        else:
            assert res_a["res_fp"] < Decimal("1e-12"), f"Expected fast fixed-point convergence on {label}, got {res_a['res_fp']}"
            assert res_a["uWu"] <= res_a["rhs_bound"] + Decimal("1e-45"), (
                f"Lean 4 Thm adaptiveResolventUniversal_neg_witness failed on {label}"
            )
            assert res_a["uWu"] < 0
        if expect_psd:
            print(
                f"  {label} | lmin={lmin:+.4e}, mu={mu:.4f}\n"
                f"    Plain Univ (800 it) : mono={res_u['monotone_ok']}, ||s||={res_u['norm2']:.4e}, "
                f"L={res_u['L_final']:+.4e}, s^T W s={res_u['quad_W']:+.4e}, fp_res={res_u['res_fp']:.2e}\n"
                f"    AdapRes    (120 it) : delta={delta:.4e}, mono={res_a['monotone_ok']}, ||s||={res_a['norm2']:.4e}, "
                f"fp_res={res_a['res_fp']:.2e}, u^T W u={res_a['uWu']:+.4e} (> 0, paramagnetic decay)"
            )
        else:
            print(
                f"  {label} | lmin={lmin:+.4e}, mu={mu:.4f}\n"
                f"    Plain Univ (800 it) : mono={res_u['monotone_ok']}, ||s||={res_u['norm2']:.4e}, "
                f"L={res_u['L_final']:+.4e}, s^T W s={res_u['quad_W']:+.4e}, fp_res={res_u['res_fp']:.2e}\n"
                f"    AdapRes    (120 it) : delta={delta:.4e}, mono={res_a['monotone_ok']}, ||s*||={res_a['norm2']:.4e}, "
                f"fp_res={res_a['res_fp']:.2e}, u^T W u={res_a['uWu']:+.4e} <= {res_a['rhs_bound']:+.4e}"
            )

    # --------------------------------------------------------------------------
    # PART 3: ROUTE B LIFTED 8x8 REAL SYMMETRIC PICK MATRIX ON REMOTE HEIGHTS
    # --------------------------------------------------------------------------
    print("\n[PART 3] ROUTE B: LIFTED 8x8 REAL SYMMETRIC PICK MATRIX (REMOTE sigma in {0.25, 0.50})")
    print("-" * 98)
    us, phis, wts = lab.build_phi_grid(Decimal("2.50"), 260)

    def eval_R_dec(gam_d: Decimal, sig_d: Decimal, t_d: Decimal) -> CDec:
        """
        Exact 65-digit evaluation of R_xi(z) = i * xi'(1/2 - i*z) / xi(1/2 - i*z) = -Xi'(z) / Xi(z),
        where Xi(z) = 2 * int_0^inf Phi_t(u) * cos(z u) du and
        -Xi'(z) = 2 * int_0^inf u * Phi_t(u) * sin(z u) du.
        """
        x0_r = x0_i = nx1_r = nx1_i = Decimal(0)
        for u, p, w in zip(us, phis, wts):
            pt = p * (t_d * u * u).exp() if t_d != 0 else p
            pw = Decimal(2) * pt * w
            ch, sh = lab.dec_cosh(sig_d * u), lab.dec_sinh(sig_d * u)
            cs, sn = lab.dec_cos(gam_d * u), lab.dec_sin(gam_d * u)
            # cos((gam + i*sig) u) = cos(gam u) cosh(sig u) - i sin(gam u) sinh(sig u)
            x0_r += pw * ch * cs
            x0_i += -pw * sh * sn
            # sin((gam + i*sig) u) = sin(gam u) cosh(sig u) + i cos(gam u) sinh(sig u)
            nx1_r += pw * u * ch * sn
            nx1_i += pw * u * sh * cs
        return CDec(nx1_r, nx1_i) / CDec(x0_r, x0_i)

    cases_B = [
        ("TRUE xi      (t =  0.000, remote sigma=0.25,0.50)", Decimal("0"), Decimal("48.62253"), True),
        ("POST-COLL.   (t = -0.475, remote sigma=0.25,0.50)", Decimal("-0.475"), Decimal("49.67815"), False),
    ]

    for label, t_d, center, expect_psd in cases_B:
        pts = [
            (center - Decimal("0.15"), Decimal("0.25")),
            (center, Decimal("0.25")),
            (center + Decimal("0.15"), Decimal("0.25")),
            (center, Decimal("0.50")),
        ]
        zs = [CDec(g, s) for g, s in pts]
        Rs = [eval_R_dec(g, s, t_d) for g, s in pts]
        n = 4
        P = [[(Rs[j] - Rs[k].conj()) / (zs[j] - zs[k].conj()) for k in range(n)] for j in range(n)]
        # Verify exact Hermitian lifting identity: v^H P v == v_tilde^T P_tilde v_tilde
        M = [[Decimal(0)] * (2 * n) for _ in range(2 * n)]
        for j in range(n):
            for k in range(n):
                M[j][k] = P[j][k].re
                M[n + j][n + k] = P[j][k].re
                M[j][n + k] = -P[j][k].im
                M[n + j][k] = P[j][k].im
        # Test lifting identity on a non-trivial complex vector v
        v_re = [Decimal("0.3"), Decimal("-0.7"), Decimal("0.5"), Decimal("-0.2")]
        v_im = [Decimal("-0.4"), Decimal("0.2"), Decimal("-0.8"), Decimal("0.6")]
        v_c = [CDec(v_re[j], v_im[j]) for j in range(n)]
        herm_quad = CDec(0, 0)
        for j in range(n):
            for k in range(n):
                herm_quad = herm_quad + v_c[j].conj() * P[j][k] * v_c[k]
        lift_quad = dec_quad(M, v_re + v_im)
        lift_err = abs(herm_quad.re - lift_quad) + abs(herm_quad.im)
        assert lift_err < Decimal("1e-55"), f"Lifting identity error too large: {lift_err}"

        ev, _ = lab.jacobi_dec_eig(M)
        lmin, lmax = ev[0], ev[-1]
        mu = lmax * Decimal("1.05")
        res_u = run_universal_solver_dec(M, mu, steps=2000)
        assert res_u["monotone_ok"], f"Lyapunov descent failed on Route B {label}"
        delta = Decimal("1.8") * abs(lmin)
        res_a = run_adaptive_resolvent_universal_dec(M, delta, steps=120)
        assert res_a["monotone_ok"], f"Adaptive Resolvent Lyapunov failed on Route B {label}"

        if expect_psd:
            assert lmin > 0
            assert res_u["L_final"] >= res_u["quartic_lower_L"] - Decimal("1e-50")
            assert res_u["quad_W"] > 0
            assert res_a["norm2"] < Decimal("1e-18"), f"Expected decay on {label}, got {res_a['norm2']}"
            assert res_a["uWu"] >= 0
            print(
                f"  {label} | lift_err={lift_err:.2e}, lmin={lmin:+.4e}, mu={mu:.2f}\n"
                f"    Plain Univ (2000 it): mono={res_u['monotone_ok']}, ||s||={res_u['norm2']:.4e}, "
                f"L={res_u['L_final']:+.4e}, fp_res={res_u['res_fp']:.2e}, s^T P s={res_u['quad_W']:+.4e} (> 0)\n"
                f"    AdapRes    (120 it) : delta={delta:.4e}, mono={res_a['monotone_ok']}, ||s||={res_a['norm2']:.4e}, "
                f"fp_res={res_a['res_fp']:.2e}, u^T P u={res_a['uWu']:+.4e} (> 0, paramagnetic decay)"
            )
        else:
            assert lmin < 0
            assert res_u["res_fp"] < Decimal("1e-10")
            assert res_u["quad_W"] <= res_u["quartic_upper_neg"] + Decimal("1e-45")
            assert res_u["quad_W"] < 0
            assert res_a["res_fp"] < Decimal("1e-20")
            assert res_a["uWu"] <= res_a["rhs_bound"] + Decimal("1e-45")
            assert res_a["uWu"] < 0
            print(
                f"  {label} | lift_err={lift_err:.2e}, lmin={lmin:+.4e}, mu={mu:.2f}\n"
                f"    Plain Univ (2000 it): mono={res_u['monotone_ok']}, ||s*||={res_u['norm2']:.4f}, "
                f"L={res_u['L_final']:+.4e}, fp_res={res_u['res_fp']:.2e}\n"
                f"                          s^T P s={res_u['quad_W']:+.4e} <= {res_u['quartic_upper_neg']:+.4e}\n"
                f"    AdapRes    (120 it) : delta={delta:.4e}, mono={res_a['monotone_ok']}, ||s*||={res_a['norm2']:.4f}, "
                f"fp_res={res_a['res_fp']:.2e}\n"
                f"                          u^T P u={res_a['uWu']:+.4e} <= {res_a['rhs_bound']:+.4e}"
            )

    # --------------------------------------------------------------------------
    # PART 4: EXACT ALL-PRIMES VON MANGOLDT RESOLVENT IDENTITY ON Im(z) > 1/2
    # --------------------------------------------------------------------------
    print("\n[PART 4] EXACT ALL-PRIMES VON MANGOLDT RESOLVENT IDENTITY (Im(z) > 1/2)")
    print("  R_xi(z) = i * (1/s + 1/(s-1) - (1/2) ln(pi) + (1/2) psi(s/2) - L(Lambda, s)),  s = 1/2 - i*z")
    print("-" * 98)
    vm_entries = sieve_von_mangoldt(8000)
    half_ln_pi = Decimal("0.5") * lab.DEC_PI.ln()
    test_points = [
        (Decimal("14.134725"), Decimal("3.5")),  # Re(s) = 4.0
        (Decimal("21.022040"), Decimal("4.5")),  # Re(s) = 5.0
        (Decimal("30.424876"), Decimal("5.5")),  # Re(s) = 6.0
    ]
    for gam_d, sig_d in test_points:
        # LHS directly from completed-zeta Phi(u) Fourier-Laplace representation
        lhs = eval_R_dec(gam_d, sig_d, Decimal(0))
        # RHS from Lean 4 Thm xiResolvent_eq_explicit_vonMangoldt_of_half_lt_im
        # s = 1/2 - i*(gam + i*sig) = (1/2 + sig) - i*gam
        s = CDec(Decimal("0.5") + sig_d, -gam_d)
        one = CDec(1, 0)
        pole_terms = (one / s) + (one / (s - one))
        half_s = CDec(Decimal("0.5") * s.re, Decimal("0.5") * s.im)
        psi_term = CDec(Decimal("0.5"), 0) * cdec_digamma(half_s)
        l_vm = cdec_lseries_von_mangoldt(s, vm_entries)
        rhs = CDec(0, 1) * (pole_terms - CDec(half_ln_pi, 0) + psi_term - l_vm)
        err = (lhs - rhs).abs()
        # Tail bound for sum_{n > 8000} Lambda(n) n^{-Re(s)} <= O(8000^{1 - Re(s)})
        tol = Decimal(8000) ** (Decimal(1) - s.re) * Decimal(10)
        assert err < tol, f"von Mangoldt resolvent mismatch at z={gam_d}+i*{sig_d}: err={err}"
        print(
            f"  z = {str(gam_d):9s} + {sig_d}i (Re(s)={s.re}): "
            f"Re(R)={lhs.re:+.12f}, Im(R)={lhs.im:+.12f} | |LHS - RHS| = {err:.3e} (< tail {tol:.1e})"
        )

    print("\n" + "=" * 98)
    print(f"ALL 65-DIGIT MODULE #14 ASSERTIONS PASSED (0 failures) in {time.time() - t0:.2f} s.")
    print("=" * 98)


if __name__ == "__main__":
    main()
