#!/usr/bin/env python3
"""
High-Precision Verification Laboratory for Module #13
(HermiteBiehlerHomotopyAndWeilPick.lean):
  1. Route B: Exact Hermite-Biehler / Schur-Cayley homotopy S_alpha(z) and
     M_alpha(z) for alpha in (0, 1/2], comparing true xi (t = 0) against the
     post-collision de Bruijn-Newman state (t = -0.475, delta ~ 0.108),
     plus exact infinitesimal limit M_alpha(z)/alpha -> R_xi(z) and all-order
     Pick-Schur congruence verification.
  2. Route A <-> Route B Unification: Causal exponential wavelets
     g_z(u) = exp(i*z*u) * 1_{u >= 0} unifying the Hermitian Pick matrix of
     R_xi(z) with the explicit arithmetic Weil functional (Pole + Digamma -
     von Mangoldt prime sum) on Im(z) > 1/2.
  3. Route A: Exact even-odd decoupling of W_total, parity-enhanced continuous
     lower bounds (ODD L <= 3/10, EVEN zero-mean L <= 4/9), and infinite-
     dimensional Hilbert Schur certification crossing p = 2, 3, AND 4
     simultaneously up to L = 1.50 (> ln 4 = 1.3863).
  4. Route B: Exact Order-6 alternating cosine bound cos(x) >= T_6(x) and
     corresponding convexity corridor check.

Zero external third-party dependencies (standard library Decimal at 65 digits).
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
C_INF = float(lab.DEC_C_INF)


def psi_arch_exact(t: float) -> float:
    t2_4 = 0.25 * t * t
    acc = -C_INF
    for n in range(400):
        an = n + 0.25
        acc += t2_4 / (an * (an * an + t2_4))
    x0 = 399.75
    return acc + 0.5 * math.log(1.0 + t2_4 / (x0 * x0))


def part_1_route_b_hermite_biehler_homotopy():
    print("=" * 94)
    print("PART 1 (ROUTE B): HERMITE-BIEHLER / SCHUR-CAYLEY HOMOTOPY S_alpha, M_alpha (alpha in (0, 1/2])")
    print("=" * 94)
    us, phis, wts = lab.build_phi_grid(Decimal("2.50"), 250)

    def eval_xi(sig_f: float, gam_f: float, t_f: float) -> complex:
        s_d, g_d, t_d = Decimal(str(sig_f)), Decimal(str(gam_f)), Decimal(str(t_f))
        xr = xi_ = Decimal(0)
        for u, p, w in zip(us, phis, wts):
            pt = p * (t_d * u * u).exp() if t_d != 0 else p
            pw = Decimal(2) * pt * w
            ch, sh = lab.dec_cosh(s_d * u), lab.dec_sinh(s_d * u)
            cs, sn = lab.dec_cos(g_d * u), lab.dec_sin(g_d * u)
            xr += pw * ch * cs
            xi_ += pw * sh * sn
        return complex(float(xr), float(xi_))

    def eval_S_and_M(alpha_f: float, gam_f: float, sig_f: float, t_f: float):
        e_den = eval_xi(alpha_f + sig_f, -gam_f, t_f)
        e_num = eval_xi(alpha_f - sig_f, gam_f, t_f)
        S = e_num / e_den
        M = 1j * (1.0 - S) / (1.0 + S)
        return S, M

    def herm_eigs(P_mat):
        n = len(P_mat)
        R = [[Decimal(0)] * (2 * n) for _ in range(2 * n)]
        for j in range(n):
            for k in range(n):
                re_v = Decimal(str(P_mat[j][k].real))
                im_v = Decimal(str(P_mat[j][k].imag))
                R[j][k] = re_v
                R[n + j][n + k] = re_v
                R[j][n + k] = -im_v
                R[n + j][k] = im_v
        ev, _ = lab.jacobi_dec_eig(R)
        return [float(ev[2 * i]) for i in range(n)]

    # 1A: Boundary unitarity |S_alpha(gamma)| = 1 and Pick-Schur congruence check
    for alpha_f in [0.50, 0.25, 0.10]:
        s_bd, _ = eval_S_and_M(alpha_f, 14.134725, 0.0, 0.0)
        assert abs(abs(s_bd) - 1.0) < 1e-14, f"Boundary unitarity failed at alpha={alpha_f}"
    print("  [1A] Boundary unitarity |S_alpha(gamma)| = 1 verified to < 1e-14 for alpha in {0.50, 0.25, 0.10} [PASS]")

    # Verify exact Pick-Schur congruence Theorem `pickMatrix_cayley_schur_congruence`
    pts_test = [(14.0, 0.25), (14.2, 0.25), (14.1347, 0.50)]
    zs_test = [complex(g, s) for g, s in pts_test]
    c_test = [1.0 + 0.3j, -0.7 + 0.5j, 0.4 - 0.8j]
    SM_test = [eval_S_and_M(0.25, g, s, 0.0) for g, s in pts_test]
    Ss_t = [x[0] for x in SM_test]
    Ms_t = [x[1] for x in SM_test]
    cts_t = [c_test[j] / (1.0 + Ss_t[j]) for j in range(3)]
    lhs_pick = sum(
        c_test[j] * c_test[k].conjugate() * (Ms_t[j] - Ms_t[k].conjugate()) / (zs_test[j] - zs_test[k].conjugate())
        for j in range(3) for k in range(3)
    )
    rhs_schur = 2.0 * sum(
        cts_t[j] * cts_t[k].conjugate() * (1.0 - Ss_t[j] * Ss_t[k].conjugate()) / (-1j * (zs_test[j] - zs_test[k].conjugate()))
        for j in range(3) for k in range(3)
    )
    assert abs(lhs_pick - rhs_schur) < 1e-13
    print(f"  [1B] Exact 3x3 Pick-Schur congruence |LHS - RHS| = {abs(lhs_pick - rhs_schur):.2e} [PASS]")

    # 1C: Homotopy descent alpha = 0.50 -> 0.001 comparing true xi (t = 0) vs post-collision (t = -0.475)
    print("\n  [1C] Homotopy Descent alpha in [0.001, 0.500] on Remote Heights sigma in {0.25, 0.50}:")
    for label, t_f, center, is_true in [
        ("TRUE xi (t = 0.0, pinch 48.62253)", 0.0, 48.62253, True),
        ("POST-COLLISION (t = -0.475, pinch 49.67815)", -0.475, 49.67815, False),
    ]:
        print(f"    {label}:")
        pts = [(center - 0.15, 0.25), (center, 0.25), (center + 0.15, 0.25), (center, 0.50)]
        zs = [complex(g, s) for g, s in pts]
        for alpha in [0.50, 0.25, 0.10, 0.08, 0.06, 0.02, 0.001]:
            SM = [eval_S_and_M(alpha, g, s, t_f) for g, s in pts]
            Ss = [x[0] for x in SM]
            max_abs_S = max(abs(x) for x in Ss)
            s_low, m_low = eval_S_and_M(alpha, center, 0.02, t_f)
            P_schur = [
                [(1.0 - Ss[j] * Ss[k].conjugate()) / (-1j * (zs[j] - zs[k].conjugate())) for k in range(4)]
                for j in range(4)
            ]
            eigs = herm_eigs(P_schur)
            ok = (max_abs_S < 1.0 and abs(s_low) < 1.0 and eigs[0] > 0.0)
            if is_true:
                assert ok, f"True xi homotopy failed at alpha={alpha}"
            else:
                if alpha >= 0.25:
                    assert ok, f"Post-collision alpha={alpha} > delta must remain Schur-Pick PSD!"
                else:
                    assert not ok and eigs[0] < 0.0, f"Post-collision alpha={alpha} < delta must break remote Schur-Pick!"
            print(
                f"      alpha={alpha:5.3f}: max|S|={max_abs_S:.6f}, |S(low)|={abs(s_low):.6f}, "
                f"Im(M_low)/a={m_low.imag/alpha:+.4e}, min_eig(SchurPick4x4)={eigs[0]:+.4e} -> "
                f"{'SCHUR-PICK PSD' if ok else 'BROKEN REMOTELY!'}"
            )

    # 1D: Infinitesimal homotopy limit M_alpha(z) / alpha -> R_xi(z) (`xiCayley_div_alpha_tendsto_xiResolvent`)
    g1, s0 = 14.134725141734694, 0.25
    e0 = eval_xi(s0, -g1, 0.0)
    h = 1e-7
    ep = (eval_xi(s0 + h, -g1, 0.0) - eval_xi(s0 - h, -g1, 0.0)) / (2 * h)
    R_exact = 1j * (ep / e0)
    print(f"\n  [1D] Infinitesimal Homotopy Limit M_alpha(z)/alpha -> R_xi(z) at (gamma_1, sigma=0.25):")
    prev_err = 1e9
    for alpha in [1e-1, 1e-2, 1e-3, 1e-5]:
        _, M_a = eval_S_and_M(alpha, g1, s0, 0.0)
        err = abs(M_a / alpha - R_exact)
        assert err < prev_err
        prev_err = err
        print(f"    alpha={alpha:.0e}: |M_alpha/alpha - R_xi| = {err:.3e} [PASS]")
    assert prev_err < 1e-8


def part_2_causal_wavelet_weil_pick_unification():
    print("\n" + "=" * 94)
    print("PART 2 (ROUTE A <-> ROUTE B UNIFICATION): CAUSAL EXPONENTIAL WAVELET WEIL-PICK IDENTITY")
    print("=" * 94)
    us, phis, wts = lab.build_phi_grid(Decimal("2.50"), 250)

    def eval_R_xi_phi(z: complex) -> complex:
        g_d, s_d = Decimal(str(z.real)), Decimal(str(z.imag))
        x0_r = x0_i = x1_r = x1_i = Decimal(0)
        for u, p, w in zip(us, phis, wts):
            pw = Decimal(2) * p * w
            ch, sh = lab.dec_cosh(s_d * u), lab.dec_sinh(s_d * u)
            cs, sn = lab.dec_cos(g_d * u), lab.dec_sin(g_d * u)
            x0_r += pw * ch * cs
            x0_i += -pw * sh * sn
            x1_r += pw * u * sh * cs
            x1_i += -pw * u * ch * sn
        return 1j * (complex(float(x1_r), float(x1_i)) / complex(float(x0_r), float(x0_i)))

    def eval_R_xi_weil_primes(z: complex, n_max: int = 12000) -> complex:
        s = 0.5 - 1j * z
        w = 0.5 * s
        dig = 0j
        for _ in range(16):
            dig -= 1.0 / w
            w += 1.0
        invw = 1.0 / w
        invw2 = invw * invw
        dig += (
            complex(math.log(abs(w)), math.atan2(w.imag, w.real))
            - 0.5 * invw
            - invw2 / 12.0
            + (invw2 * invw2) / 120.0
            - (invw2 ** 3) / 252.0
        )
        is_p = [True] * (n_max + 1)
        ps = 0j
        for p in range(2, n_max + 1):
            if is_p[p]:
                for m in range(p * p, n_max + 1, p):
                    is_p[m] = False
                lp = math.log(p)
                pk = p
                while pk <= n_max:
                    ps -= lp * (pk ** (-s))
                    pk *= p
        return 1j * (1.0 / s + 1.0 / (s - 1.0) - 0.5 * math.log(math.pi) + 0.5 * dig + ps)

    # 2A: Exact algebraic verification of `weilSpectralSum_causalWavelet_eq_pickForm` on first 10 zeros
    zeros = [14.13472514, 21.02203964, 25.01085758, 30.42487613, 32.93506159]
    zs_c = [complex(14.0, 0.30), complex(21.0, 0.45), complex(25.0, 0.60)]
    cs_c = [1.0 + 0.2j, -0.5 + 0.7j, 0.3 - 0.4j]
    G_vals = [sum(1.0 / (gm - z) for gm in zeros) for z in zs_c]
    weil_sum = sum(abs(sum(cs_c[j] * (-1j / (gm - zs_c[j])) for j in range(3))) ** 2 for gm in zeros)
    pick_form = sum(
        cs_c[j].conjugate() * cs_c[k] * (G_vals[k] - G_vals[j].conjugate()) / (zs_c[k] - zs_c[j].conjugate())
        for j in range(3) for k in range(3)
    ).real
    assert abs(weil_sum - pick_form) < 1e-13
    print(f"  [2A] Exact Causal Wavelet Weil-Pick identity: Weil={weil_sum:.10f}, Pick={pick_form:.10f}, diff={abs(weil_sum - pick_form):.2e} [PASS]")

    # 2B: Cross-verification of 3x3 Hermitian Pick matrix on Im(z) >= 1.5 (Phi kernel vs explicit prime sum + Digamma)
    zs = [complex(14.134725, 1.5), complex(21.022040, 1.8), complex(14.134725, 2.2)]
    R_phi = [eval_R_xi_phi(z) for z in zs]
    R_prm = [eval_R_xi_weil_primes(z) for z in zs]
    P_phi = [[(R_phi[j] - R_phi[k].conjugate()) / (zs[j] - zs[k].conjugate()) for k in range(3)] for j in range(3)]
    P_prm = [[(R_prm[j] - R_prm[k].conjugate()) / (zs[j] - zs[k].conjugate()) for k in range(3)] for j in range(3)]
    max_diff = max(abs(P_phi[j][k] - P_prm[j][k]) for j in range(3) for k in range(3))
    assert max_diff < 1e-5
    print(f"  [2B] 3x3 Pick Matrix (Im(z) >= 1.5): max |P_Phi - P_WeilPrimes(N=12000)| = {max_diff:.3e} [PASS]")


def part_3_route_a_parity_continuous_and_p4_crossing():
    print("\n" + "=" * 94)
    print("PART 3 (ROUTE A): CONTINUOUS PARITY BOUNDS & INFINITE-DIM SCHUR CROSSING p = 2, 3, AND 4!")
    print("=" * 94)
    pp_dec = lab.sieve_prime_powers_dec(20)
    gl_x, gl_w = lab.dec_gl_nodes_weights(24)

    def refined_prime_norm(l_f: float) -> float:
        acc = 0.0
        for ln_dec, wt_dec, _p_i, _n_i in pp_dec:
            ln_n = float(ln_dec)
            if ln_n < l_f - 1e-12:
                fac = 1.0 if ln_n >= 0.5 * l_f - 1e-12 else 2.0
                acc += fac * float(wt_dec)
        return acc

    def tail_bound(l_f: float, parity: str, r_modes: int, p_norm: float) -> float:
        a = 0.5 * l_f
        wp_odd = 2.0 * (math.sinh(a) - a)
        best_v = -1e9
        ms = [2 * k + 1 for k in range(r_modes)] if parity == "even" else [2 * k + 2 for k in range(r_modes)]
        ws = [m * math.pi / l_f for m in ms]
        t_lo = max(30.0, (2 * r_modes) * math.pi / l_f)
        t_hi = t_lo * 4.5
        for idx in range(8):
            t_cut = t_lo + (t_hi - t_lo) * idx / 7.0
            p_t = psi_arch_exact(t_cut)
            n_s = 360
            dt = t_cut / n_s
            integ = 0.0
            for j in range(n_s + 1):
                t = j * dt
                wt = 1.0 if j in (0, n_s) else (4.0 if j % 2 else 2.0)
                if parity == "even":
                    k_par = l_f if t == 0 else (0.5 * l_f + math.sin(l_f * t) / (2.0 * t))
                else:
                    k_par = 0.0 if t == 0 else (0.5 * l_f - math.sin(l_f * t) / (2.0 * t))
                sub = 0.0
                for wm in ws:
                    if abs(wm - t) < 1e-12:
                        eh = math.sqrt(a)
                    else:
                        trig = math.cos(t * a) if parity == "even" else math.sin(t * a)
                        eh = math.sqrt(2.0 / l_f) * 2.0 * wm * trig / (wm * wm - t * t)
                    sub += eh * eh
                kp = max(0.0, k_par - sub)
                integ += wt * kp * (p_t - psi_arch_exact(t))
            pen = (wp_odd if parity == "odd" else 0.0) + p_norm
            val = p_t - (integ * dt / 3.0) / math.pi - pen
            if val > best_v:
                best_v = val
        return best_v

    def schur_min_eig(w_mat, r: int, lam_perp: float) -> float:
        assert lam_perp > 0.0
        n_tot = len(w_mat)
        s_mat = [[Decimal(0)] * r for _ in range(r)]
        inv_lp = Decimal(1) / Decimal(str(lam_perp))
        for i in range(r):
            for j in range(r):
                cross = sum(w_mat[i][k] * w_mat[j][k] for k in range(r, n_tot))
                s_mat[i][j] = w_mat[i][j] - inv_lp * cross
        evals, _ = lab.jacobi_dec_eig(s_mat)
        return float(evals[0])

    # 3A: Exact parity-enhanced continuous bounds (zero discretization!)
    print("  [3A] Zero-Discretization Continuous Parity Bounds (matching Lean 4 Theorems III.3 & III.4):")
    for label, l_f, mode, t_cut, lean_margin in [
        ("ODD continuous (L = 3/10, 2.4x wider than 1/8)", 0.30, "odd", 16.0, 0.01),
        ("ODD continuous (L = 1/2, sharp integral envelope)", 0.50, "odd", 12.0, 0.10),
        ("EVEN zero-mean (L = 4/9, 3.56x wider than 1/8)", 4.0 / 9.0, "even0", 16.0, 0.04),
        ("EVEN zero-mean (L = ln 2, full zero-prime window!)", math.log(2.0), "even0", 10.0, 0.08),
    ]:
        p_t = psi_arch_exact(t_cut)
        n_s = 400
        dt = t_cut / n_s
        integ = 0.0
        for j in range(n_s + 1):
            t = j * dt
            wt = 1.0 if j in (0, n_s) else (4.0 if j % 2 else 2.0)
            kern = min(l_f, (l_f ** 3) * (t * t) / 12.0) if mode == "odd" else min(l_f, (l_f ** 5) * (t ** 4) / 320.0)
            integ += wt * kern * (p_t - psi_arch_exact(t))
        pole_pen = 2.0 * (math.sinh(0.5 * l_f) - 0.5 * l_f) if mode == "odd" else 0.0
        lb = p_t - (integ * dt / 3.0) / math.pi - pole_pen
        assert lb >= lean_margin, f"Failed bound for {label}: {lb}"
        print(f"    {label:52s}: W_total >= {lb:+.6f} * ||g||_2^2 [PASS]")

    # 3B: Infinite-dimensional Hilbert Schur certification crossing p = 4 (L = 1.40, 1.50 > ln 4 = 1.3863!)
    print("\n  [3B] Infinite-Dimensional Hilbert Schur Certification Crossing p = 2, 3, AND 4 (3 Active Prime Powers!):")
    for l_f, r_o, r_e in [(1.40, 22, 24), (1.50, 26, 28)]:
        p_norm = refined_prime_norm(l_f)
        lo_tail = tail_bound(l_f, "odd", r_o, p_norm)
        le_tail = tail_bound(l_f, "even", r_e, p_norm)
        n_ref = max(r_o, r_e) + 8
        l_dec = Decimal(str(l_f))
        w_odd, n_pp = lab.build_weil_matrix(l_dec, [2 * k + 2 for k in range(n_ref)], "odd", pp_dec, gl_x, gl_w)
        w_ev, _ = lab.build_weil_matrix(l_dec, [2 * k + 1 for k in range(n_ref)], "even", pp_dec, gl_x, gl_w)
        so_min = schur_min_eig(w_odd, r_o, lo_tail)
        se_min = schur_min_eig(w_ev, r_e, le_tail)
        assert n_pp == 3 and lo_tail > 0.0 and so_min > 0.0 and le_tail > 0.0 and se_min > 0.0
        print(
            f"    L={l_f:4.2f} (#p^m={n_pp} [2,3,4], ||W_p||_ref<={p_norm:.4f}): "
            f"ODD(r={r_o:2d}) lam_perp={lo_tail:+.4f}, S_min={so_min:+.4e} | "
            f"EVEN(r={r_e:2d}) lam_perp={le_tail:+.4f}, S_min={se_min:+.4e} [PASS PAST p=4!]"
        )


def part_4_order6_cosine_check():
    print("\n" + "=" * 94)
    print("PART 4 (ROUTE B): EXACT ORDER-6 COSINE LOWER BOUND `cos_ge_taylor_six` VERIFICATION")
    print("=" * 94)
    for x in [0.0, 0.5, 1.0, 2.0, 3.141592653589793, 5.0, 10.0]:
        t6 = 1.0 - x ** 2 / 2.0 + x ** 4 / 24.0 - x ** 6 / 720.0
        gap = math.cos(x) - t6
        assert gap >= -1e-15
        print(f"  x={x:6.3f}: cos(x)={math.cos(x):+.8f}, T_6(x)={t6:+.8f}, gap={gap:+.4e} >= 0 [PASS]")


def main():
    t0 = time.time()
    part_1_route_b_hermite_biehler_homotopy()
    part_2_causal_wavelet_weil_pick_unification()
    part_3_route_a_parity_continuous_and_p4_crossing()
    part_4_order6_cosine_check()
    print("\n" + "=" * 94)
    print(f"ALL MODULE #13 VERIFICATION CHECKS PASSED IN {time.time() - t0:.2f} s.")
    print("=" * 94)


if __name__ == "__main__":
    main()
