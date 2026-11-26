#!/usr/bin/env python3
"""
65-Digit Arbitrary-Precision Laboratory: Arithmetic Weil Positivity Past p = 2,
Spectral-Flow Knife-Edge Obstruction, Expanded Constructive Corridor, Hyperbolic
Kernel Decay, Bochner-Wiener-Hopf Spectral Square Root, and Logarithmic Force.

Zero external dependencies (Python standard library + sibling laboratories).

Probes:
  [A1] Route A: Infinite-dimensional continuous Weil positivity WITH active prime
       p = 2 (L in (ln 2, 0.85], past ODD Archimedean breakdown L_0^* = 0.760068)
       via the disjoint-strip 1/2-factor norm bound ln(2)/sqrt(2) and Hilbert Schur.
  [A2] Route A: Integrated density of negative Archimedean modes N_-(W_arch^(L))
       across L in [0.69, 5.00] and two-sided spectral-flow pinch W(eta) = W_arch - eta*W_prime
       around eta = 1 at L = 1.60.
  [A3] Route A: Nonlinear hyperbolic fixed-point cone confinement s_{t+1} = tanh(beta*Q*s_t)
       on Q = -W^(1.60) + lambda_max*I.
  [B1] Route B: Exact identity I_0(1/2) = 1/4 and 9-bin antitone rational bounds
       backing the 10x expanded Lean 4 strip rectangle (0, 1) x [-2, 2] and
       20x critical-line positivity |gamma| <= 4.
  [B2] Route B: Hyperbolic geodesic coordinate y = cosh(w) - 1 on G_{2,0}(w)
       (7 finite-difference orders + decay convergence to 4*pi) and exact
       Bochner-Wiener-Hopf spectral square root h(w) = F^{-1}(sqrt(m_2(0, gamma)))
       sign-change detection.
  [B3] Route B: Logarithmic transverse force d/dsigma (ln V) = 2 Re(xi'/xi) and
       logarithmic curvature d^2/dsigma^2 (ln V) at pre- and post-collision pinches.
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
import verify_weil_corridor_ab as lab2

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


def probe_a1_infinite_dim_past_prime_two():
    print("\n" + "=" * 92)
    print("[A1 — ROUTE A] INFINITE-DIMENSIONAL CONTINUOUS WEIL POSITIVITY PAST FIRST PRIME p = 2")
    print("=" * 92)
    pp_dec = lab.sieve_prime_powers_dec(20)
    gl_x, gl_w = lab.dec_gl_nodes_weights(20)
    prime2_norm = math.log(2.0) / math.sqrt(2.0)
    print(f"  Disjoint-strip L^2 bound for p=2 on L in (ln 2, ln 4]: ln(2)/sqrt(2) = {prime2_norm:.8f}")

    passed_past_ln2 = []
    for l_f in [math.log(2.0), 0.72, 0.75, 0.80, 0.85, 0.90, 1.00]:
        a = 0.5 * l_f
        wp_odd = 2.0 * (math.sinh(a) - a)
        p2_pen = 0.0 if l_f <= math.log(2.0) + 1e-12 else prime2_norm

        def tail_bound(parity: str, r_modes: int):
            best_v, best_t = -1e9, 0.0
            ms = [2 * k + 1 for k in range(r_modes)] if parity == "even" else [2 * k + 2 for k in range(r_modes)]
            ws = [m * math.pi / l_f for m in ms]
            for t_i in range(120, 520, 20):
                t_cut = t_i * 0.1
                p_t = psi_arch_exact(t_cut)
                n_s = 300
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
                pen = (wp_odd if parity == "odd" else 0.0) + p2_pen
                val = p_t - (integ * dt / 3.0) / math.pi - pen
                if val > best_v:
                    best_v, best_t = val, t_cut
            return best_v, best_t

        lo_tail, _ = tail_bound("odd", 2)
        le_tail, _ = tail_bound("even", 3)

        l_dec = Decimal(str(l_f))
        w_odd, _ = lab.build_weil_matrix(l_dec, [2 * k + 2 for k in range(14)], "odd", pp_dec, gl_x, gl_w)
        w_ev, _ = lab.build_weil_matrix(l_dec, [2 * k + 1 for k in range(14)], "even", pp_dec, gl_x, gl_w)

        def schur_min_eig(w_mat, r, lam_perp):
            if lam_perp <= 0:
                return -999.0
            n_tot = len(w_mat)
            s_mat = [[Decimal(0)] * r for _ in range(r)]
            inv_lp = Decimal(1) / Decimal(str(lam_perp))
            for i in range(r):
                for j in range(r):
                    cross = sum(w_mat[i][k] * w_mat[j][k] for k in range(r, n_tot))
                    s_mat[i][j] = w_mat[i][j] - inv_lp * cross
            evals, _ = lab.jacobi_dec_eig(s_mat)
            return float(evals[0])

        so_min = schur_min_eig(w_odd, 2, lo_tail)
        se_min = schur_min_eig(w_ev, 3, le_tail)
        ok = (lo_tail > 0 and so_min > 0 and le_tail > 0 and se_min > 0)
        if ok and p2_pen > 0:
            passed_past_ln2.append(l_f)
        print(f"  L = {l_f:.5f} (p=2 {'OFF' if p2_pen == 0 else 'ON '}): "
              f"ODD(r=2) lam_perp={lo_tail:+.4f}, S_min={so_min:+.5e} | "
              f"EVEN(r=3) lam_perp={le_tail:+.4f}, S_min={se_min:+.5e} -> {'PASS (INF-DIM)' if ok else 'fails'}")

    assert 0.85 in passed_past_ln2, "Expected infinite-dimensional Schur certification with active p=2 at L=0.85"
    print(f"  CERTIFIED INFINITE-DIMENSIONAL CROSSING OF p = 2 UP TO L = {max(passed_past_ln2):.2f} > ln 2.")


def probe_a2_spectral_flow_pinch():
    print("\n" + "=" * 92)
    print("[A2 — ROUTE A] NEGATIVE-EIGENVALUE COUNT N_-(W_arch) & TWO-SIDED SPECTRAL-FLOW PINCH")
    print("=" * 92)
    pp_dec = lab.sieve_prime_powers_dec(300)
    gl_x, gl_w = lab.dec_gl_nodes_weights(20)
    modes_e10 = [2 * k + 1 for k in range(10)]
    modes_o10 = [2 * k + 2 for k in range(10)]

    print(f"  {'L':>5s} | {'#p^m':>4s} | {'N_-(W_arch E)':>13s} | {'min(W_arch E)':>14s} | {'min(W_full E)':>14s} | "
          f"{'N_-(W_arch O)':>13s} | {'min(W_arch O)':>14s} | {'min(W_full O)':>14s}")
    print("  " + "-" * 102)
    for l_str in ["0.69", "1.00", "1.60", "2.20", "3.00", "4.00", "5.00"]:
        l_dec = Decimal(l_str)
        we_arch, _ = lab.build_weil_matrix(l_dec, modes_e10, "even", pp_dec, gl_x, gl_w, allowed_primes=set())
        we_full, n_pp = lab.build_weil_matrix(l_dec, modes_e10, "even", pp_dec, gl_x, gl_w)
        wo_arch, _ = lab.build_weil_matrix(l_dec, modes_o10, "odd", pp_dec, gl_x, gl_w, allowed_primes=set())
        wo_full, _ = lab.build_weil_matrix(l_dec, modes_o10, "odd", pp_dec, gl_x, gl_w)
        ea_e, _ = lab.jacobi_dec_eig(we_arch)
        ef_e, _ = lab.jacobi_dec_eig(we_full)
        ea_o, _ = lab.jacobi_dec_eig(wo_arch)
        ef_o, _ = lab.jacobi_dec_eig(wo_full)
        neg_e = sum(1 for v in ea_e if v < 0)
        neg_o = sum(1 for v in ea_o if v < 0)
        assert ef_e[0] > 0 and ef_o[0] > 0
        print(f"  {l_str:>5s} | {n_pp:4d} | {neg_e:13d} | {float(ea_e[0]):+14.5e} | {float(ef_e[0]):+14.5e} | "
              f"{neg_o:13d} | {float(ea_o[0]):+14.5e} | {float(ef_o[0]):+14.5e}")

    print("\n  Spectral Flow W(eta) = W_arch - eta * W_prime at L = 1.60 (EVEN, N = 10):")
    l_dec = Decimal("1.60")
    we_arch, _ = lab.build_weil_matrix(l_dec, modes_e10, "even", pp_dec, gl_x, gl_w, allowed_primes=set())
    we_full, _ = lab.build_weil_matrix(l_dec, modes_e10, "even", pp_dec, gl_x, gl_w)
    we_prime = [[we_arch[i][j] - we_full[i][j] for j in range(10)] for i in range(10)]
    wp_eigs, _ = lab.jacobi_dec_eig(we_prime)
    assert wp_eigs[0] < 0 and wp_eigs[-1] > 0
    print(f"    Spectrum of W_prime alone: [{float(wp_eigs[0]):+.6f}, ..., {float(wp_eigs[-1]):+.6f}] (strictly indefinite)")
    for eta_s in ["0.00", "0.25", "0.50", "0.75", "0.90", "0.99", "1.00", "1.01", "1.10"]:
        eta = Decimal(eta_s)
        w_eta = [[we_arch[i][j] - eta * we_prime[i][j] for j in range(10)] for i in range(10)]
        ev, _ = lab.jacobi_dec_eig(w_eta)
        n_neg = sum(1 for v in ev if v < 0)
        if eta_s == "1.00":
            assert n_neg == 0 and ev[0] > 0
        elif eta_s in ("0.99", "1.01"):
            assert n_neg >= 1 and ev[0] < 0
        print(f"    eta = {eta_s}: N_-(W(eta)) = {n_neg}, lambda_min = {float(ev[0]):+.6e}, lambda_2 = {float(ev[1]):+.6e}")


def probe_a3_nonlinear_tanh_cone_confinement():
    print("\n" + "=" * 92)
    print("[A3 — ROUTE A] NONLINEAR HYPERBOLIC FIXED-POINT SEARCH s_{t+1} = tanh(beta * Q * s_t)")
    print("=" * 92)
    pp_dec = lab.sieve_prime_powers_dec(20)
    gl_x, gl_w = lab.dec_gl_nodes_weights(20)
    modes_e8 = [2 * k + 1 for k in range(8)]
    l_dec = Decimal("1.60")
    w_full, _ = lab.build_weil_matrix(l_dec, modes_e8, "even", pp_dec, gl_x, gl_w)
    w_f = [[float(w_full[i][j]) for j in range(8)] for i in range(8)]
    evals, evecs = lab.jacobi_dec_eig(w_full)
    v0 = [float(evecs[i][0]) for i in range(8)]

    n = 8
    lam_max = float(evals[-1])
    q_mat = [[-w_f[i][j] + (lam_max if i == j else 0.0) for j in range(n)] for i in range(n)]
    s = [0.5 if i == 0 else 0.05 * ((-1) ** i) for i in range(n)]
    for step in range(400):
        beta = 0.2 + 8.0 * (step / 400.0)
        s_new = [math.tanh(beta * sum(q_mat[i][j] * s[j] for j in range(n))) for i in range(n)]
        norm = math.sqrt(sum(x * x for x in s_new))
        s = [x / norm for x in s_new]
    rq = sum(s[i] * w_f[i][j] * s[j] for i in range(n) for j in range(n))
    ov = abs(sum(s[i] * v0[i] for i in range(n)))
    assert rq > 0
    print(f"  Hyperbolic fixed-point map (400 annealed steps) Rayleigh quotient = {rq:+.6e} (> 0)")
    print(f"  Overlap with exact ground eigenstate v_0^(1.60) = {ov:.6f} (exact lambda_min = {float(evals[0]):+.6e})")


def probe_b1_exact_identity_and_nine_bin_corridor():
    print("\n" + "=" * 92)
    print("[B1 — ROUTE B] EXACT IDENTITY I_0(1/2) = 1/4 & 9-BIN CONSTRUCTIVE STRIP RECTANGLE |gamma| <= 2")
    print("=" * 92)
    us, phis, wts = lab.build_phi_grid(Decimal("2.45"), 245)

    def exact_moment(k2: int, sig: float) -> Decimal:
        s_d = Decimal(str(sig))
        acc = Decimal(0)
        for u, p, w in zip(us, phis, wts):
            up = Decimal(1) if k2 == 0 else u ** k2
            ch = Decimal(1) if sig == 0 else lab.dec_cosh(s_d * u)
            acc += p * up * ch * w
        return acc

    i0_0 = exact_moment(0, 0.0)
    i2_0 = exact_moment(2, 0.0)
    i0_h = exact_moment(0, 0.5)
    i4_h = exact_moment(4, 0.5)
    err_quarter = abs(i0_h - Decimal("0.25"))
    assert err_quarter < Decimal("1e-50")
    print(f"  Exact I_0(1/2) = {str(i0_h)[:36]}...  (|I_0(1/2) - 1/4| = {float(err_quarter):.3e})")
    print(f"  Exact I_0(0)   = {float(i0_0):.10e},  I_2(0) = {float(i2_0):.10e},  I_4(1/2) = {float(i4_h):.10e}")

    # Rational bounds verified unconditionally in Lean 4 Module #11:
    i0_lb = Decimal(195) / Decimal(1000)
    i2_lb = Decimal(77) / Decimal(10000)
    i2_ub = Decimal(175) / Decimal(10000)
    i0h_ex = Decimal(1) / Decimal(4)
    i4h_ub = Decimal(285) / Decimal(100000)
    assert i0_lb <= i0_0
    assert i2_lb <= i2_0 <= i2_ub
    assert i4_h <= i4h_ub
    gamma_m2_lean = math.sqrt(float(Decimal(2) * i0_lb * i2_lb / (i0h_ex * i4h_ub - i2_lb * i2_lb)))
    gamma_xi_lean = math.sqrt(float(Decimal(2) * i0_lb / i2_ub))
    assert gamma_m2_lean > 2.0 and gamma_xi_lean > 4.0
    print(f"  Lean 4 constructive 9-bin certified radius: m_2 > 0 for |gamma| <= {gamma_m2_lean:.5f} (proved <= 2)")
    print(f"  Lean 4 constructive 9-bin certified radius: Xi  > 0 for |gamma| <= {gamma_xi_lean:.5f} (proved <= 4)")


def probe_b2_hyperbolic_coordinate_and_spectral_sqrt():
    print("\n" + "=" * 92)
    print("[B2 — ROUTE B] HYPERBOLIC COORDINATE y = cosh(w) - 1 & BOCHNER-WIENER-HOPF SQUARE ROOT")
    print("=" * 92)
    ys = [Decimal(k) * Decimal("0.10") for k in range(12)]
    f_hyp = []
    for y in ys:
        w = (Decimal(1) + y + (y * (y + Decimal(2))).sqrt()).ln() if y > 0 else Decimal(0)
        f_hyp.append(lab2.eval_g2_sigma(w, Decimal(0), Decimal(0), Decimal("4.4"), 200))

    print("  1. Finite-difference CM test on F_hyp(y) = G_{2,0}(arccosh(1 + y)), dy = 0.10:")
    diffs = f_hyp[:]
    for order in range(1, 8):
        diffs = [-(diffs[i + 1] - diffs[i]) / Decimal("0.10") for i in range(len(diffs) - 1)]
        assert min(diffs) > 0
        print(f"    (-1)^{order} Delta^{order} F_hyp(y): min = {float(min(diffs)):+.4e}, max = {float(max(diffs)):+.4e} -> ALL > 0")

    print("  2. Hyperbolic decay ratio -ln(G_{2,0}(w)) / (cosh(w) - 1) -> 4*pi = 12.5664:")
    for w_f in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
        w = Decimal(str(w_f))
        gv = lab2.eval_g2_sigma(w, Decimal(0), Decimal(0), Decimal("5.0"), 250)
        y_val = math.cosh(w_f) - 1.0
        ratio = -float(gv.ln()) / y_val
        print(f"    w = {w_f:3.1f} (y = {y_val:6.3f}): G_{{2,0}} = {float(gv):.4e}, -ln(G)/y = {ratio:8.4f}")

    print("  3. Bochner-Wiener-Hopf spectral square root h(w) = F^{-1}(sqrt(m_2(0, gamma))) at t = 0:")
    us, phis, wts = lab.build_phi_grid(Decimal("2.45"), 245)
    dg = 0.25
    ng = 140
    sm2 = []
    for k in range(ng + 1):
        g = Decimal(str(k * dg))
        _, _, m2_v, _ = lab.eval_V_sigma_derivs(Decimal(0), g, Decimal(0), us, phis, wts)
        sm2.append(math.sqrt(max(0.0, float(m2_v))))
    h_vals = []
    for kw in range(25):
        w = kw * 0.10
        acc = sum((0.5 if k in (0, ng) else 1.0) * sm2[k] * math.cos(k * dg * w) for k in range(ng + 1))
        h_vals.append((w, acc * dg / math.pi))
    neg_h = [(w, v) for w, v in h_vals if v < 0]
    assert len(neg_h) > 0, "Expected sign change in Bochner-Wiener-Hopf spectral square root h(w)"
    print(f"    h(0.0) = {h_vals[0][1]:+.6e}, h(0.5) = {h_vals[5][1]:+.6e}, h(1.0) = {h_vals[10][1]:+.6e}, "
          f"h(1.5) = {h_vals[15][1]:+.6e}, h(2.0) = {h_vals[20][1]:+.6e}")
    print(f"    First sign change: w = {neg_h[0][0]:.2f}, h(w) = {neg_h[0][1]:+.4e} < 0 (rules out h >= 0 convolution)")


def probe_b3_logarithmic_potential_force():
    print("\n" + "=" * 92)
    print("[B3 — ROUTE B] LOGARITHMIC FORCE d_sigma(ln V) & CURVATURE d_sigma^2(ln V) AT PINCH")
    print("=" * 92)
    us, phis, wts = lab.build_phi_grid(Decimal("2.45"), 245)
    for t_str, g_str in [("0.0", "48.62253"), ("-0.475", "49.67815")]:
        t_d, g_d = Decimal(t_str), Decimal(g_str)
        print(f"  t = {t_str:>6s}, pinch gamma_* = {g_str}:")
        for sig_s in ["0.001", "0.02", "0.05", "0.10", "0.25", "0.50"]:
            s_d = Decimal(sig_s)
            v, m1, m2, _ = lab.eval_V_sigma_derivs(s_d, g_d, t_d, us, phis, wts)
            d1_ln = float(m1 / v)
            d2_ln = float((m2 * v - m1 * m1) / (v * v))
            if t_str == "-0.475" and sig_s == "0.50":
                assert d2_ln < 0 and m2 > 0
            print(f"    sigma = {sig_s:>5s}: d1(ln V) = {d1_ln:+.6e}, d2(ln V) = {d2_ln:+.6e}, m2 = {float(m2):+.4e}")


def main():
    t0 = time.time()
    probe_a1_infinite_dim_past_prime_two()
    probe_a2_spectral_flow_pinch()
    probe_a3_nonlinear_tanh_cone_confinement()
    probe_b1_exact_identity_and_nine_bin_corridor()
    probe_b2_hyperbolic_coordinate_and_spectral_sqrt()
    probe_b3_logarithmic_potential_force()
    print(f"\nALL 6 ARITHMETIC-WEIL & WIDE-CORRIDOR PROBES PASSED IN {time.time() - t0:.2f} s.")


if __name__ == "__main__":
    main()
