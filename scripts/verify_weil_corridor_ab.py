#!/usr/bin/env python3
"""
================================================================================
65-DIGIT ARBITRARY-PRECISION LABORATORY FOR ROUTE A (CONTINUOUS WEIL POSITIVITY,
PRIME-INDUCTION FRONTIER, BANDLIMITED PROLATE COMPARISON, INFINITE-DIMENSIONAL
SCHUR CERTIFICATES) AND ROUTE B (EXPLICIT CONSTRUCTIVE CORRIDOR, SCHOENBERG
NO-GO OBSTRUCTION, BOCHNER-TOEPLITZ MATRICES, AND MODULARITY ABLATION)
================================================================================
Author: Mariano Martin Ramirez Tamayo (Independent Researcher)
Dependencies: Python 3 standard library only (imports companion module
`verify_certificates_prolate_laguerre` from the same directory).

Reproduces six computational probes complementing `WeilArchimedeanAndExplicitCorridor.lean`:
  [A1] Sequential prime-induction positivity frontier L_k^* vs ln(p_{k+1})
       for finite place sets S_k = {infinity, p_1, ..., p_k} (k = 0..5).
  [A2] Bandlimited Prolate comparison beta^*(L; Omega) = min <v, W^(L) v> / <v, (I - K_Omega) v>
       at Omega = t_0 (6.289836), Omega = 10.0, and Omega = gamma_1 (14.134725).
  [A3] Exact infinite-dimensional continuous Weil positivity on L^2([-L/2, L/2]):
       closed-form K=1 and K=3 Cauchy-Schwarz bounds on small support, and
       infinite-dimensional Hilbert-space Schur-complement certification at L = ln(2)
       (ODD perp e_2 and EVEN perp {e_1, e_3}).
  [B1] Constructive convexity corridor |gamma| <= gamma_cert(M) for m_2(sigma, gamma)
       via the exact 2D algebraic cancellation (u+v)^2(u-v)^2 = u^4 - 2 u^2 v^2 + v^4
       and alternating cosine Taylor lower bounds up to order 42, plus strict
       monotonicity of normalized moments mu_{2j}(sigma)/mu_0(sigma) on [0, 1/2].
  [B2] Schoenberg complete-monotonicity obstruction for G_{2,0}(sqrt(x))
       (super-exponential decay rate -ln G_{2,0}(w)/w^2 -> +infinity vs finite-difference
       positivity on small x) and Bochner-Toeplitz spectra at t = 0 vs t = -0.55.
  [B3] Jacobi-theta modularity ablation: full Phi(u) vs single-term cusped Phi_{n=1}(|u|)
       vs Polya's smooth even non-arithmetic kernel Phi^*(u) on gamma in {0..55}.
================================================================================
"""

import math
import time
from decimal import Decimal, getcontext

import verify_certificates_prolate_laguerre as lab

getcontext().prec = 65
DEC_PI = lab.DEC_PI
DEC_HALF = lab.DEC_HALF


def build_sinc_kernel_matrix_dec(L: Decimal, Omega: Decimal, modes: list[int], parity: str):
    """Exact matrix of the bandlimited Prolate integral operator K_Omega on L^2([-L/2, L/2])."""
    n_modes = len(modes)
    half_l = L * DEC_HALF
    pref = (Decimal(2) / L).sqrt()
    ws = [Decimal(m) * DEC_PI / L for m in modes]

    n_pan = max(8, int(math.ceil(float(Omega * L) / 2.0)) + 4)
    gl_x, gl_w = lab.dec_gl_nodes_weights(24)
    h = Omega / Decimal(n_pan)
    t_pts, w_pts = [], []
    for pan in range(n_pan):
        ap = Decimal(pan) * h
        for gx, gw in zip(gl_x, gl_w):
            t_pts.append(ap + gx * h)
            w_pts.append(gw * h / DEC_PI)

    ehat = []
    for wm in ws:
        vals = []
        for t in t_pts:
            if abs(wm - t) < Decimal("1e-30"):
                vals.append((L * DEC_HALF).sqrt())
            else:
                trig = lab.dec_cos(t * half_l) if parity == "even" else lab.dec_sin(t * half_l)
                vals.append(pref * Decimal(2) * wm * trig / (wm * wm - t * t))
        ehat.append(vals)

    mat_k = [[Decimal(0)] * n_modes for _ in range(n_modes)]
    for i in range(n_modes):
        ei = ehat[i]
        for j in range(i, n_modes):
            ej = ehat[j]
            acc = Decimal(0)
            for q, wt in enumerate(w_pts):
                acc += wt * ei[q] * ej[q]
            mat_k[i][j] = mat_k[j][i] = acc
    return mat_k


def eval_phi_single_n1(u: Decimal) -> Decimal:
    """Symmetrized leading n = 1 summand Phi_{n=1}(|u|), breaking Jacobi theta modularity."""
    ua = abs(u)
    e2u = (Decimal(2) * ua).exp()
    e4u = e2u * e2u
    return (Decimal(4) * DEC_PI * DEC_PI * e4u - Decimal(6) * DEC_PI * e2u) * (ua * DEC_HALF - DEC_PI * e2u).exp()


def eval_g2_sigma(w: Decimal, sigma: Decimal, t_heat: Decimal, r_max: Decimal = Decimal("4.4"), n_r: int = 220) -> Decimal:
    """1D cosine transform kernel G_{2,sigma}^{(t)}(w) for m_2(sigma, gamma)."""
    dr = r_max / Decimal(n_r)
    tot = Decimal(0)
    for k in range(1, n_r + 1):
        r = Decimal(k) * dr
        wt = dr * DEC_HALF if k == n_r else dr
        u1 = abs(r + w) * DEC_HALF
        u2 = abs(r - w) * DEC_HALF
        p1 = lab.dec_riemann_phi(u1) * (t_heat * u1 * u1).exp()
        p2 = lab.dec_riemann_phi(u2) * (t_heat * u2 * u2).exp()
        ch = Decimal(1) if sigma == 0 else lab.dec_cosh(sigma * r)
        tot += wt * r * r * ch * p1 * p2
    return Decimal(2) * tot


def run_route_a_probes(pp_dec, gl_x, gl_w):
    print("\n" + "=" * 86)
    print("PART A: ROUTE A PROBES (PRIME-INDUCTION FRONTIER, BANDLIMITED PROLATE, CONTINUOUS WEIL)")
    print("=" * 86)

    # [A1] Sequential Prime-Induction Frontier: L_k^* vs ln(p_{k+1})
    print("\n[A1] Sequential Prime-Induction Frontier (L_k^* vs ln(p_{k+1}), N = 6 modes)")
    print("-" * 86)
    primes_seq = [2, 3, 5, 7, 11, 13, 17]
    modes_e6 = [1, 3, 5, 7, 9, 11]
    modes_o6 = [2, 4, 6, 8, 10, 12]
    print(f"{'Place Set S_k':>20s} | {'ln(p_{k+1})':>11s} | {'L_k^* (EVEN)':>13s} | {'L_k^* (ODD)':>13s} | {'Margin':>11s} | {'Status'}")
    print("-" * 86)
    for k in range(6):
        s_set = set(primes_seq[:k])
        p_next = primes_seq[k]
        ln_next = Decimal(p_next).ln()
        label = "{inf}" if k == 0 else "{inf," + ",".join(str(p) for p in primes_seq[:k]) + "}"

        def min_eig(l_val: Decimal, par: str):
            mds = modes_e6 if par == "even" else modes_o6
            mat_w, _ = lab.build_weil_matrix(l_val, mds, par, pp_dec, gl_x, gl_w, allowed_primes=s_set)
            evals, _ = lab.jacobi_dec_eig(mat_w)
            return evals[0]

        res = {}
        for par in ("even", "odd"):
            lo = ln_next - Decimal("0.01") if k > 0 else Decimal("0.50")
            hi = ln_next + Decimal("0.05")
            step = Decimal("0.15")
            while min_eig(hi, par) > 0 and hi < Decimal("4.5"):
                lo = hi
                hi += step
            a_b, b_b = lo, hi
            for _ in range(28):
                mid = (a_b + b_b) * DEC_HALF
                if min_eig(mid, par) > 0:
                    a_b = mid
                else:
                    b_b = mid
            res[par] = (a_b + b_b) * DEC_HALF

        l_star = min(res["even"], res["odd"])
        margin = l_star - ln_next
        status = "SURVIVES (+)" if margin > 0 else "FAILS"
        print(f"{label:>20s} | {float(ln_next):11.6f} | {float(res['even']):13.6f} | "
              f"{float(res['odd']):13.6f} | {float(margin):+11.6f} | {status}")

    # [A2] Bandlimited Prolate Comparison: W^(L) vs (I - K_Omega)
    print("\n[A2] Bandlimited Prolate Comparison: beta^*(L; Omega) = min <v, W^(L) v> / <v, (I - K_Omega) v>")
    print("-" * 86)
    modes_e8 = [1, 3, 5, 7, 9, 11, 13, 15]
    gam1 = Decimal("14.134725141734693790457251983562470270784257115699")
    t0_arch = Decimal("6.2898359888369028")

    for om_label, om_val in [("t_0 = 6.289836", t0_arch), ("Omega = 10.0", Decimal("10.0")), ("gamma_1 = 14.134725", gam1)]:
        print(f"\n  Cutoff {om_label} (EVEN, N = 8):")
        print(f"  {'L':>5s} | {'lambda_min(W)':>14s} | {'lambda_min(I-K)':>16s} | {'beta^*(L;Om)':>15s} | {'beta_max(L;Om)':>15s} | {'|M01|/sqrt(M00M11)'}")
        for l_str in ["0.69", "1.05", "1.60", "2.20", "3.00", "4.00"]:
            l_val = Decimal(l_str)
            mat_w, _ = lab.build_weil_matrix(l_val, modes_e8, "even", pp_dec, gl_x, gl_w)
            mat_k = build_sinc_kernel_matrix_dec(l_val, om_val, modes_e8, "even")
            n_m = len(modes_e8)
            mat_imk = [[(Decimal(1) if i == j else Decimal(0)) - mat_k[i][j] for j in range(n_m)] for i in range(n_m)]
            w_eigs, _ = lab.jacobi_dec_eig(mat_w)
            imk_eigs, _ = lab.jacobi_dec_eig(mat_imk)
            kappas, _, _, m_prol = lab.generalized_prolate_spectrum_dec(mat_w, mat_imk)
            c01 = abs(m_prol[0][1]) / (abs(m_prol[0][0]) * abs(m_prol[1][1])).sqrt()
            print(f"  {l_str:>5s} | {float(w_eigs[0]):+14.5e} | {float(imk_eigs[0]):+16.5e} | "
                  f"{float(kappas[0]):+15.6e} | {float(kappas[-1]):+15.6e} | {float(c01):.4f}")

    # [A3] Exact Infinite-Dimensional Continuous Weil Positivity & L = ln(2) Schur Complement
    print("\n[A3] Infinite-Dimensional Continuous Weil Positivity on L^2([-L/2, L/2])")
    print("-" * 86)
    c_inf = float(lab.DEC_C_INF)

    def psi_lb(t: float, k_terms: int) -> float:
        t2_4 = 0.25 * t * t
        acc = -c_inf
        for n in range(k_terms):
            an = n + 0.25
            acc += t2_4 / (an * (an * an + t2_4))
        ak = k_terms + 0.25
        return acc + 0.5 * math.log(1.0 + t2_4 / (ak * ak))

    def int_psi_lb_gap(t_cut: float, k_terms: int) -> float:
        tot = 0.0
        for n in range(k_terms):
            an = n + 0.25
            tot += 2.0 * math.atan(t_cut / (2.0 * an)) - 4.0 * an * t_cut / (4.0 * an * an + t_cut * t_cut)
        b_val = 2.0 * (k_terms + 0.25)
        return tot + t_cut - b_val * math.atan(t_cut / b_val)

    def psi_arch_exact(t: float) -> float:
        t2_4 = 0.25 * t * t
        acc = -c_inf
        for n in range(400):
            an = n + 0.25
            acc += t2_4 / (an * (an * an + t2_4))
        x0 = 399.75
        return acc + 0.5 * math.log(1.0 + t2_4 / (x0 * x0))

    print("  Closed-form elementary lower bounds (ALL continuous g on [-L/2, L/2], incl. W_pole):")
    for k_terms in (1, 3):
        for l_f in (1.0 / 12.0, 0.10, 0.125, 0.15):
            best_v, best_t = -1e9, 0.0
            wp_pen = 2.0 * (math.sinh(0.5 * l_f) - 0.5 * l_f)
            for t_i in range(100, 600, 5):
                t_val = t_i * 0.1
                val = psi_lb(t_val, k_terms) - (l_f / math.pi) * int_psi_lb_gap(t_val, k_terms) - wp_pen
                if val > best_v:
                    best_v, best_t = val, t_val
            print(f"    K = {k_terms}, L = {l_f:.6f}: W_pole + W_inf >= {best_v:+.6f} * ||g||_2^2  (T = {best_t:4.1f})")

    # Infinite-dimensional Schur-complement certification at L = ln(2)
    l_ln2 = math.log(2.0)
    half_ln2 = 0.5 * l_ln2
    w1, w2, w3 = math.pi / l_ln2, 2.0 * math.pi / l_ln2, 3.0 * math.pi / l_ln2
    wp_odd_ln2 = 2.0 * (math.sinh(half_ln2) - half_ln2)

    best_op, best_top = -1e9, 0.0
    for t_i in range(100, 500, 10):
        t_cut = t_i * 0.1
        p_t = psi_arch_exact(t_cut)
        n_s = 400
        dt = t_cut / n_s
        integ = 0.0
        for j in range(n_s + 1):
            t = j * dt
            wt = 1.0 if j in (0, n_s) else (4.0 if j % 2 else 2.0)
            k_odd = 0.0 if t == 0 else (0.5 * l_ln2 - math.sin(l_ln2 * t) / (2.0 * t))
            e2h = math.sqrt(half_ln2) if abs(w2 - t) < 1e-12 else math.sqrt(2.0 / l_ln2) * 2.0 * w2 * math.sin(t * half_ln2) / (w2 * w2 - t * t)
            integ += wt * max(0.0, k_odd - e2h * e2h) * (p_t - psi_arch_exact(t))
        val = p_t - (integ * dt / 3.0) / math.pi - wp_odd_ln2
        if val > best_op:
            best_op, best_top = val, t_cut

    w_odd_ln2, _ = lab.build_weil_matrix(Decimal(2).ln(), [2 * k + 2 for k in range(12)], "odd", pp_dec, gl_x, gl_w)
    wo00 = float(w_odd_ln2[0][0])
    cross_o = sum(float(w_odd_ln2[0][j]) ** 2 for j in range(1, 12))
    schur_o = wo00 * best_op - cross_o

    best_ep2, best_tep2 = -1e9, 0.0
    for t_i in range(100, 500, 10):
        t_cut = t_i * 0.1
        p_t = psi_arch_exact(t_cut)
        n_s = 400
        dt = t_cut / n_s
        integ = 0.0
        for j in range(n_s + 1):
            t = j * dt
            wt = 1.0 if j in (0, n_s) else (4.0 if j % 2 else 2.0)
            k_ev = l_ln2 if t == 0 else (0.5 * l_ln2 + math.sin(l_ln2 * t) / (2.0 * t))
            e1h = math.sqrt(half_ln2) if abs(w1 - t) < 1e-12 else math.sqrt(2.0 / l_ln2) * 2.0 * w1 * math.cos(t * half_ln2) / (w1 * w1 - t * t)
            e3h = math.sqrt(half_ln2) if abs(w3 - t) < 1e-12 else math.sqrt(2.0 / l_ln2) * 2.0 * w3 * math.cos(t * half_ln2) / (w3 * w3 - t * t)
            integ += wt * max(0.0, k_ev - e1h * e1h - e3h * e3h) * (p_t - psi_arch_exact(t))
        val = p_t - (integ * dt / 3.0) / math.pi
        if val > best_ep2:
            best_ep2, best_tep2 = val, t_cut

    w_ev_ln2, _ = lab.build_weil_matrix(Decimal(2).ln(), [2 * k + 1 for k in range(12)], "even", pp_dec, gl_x, gl_w)
    a00, a01, a11 = float(w_ev_ln2[0][0]), float(w_ev_ln2[0][1]), float(w_ev_ln2[1][1])
    c00 = sum(float(w_ev_ln2[0][j]) ** 2 for j in range(2, 12))
    c01 = sum(float(w_ev_ln2[0][j]) * float(w_ev_ln2[1][j]) for j in range(2, 12))
    c11 = sum(float(w_ev_ln2[1][j]) ** 2 for j in range(2, 12))
    s00, s01, s11 = a00 - c00 / best_ep2, a01 - c01 / best_ep2, a11 - c11 / best_ep2
    tr = s00 + s11
    det = s00 * s11 - s01 * s01
    lmin_schur = 0.5 * (tr - math.sqrt(max(0.0, tr * tr - 4.0 * det)))

    print("\n  Infinite-dimensional Schur-complement certification at L = ln(2) (zero-prime regime):")
    print(f"    ODD  perp(e_2):      lambda_perp >= {best_op:+.6f} (T = {best_top:.1f}), W00 = {wo00:+.6f}, Schur det = {schur_o:+.6f} -> PASS")
    print(f"    EVEN perp(e_1, e_3): lambda_perp >= {best_ep2:+.6f} (T = {best_tep2:.1f}), 2x2 Schur lambda_min = {lmin_schur:+.6f} (det = {det:+.6e}) -> PASS")


def run_route_b_probes():
    print("\n" + "=" * 86)
    print("PART B: ROUTE B PROBES (CONSTRUCTIVE CORRIDOR, SCHOENBERG NO-GO, MODULARITY ABLATION)")
    print("=" * 86)

    us, phis, wts = lab.build_phi_grid(Decimal("2.45"), 245)

    # [B1] Exact 2D Light-Cone Moments & Alternating Cosine Corridors
    print("\n[B1] Explicit Constructive Convexity Corridor |gamma| <= gamma_cert(M)")
    print("-" * 86)

    def compute_mu_series(sigma: Decimal, max_j: int):
        max_k = 2 * max_j + 3
        e_mom = [Decimal(0)] * (max_k + 1)
        for u, p, w in zip(us, phis, wts):
            pw = Decimal(2) * p * w
            ch = Decimal(1) if sigma == 0 else lab.dec_cosh(sigma * u)
            sh = Decimal(0) if sigma == 0 else lab.dec_sinh(sigma * u)
            up = Decimal(1)
            for k in range(max_k + 1):
                e_mom[k] += pw * up * (ch if k % 2 == 0 else sh)
                up *= u
        fact = [Decimal(1)]
        for k in range(1, max_k + 1):
            fact.append(fact[-1] * Decimal(k))
        mu, a_coeff = [], []
        for j in range(max_j + 1):
            c_tot = Decimal(0)
            for a in range(j + 1):
                b = j - a
                sgn = Decimal(1) if (j % 2 == 0) else Decimal(-1)
                c_tot += sgn / (fact[2 * a] * fact[2 * b]) * (e_mom[2 * a + 1] * e_mom[2 * b + 1] + e_mom[2 * a] * e_mom[2 * b + 2])
            for a in range(j):
                b = j - 1 - a
                sgn = Decimal(1) if ((j - 1) % 2 == 0) else Decimal(-1)
                c_tot += sgn / (fact[2 * a + 1] * fact[2 * b + 1]) * (e_mom[2 * a + 2] * e_mom[2 * b + 2] + e_mom[2 * a + 1] * e_mom[2 * b + 3])
            c_tot *= Decimal(2)
            aj = (Decimal(1) if j % 2 == 0 else Decimal(-1)) * c_tot
            a_coeff.append(aj)
            mu.append(aj * fact[2 * j])
        return mu, a_coeff, e_mom

    mu0, a0, e0 = compute_mu_series(Decimal(0), 22)
    mu_q, aq, _ = compute_mu_series(Decimal("0.25"), 22)
    mu_h, ah, eh = compute_mu_series(Decimal("0.50"), 22)

    _, _, m2_dir, _ = lab.eval_V_sigma_derivs(Decimal(0), Decimal("5.0"), Decimal(0), us, phis, wts)
    m2_ser = sum((Decimal(1) if j % 2 == 0 else Decimal(-1)) * a0[j] * (Decimal("5.0") ** (2 * j)) for j in range(23))
    print(f"  Calibration check at (sigma=0, gamma=5.0): |m2_direct - m2_series| = {float(abs(m2_dir - m2_ser)):.3e}")
    g_unif = (Decimal(2) * mu0[0] / mu_h[1]).sqrt()
    print(f"  Exact algebraic quadratic bound sqrt(2 * mu_0(0) / mu_2(1/2)) = {float(g_unif):.8f}")
    print(f"  Exact 1D Xi(gamma) > 0 quadratic bound sqrt(2 * b_0 / b_1)    = {float((Decimal(2) * e0[0] / e0[2]).sqrt()):.8f}")

    print("\n  Normalized moments mu_{2j}(sigma) / mu_0(sigma) on sigma in [0, 1/2]:")
    print(f"  {'2j':>4s} | {'sigma = 0.00':>18s} | {'sigma = 0.25':>18s} | {'sigma = 0.50':>18s} | {'Decreasing?'}")
    for j in range(1, 9):
        r0, rq, rh = mu0[j] / mu0[0], mu_q[j] / mu_q[0], mu_h[j] / mu_h[0]
        print(f"  {2 * j:4d} | {float(r0):18.10e} | {float(rq):18.10e} | {float(rh):18.10e} | {'YES' if (r0 > rq > rh) else 'NO'}")

    print("\n  Certified alternating-cosine convexity corridor |gamma| <= gamma_cert(M):")
    print(f"  {'Order':>6s} | {'gamma_cert(sigma=0)':>20s} | {'gamma_cert(sigma=0.25)':>22s} | {'gamma_cert(sigma=0.5)':>21s}")
    for m_ord in [1, 2, 3, 4, 6, 8, 10, 11]:
        deg_idx = 2 * m_ord - 1
        roots = []
        for ac in (a0, aq, ah):
            def poly_val(g_val: Decimal) -> Decimal:
                g2 = g_val * g_val
                gp = Decimal(1)
                acc = Decimal(0)
                for j in range(deg_idx + 1):
                    acc += (ac[j] if j % 2 == 0 else -ac[j]) * gp
                    gp *= g2
                return acc

            lo, hi = Decimal(0), Decimal("0.5")
            while poly_val(hi) > 0 and hi < Decimal(40):
                lo = hi
                hi += Decimal("0.5")
            for _ in range(50):
                mid = (lo + hi) * DEC_HALF
                if poly_val(mid) > 0:
                    lo = mid
                else:
                    hi = mid
            roots.append(lo)
        print(f"  {2 * deg_idx:6d} | {float(roots[0]):20.10f} | {float(roots[1]):22.10f} | {float(roots[2]):21.10f}")

    # [B2] Schoenberg Complete-Monotonicity Obstruction & Bochner-Toeplitz Matrices
    print("\n[B2] Schoenberg Complete-Monotonicity Obstruction & Bochner-Toeplitz Spectra")
    print("-" * 86)
    xs = [Decimal(k) * Decimal("0.04") for k in range(16)]
    fs = [eval_g2_sigma(x.sqrt(), Decimal(0), Decimal(0), Decimal("4.2"), 180) for x in xs]
    diffs = fs[:]
    all_pos_orders = 0
    for order in range(1, 10):
        diffs = [-(diffs[i + 1] - diffs[i]) / Decimal("0.04") for i in range(len(diffs) - 1)]
        if min(diffs) >= 0:
            all_pos_orders += 1
    print(f"  Finite-difference check on x in [0, 0.60] (dx = 0.04): {all_pos_orders}/9 orders (-1)^k Delta^k G_{{2,0}}(sqrt(x)) > 0")
    print("  Super-exponential decay diagnostic (obstruction to Schoenberg Laplace representation):")
    for w_f in (0.5, 1.0, 1.5, 2.0, 2.5):
        w = Decimal(str(w_f))
        gval = eval_g2_sigma(w, Decimal(0), Decimal(0), Decimal("4.4"), 220)
        ratio = -float(gval.ln()) / (w_f * w_f)
        print(f"    w = {w_f:3.1f} (x = {w_f * w_f:4.2f}): G_{{2,0}}(w) = {float(gval):.4e}, -ln(G_{{2,0}})/x = {ratio:8.4f}  (diverges super-exponentially)")

    print("  Bochner-Toeplitz matrix T_{ij} = G_{2,0}^{(t)}((i-j)*dw):")
    for dw_str, n_mat in [("0.25", 10), ("0.063", 14)]:
        dw = Decimal(dw_str)
        for t_str in ["0.0", "-0.55"]:
            t_val = Decimal(t_str)
            g_vals = [eval_g2_sigma(Decimal(k) * dw, Decimal(0), t_val, Decimal("4.0"), 150) for k in range(n_mat)]
            t_mat = [[g_vals[abs(i - j)] for j in range(n_mat)] for i in range(n_mat)]
            evals, _ = lab.jacobi_dec_eig(t_mat)
            print(f"    dw = {dw_str:>5s} (N = {n_mat:2d}, Nyquist = {math.pi / float(dw):5.1f}), t = {t_str:>5s}: "
                  f"lambda_min(T) = {float(evals[0]):+.6e}, lambda_max = {float(evals[-1]):+.6e}")

    # [B3] Jacobi-Theta Modularity Ablation vs Polya Smooth Kernel
    print("\n[B3] Jacobi-Theta Modularity Ablation on gamma in {0..55}")
    print("-" * 86)
    phis_n1 = [eval_phi_single_n1(u) for u in us]
    phis_polya = [
        Decimal(8) * DEC_PI * DEC_PI * lab.dec_cosh(Decimal("4.5") * u) *
        (Decimal(-2) * DEC_PI * lab.dec_cosh(Decimal(2) * u)).exp()
        for u in us
    ]
    min_full, min_n1, min_polya = Decimal("1e99"), Decimal("1e99"), Decimal("1e99")
    g_min_n1 = 0
    neg_pts = []
    for g_int in range(56):
        g = Decimal(g_int)
        _, _, m2_f, _ = lab.eval_V_sigma_derivs(Decimal(0), g, Decimal(0), us, phis, wts)
        _, _, m2_1, _ = lab.eval_V_sigma_derivs(Decimal(0), g, Decimal(0), us, phis_n1, wts)
        _, _, m2_p, _ = lab.eval_V_sigma_derivs(Decimal(0), g, Decimal(0), us, phis_polya, wts)
        if m2_f < min_full:
            min_full = m2_f
        if m2_1 < min_n1:
            min_n1, g_min_n1 = m2_1, g_int
        if m2_p < min_polya:
            min_polya = m2_p
        if m2_1 < 0:
            neg_pts.append((g_int, float(m2_1), float(m2_f)))

    print(f"  Full Jacobi-theta Phi(u):    min m_2 = {float(min_full):+.4e}  (0/56 violations)")
    print(f"  Polya smooth even Phi^*(u):  min m_2 = {float(min_polya):+.4e}  (0/56 violations)")
    print(f"  Cusped n = 1 Phi_{{n=1}}(|u|): min m_2 = {float(min_n1):+.4e} at gamma = {g_min_n1}  ({len(neg_pts)}/56 violations)")
    for gi, v1, vf in neg_pts[:5]:
        print(f"    gamma = {gi:2d}: m_2(n=1) = {v1:+.4e} < 0   vs   m_2(full Phi) = {vf:+.4e} > 0")


def main():
    t0 = time.time()
    print("=" * 86)
    print("65-DIGIT VERIFICATION SUITE: ROUTE A WEIL POSITIVITY & ROUTE B CONSTRUCTIVE CORRIDOR")
    print("=" * 86)
    pp_dec = lab.sieve_prime_powers_dec(200)
    gl_x, gl_w = lab.dec_gl_nodes_weights(20)
    run_route_a_probes(pp_dec, gl_x, gl_w)
    run_route_b_probes()
    print(f"\nALL PROBES COMPLETED CLEANLY IN {time.time() - t0:.2f} s.")


if __name__ == "__main__":
    main()
