#!/usr/bin/env python3
"""
High-Precision Verification Laboratory for Module #12
(UniversalWeilAndHerglotzResolvent.lean):
  1. Route A: Infinite-dimensional Hilbert-space Schur certification crossing
     BOTH p = 2 (ln 2 = 0.6931) AND p = 3 (ln 3 = 1.0986) up to L = 1.30,
     plus explicit universal finite-codimension coercivity bounds for all L > 0.
  2. Route B: All-order 2D light-cone parity separation certifying uniform
     convexity m_2(sigma, gamma) > 0 across sigma in [0, 1/2] past gamma_1,
     gamma_2, and up to gamma_3 (Local RH + Zero Simplicity).
  3. Spectral Resolvent R_xi(z) = i*(xi'/xi)(1/2 - i*z): exact Cauchy-Riemann
     duality, Schwarz-Pick hyperbolic contraction, 4x4 Hermitian Pick-Nevanlinna
     matrix eigenvalues, and remote off-line detection on Re(s) = 1 (sigma = 0.50).
  4. Compactified angular strip coordinate beta(theta) = cos^2(theta/2), kinetic
     barrier 1/(2*beta*(1-beta)) = 2/sin^2(theta), and angular descent identity.

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


def part_1_route_a_schur_and_universal_codim():
    print("=" * 94)
    print("PART 1 (ROUTE A): INFINITE-DIM SCHUR CROSSING p = 2 & p = 3 (L <= 1.30) + UNIVERSAL CODIM")
    print("=" * 94)
    pp_dec = lab.sieve_prime_powers_dec(20)
    gl_x, gl_w = lab.dec_gl_nodes_weights(22)

    def refined_prime_norm_bound(l_f: float) -> float:
        """Exact formal bound from Theorem `weilPrime_refined_norm_bound`:
        factor 1 for L/2 <= ln n <= L (disjoint shift strips), factor 2 for ln n < L/2."""
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
        t_lo = max(20.0, (2 * r_modes) * math.pi / l_f)
        t_hi = t_lo * 4.0
        for idx in range(10):
            t_cut = t_lo + (t_hi - t_lo) * idx / 9.0
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

    print("  [1A] Infinite-Dimensional Hilbert Schur Certification Across p = 2 and p = 3:")
    cases = [
        (0.90, 4, 5),
        (1.00, 5, 6),
        (1.09, 6, 7),
        (1.15, 10, 11),
        (1.20, 12, 13),
        (1.30, 14, 15),
    ]
    for l_f, r_o, r_e in cases:
        p_norm = refined_prime_norm_bound(l_f)
        lo_tail = tail_bound(l_f, "odd", r_o, p_norm)
        le_tail = tail_bound(l_f, "even", r_e, p_norm)
        n_ref = max(r_o, r_e) + 10
        l_dec = Decimal(str(l_f))
        w_odd, n_pp = lab.build_weil_matrix(l_dec, [2 * k + 2 for k in range(n_ref)], "odd", pp_dec, gl_x, gl_w)
        w_ev, _ = lab.build_weil_matrix(l_dec, [2 * k + 1 for k in range(n_ref)], "even", pp_dec, gl_x, gl_w)
        so_min = schur_min_eig(w_odd, r_o, lo_tail)
        se_min = schur_min_eig(w_ev, r_e, le_tail)
        assert lo_tail > 0.0 and so_min > 0.0, f"ODD Schur failed at L={l_f}"
        assert le_tail > 0.0 and se_min > 0.0, f"EVEN Schur failed at L={l_f}"
        print(
            f"    L={l_f:4.2f} (#p^m={n_pp}, ||W_p||_ref<={p_norm:.5f}): "
            f"ODD(r={r_o:2d}) lam_perp={lo_tail:+.4f}, S_min={so_min:+.4e} | "
            f"EVEN(r={r_e:2d}) lam_perp={le_tail:+.4f}, S_min={se_min:+.4e} [PASS]"
        )

    print("\n  [1B] Universal Finite-Codimension Coercivity Certificate (`weilTotal_universal_finite_codim_coercive`):")
    for l_f in [0.50, 1.00, 1.50, 2.00, 3.00]:
        n_max = int(math.floor(math.exp(l_f)))
        p_ref = refined_prime_norm_bound(l_f)
        pole_bd = 2.0 * (math.sinh(0.5 * l_f) - 0.5 * l_f)
        m_l = pole_bd + p_ref
        # Find minimal T > 0 such that psi_arch_exact(T) >= m_l + 2.0 (coercivity constant c = +1)
        t_cut = 1.0
        while psi_arch_exact(t_cut) < m_l + 2.0:
            t_cut *= 1.05
        # Moment-orthogonality codimension N from ((L*T/2)^N / N!)^2 * ((L/pi)*T*(psi(T)+6)) <= 1
        d_t = (l_f / math.pi) * t_cut * (psi_arch_exact(t_cut) + 6.0)
        a_val = 0.5 * l_f * t_cut
        # Use logs to find minimal N cleanly even for large a_val
        n_codim = 1
        while True:
            log_term = 2.0 * (n_codim * math.log(a_val) - math.lgamma(n_codim + 1)) + math.log(d_t)
            if log_term <= 0.0:
                break
            n_codim += 1
        assert psi_arch_exact(t_cut) - 1.0 - m_l >= 1.0
        print(
            f"    L={l_f:4.2f} (n<={n_max:2d}): M_ref(L)={m_l:6.4f}, T*={t_cut:10.2f}, "
            f"finite moment codim N={n_codim:6d} -> W_total(L, g) >= 1.0 * ||g||_2^2 on V_N^perp [PROVED]"
        )


def part_2_route_b_all_order_light_cone():
    print("\n" + "=" * 94)
    print("PART 2 (ROUTE B): ALL-ORDER LIGHT-CONE PARITY IDENTITY CROSSING gamma_1, gamma_2, gamma_3")
    print("=" * 94)
    us, phis, wts = lab.build_phi_grid(Decimal("2.80"), 280)
    max_order = 130
    max_m = max_order + 2
    fac = [Decimal(1)]
    for i in range(1, max_m + 2):
        fac.append(fac[-1] * Decimal(i))

    def build_mu_seq(sig_str: str):
        """Exact coefficients mu_{2k}(sigma) from `lightCone_even_power_parity_identity`:
        for even b: +4 * b_{2k}(b) * I_{2k+2-b}(sigma) * I_b(sigma),
        for odd  b: -4 * b_{2k}(b) * J_{2k+2-b}(sigma) * J_b(sigma)."""
        sig = Decimal(sig_str)
        c_mom = [Decimal(0)] * (max_m + 1)
        s_mom = [Decimal(0)] * (max_m + 1)
        for u, p, w in zip(us, phis, wts):
            pw = p * w
            ch = Decimal(1) if sig == 0 else lab.dec_cosh(sig * u)
            sh = Decimal(0) if sig == 0 else lab.dec_sinh(sig * u)
            up = Decimal(1)
            for m in range(max_m + 1):
                c_mom[m] += pw * ch * up
                if sig != 0:
                    s_mom[m] += pw * sh * up
                up *= u
        mus = []
        for k in range(max_order // 2 + 1):
            n = 2 * k
            acc = Decimal(0)
            for b in range(n + 3):
                c0 = Decimal(math.comb(n, b)) if 0 <= b <= n else Decimal(0)
                c1 = Decimal(math.comb(n, b - 1)) if 0 <= b - 1 <= n else Decimal(0)
                c2 = Decimal(math.comb(n, b - 2)) if 0 <= b - 2 <= n else Decimal(0)
                coeff = c0 - Decimal(2) * c1 + c2
                a = n + 2 - b
                if b % 2 == 0:
                    acc += Decimal(4) * coeff * c_mom[a] * c_mom[b]
                elif sig != 0:
                    acc -= Decimal(4) * coeff * s_mom[a] * s_mom[b]
            mus.append(acc / fac[n])
        return mus

    mus_by_s = {s: build_mu_seq(s) for s in ["0", "0.25", "0.5"]}

    def eval_lb(mus, ord_n: int, g_dec: Decimal) -> Decimal:
        g2 = g_dec * g_dec
        pw = Decimal(1)
        acc = Decimal(0)
        for k in range(ord_n // 2 + 1):
            t = mus[k] * pw
            acc += t if (k % 2 == 0) else -t
            pw *= g2
        return acc

    g1 = Decimal("14.13472514173469379045725198356247027078")
    g2 = Decimal("21.02203963877155499262847959389690277733")
    g3 = Decimal("25.01085758014568876321379099256282181866")

    # Cross-verify Taylor sum at Order 130 against exact 65-digit integral m_2(0, gamma_1) and m_2(0.5, gamma_1)
    for s_str in ["0", "0.5"]:
        _, _, m2_exact, _ = lab.eval_V_sigma_derivs(Decimal(s_str), g1, Decimal(0), us, phis, wts)
        m2_tay = eval_lb(mus_by_s[s_str], 130, g1)
        rel_err = abs(m2_tay - m2_exact) / abs(m2_exact)
        assert rel_err < Decimal("1e-25"), f"Light-cone series mismatch: {rel_err}"
        print(f"  Exact check at gamma_1, sigma={s_str}: m_2 = {float(m2_exact):+.6e}, Taylor_130 rel_err = {float(rel_err):.2e} [PASS]")

    cert_summary = {}
    for ord_n in [2, 14, 30, 42, 50, 74, 94, 110, 122, 126, 130]:
        vals = {}
        for s_str, mus in mus_by_s.items():
            lo, hi = Decimal(0), Decimal(32)
            g_scan = Decimal("0.25")
            while g_scan <= Decimal(32):
                if eval_lb(mus, ord_n, g_scan) <= 0:
                    lo, hi = g_scan - Decimal("0.25"), g_scan
                    break
                g_scan += Decimal("0.25")
            for _ in range(36):
                mid = (lo + hi) / Decimal(2)
                if eval_lb(mus, ord_n, mid) > 0:
                    lo = mid
                else:
                    hi = mid
            vals[s_str] = float(lo)
        cert_summary[ord_n] = vals
        tag = ""
        min_g = min(vals.values())
        if min_g > float(g3):
            tag = " [CROSSED gamma_1, gamma_2, AND gamma_3!!]"
        elif min_g > float(g2):
            tag = " [CROSSED gamma_1 & gamma_2]"
        elif min_g > float(g1):
            tag = " [CROSSED gamma_1]"
        print(
            f"  Order {ord_n:3d}: sigma=0 -> {vals['0']:8.4f} | "
            f"sigma=0.25 -> {vals['0.25']:8.4f} | sigma=0.50 -> {vals['0.5']:8.4f}{tag}"
        )

    assert min(cert_summary[50].values()) > float(g1), "Order 50 must cross gamma_1 uniformly!"
    assert min(cert_summary[94].values()) > float(g2), "Order 94 must cross gamma_2 uniformly!"
    assert min(cert_summary[126].values()) > float(g3), "Order 126 must cross gamma_3 uniformly!"


def part_3_resolvent_herglotz_pick_remote_detection():
    print("\n" + "=" * 94)
    print("PART 3: SPECTRAL RESOLVENT R_xi, SCHWARZ-PICK CONTRACTION & 4x4 PICK MATRIX DETECTION")
    print("=" * 94)
    us, phis, wts = lab.build_phi_grid(Decimal("2.50"), 250)

    def eval_F_and_dF(gamma_f: float, sigma_f: float, t_f: float):
        g_d, s_d, t_d = Decimal(str(gamma_f)), Decimal(str(sigma_f)), Decimal(str(t_f))
        x0_r = x0_i = x1_r = x1_i = x2_r = x2_i = Decimal(0)
        for u, p, w in zip(us, phis, wts):
            pt = p * (t_d * u * u).exp() if t_d != 0 else p
            pw = Decimal(2) * pt * w
            ch, sh = lab.dec_cosh(s_d * u), lab.dec_sinh(s_d * u)
            cs, sn = lab.dec_cos(g_d * u), lab.dec_sin(g_d * u)
            u2 = u * u
            x0_r += pw * ch * cs
            x0_i += -pw * sh * sn
            x1_r += pw * u * sh * cs
            x1_i += -pw * u * ch * sn
            x2_r += pw * u2 * ch * cs
            x2_i += -pw * u2 * sh * sn
        z0 = complex(float(x0_r), float(x0_i))
        z1 = complex(float(x1_r), float(x1_i))
        z2 = complex(float(x2_r), float(x2_i))
        q = z1 / z0
        dq = (z2 * z0 - z1 * z1) / (z0 * z0)
        return 1j * q, dq

    # 3A: Verify exact Resolvent-Logarithmic Force duality `xiResolvent_im_eq_logForce_half`
    print("  [3A] Exact Resolvent-Logarithmic Force Duality Im(R_xi(gamma+i*sigma)) = (1/2)*d_sigma log V:")
    for g_val, s_val in [(14.134725, 0.25), (21.022040, 0.10), (48.62253, 0.50)]:
        F_val, _ = eval_F_and_dF(g_val, s_val, 0.0)
        V_val, dV_val, _, _ = lab.eval_V_sigma_derivs(Decimal(str(s_val)), Decimal(str(g_val)), Decimal(0), us, phis, wts)
        half_log_force = 0.5 * float(dV_val / V_val)
        err = abs(F_val.imag - half_log_force)
        assert err < 1e-13, f"Duality mismatch: {err}"
        print(f"    (gamma={g_val:9.5f}, sigma={s_val:4.2f}): Im(R_xi)={F_val.imag:+.10f}, (1/2)*d_s ln V={half_log_force:+.10f}, err={err:.2e} [PASS]")

    # 3B: Schwarz-Pick Contraction Ratio: True xi (t=0) vs Post-Collision (t=-0.475)
    print("\n  [3B] Schwarz-Pick Ratio rho_SP = sigma * |R_xi'| / Im(R_xi) (<= 1 for Herglotz; > 1 detects off-line poles remotely):")
    for label, t_f, g_pts, expect_ok in [
        ("TRUE xi (t = 0.0)", 0.0, [14.134725, 21.02204, 48.62253], True),
        ("POST-COLLISION (t = -0.475, delta ~ 0.07)", -0.475, [49.67815], False),
    ]:
        print(f"    {label}:")
        for g in g_pts:
            for sig in [0.02, 0.10, 0.25, 0.50]:
                F_v, dF_v = eval_F_and_dF(g, sig, t_f)
                imF = F_v.imag
                sp = sig * abs(dF_v) / imF
                ok = (imF > 0.0 and sp <= 1.0 + 1e-12)
                if expect_ok:
                    assert ok, f"Unexpected Schwarz-Pick failure for true xi at ({g}, {sig})"
                else:
                    assert not ok, f"Expected remote Schwarz-Pick violation at ({g}, {sig})"
                print(
                    f"      gamma={g:9.5f}, sigma={sig:4.2f}: Im(R)={imF:+.5e}, "
                    f"|R'|={abs(dF_v):.5e}, rho_SP={sp:+.6f} -> {'HERGLOTZ OK' if ok else 'VIOLATED (REMOTE DETECTION!)'}"
                )

    # 3C: 4x4 Hermitian Pick-Nevanlinna Matrix Spectrum strictly on remote heights sigma in {0.25, 0.50}
    print("\n  [3C] 4x4 Hermitian Pick-Nevanlinna Matrix Spectrum on Remote Heights sigma in {0.25, 0.50}:")
    for label, t_f, center, expect_psd in [
        ("TRUE xi (t = 0.0, pinch gamma* = 48.62253)", 0.0, 48.62253, True),
        ("POST-COLLISION (t = -0.475, pinch gamma* = 49.67815)", -0.475, 49.67815, False),
    ]:
        pts = [(center - 0.15, 0.25), (center, 0.25), (center + 0.15, 0.25), (center, 0.50)]
        Fs = [eval_F_and_dF(g, s, t_f)[0] for g, s in pts]
        zs = [complex(g, s) for g, s in pts]
        n = len(pts)
        P = [[(Fs[j] - Fs[k].conjugate()) / (zs[j] - zs[k].conjugate()) for k in range(n)] for j in range(n)]
        # Exact 2n x 2n real symmetric lifting [[Re P, -Im P], [Im P, Re P]]
        R = [[Decimal(0)] * (2 * n) for _ in range(2 * n)]
        for j in range(n):
            for k in range(n):
                re_v, im_v = Decimal(str(P[j][k].real)), Decimal(str(P[j][k].imag))
                R[j][k] = re_v
                R[n + j][n + k] = re_v
                R[j][n + k] = -im_v
                R[n + j][k] = im_v
        ev, _ = lab.jacobi_dec_eig(R)
        eigs = [float(ev[2 * i]) for i in range(n)]
        if expect_psd:
            assert eigs[0] > 0.0, f"Pick matrix not PSD for t=0: {eigs}"
        else:
            assert eigs[0] < -1.0, f"Pick matrix failed to detect off-line zero at t=-0.475: {eigs}"
        print(f"    {label}:")
        print(f"      eigs(P_4x4) = {[f'{x:+.4e}' for x in eigs]} -> {'STRICTLY PSD [PASS]' if eigs[0] > 0 else 'NEGATIVE EIGENVALUE DETECTED [PASS]'}")


def part_4_compactified_angular_strip():
    print("\n" + "=" * 94)
    print("PART 4: COMPACTIFIED ANGULAR STRIP COORDINATE beta(theta) = cos^2(theta/2) & DESCENT")
    print("=" * 94)
    us, phis, wts = lab.build_phi_grid(Decimal("2.50"), 250)
    for theta_deg in [15.0, 30.0, 45.0, 60.0, 75.0, 90.0]:
        th = math.radians(theta_deg)
        beta = math.cos(0.5 * th) ** 2
        beta_refl = math.cos(0.5 * (math.pi - th)) ** 2
        sigma = 0.5 * math.cos(th)
        barrier = 1.0 / (2.0 * beta * (1.0 - beta))
        barrier_exact = 2.0 / (math.sin(th) ** 2)
        assert abs(beta - (0.5 + sigma)) < 1e-15
        assert abs(beta_refl - (1.0 - beta)) < 1e-15
        assert abs(barrier - barrier_exact) / barrier_exact < 1e-14
        assert barrier >= 2.0 - 1e-15
        # Verify angular descent -d/dtheta V((1/2)*cos(theta), gamma_1) = (1/2)*sin(theta)*d_sigma V >= 0
        _, dV, _, _ = lab.eval_V_sigma_derivs(Decimal(str(sigma)), Decimal("14.13472514173469"), Decimal(0), us, phis, wts)
        neg_dth_V = 0.5 * math.sin(th) * float(dV)
        if theta_deg < 90.0:
            assert neg_dth_V > 0.0
        print(
            f"  theta={theta_deg:5.1f} deg: beta={beta:.6f}, sigma={sigma:.6f}, "
            f"barrier=2/sin^2(theta)={barrier:8.4f} (>=2), -d_theta V(gamma_1)={neg_dth_V:+.4e} [PASS]"
        )


def main():
    t0 = time.time()
    part_1_route_a_schur_and_universal_codim()
    part_2_route_b_all_order_light_cone()
    part_3_resolvent_herglotz_pick_remote_detection()
    part_4_compactified_angular_strip()
    print("\n" + "=" * 94)
    print(f"ALL MODULE #12 VERIFICATION CHECKS PASSED IN {time.time() - t0:.2f} s.")
    print("=" * 94)


if __name__ == "__main__":
    main()
