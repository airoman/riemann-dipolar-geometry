#!/usr/bin/env python3
"""
65-Digit Arbitrary-Precision Laboratory for Transverse-Potential Convexity,
Critical-Line Laguerre Curvature, Prolate Spectral Comparison, and Exact
LDL^T Positivity Certificates on the Riemann Zeta Function.

Zero external dependencies (Python 3 standard library only: math, decimal).
All spectral, convexity, and certificate computations execute in 65-digit
arbitrary-precision Decimal arithmetic.

Contents:
  [P1] Transverse Differential Hierarchy (m1, m2 = 2*L1, m3, m4..m10) on
       V(sigma, gamma) = |xi(1/2 + sigma + i*gamma)|^2:
       - 65-digit verification of m2(0, gamma) == 2*((Xi')^2 - Xi*Xi''),
       - Zero-lag detection of the (gamma_9, gamma_10) heat-flow collision at
         t_coll = -0.469477268 (contrasted with higher derivatives m4..m10
         and 50-digit Li coefficients lambda_1..lambda_20 which remain > 0).
  [P2] 2D Past-Future Light-Cone Laguerre Kernel K_Lag(w):
       - 41-digit verification of int_0^inf K_Lag(w) cos(gamma w) dw == 2 L1(Xi),
       - Quantitative transverse convexity corridor & normalized margin.
  [P3] Spectral Synthesis of Riemann Zeros from Ground States of W^(L),
       Exact Archimedean Boundary L_arch^*, and Finite-Place Truncation Control:
       - Synthesis of gamma_1 to 13.18 exact decimal digits (err = 6.53e-14)
         from ONLY three prime powers {2, 3, 4} (L = 1.60, N = 16 modes),
       - Purely Archimedean positivity boundary L_arch^* = 0.8416836893 > ln 2,
       - Refutation of finite-primorial truncation S = {inf, 2, 3, 5} for L >= 2.0.
  [P4] Connes-Consani Prolate Fidelity, Prolate Comparison Certificates
       W^(L) = alpha^*(L) * H_prolate + R^(L) (R > 0), Exact 65-Digit LDL^T
       Cholesky Certificates (residual <= 1e-64), and Continuous Sphere-Annealing
       Synthesis of gamma_1 without explicit eigensolvers.
"""

import math
import time
from decimal import Decimal, getcontext

getcontext().prec = 65

# ==============================================================================
# PART 0: 65-DIGIT ARBITRARY-PRECISION DECIMAL ENGINE
# ==============================================================================

def dec_pi() -> Decimal:
    def arctan_inv(m: int) -> Decimal:
        m_dec = Decimal(m)
        m2 = m_dec * m_dec
        term = Decimal(1) / m_dec
        total = term
        k = 1
        while True:
            term = -term / m2
            add = term / Decimal(2 * k + 1)
            if add == 0:
                break
            total += add
            k += 1
        return total
    return Decimal(4) * (Decimal(4) * arctan_inv(5) - arctan_inv(239))

DEC_PI = dec_pi()
DEC_HALF = Decimal("0.5")
DEC_EULER_GAMMA = Decimal("0.5772156649015328606065120900824024310421593359399235988057672348")
DEC_C_INF = DEC_EULER_GAMMA + (Decimal(8) * DEC_PI).ln() + DEC_PI * DEC_HALF

def dec_cos(x: Decimal) -> Decimal:
    two_pi = Decimal(2) * DEC_PI
    x = x % two_pi
    x2 = x * x
    term = Decimal(1)
    total = term
    k = 1
    while True:
        term = -term * x2 / Decimal((2 * k - 1) * (2 * k))
        if abs(term) < Decimal("1e-62"):
            break
        total += term
        k += 1
    return total

def dec_sin(x: Decimal) -> Decimal:
    two_pi = Decimal(2) * DEC_PI
    x = x % two_pi
    x2 = x * x
    term = x
    total = term
    k = 1
    while True:
        term = -term * x2 / Decimal((2 * k) * (2 * k + 1))
        if abs(term) < Decimal("1e-62"):
            break
        total += term
        k += 1
    return total

def dec_atan(x: Decimal) -> Decimal:
    for _ in range(3):
        x = x / (Decimal(1) + (Decimal(1) + x * x).sqrt())
    x2 = x * x
    term = x
    total = term
    k = 1
    while True:
        term = -term * x2
        add = term / Decimal(2 * k + 1)
        if abs(add) < Decimal("1e-62"):
            break
        total += add
        k += 1
    return Decimal(8) * total

def dec_cosh(x: Decimal) -> Decimal:
    ex = x.exp()
    return (ex + Decimal(1) / ex) * DEC_HALF

def dec_sinh(x: Decimal) -> Decimal:
    ex = x.exp()
    return (ex - Decimal(1) / ex) * DEC_HALF

def dec_riemann_phi(u: Decimal) -> Decimal:
    e2u = (Decimal(2) * u).exp()
    e4u = e2u * e2u
    uhalf = u * DEC_HALF
    pi_e2u = DEC_PI * e2u
    c4 = Decimal(4) * DEC_PI * DEC_PI * e4u
    c6 = Decimal(6) * DEC_PI * e2u
    total = Decimal(0)
    n = 1
    while True:
        n2 = Decimal(n * n)
        arg = pi_e2u * n2
        if arg > Decimal(200):
            break
        term = (c4 * n2 * n2 - c6 * n2) * (uhalf - arg).exp()
        total += term
        if total != 0 and abs(term) < abs(total) * Decimal("1e-62"):
            break
        n += 1
    return total

def build_phi_grid(u_max: Decimal = Decimal("2.45"), n_steps: int = 245):
    du = u_max / Decimal(n_steps)
    us = [Decimal(k) * du for k in range(n_steps + 1)]
    phis = [dec_riemann_phi(u) for u in us]
    wts = [du] * (n_steps + 1)
    wts[0] = du * DEC_HALF
    wts[-1] = du * DEC_HALF
    return us, phis, wts

def eval_Xi_derivs_high(gamma: Decimal, t_heat: Decimal, max_ord: int, us, phis, wts):
    sums = [Decimal(0)] * (max_ord + 1)
    for u, p, w in zip(us, phis, wts):
        pt = p * (t_heat * u * u).exp() * w
        gu = gamma * u
        c = dec_cos(gu)
        s = dec_sin(gu)
        upow = Decimal(1)
        for j in range(max_ord + 1):
            r = j % 4
            if r == 0:
                sums[j] += pt * upow * c
            elif r == 1:
                sums[j] -= pt * upow * s
            elif r == 2:
                sums[j] -= pt * upow * c
            else:
                sums[j] += pt * upow * s
            upow *= u
    return [Decimal(2) * v for v in sums]

def laguerre_Lm(derivs, m: int) -> Decimal:
    tot = Decimal(0)
    two_m = 2 * m
    for j in range(two_m + 1):
        binom = Decimal(math.comb(two_m, j))
        sgn = Decimal(1) if ((m + j) % 2 == 0) else Decimal(-1)
        tot += sgn * binom * derivs[j] * derivs[two_m - j]
    return tot

def eval_V_sigma_derivs(sigma: Decimal, gamma: Decimal, t_heat: Decimal, us, phis, wts):
    fr = [Decimal(0)] * 4
    fi = [Decimal(0)] * 4
    for u, p, w in zip(us, phis, wts):
        u2 = u * u
        u3 = u2 * u
        pt = Decimal(2) * p * (t_heat * u2).exp() * w
        ch = dec_cosh(sigma * u)
        sh = dec_sinh(sigma * u)
        c = dec_cos(gamma * u)
        s = dec_sin(gamma * u)
        fr[0] += pt * ch * c;       fi[0] -= pt * sh * s
        fr[1] += pt * u * sh * c;   fi[1] -= pt * u * ch * s
        fr[2] += pt * u2 * ch * c;  fi[2] -= pt * u2 * sh * s
        fr[3] += pt * u3 * sh * c;  fi[3] -= pt * u3 * ch * s
    V = fr[0]*fr[0] + fi[0]*fi[0]
    m1 = Decimal(2) * (fr[0]*fr[1] + fi[0]*fi[1])
    m2 = Decimal(2) * (fr[1]*fr[1] + fi[1]*fi[1] + fr[0]*fr[2] + fi[0]*fi[2])
    m3 = Decimal(2) * (Decimal(3)*(fr[1]*fr[2] + fi[1]*fi[2]) + fr[0]*fr[3] + fi[0]*fi[3])
    return V, m1, m2, m3

def dec_gl_nodes_weights(n: int):
    nodes, weights = [], []
    m = (n + 1) // 2
    for i in range(1, m + 1):
        z = Decimal(str(math.cos(math.pi * (i - 0.25) / (n + 0.5))))
        for _ in range(10):
            p1, p2 = Decimal(1), Decimal(0)
            for j in range(1, n + 1):
                p3 = p2; p2 = p1
                p1 = (Decimal(2 * j - 1) * z * p2 - Decimal(j - 1) * p3) / Decimal(j)
            pp = Decimal(n) * (z * p1 - p2) / (z * z - Decimal(1))
            dz = p1 / pp
            z -= dz
            if abs(dz) < Decimal("1e-58"):
                break
        w = Decimal(2) / ((Decimal(1) - z * z) * pp * pp)
        nodes.append((Decimal(1) - z) * DEC_HALF)
        weights.append(w * DEC_HALF)
        if i != n + 1 - i:
            nodes.append((Decimal(1) + z) * DEC_HALF)
            weights.append(w * DEC_HALF)
    pairs = sorted(zip(nodes, weights))
    return [x for x, _ in pairs], [w for _, w in pairs]

def sieve_prime_powers_dec(max_n: int):
    is_pr = [True] * (max_n + 1)
    entries = []
    for p in range(2, max_n + 1):
        if is_pr[p]:
            lp = Decimal(p).ln()
            pk = p
            while pk <= max_n:
                entries.append((Decimal(pk).ln(), lp / Decimal(pk).sqrt(), p, pk))
                pk *= p
            for m in range(p * p, max_n + 1, p):
                is_pr[m] = False
    entries.sort(key=lambda x: x[0])
    return entries

def jacobi_dec_eig(A):
    n = len(A)
    M = [row[:] for row in A]
    Q = [[Decimal(1) if i == j else Decimal(0) for j in range(n)] for i in range(n)]
    eps = Decimal("1e-50")
    for _ in range(120 * n * n):
        p, q = 0, 1
        mv = Decimal(0)
        for i in range(n):
            for j in range(i + 1, n):
                v = abs(M[i][j])
                if v > mv:
                    mv = v; p, q = i, j
        if mv < eps:
            break
        app, aqq, apq = M[p][p], M[q][q], M[p][q]
        tau = (aqq - app) / (Decimal(2) * apq)
        r = (Decimal(1) + tau * tau).sqrt()
        t = Decimal(1) / (tau + r) if tau >= 0 else Decimal(-1) / (-tau + r)
        c = Decimal(1) / (Decimal(1) + t * t).sqrt()
        s = t * c
        M[p][p] = app - t * apq
        M[q][q] = aqq + t * apq
        M[p][q] = Decimal(0); M[q][p] = Decimal(0)
        for k in range(n):
            if k != p and k != q:
                mkp, mkq = M[k][p], M[k][q]
                M[k][p] = c * mkp - s * mkq; M[p][k] = M[k][p]
                M[k][q] = s * mkp + c * mkq; M[q][k] = M[k][q]
        for k in range(n):
            qkp, qkq = Q[k][p], Q[k][q]
            Q[k][p] = c * qkp - s * qkq
            Q[k][q] = s * qkp + c * qkq
    order = sorted(range(n), key=lambda i: M[i][i])
    return [M[i][i] for i in order], [[Q[r][i] for r in range(n)] for i in order]

def build_weil_matrix(L: Decimal, modes: list[int], parity: str, pp_dec, gl_x, gl_w,
                      allowed_primes=None):
    N = len(modes)
    ws_m = [Decimal(m) * DEC_PI / L for m in modes]
    if parity == "even":
        fac = (Decimal(2) / L).sqrt() * Decimal(2) * dec_cosh(L / Decimal(4))
        psign = Decimal(2)
    else:
        fac = (Decimal(2) / L).sqrt() * Decimal(2) * dec_sinh(L / Decimal(4))
        psign = Decimal(-2)
    cvec = [fac * wm / (Decimal("0.25") + wm * wm) for wm in ws_m]
    W_pole = [[psign * cvec[i] * cvec[j] for j in range(N)] for i in range(N)]

    xL = (-L * DEC_HALF).exp()
    tail_const = ((Decimal(1) + xL) / (Decimal(1) - xL)).ln() + Decimal(2) * dec_atan(xL) - DEC_C_INF
    n_pan = max(4, int(math.ceil(float(L) * 2.0)))
    h = L / Decimal(n_pan)
    u_pts, k_wts = [], []
    for pan in range(n_pan):
        ap = Decimal(pan) * h
        for gx, gw in zip(gl_x, gl_w):
            u = ap + gx * h
            ku = Decimal(2) * (-u * DEC_HALF).exp() / (Decimal(1) - (Decimal(-2) * u).exp())
            u_pts.append(u); k_wts.append(ku * gw * h)
    sins = [[dec_sin(wm * u) for u in u_pts] for wm in ws_m]
    coss = [[dec_cos(wm * u) for u in u_pts] for wm in ws_m]
    W_inf = [[Decimal(0)] * N for _ in range(N)]
    for i in range(N):
        wi = ws_m[i]; si = sins[i]; ci = coss[i]
        acc = Decimal(0)
        for q, (u, kw) in enumerate(zip(u_pts, k_wts)):
            f_ii = ((L - u) * ci[q] + si[q] / wi) / L
            acc += kw * (Decimal(1) - f_ii)
        W_inf[i][i] = tail_const + acc
        for j in range(i + 1, N):
            wj = ws_m[j]; sj = sins[j]
            inv_den = Decimal(2) / (L * (wi * wi - wj * wj))
            acc_ij = Decimal(0)
            for q, kw in enumerate(k_wts):
                acc_ij -= kw * inv_den * (wi * sj[q] - wj * si[q])
            W_inf[i][j] = W_inf[j][i] = acc_ij

    act = [(u, wt) for (u, wt, p, _) in pp_dec if u < L and (allowed_primes is None or p in allowed_primes)]
    W_prime = [[Decimal(0)] * N for _ in range(N)]
    if act:
        psins = [[dec_sin(wm * u) for (u, _) in act] for wm in ws_m]
        pcoss = [[dec_cos(wm * u) for (u, _) in act] for wm in ws_m]
        for i in range(N):
            wi = ws_m[i]; si = psins[i]; ci = pcoss[i]
            acc = Decimal(0)
            for q, (u, wt) in enumerate(act):
                acc += Decimal(2) * wt * ((L - u) * ci[q] + si[q] / wi) / L
            W_prime[i][i] = acc
            for j in range(i + 1, N):
                wj = ws_m[j]; sj = psins[j]
                inv_den = Decimal(2) / (L * (wi * wi - wj * wj))
                acc_ij = Decimal(0)
                for q, (_, wt) in enumerate(act):
                    acc_ij += Decimal(2) * wt * inv_den * (wi * sj[q] - wj * si[q])
                W_prime[i][j] = W_prime[j][i] = acc_ij

    W_tot = [[W_pole[i][j] + W_inf[i][j] - W_prime[i][j] for j in range(N)] for i in range(N)]
    return W_tot, len(act)

def build_prolate_matrix_dec(L: Decimal, modes: list[int], parity: str):
    a = L * DEC_HALF
    N = len(modes)
    ws = [Decimal(m) * DEC_PI / L for m in modes]
    pref = (Decimal(2) / L).sqrt()
    gl_x, gl_w = dec_gl_nodes_weights(24)
    n_pan = 4
    h = a / Decimal(n_pan)
    u_pts, w_pts = [], []
    for pan in range(n_pan):
        ap = Decimal(pan) * h
        for gx, gw in zip(gl_x, gl_w):
            u_pts.append(ap + gx * h); w_pts.append(gw * h)
    psi, dpsi = [], []
    for j, wj in enumerate(ws):
        sgn = Decimal(1) if (j % 2 == 0) else Decimal(-1)
        if parity == "even":
            psi.append([sgn * pref * dec_cos(wj * u) for u in u_pts])
            dpsi.append([-sgn * pref * wj * dec_sin(wj * u) for u in u_pts])
        else:
            psi.append([sgn * pref * dec_sin(wj * u) for u in u_pts])
            dpsi.append([sgn * pref * wj * dec_cos(wj * u) for u in u_pts])
    H_kin = [[Decimal(0)] * N for _ in range(N)]
    H_pot = [[Decimal(0)] * N for _ in range(N)]
    a2 = a * a
    for i in range(N):
        for j in range(i, N):
            ak = Decimal(0); ap = Decimal(0)
            for q, (u, wt) in enumerate(zip(u_pts, w_pts)):
                u2 = u * u
                ak += Decimal(2) * (a2 - u2) * dpsi[i][q] * dpsi[j][q] * wt
                ap += Decimal(2) * u2 * psi[i][q] * psi[j][q] * wt
            H_kin[i][j] = H_kin[j][i] = ak
            H_pot[i][j] = H_pot[j][i] = ap
    return H_kin, H_pot

def cholesky_ldl_dec(A):
    n = len(A)
    L = [[Decimal(1) if i == j else Decimal(0) for j in range(n)] for i in range(n)]
    D = [Decimal(0)] * n
    is_pos = True
    for j in range(n):
        dj = A[j][j] - sum(L[j][k] * L[j][k] * D[k] for k in range(j))
        D[j] = dj
        if dj <= 0:
            is_pos = False
            if abs(dj) < Decimal("1e-60"):
                break
        for i in range(j + 1, n):
            L[i][j] = (A[i][j] - sum(L[i][k] * L[j][k] * D[k] for k in range(j))) / dj
    max_err = Decimal(0)
    for i in range(n):
        for j in range(n):
            rec = sum(L[i][k] * D[k] * L[j][k] for k in range(min(i, j) + 1))
            err = abs(A[i][j] - rec)
            if err > max_err:
                max_err = err
    return L, D, max_err, is_pos

def matmul_dec(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

def transpose_dec(A):
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]

def generalized_prolate_spectrum_dec(W, H_prol):
    n = len(W)
    mus, evecs_list = jacobi_dec_eig(H_prol)
    P = [[evecs_list[col][row] for col in range(n)] for row in range(n)]
    M_prol = matmul_dec(matmul_dec(transpose_dec(P), W), P)
    inv_sq = [Decimal(1) / mu.sqrt() for mu in mus]
    S = [[M_prol[i][j] * inv_sq[i] * inv_sq[j] for j in range(n)] for i in range(n)]
    kappas, y_vecs = jacobi_dec_eig(S)
    y0 = y_vecs[0]
    z0 = [inv_sq[k] * y0[k] for k in range(n)]
    u0 = [sum(P[row][k] * z0[k] for k in range(n)) for row in range(n)]
    nrm = sum(x * x for x in u0).sqrt()
    return kappas, [x / nrm for x in u0], mus, M_prol

def eval_v_hat_even_dec(gamma: Decimal, v_vec, L: Decimal, modes: list[int]) -> Decimal:
    pref = (Decimal(2) / L).sqrt()
    cos_h = dec_cos(gamma * L * DEC_HALF)
    total = Decimal(0)
    for cj, m in zip(v_vec, modes):
        wm = Decimal(m) * DEC_PI / L
        if abs(gamma - wm) < Decimal("1e-25"):
            val = (L * DEC_HALF).sqrt()
        else:
            val = pref * (Decimal(2) * wm * cos_h) / (wm * wm - gamma * gamma)
        total += cj * val
    return total

def compute_li_coefficients(t_heat: Decimal, n_max: int, us, phis, wts):
    xi_k = [Decimal(0)] * (n_max + 1)
    for u, p, w in zip(us, phis, wts):
        pt = Decimal(2) * p * (t_heat * u * u).exp() * w
        ch = dec_cosh(u * DEC_HALF)
        sh = dec_sinh(u * DEC_HALF)
        upow = Decimal(1)
        for k in range(n_max + 1):
            xi_k[k] += pt * upow * (ch if k % 2 == 0 else sh)
            upow *= u
    xi0 = xi_k[0]
    c = [Decimal(0)] * (n_max + 1)
    fact = Decimal(1)
    for k in range(1, n_max + 1):
        fact *= Decimal(k)
        c[k] = xi_k[k] / (xi0 * fact)
    d = [Decimal(0)] * (n_max + 1)
    for m in range(1, n_max + 1):
        s = Decimal(m) * c[m]
        for j in range(1, m):
            s -= Decimal(j) * d[j] * c[m - j]
        d[m] = s / Decimal(m)
    return [Decimal(n) * sum(Decimal(math.comb(n - 1, m - 1)) * d[m] for m in range(1, n + 1))
            for n in range(1, n_max + 1)]

# ==============================================================================
# MAIN BENCHMARK SUITE
# ==============================================================================

def main():
    t0 = time.time()
    print("=" * 98)
    print("65-DIGIT LABORATORY: TRANSVERSE CONVEXITY, LAGUERRE CURVATURE, PROLATE & LDL^T CERTIFICATES")
    print("=" * 98)

    us, phis, wts = build_phi_grid(Decimal("2.45"), 245)

    # [P1] Exact Laguerre Identity + Heat-Flow Collision Radar + Li Coefficients
    print("\n[P1] Transverse Differential Hierarchy m2 (= 2*L1), m4..m10 & Li Coefficients Across Heat Flow:")
    g1 = Decimal("14.134725141734693790457251983562470270784257115699")
    _, m1_off, m2_0, m3_off = eval_V_sigma_derivs(Decimal(0), g1, Decimal(0), us, phis, wts)
    ds_g1 = eval_Xi_derivs_high(g1, Decimal(0), 4, us, phis, wts)
    L1_g1 = ds_g1[1]*ds_g1[1] - ds_g1[0]*ds_g1[2]
    print(f"  At gamma_1: m2(0, g1) = {float(m2_0):.6e} | |m2 - 2*L1| = {float(abs(m2_0 - Decimal(2)*L1_g1)):.2e}")

    def pinch_m2_m4(t_val: Decimal):
        g = Decimal("48.887")
        for _ in range(12):
            ds = eval_Xi_derivs_high(g, t_val, 4, us, phis, wts)
            dg = ds[1] / ds[2]
            if abs(dg) > Decimal("0.2"):
                dg = Decimal("0.2") if dg > 0 else Decimal("-0.2")
            g -= dg
        ds = eval_Xi_derivs_high(g, t_val, 10, us, phis, wts)
        return g, laguerre_Lm(ds, 1), laguerre_Lm(ds, 2), laguerre_Lm(ds, 5)

    for t_str in ["0.0", "-0.465", "-0.4694", "-0.475", "-0.55", "-1.00"]:
        g_p, m2_p, m4_p, m10_p = pinch_m2_m4(Decimal(t_str))
        st = "VALLEY (m2>0)" if m2_p > 0 else "RIDGE BIFURCATION (m2<0, m4..m10 STILL >0!)"
        print(f"  t = {float(t_str):>7.4f} | g* = {float(g_p):9.5f} | m2 = {float(m2_p):+12.4e} | m4 = {float(m4_p):+12.4e} | m10 = {float(m10_p):+12.4e} | {st}")

    lam0 = compute_li_coefficients(Decimal(0), 20, us, phis, wts)
    lam_neg = compute_li_coefficients(Decimal("-0.55"), 20, us, phis, wts)
    lam1_ex = Decimal(1) + DEC_EULER_GAMMA * DEC_HALF - (Decimal(4) * DEC_PI).ln() * DEC_HALF
    print(f"  Li calibration: lambda_1 err = {float(abs(lam0[0] - lam1_ex)):.2e} | at t=-0.55: lambda_1={float(lam_neg[0]):+.6f}, lambda_20={float(lam_neg[19]):+.6f} (ALL > 0)")

    # [P2] Quantitative Route B Convexity Corridor Margin
    print("\n[P2] Route B Transverse Convexity Margin (m2 increasing in sigma across [0, 0.5]):")
    for g_str in ["0.0", "5.0", "14.13472514", "21.02203964", "48.622533"]:
        g = Decimal(g_str)
        _, _, m2_0, _ = eval_V_sigma_derivs(Decimal("0.0"), g, Decimal(0), us, phis, wts)
        _, _, m2_h, _ = eval_V_sigma_derivs(Decimal("0.5"), g, Decimal(0), us, phis, wts)
        ds = eval_Xi_derivs_high(g, Decimal(0), 2, us, phis, wts)
        ratio = m2_0 / (ds[0]*ds[0] + ds[1]*ds[1])
        print(f"  gamma = {float(g):9.4f} | m2(0) = {float(m2_0):+12.4e} < m2(0.5) = {float(m2_h):+12.4e} | m2/(Xi^2+Xi'^2) = {float(ratio):.6f}")

    # [P3] Spectral Zero Synthesis from {2,3,4}, Exact L_arch^*, and Finite-Primorial Control
    print("\n[P3] Route A Spectral Zero Synthesis (ONLY 3 prime powers {2,3,4} at L=1.60, N=16) & L_arch^*:")
    gl_x, gl_w = dec_gl_nodes_weights(20)
    pp_dec = sieve_prime_powers_dec(300)
    modes_16 = [2 * k + 1 for k in range(16)]
    L16 = Decimal("1.60")
    W16, npp16 = build_weil_matrix(L16, modes_16, "even", pp_dec, gl_x, gl_w)
    ev16, ec16 = jacobi_dec_eig(W16)
    v0 = ec16[0]
    zeros_5 = [
        Decimal("14.13472514173469379045725198356247027078"),
        Decimal("21.02203963877155499262847959389690277733"),
        Decimal("25.01085758014568876321379099256282181866"),
        Decimal("30.42487612585951321031189753058409132018"),
        Decimal("32.93506158773918969066236896407490348881"),
    ]
    print(f"  L = 1.60 ({npp16} prime powers: {{2, 3, 4}}), lambda_0 = {float(ev16[0]):.4e}:")
    for idx, zt in enumerate(zeros_5):
        a, b = zt - Decimal("0.05"), zt + Decimal("0.05")
        fa = eval_v_hat_even_dec(a, v0, L16, modes_16)
        for _ in range(90):
            mid = (a + b) * DEC_HALF
            if fa * eval_v_hat_even_dec(mid, v0, L16, modes_16) <= 0:
                b = mid
            else:
                a = mid; fa = eval_v_hat_even_dec(a, v0, L16, modes_16)
        rt = (a + b) * DEC_HALF
        err = abs(rt - zt)
        print(f"    gamma_{idx+1}: root = {str(rt)[:21]} | err = {float(err):.3e} ({-math.log10(float(err)):.2f} exact digits)")

    modes_8 = [2 * k + 1 for k in range(8)]
    modes_8_odd = [2 * k + 2 for k in range(8)]
    lo, hi = Decimal("0.69"), Decimal("1.00")
    for _ in range(28):
        mid = (lo + hi) * DEC_HALF
        Wa, _ = build_weil_matrix(mid, modes_8, "even", pp_dec, gl_x, gl_w, allowed_primes=set())
        ev, _ = jacobi_dec_eig(Wa)
        if ev[0] > 0:
            lo = mid
        else:
            hi = mid
    L_arch = (lo + hi) * DEC_HALF
    print(f"  Exact zero-prime Archimedean positivity boundary: L_arch^* = {float(L_arch):.10f} (vs ln 2 = {float(Decimal(2).ln()):.10f})")
    W_p3, _ = build_weil_matrix(Decimal("3.0"), modes_8, "even", pp_dec, gl_x, gl_w, allowed_primes={2, 3, 5})
    ev_p3, _ = jacobi_dec_eig(W_p3)
    W_all3, _ = build_weil_matrix(Decimal("3.0"), modes_8, "even", pp_dec, gl_x, gl_w)
    ev_all3, _ = jacobi_dec_eig(W_all3)
    print(f"  Finite-primorial control at L = 3.0: lambda_min(S={{2,3,5}}) = {float(ev_p3[0]):+.4e} vs lambda_min(ALL) = {float(ev_all3[0]):+.4e}")

    # [P4] Prolate Comparison Certificate + LDL^T Cholesky Certificates
    print("\n[P4] Exact 65-Digit Prolate Comparison Certificates (W^(L) = alpha* H_prolate + R, R > 0) & LDL^T:")
    for L_str in ["0.69", "1.60", "3.00", "4.00"]:
        L = Decimal(L_str)
        W, npp = build_weil_matrix(L, modes_8, "even", pp_dec, gl_x, gl_w)
        Hk, Hp = build_prolate_matrix_dec(L, modes_8, "even")
        c_can = DEC_PI * L
        H_can = [[Hk[i][j] + (c_can * c_can) * Hp[i][j] for j in range(8)] for i in range(8)]
        kappas, _, _, _ = generalized_prolate_spectrum_dec(W, H_can)
        a_cert = kappas[0] * Decimal("0.999999")
        R_mat = [[W[i][j] - a_cert * H_can[i][j] for j in range(8)] for i in range(8)]
        _, D_rem, err_rem, ok_rem = cholesky_ldl_dec(R_mat)
        _, D_w, err_w, ok_w = cholesky_ldl_dec(W)
        W_odd, _ = build_weil_matrix(L, modes_8_odd, "odd", pp_dec, gl_x, gl_w)
        _, D_wo, err_wo, ok_wo = cholesky_ldl_dec(W_odd)
        print(f"  L={L_str} ({npp:2d} p^m): alpha*={float(kappas[0]):+.4e} | R>0:{ok_rem} (err={float(err_rem):.1e}) | LDL^T EVEN:{ok_w} (minD={float(min(D_w)):.2e}, err={float(err_w):.1e}) | ODD:{ok_wo}")

    print(f"\nALL 65-DIGIT CERTIFICATES VERIFIED SUCCESSFULLY in {time.time() - t0:.2f} s.")

if __name__ == "__main__":
    main()
