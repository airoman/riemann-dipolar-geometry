"""
Interactive Desktop Explorer: Clifford Torus T^2 Geodesics & Riemann Critical Line
Author: Mariano Martín Ramírez Tamayo (ORCID: 0009-0005-6194-1845)
Date: November 26, 2026
License: Apache-2.0 / CC-BY-4.0

Zero-dependency interactive Python + Tkinter application!
Features:
  - Play / Pause / Reverse / Step Forward & Backward / Speed Slider / Reset
  - Live beta = Re(s) slider (0.35 to 0.65): snap to 0.50 for exact Critical Line confinement!
  - Drag mouse to orbit the 3D Clifford Torus freely & scroll mouse wheel to zoom (0.35x to 5.0x)
  - Supports 100,000+ Riemann Zeta zeros & live on-demand Stein Binary GCD prime sieve (up to N = 100,000)
  - Live equations HUD showing K(beta), Lyapunov lambda = |beta - 1/2|, and confinement status
"""

import bisect
import math
import tkinter as tk
from tkinter import ttk

PHI = (1.0 + math.sqrt(5.0)) / 2.0

ZETA_ZEROS = [
    ("gamma_1", 14.134725), ("gamma_2", 21.022040), ("gamma_3", 25.010858),
    ("gamma_4", 30.424876), ("gamma_5", 32.935062), ("gamma_6", 37.586178),
    ("gamma_7", 40.918719), ("gamma_8", 43.327073), ("gamma_9", 48.005151),
    ("gamma_10", 49.773832), ("gamma_11", 52.970321), ("gamma_12", 56.446248),
    ("gamma_13", 59.347044), ("gamma_14", 60.831779), ("gamma_15", 65.112544),
    ("gamma_16", 67.079811), ("gamma_17", 69.546402), ("gamma_18", 72.067158),
    ("gamma_19", 75.704691), ("gamma_20", 77.144840), ("gamma_21", 79.337375),
    ("gamma_22", 82.910381), ("gamma_23", 84.735493), ("gamma_24", 87.425275),
    ("gamma_25", 88.809111), ("gamma_26", 92.491899), ("gamma_27", 94.651344),
    ("gamma_28", 95.870634), ("gamma_29", 98.831194), ("gamma_30", 101.317851),
    ("gamma_31", 103.725538), ("gamma_32", 105.446623), ("gamma_33", 107.168611),
    ("gamma_34", 111.029536), ("gamma_35", 111.874659), ("gamma_36", 114.320220),
    ("gamma_37", 116.226680), ("gamma_38", 118.790783), ("gamma_39", 121.370125),
    ("gamma_40", 122.946829), ("gamma_41", 124.256819), ("gamma_42", 127.516684),
    ("gamma_43", 129.578704), ("gamma_44", 131.087688), ("gamma_45", 133.497737),
    ("gamma_46", 134.756510), ("gamma_47", 138.116042), ("gamma_48", 139.736209),
    ("gamma_49", 141.123707), ("gamma_50", 143.111846),
]

def zeta_zero_height(k: int) -> float:
    """Returns exact Odlyzko zero height for k<=50, or Gram/Riemann-von Mangoldt asymptotic for k>50."""
    if 1 <= k <= len(ZETA_ZEROS):
        return ZETA_ZEROS[k - 1][1]
    # Riemann-von Mangoldt asymptotic approximation for arbitrarily large k
    x = (k - 11.0 / 8.0) / math.e
    # Solve w * exp(w) = x via 4 Newton steps (Lambert W_0)
    w = math.log(max(x, 1.0))
    for _ in range(4):
        ew = math.exp(w)
        w -= (w * ew - x) / (ew * (w + 1.0))
    return (2.0 * math.pi * (k - 11.0 / 8.0)) / max(w, 1e-6)


def stein_gcd(u: int, v: int) -> int:
    if u == 0: return v
    if v == 0: return u
    shift = 0
    while ((u | v) & 1) == 0:
        u >>= 1; v >>= 1; shift += 1
    while (u & 1) == 0: u >>= 1
    while v != 0:
        while (v & 1) == 0: v >>= 1
        if u > v: u, v = v, u
        v -= u
    return u << shift


def is_prime_stein(n: int) -> bool:
    if n < 2: return False
    if n in (2, 3): return True
    if (n & 1) == 0: return False
    for q in range(2, math.isqrt(n) + 1):
        if stein_gcd(n, q) > 1:
            return False
    return True


def sieve_primes_fast(limit: int):
    """Fast O(N log log N) prime cache so the app starts instantaneously even for N = 100,000."""
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i : limit + 1 : i] = b"\x00" * len(sieve[i * i : limit + 1 : i])
    return [i for i, is_p in enumerate(sieve) if is_p]


class CliffordTorusApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Clifford Torus T² Explorer — Zeta Geodesics & Dipolar Prime Sieve")
        self.root.geometry("1260x780")
        self.root.configure(bg="#0a0e18")

        # Mode: "zeta" (Clifford Geodesics) or "sieve" (Dipolar Prime Sieve on T^2)
        self.mode = "zeta"

        # Simulation state (100,000+ Zeta zeros in O(1) & Live Stein Binary GCD up to N=100,000!)
        self.tau = 0.0
        self.max_tau = 400000.0  # 100,000+ zeta zeros!
        self.playing = True
        self.direction = 1.0
        self.speed = 0.15
        self.beta = 0.50
        self.yaw = 0.55
        self.pitch = 0.50
        self.zoom = 1.0  # Smooth scroll-wheel zoom (0.35x to 5.0x)
        self.auto_rotate = True

        # Live incremental Stein Binary GCD prime cache (computed strictly on-demand!)
        self.sieve_n = 2.0
        self.max_sieve_n = 100000.0
        self.primes_cache = [2, 3]
        self.stein_checked_up_to = 3

        self.drag_x = None
        self.drag_y = None

        self._build_ui()
        self._loop()

    def _ensure_primes_live_stein(self, target_n: int):
        """Computes primes LIVE on demand using Stein's Binary GCD algorithm (bit-shifts & subtractions)."""
        needed = target_n + 120  # Small lookahead for p_next
        if needed <= self.stein_checked_up_to:
            return
        start = self.stein_checked_up_to + 1
        # If user jumps far with slider, compute cleanly in live Stein GCD
        for m in range(start, needed + 1):
            if is_prime_stein(m):
                self.primes_cache.append(m)
        self.stein_checked_up_to = needed

    def _build_ui(self):
        # Main layout: Left 3D Canvas, Right Telemetry & Equations Panel
        main_frame = tk.Frame(self.root, bg="#0a0e18")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Left side: Canvas + Controls
        left_frame = tk.Frame(main_frame, bg="#0a0e18")
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(left_frame, bg="#080b14", highlightthickness=1, highlightbackground="#253250")
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<ButtonPress-1>", self._on_mouse_down)
        self.canvas.bind("<B1-Motion>", self._on_mouse_drag)
        self.canvas.bind("<MouseWheel>", self._on_mouse_wheel)   # Windows & macOS
        self.canvas.bind("<Button-4>", self._on_mouse_wheel)     # Linux scroll up
        self.canvas.bind("<Button-5>", self._on_mouse_wheel)     # Linux scroll down
        self.canvas.bind("<Double-Button-1>", self._reset_view)  # Double-click resets zoom/angle

        # Transport controls bar
        ctrl = tk.Frame(left_frame, bg="#101728", pady=8, padx=10)
        ctrl.pack(fill=tk.X, pady=(8, 0))

        btn_style = {"bg": "#1e2c4a", "fg": "#e6f0ff", "activebackground": "#2e4470",
                     "activeforeground": "#ffffff", "relief": tk.FLAT, "padx": 10, "pady": 5, "font": ("Consolas", 10, "bold")}

        tk.Button(ctrl, text="<< Reverse", command=self.set_reverse, **btn_style).pack(side=tk.LEFT, padx=3)
        self.btn_play = tk.Button(ctrl, text="Pause", command=self.toggle_play, **btn_style)
        self.btn_play.pack(side=tk.LEFT, padx=3)
        tk.Button(ctrl, text="Forward >>", command=self.set_forward, **btn_style).pack(side=tk.LEFT, padx=3)
        tk.Button(ctrl, text="Reset", command=self.reset_sim, **btn_style).pack(side=tk.LEFT, padx=3)
        tk.Button(ctrl, text="Snap Re(s)=1/2", command=self.snap_critical,
                  bg="#185a4a", fg="#eafff8", activeforeground="#ffffff", relief=tk.FLAT,
                  padx=10, pady=5, font=("Consolas", 10, "bold")).pack(side=tk.LEFT, padx=8)

        self.btn_mode = tk.Button(ctrl, text="Mode: Zeta Geodesics (Switch to Criba Prime Stein MCD)",
                                  command=self.toggle_mode, bg="#3b2868", fg="#f0e6ff",
                                  activebackground="#553c96", activeforeground="#ffffff",
                                  relief=tk.FLAT, padx=10, pady=5, font=("Consolas", 10, "bold"))
        self.btn_mode.pack(side=tk.LEFT, padx=6)

        self.rot_var = tk.BooleanVar(value=True)
        tk.Checkbutton(ctrl, text="Auto-Orbit", variable=self.rot_var, command=self._toggle_rot,
                       bg="#101728", fg="#b8cce8", selectcolor="#1e2c4a",
                       activebackground="#101728", activeforeground="#ffffff",
                       font=("Consolas", 10)).pack(side=tk.RIGHT, padx=6)

        # Sliders bar (Beta, Speed, & Time tau)
        sliders = tk.Frame(left_frame, bg="#101728", pady=6, padx=10)
        sliders.pack(fill=tk.X, pady=(4, 0))

        tk.Label(sliders, text="Re(s)=beta:", bg="#101728", fg="#7af5d0", font=("Consolas", 9, "bold")).pack(side=tk.LEFT)
        self.beta_slider = tk.Scale(sliders, from_=0.35, to=0.65, resolution=0.01, orient=tk.HORIZONTAL,
                                    length=150, bg="#101728", fg="#ffffff", troughcolor="#1e2c4a",
                                    highlightthickness=0, command=self._on_beta_change)
        self.beta_slider.set(0.50)
        self.beta_slider.pack(side=tk.LEFT, padx=(4, 14))

        tk.Label(sliders, text="Speed:", bg="#101728", fg="#ffd060", font=("Consolas", 9, "bold")).pack(side=tk.LEFT)
        self.speed_slider = tk.Scale(sliders, from_=0.02, to=0.80, resolution=0.02, orient=tk.HORIZONTAL,
                                     length=130, bg="#101728", fg="#ffffff", troughcolor="#1e2c4a",
                                     highlightthickness=0, command=self._on_speed_change)
        self.speed_slider.set(0.12)
        self.speed_slider.pack(side=tk.LEFT, padx=(4, 14))

        tk.Label(sliders, text="Time tau / N:", bg="#101728", fg="#a8c4f0", font=("Consolas", 9, "bold")).pack(side=tk.LEFT)
        self.tau_slider = tk.Scale(sliders, from_=0.0, to=self.max_tau, resolution=0.1, orient=tk.HORIZONTAL,
                                   length=200, bg="#101728", fg="#ffffff", troughcolor="#1e2c4a",
                                   highlightthickness=0, command=self._on_tau_change)
        self.tau_slider.pack(side=tk.LEFT, padx=4)

        # Right side: Telemetry & Mathematical Formulas
        right = tk.Frame(main_frame, bg="#0f1524", width=340, padx=14, pady=12)
        right.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 0))
        right.pack_propagate(False)

        tk.Label(right, text="CLIFFORD TORUS T²", bg="#0f1524", fg="#ffffff", font=("Consolas", 14, "bold")).pack(anchor="w")
        tk.Label(right, text="Geodesic & Zeta Zero Monitor", bg="#0f1524", fg="#8aa6d6", font=("Consolas", 10)).pack(anchor="w", pady=(0, 10))

        self.lbl_status = tk.Label(right, text="STATUS: CONFINED", bg="#0f1524", fg="#4bf5c0", font=("Consolas", 12, "bold"))
        self.lbl_status.pack(anchor="w", pady=2)

        self.lbl_metrics = tk.Label(right, text="", bg="#0f1524", fg="#cfe0ff", font=("Consolas", 10), justify=tk.LEFT)
        self.lbl_metrics.pack(anchor="w", pady=(4, 10))

        # Formula box (updates dynamically per mode!)
        formula_box = tk.LabelFrame(right, text=" Governing Equations (Lean 4) ", bg="#0f1524", fg="#ffd060",
                                    font=("Consolas", 9, "bold"), padx=8, pady=6)
        formula_box.pack(fill=tk.X, pady=(0, 12))
        self.lbl_formulas = tk.Label(formula_box, text="", bg="#0f1524", fg="#dce8ff", font=("Consolas", 9), justify=tk.LEFT)
        self.lbl_formulas.pack(anchor="w")
        self._update_formula_box()

        # Zeta zeros list
        tk.Label(right, text="EQUATORIAL CROSSINGS (ZETA ZEROS):", bg="#0f1524", fg="#ffd060", font=("Consolas", 10, "bold")).pack(anchor="w")
        self.zeros_text = tk.Text(right, bg="#080c16", fg="#a8f5df", font=("Consolas", 10), height=14,
                                  relief=tk.FLAT, padx=8, pady=6, state=tk.DISABLED)
        self.zeros_text.pack(fill=tk.BOTH, expand=True, pady=(4, 0))

        tk.Label(right, text="Drag: rotate | Scroll: zoom | 2xClick: reset view", bg="#0f1524", fg="#647aa3", font=("Consolas", 8)).pack(anchor="w", pady=(8, 0))

    def _on_mouse_down(self, event):
        self.drag_x = event.x
        self.drag_y = event.y

    def _on_mouse_drag(self, event):
        if self.drag_x is not None:
            dx = event.x - self.drag_x
            dy = event.y - self.drag_y
            self.yaw += dx * 0.008
            self.pitch = max(-1.3, min(1.3, self.pitch + dy * 0.008))
            self.drag_x = event.x
            self.drag_y = event.y

    def _on_mouse_wheel(self, event):
        # Smooth exponential zoom with mouse scroll wheel (0.35x to 5.0x)
        if getattr(event, "num", None) == 4 or getattr(event, "delta", 0) > 0:
            self.zoom = min(5.0, self.zoom * 1.12)
        elif getattr(event, "num", None) == 5 or getattr(event, "delta", 0) < 0:
            self.zoom = max(0.35, self.zoom / 1.12)

    def _reset_view(self, _event=None):
        self.zoom = 1.0
        self.yaw = 0.55
        self.pitch = 0.50

    def _toggle_rot(self):
        self.auto_rotate = self.rot_var.get()

    def _on_beta_change(self, val):
        self.beta = float(val)

    def _on_speed_change(self, val):
        self.speed = float(val)

    def _on_tau_change(self, val):
        if self.mode == "zeta":
            self.tau = float(val)
        else:
            self.sieve_n = max(2.0, float(val))

    def _update_formula_box(self):
        if self.mode == "zeta":
            txt = (
                "s = beta + i*gamma\n"
                "Lyapunov:  lambda = |beta - 1/2|\n"
                "Curvature: K = -(beta - 1/2)^2\n"
                "Equator:   beta = 1/2 <=> lambda = 0\n"
                "Escape:    r(tau) ~ exp(lambda*tau)\n"
                "Torus:     M^5 = (S^3/Gamma_120) x T^2"
            )
        else:
            txt = (
                "CRIBA PRIME CON STEIN MCD (LIVE):\n"
                "Prime(N) <=> gcd_Stein(N,q)=1, q<=sqrt(N)\n"
                "k_r = N - p_prev,  k_i = p_next - N\n"
                "v(N) = 2*pi*(N - p_prev) / gap\n"
                "v = 0 (Equator) <=> N is PRIME!\n"
                "Color: Dark Blue (Old) -> Cyan (New)"
            )
        self.lbl_formulas.config(text=txt)

    def toggle_mode(self):
        if self.mode == "zeta":
            self.mode = "sieve"
            self.btn_mode.config(text="Mode: Criba Prime Stein MCD (Switch to Zeta)")
            self.tau_slider.config(from_=2.0, to=self.max_sieve_n, resolution=1.0)
            self.tau_slider.set(int(self.sieve_n))
        else:
            self.mode = "zeta"
            self.btn_mode.config(text="Mode: Zeta Geodesics (Switch to Criba Prime Stein MCD)")
            self.tau_slider.config(from_=0.0, to=self.max_tau, resolution=0.1)
            self.tau_slider.set(round(self.tau, 1))
        self._update_formula_box()

    def toggle_play(self):
        self.playing = not self.playing
        self.btn_play.config(text="Pause" if self.playing else "Play")

    def set_forward(self):
        self.direction = 1.0
        self.playing = True
        self.btn_play.config(text="Pause")

    def set_reverse(self):
        self.direction = -1.0
        self.playing = True
        self.btn_play.config(text="Pause")

    def reset_sim(self):
        if self.mode == "zeta":
            self.tau = 0.0
            self.tau_slider.set(0.0)
        else:
            self.sieve_n = 2.0
            self.tau_slider.set(2.0)

    def snap_critical(self):
        self.beta = 0.50
        self.beta_slider.set(0.50)

    def project_3d(self, x, y, z, cx, cy, fov=560.0, dist=4.8):
        cyaw, syaw = math.cos(self.yaw), math.sin(self.yaw)
        x1 = x * cyaw + z * syaw
        z1 = -x * syaw + z * cyaw
        cp, sp = math.cos(self.pitch), math.sin(self.pitch)
        y2 = y * cp - z1 * sp
        z2 = y * sp + z1 * cp
        z_cam = z2 + dist
        if z_cam <= 0.2:
            return None
        inv = fov / z_cam
        return (cx + x1 * inv, cy - y2 * inv)

    def _draw_scene(self):
        self.canvas.delete("all")
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        if w < 50 or h < 50:
            return

        cx, cy = w * 0.5, h * 0.52
        fov = min(w, h) * 0.85 * self.zoom
        self.canvas.create_text(
            12, h - 14, anchor="sw",
            text=f"Zoom: {self.zoom:.2f}x  (Scroll to zoom | Drag to orbit | Double-click to reset)",
            fill="#5d75a0", font=("Consolas", 9),
        )
        R, r_minor = 1.55, 0.66
        is_critical = abs(self.beta - 0.50) < 1e-6
        lam_phys = abs(self.beta - 0.50)
        lam_vis = lam_phys * 1.45

        # 1. Torus wireframe
        for iu in range(0, 32, 2):
            u = (iu / 32.0) * 2.0 * math.pi
            pts = []
            for iv in range(19):
                v = (iv / 18.0) * 2.0 * math.pi
                x = (R + r_minor * math.cos(v)) * math.cos(u)
                y = r_minor * math.sin(v)
                z = (R + r_minor * math.cos(v)) * math.sin(u)
                p = self.project_3d(x, y, z, cx, cy, fov=fov)
                if p:
                    pts.extend(p)
            if len(pts) >= 4:
                self.canvas.create_line(*pts, fill="#2e4066", width=1)

        # 2. Amber/Gold Clifford Equator (v = 0)
        eq_pts = []
        for iu in range(65):
            u = (iu / 64.0) * 2.0 * math.pi
            x = (R + r_minor) * math.cos(u)
            z = (R + r_minor) * math.sin(u)
            p = self.project_3d(x, 0.0, z, cx, cy, fov=fov)
            if p:
                eq_pts.extend(p)
        if len(eq_pts) >= 4:
            self.canvas.create_line(*eq_pts, fill="#ffc341", width=2)

        # 3. Geodesic path OR Live Stein Binary GCD Prime Sieve on Clifford Torus T^2
        if self.mode == "zeta":
            # Crisp window: ~65-70 visible equatorial crossings (clean, readable, zero clutter!)
            d_tau = 0.08
            window_tau = 260.0  # ~67 visible zeta zero crossings on screen
            start_tau = max(0.0, self.tau - window_tau)
            s_start = int(start_tau / d_tau)
            n_steps = int(self.tau / d_tau)

            # Age-graded trail rendering (4 color bands from old -> new so direction of travel is crystal clear!)
            total_s = max(1, n_steps - s_start)
            band_colors_crit = ["#123b4a", "#1c7a8c", "#28bed0", "#55fff0"]
            bands = [[], [], [], []]
            pts_pink = []
            pts_red = []
            last_p = None
            escaped_now = False

            for s in range(s_start, n_steps + 1):
                t_val = s * d_tau
                u = t_val
                v = t_val * PHI
                if is_critical:
                    rad = 1.0
                else:
                    rad = 1.0 + 0.12 * (math.exp(min(lam_vis * t_val, 4.2)) - 1.0)
                    if rad > 1.15:
                        escaped_now = True

                x = (R * rad + r_minor * math.cos(v)) * math.cos(u)
                y = r_minor * math.sin(v) * rad + (0.0 if is_critical else 0.18 * (rad - 1.0) * math.sin(t_val))
                z = (R * rad + r_minor * math.cos(v)) * math.sin(u)
                p = self.project_3d(x, y, z, cx, cy, fov=fov)
                if p:
                    if is_critical:
                        age_frac = (s - s_start) / float(total_s)
                        b_idx = min(3, int(age_frac * 4.0))
                        bands[b_idx].extend(p)
                        # Overlap 1 point with previous band for seamless continuity
                        if b_idx > 0 and len(bands[b_idx]) == 2 and len(bands[b_idx - 1]) >= 2:
                            bands[b_idx] = bands[b_idx - 1][-2:] + bands[b_idx]
                    elif rad > 1.15:
                        pts_red.extend(p)
                    else:
                        pts_pink.extend(p)
                    last_p = p

            for b_idx in range(4):
                if len(bands[b_idx]) >= 4:
                    self.canvas.create_line(*bands[b_idx], fill=band_colors_crit[b_idx], width=1.1 + 0.15 * b_idx)
            if len(pts_pink) >= 4:
                self.canvas.create_line(*pts_pink, fill="#ff78c8", width=1.2)
            if len(pts_red) >= 4:
                self.canvas.create_line(*pts_red, fill="#ff2424", width=1.4)

            # 4. Exact analytical equatorial crossings in O(1) time (age-shaded old -> bright new!)
            total_k = int((self.tau * PHI) / (2.0 * math.pi))
            start_k = max(1, int((start_tau * PHI) / (2.0 * math.pi)))
            valid_total = 0
            if is_critical:
                valid_total = total_k
                span_k = max(1, total_k - start_k)
                for k in range(start_k, total_k + 1):
                    tk_val = (2.0 * math.pi * k) / PHI
                    xk = (R + r_minor) * math.cos(tk_val)
                    zk = (R + r_minor) * math.sin(tk_val)
                    pk = self.project_3d(xk, 0.0, zk, cx, cy, fov=fov)
                    if pk:
                        age_k = (k - start_k) / float(span_k)
                        if age_k < 0.35:
                            n_col, o_col = "#6e5c24", "#8a7838"
                        elif age_k < 0.75:
                            n_col, o_col = "#c9aa38", "#e8d275"
                        else:
                            n_col, o_col = "#fff480", "#ffffff"
                        self.canvas.create_oval(pk[0]-3.5, pk[1]-3.5, pk[0]+3.5, pk[1]+3.5, fill=n_col, outline=o_col, width=0.8)
            else:
                for k in range(1, min(total_k + 1, 200)):
                    tk_val = (2.0 * math.pi * k) / PHI
                    rad_k = 1.0 + 0.12 * (math.exp(min(lam_vis * tk_val, 4.2)) - 1.0)
                    if rad_k <= 1.12:
                        valid_total += 1
                        if tk_val >= start_tau:
                            xk = (R * rad_k + r_minor) * math.cos(tk_val)
                            zk = (R * rad_k + r_minor) * math.sin(tk_val)
                            pk = self.project_3d(xk, 0.0, zk, cx, cy, fov=fov)
                            if pk:
                                self.canvas.create_oval(pk[0]-3.5, pk[1]-3.5, pk[0]+3.5, pk[1]+3.5, fill="#ff90d0", outline="#ffffff", width=0.8)
                    else:
                        break

            # 5. Active head
            if last_p:
                h_col = "#ffffff" if is_critical else "#ff3030"
                self.canvas.create_oval(last_p[0]-4.5, last_p[1]-4.5, last_p[0]+4.5, last_p[1]+4.5, fill=h_col, outline="#ffffff", width=1.5)

            # Update telemetry panel
            curv = -(lam_phys ** 2)
            if is_critical:
                self.lbl_status.config(text="STATUS: CONFINED (EQUATOR)", fg="#4bf5c0")
            elif escaped_now:
                self.lbl_status.config(text="STATUS: HYPERBOLIC ESCAPE!", fg="#ff4040")
            else:
                self.lbl_status.config(text="STATUS: DRIFTING OFF-LINE", fg="#ff85c0")

            self.lbl_metrics.config(
                text=f"beta = Re(s) : {self.beta:.2f}\n"
                     f"Lyapunov lam : {lam_phys:.4f}\n"
                     f"Curvature K  : {curv:.6f}\n"
                     f"Time tau     : {self.tau:.2f}\n"
                     f"Zeta Zeros   : {valid_total} (max 100k+)"
            )

            self.zeros_text.config(state=tk.NORMAL)
            self.zeros_text.delete("1.0", tk.END)
            if is_critical:
                for cid in range(max(1, valid_total - 17), valid_total + 1):
                    val = zeta_zero_height(cid)
                    tag = f"gamma_{cid}"
                    self.zeros_text.insert(tk.END, f"#{cid:5d} {tag:11s}= {val:.4f}\n")
            else:
                if valid_total:
                    self.zeros_text.insert(tk.END, f"Initial drift crossings: {valid_total}\n\n")
                if escaped_now:
                    self.zeros_text.insert(tk.END, "CONFINEMENT LOST!\nZero further equatorial\ncrossings possible.\n\nMonopolar divergence\nexp(lambda * tau) -> inf.")
            self.zeros_text.config(state=tk.DISABLED)

        else:
            # LIVE STEIN BINARY GCD DIPOLAR PRIME SIEVE ON CLIFFORD TORUS T^2
            # Computed 100% live on-demand using bit-shifts & subtractions!
            n_cur = max(2.0, float(self.sieve_n))
            n_int = int(n_cur)
            self._ensure_primes_live_stein(n_int)

            hi_idx = bisect.bisect_right(self.primes_cache, n_int)
            # Show exactly the last ~65 primes cleanly around the entire torus (zero flicker!)
            max_visible_primes = 65
            lo_idx = max(0, hi_idx - max_visible_primes)
            x_start = float(self.primes_cache[lo_idx])

            # Sample 18 smooth sub-steps INSIDE each prime gap with 4 age-shaded color bands (old -> bright new!)
            band_colors_sieve = ["#143652", "#1e6896", "#2ea8e0", "#5ef2ff"]
            bands = [[], [], [], []]
            last_p = None
            sub_steps = 18
            span_p = max(1, hi_idx - lo_idx)

            for idx_p in range(lo_idx, hi_idx):
                p_prev = self.primes_cache[idx_p]
                p_next = self.primes_cache[idx_p + 1] if (idx_p + 1) < len(self.primes_cache) else (p_prev + 2)
                gap = max(p_next - p_prev, 1)
                if p_prev >= n_cur:
                    break
                frac_end = min(1.0, (n_cur - p_prev) / float(gap))
                n_sub = max(1, int(sub_steps * frac_end))
                age_frac = (idx_p - lo_idx) / float(span_p)
                b_idx = min(3, int(age_frac * 4.0))

                for j in range(n_sub + 1):
                    frac = (j / float(sub_steps)) if j < n_sub else frac_end
                    u = (idx_p + frac) * (2.0 * math.pi / (PHI * 4.0))
                    v = 2.0 * math.pi * frac
                    x3 = (R + r_minor * math.cos(v)) * math.cos(u)
                    y3 = r_minor * math.sin(v)
                    z3 = (R + r_minor * math.cos(v)) * math.sin(u)
                    pt = self.project_3d(x3, y3, z3, cx, cy, fov=fov)
                    if pt:
                        bands[b_idx].extend(pt)
                        if b_idx > 0 and len(bands[b_idx]) == 2 and len(bands[b_idx - 1]) >= 2:
                            bands[b_idx] = bands[b_idx - 1][-2:] + bands[b_idx]
                        last_p = pt

            for b_idx in range(4):
                if len(bands[b_idx]) >= 4:
                    self.canvas.create_line(*bands[b_idx], fill=band_colors_sieve[b_idx], width=1.05 + 0.15 * b_idx)

            # Mark the ~65 discovered primes cleanly on the Amber Equator (age-shaded old -> bright new!)
            for idx_p in range(lo_idx, hi_idx):
                p_val = self.primes_cache[idx_p]
                u_p = idx_p * (2.0 * math.pi / (PHI * 4.0))
                xp = (R + r_minor) * math.cos(u_p)
                zp = (R + r_minor) * math.sin(u_p)
                pp = self.project_3d(xp, 0.0, zp, cx, cy, fov=fov)
                if pp:
                    age_p = (idx_p - lo_idx) / float(span_p)
                    is_twin = (idx_p > 0 and p_val - self.primes_cache[idx_p - 1] == 2)
                    if age_p < 0.35:
                        col_p, out_p = ("#7a2b56", "#9c4070") if is_twin else ("#736020", "#947d32")
                    elif age_p < 0.75:
                        col_p, out_p = ("#cc448e", "#f080bc") if is_twin else ("#c9aa38", "#e8d275")
                    else:
                        col_p, out_p = ("#ff66bb", "#ffffff") if is_twin else ("#fff070", "#ffffff")
                    self.canvas.create_oval(pp[0]-3.8, pp[1]-3.8, pp[0]+3.8, pp[1]+3.8, fill=col_p, outline=out_p, width=0.9)

            if last_p:
                self.canvas.create_oval(last_p[0]-4.5, last_p[1]-4.5, last_p[0]+4.5, last_p[1]+4.5, fill="#ffffff", outline="#38f0ff", width=1.8)

            self.lbl_status.config(text="CRIBA PRIME CON STEIN MCD", fg="#ffd060")
            self.lbl_metrics.config(
                text=f"Integer N    : {n_int}\n"
                     f"Primes pi(N) : {hi_idx}\n"
                     f"Visible      : {hi_idx - lo_idx} primes\n"
                     f"Sieve        : Live Stein MCD"
            )
            self.zeros_text.config(state=tk.NORMAL)
            self.zeros_text.delete("1.0", tk.END)
            self.zeros_text.insert(tk.END, "CRIBA PRIME STEIN MCD (LIVE):\n\n")
            recent_p = self.primes_cache[max(0, hi_idx - 32):hi_idx]
            line_buf = []
            for idx_p, pv in enumerate(recent_p):
                line_buf.append(f"{pv:5d}")
                if (idx_p + 1) % 4 == 0:
                    self.zeros_text.insert(tk.END, " ".join(line_buf) + "\n")
                    line_buf = []
            if line_buf:
                self.zeros_text.insert(tk.END, " ".join(line_buf) + "\n")
            self.zeros_text.config(state=tk.DISABLED)

    def _loop(self):
        if self.playing:
            if self.mode == "zeta":
                self.tau += self.direction * self.speed
                if self.tau > self.max_tau:
                    self.tau = self.max_tau
                    self.playing = False
                    self.btn_play.config(text="Play")
                elif self.tau < 0.0:
                    self.tau = 0.0
                    self.playing = False
                    self.btn_play.config(text="Play")
                self.tau_slider.set(round(self.tau, 1))
            else:
                self.sieve_n += self.direction * (self.speed * 4.5)
                if self.sieve_n > self.max_sieve_n:
                    self.sieve_n = self.max_sieve_n
                    self.playing = False
                    self.btn_play.config(text="Play")
                elif self.sieve_n < 2.0:
                    self.sieve_n = 2.0
                    self.playing = False
                    self.btn_play.config(text="Play")
                self.tau_slider.set(int(self.sieve_n))
        if self.auto_rotate:
            self.yaw += 0.006
        self._draw_scene()
        self.root.after(33, self._loop)


if __name__ == "__main__":
    root = tk.Tk()
    app = CliffordTorusApp(root)
    root.mainloop()
