"""
Pure Python + FFmpeg High-Definition Animation Generator (Zero External Dependencies)
Generates 3 full-width publication-grade animations (.mp4 & .gif) visualizing:
  1. Dipolar Prime Lattice (Past-Future Symmetry, Goldbach Centers D=0, Twin Primes E=2)
     - Advances up to N = 250 with crisp pixel-font prime numbers & live N/p readout.
  2. Clifford Torus T^2 Geodesics (Critical Line beta=1/2 Equilibrium vs. Hyperbolic Escape)
     - Brighter torus wireframe, marked equatorial crossings, and color transition
       from pink/magenta on the torus to intense crimson red upon hyperbolic escape.
  3. Golden Ratio Spiral on the 5D Manifold M^5 = (S^3 / Gamma_120) x T^2 (KAM Stability)

Author: Mariano Martín Ramírez Tamayo (ORCID: 0009-0005-6194-1845)
License: Apache-2.0 / CC-BY-4.0
"""

import math
import os
import subprocess

WIDTH = 1280
HEIGHT = 720
FPS = 30
OUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "figures", "animations")

# Crisp 5x7 bitmap font for zero-dependency HUD labels and prime numbers
FONT_5X7 = {
    '0': ["01110", "10001", "10011", "10101", "11001", "10001", "01110"],
    '1': ["00100", "01100", "00100", "00100", "00100", "00100", "01110"],
    '2': ["01110", "10001", "00001", "00110", "01000", "10000", "11111"],
    '3': ["11110", "00001", "00001", "01110", "00001", "00001", "11110"],
    '4': ["00010", "00110", "01010", "10010", "11111", "00010", "00010"],
    '5': ["11111", "10000", "11110", "00001", "00001", "10001", "01110"],
    '6': ["00110", "01000", "10000", "11110", "10001", "10001", "01110"],
    '7': ["11111", "00001", "00010", "00100", "01000", "01000", "01000"],
    '8': ["01110", "10001", "10001", "01110", "10001", "10001", "01110"],
    '9': ["01110", "10001", "10001", "01111", "00001", "00010", "01100"],
    'A': ["01110", "10001", "10001", "11111", "10001", "10001", "10001"],
    'B': ["11110", "10001", "10001", "11110", "10001", "10001", "11110"],
    'C': ["01110", "10001", "10000", "10000", "10000", "10001", "01110"],
    'D': ["11100", "10010", "10001", "10001", "10001", "10010", "11100"],
    'E': ["11111", "10000", "10000", "11110", "10000", "10000", "11111"],
    'F': ["11111", "10000", "10000", "11110", "10000", "10000", "10000"],
    'G': ["01110", "10001", "10000", "10111", "10001", "10001", "01110"],
    'H': ["10001", "10001", "10001", "11111", "10001", "10001", "10001"],
    'I': ["01110", "00100", "00100", "00100", "00100", "00100", "01110"],
    'K': ["10001", "10010", "10100", "11000", "10100", "10010", "10001"],
    'L': ["10000", "10000", "10000", "10000", "10000", "10000", "11111"],
    'M': ["10001", "11011", "10101", "10101", "10001", "10001", "10001"],
    'N': ["10001", "11001", "10101", "10011", "10001", "10001", "10001"],
    'O': ["01110", "10001", "10001", "10001", "10001", "10001", "01110"],
    'P': ["11110", "10001", "10001", "11110", "10000", "10000", "10000"],
    'Q': ["01110", "10001", "10001", "10001", "10101", "10010", "01101"],
    'R': ["11110", "10001", "10001", "11110", "10100", "10010", "10001"],
    'S': ["01111", "10000", "10000", "01110", "00001", "00001", "11110"],
    'T': ["11111", "00100", "00100", "00100", "00100", "00100", "00100"],
    'U': ["10001", "10001", "10001", "10001", "10001", "10001", "01110"],
    'V': ["10001", "10001", "10001", "10001", "10001", "01010", "00100"],
    'W': ["10001", "10001", "10001", "10101", "10101", "11011", "10001"],
    'X': ["10001", "10001", "01010", "00100", "01010", "10001", "10001"],
    'Y': ["10001", "10001", "01010", "00100", "00100", "00100", "00100"],
    'Z': ["11111", "00001", "00010", "00100", "01000", "10000", "11111"],
    '=': ["00000", "00000", "11111", "00000", "11111", "00000", "00000"],
    '!': ["00100", "00100", "00100", "00100", "00100", "00000", "00100"],
    '/': ["00001", "00010", "00010", "00100", "01000", "01000", "10000"],
    '.': ["00000", "00000", "00000", "00000", "00000", "01100", "01100"],
    ',': ["00000", "00000", "00000", "00000", "00100", "00100", "01000"],
    ':': ["00000", "00100", "00100", "00000", "00100", "00100", "00000"],
    '-': ["00000", "00000", "00000", "11111", "00000", "00000", "00000"],
    '+': ["00000", "00100", "00100", "11111", "00100", "00100", "00000"],
    '(': ["00010", "00100", "01000", "01000", "01000", "00100", "00010"],
    ')': ["01000", "00100", "00010", "00010", "00010", "00100", "01000"],
    '>': ["10000", "01000", "00100", "00010", "00100", "01000", "10000"],
    ' ': ["00000", "00000", "00000", "00000", "00000", "00000", "00000"],
}


def clamp(v, lo=0, hi=255):
    return lo if v < lo else (hi if v > hi else int(v))


class Canvas:
    """Fast RGB24 software rasterizer using pure Python bytearray."""
    def __init__(self, w, h, bg=(10, 14, 24)):
        self.w = w
        self.h = h
        self.bg = bg
        self.buf = bytearray(w * h * 3)
        self.clear()

    def clear(self):
        r, g, b = self.bg
        row = bytes([r, g, b]) * self.w
        self.buf[:] = row * self.h

    def blend_pixel(self, x, y, r, g, b, alpha=1.0):
        if 0 <= x < self.w and 0 <= y < self.h:
            idx = (y * self.w + x) * 3
            if alpha >= 0.999:
                self.buf[idx] = r
                self.buf[idx + 1] = g
                self.buf[idx + 2] = b
            else:
                inv = 1.0 - alpha
                self.buf[idx] = clamp(self.buf[idx] * inv + r * alpha)
                self.buf[idx + 1] = clamp(self.buf[idx + 1] * inv + g * alpha)
                self.buf[idx + 2] = clamp(self.buf[idx + 2] * inv + b * alpha)

    def add_pixel(self, x, y, r, g, b, intensity=1.0):
        if 0 <= x < self.w and 0 <= y < self.h:
            idx = (y * self.w + x) * 3
            self.buf[idx] = clamp(self.buf[idx] + r * intensity)
            self.buf[idx + 1] = clamp(self.buf[idx + 1] + g * intensity)
            self.buf[idx + 2] = clamp(self.buf[idx + 2] + b * intensity)

    def draw_text(self, x, y, text, color, scale=2, alpha=1.0):
        r, g, b = color
        cx = int(x)
        cy = int(y)
        for ch in text.upper():
            glyph = FONT_5X7.get(ch, FONT_5X7[' '])
            for row_i, row in enumerate(glyph):
                for col_i, bit in enumerate(row):
                    if bit == '1':
                        for sy in range(scale):
                            for sx in range(scale):
                                self.blend_pixel(cx + col_i * scale + sx, cy + row_i * scale + sy, r, g, b, alpha)
            cx += 6 * scale

    def draw_line(self, x0, y0, x1, y1, color, alpha=1.0, additive=False, thick=False):
        r, g, b = color
        x0, y0, x1, y1 = int(x0), int(y0), int(x1), int(y1)
        dx = abs(x1 - x0)
        dy = -abs(y1 - y0)
        sx = 1 if x0 < x1 else -1
        sy = 1 if y0 < y1 else -1
        err = dx + dy
        while True:
            if additive:
                self.add_pixel(x0, y0, r, g, b, alpha)
                if thick:
                    self.add_pixel(x0 + 1, y0, r, g, b, alpha * 0.65)
                    self.add_pixel(x0, y0 + 1, r, g, b, alpha * 0.65)
            else:
                self.blend_pixel(x0, y0, r, g, b, alpha)
                if thick:
                    self.blend_pixel(x0 + 1, y0, r, g, b, alpha * 0.65)
                    self.blend_pixel(x0, y0 + 1, r, g, b, alpha * 0.65)
            if x0 == x1 and y0 == y1:
                break
            e2 = 2 * err
            if e2 >= dy:
                err += dy
                x0 += sx
            if e2 <= dx:
                err += dx
                y0 += sy

    def draw_circle(self, cx, cy, radius, color, alpha=1.0, glow=False):
        r, g, b = color
        cx, cy = int(cx), int(cy)
        rad = int(radius)
        r2 = radius * radius
        for dy in range(-rad, rad + 1):
            yy = cy + dy
            if yy < 0 or yy >= self.h:
                continue
            for dx in range(-rad, rad + 1):
                xx = cx + dx
                if xx < 0 or xx >= self.w:
                    continue
                d2 = dx * dx + dy * dy
                if d2 <= r2:
                    if glow:
                        falloff = max(0.0, 1.0 - math.sqrt(d2) / max(radius, 1e-6))
                        self.add_pixel(xx, yy, r, g, b, alpha * (falloff ** 1.5))
                    else:
                        self.blend_pixel(xx, yy, r, g, b, alpha)


def open_ffmpeg_mp4(path, w, h, fps):
    cmd = [
        "ffmpeg", "-y",
        "-f", "rawvideo",
        "-vcodec", "rawvideo",
        "-s", f"{w}x{h}",
        "-pix_fmt", "rgb24",
        "-r", str(fps),
        "-i", "-",
        "-c:v", "libx264",
        "-pix_fmt", "yuv420p",
        "-crf", "18",
        "-preset", "fast",
        path
    ]
    return subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def mp4_to_gif(mp4_path, gif_path, width=960, fps=20):
    palette = gif_path + ".palette.png"
    subprocess.run([
        "ffmpeg", "-y", "-i", mp4_path,
        "-vf", f"fps={fps},scale={width}:-1:flags=lanczos,palettegen",
        palette
    ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
    subprocess.run([
        "ffmpeg", "-y", "-i", mp4_path, "-i", palette,
        "-lavfi", f"fps={fps},scale={width}:-1:flags=lanczos[x];[x][1:v]paletteuse=dither=bayer",
        gif_path
    ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
    if os.path.exists(palette):
        os.remove(palette)


def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0: return False
    for q in range(3, math.isqrt(n) + 1, 2):
        if n % q == 0: return False
    return True


def generate_video_1_dipolar_lattice():
    """Video 1: Dipolar Prime Lattice up to N=250 with live prime numbers, Goldbach D=0, Twin E=2."""
    print("[1/3] Rendering Video 1: Dipolar Prime Lattice (N = 2..250)...")
    mp4_path = os.path.join(OUT_DIR, "01_dipolar_prime_lattice.mp4")
    gif_path = os.path.join(OUT_DIR, "01_dipolar_prime_lattice.gif")

    N_MAX = 250
    primes = [n for n in range(2, N_MAX + 30) if is_prime(n)]
    data = []
    found_primes_at = []
    cur_primes = []
    for n in range(2, N_MAX + 1):
        pp = max(p for p in primes if p <= n)
        pn = min(p for p in primes if p >= n)
        kr = n - pp
        ki = pn - n
        if kr == 0 and ki == 0:
            cur_primes.append(n)
        data.append((n, pp, pn, kr, ki, ki - kr, kr * kr + ki * ki))
        found_primes_at.append(list(cur_primes))

    proc = open_ffmpeg_mp4(mp4_path, WIDTH, HEIGHT, FPS)
    canvas = Canvas(WIDTH, HEIGHT, bg=(10, 14, 24))

    total_frames = 360  # 12 seconds at 30 fps
    ox, oy = 110, HEIGHT - 90
    scale = 36.0  # covers up to k_r, k_i = 14 (gap up to 14 like 113->127)

    for f in range(total_frames):
        canvas.clear()
        progress = f / float(total_frames - 1)
        max_idx = progress * (len(data) - 1)
        last_i = int(max_idx)

        # Draw grid and axis ticks
        for k in range(0, 15):
            gx = ox + int(k * scale)
            gy = oy - int(k * scale)
            if gx < WIDTH - 320:
                canvas.draw_line(gx, oy, gx, 65, (28, 38, 60), 0.7)
                if k % 2 == 0:
                    canvas.draw_text(gx - 6, oy + 14, str(k), (130, 150, 190), scale=2)
            if gy > 65:
                canvas.draw_line(ox, gy, WIDTH - 320, gy, (28, 38, 60), 0.7)
                if k % 2 == 0:
                    canvas.draw_text(ox - 38, gy - 6, str(k), (130, 150, 190), scale=2)

        # Goldbach Symmetry Axis (k_r = k_i, D(N) = 0)
        canvas.draw_line(ox, oy, ox + int(14 * scale), oy - int(14 * scale), (50, 220, 165), 0.65, thick=True)
        canvas.draw_text(ox + int(8.2 * scale), oy - int(9.2 * scale), "GOLDBACH AXIS D=0", (70, 235, 180), scale=2)

        # Main axes
        canvas.draw_line(ox, oy, WIDTH - 310, oy, (150, 175, 220), 0.95, thick=True)
        canvas.draw_line(ox, oy, ox, 60, (150, 175, 220), 0.95, thick=True)
        canvas.draw_text(WIDTH - 510, oy + 36, "PAST GAP DIST KR = N - P_PREV", (160, 185, 230), scale=2)
        canvas.draw_text(20, 42, "FUTURE KI = P_NEXT - N", (160, 185, 230), scale=2)

        # Title HUD
        canvas.draw_text(ox, 16, "DIPOLAR PRIME LATTICE (GAP SPACE KR VS KI, N=2..250)", (235, 245, 255), scale=2)

        # Draw trail of visited points
        for i in range(last_i):
            _, _, _, kr1, ki1, _, _ = data[i]
            _, _, _, kr2, ki2, _, _ = data[i + 1]
            x1, y1 = ox + kr1 * scale, oy - ki1 * scale
            x2, y2 = ox + kr2 * scale, oy - ki2 * scale
            age = (last_i - i) / max(last_i, 1)
            alpha = max(0.18, 1.0 - age * 0.75)
            col = (255, 200, 75) if (kr2 == 0 and ki2 == 0) else (75, 205, 255)
            canvas.draw_line(x1, y1, x2, y2, col, alpha * 0.75, additive=True, thick=True)

        # Highlight Goldbach (D=0) & Twin Primes (E=2)
        for i in range(last_i + 1):
            n, _, _, kr, ki, d, e = data[i]
            px, py = ox + kr * scale, oy - ki * scale
            if kr == 0 and ki == 0:
                canvas.draw_circle(px, py, 14, (255, 220, 90), 0.25, glow=True)
            elif e == 2:
                canvas.draw_circle(px, py, 16, (255, 85, 165), 0.45, glow=True)
                canvas.draw_circle(px, py, 5, (255, 195, 230), 0.95)
            elif d == 0:
                canvas.draw_circle(px, py, 12, (60, 255, 185), 0.40, glow=True)
                canvas.draw_circle(px, py, 4, (190, 255, 225), 0.95)

        # Interpolated active head
        frac = max_idx - last_i
        n_cur, pp_cur, pn_cur, kr1, ki1, d_cur, e_cur = data[last_i]
        if last_i + 1 < len(data):
            _, _, _, kr2, ki2, _, _ = data[last_i + 1]
            cur_kr = kr1 + (kr2 - kr1) * frac
            cur_ki = ki1 + (ki2 - ki1) * frac
        else:
            cur_kr, cur_ki = kr1, ki1

        hx, hy = ox + cur_kr * scale, oy - cur_ki * scale
        canvas.draw_circle(hx, hy, 22, (110, 230, 255), 0.8, glow=True)
        canvas.draw_circle(hx, hy, 6, (255, 255, 255), 1.0)

        # Right-side live telemetry & discovered primes panel
        rx = WIDTH - 290
        canvas.draw_line(rx - 15, 65, rx - 15, HEIGHT - 50, (45, 60, 95), 0.9)
        canvas.draw_text(rx, 75, f"N = {n_cur}", (255, 255, 255), scale=3)
        canvas.draw_text(rx, 115, f"PREV P: {pp_cur}", (255, 215, 100), scale=2)
        canvas.draw_text(rx, 142, f"NEXT P: {pn_cur}", (100, 220, 255), scale=2)
        canvas.draw_text(rx, 175, f"D(N) = {d_cur:+d}", (80, 240, 185) if d_cur == 0 else (200, 210, 230), scale=2)
        canvas.draw_text(rx, 202, f"E(N) = {e_cur}", (255, 110, 180) if e_cur == 2 else (200, 210, 230), scale=2)

        if kr1 == 0 and ki1 == 0:
            canvas.draw_text(rx, 238, "PRIME HIT!", (255, 225, 95), scale=2)
        elif e_cur == 2:
            canvas.draw_text(rx, 238, "TWIN PRIME!", (255, 110, 190), scale=2)
        elif d_cur == 0:
            canvas.draw_text(rx, 238, "GOLDBACH D=0", (75, 245, 185), scale=2)

        # Display discovered primes list (last 30 primes in 5 columns)
        p_list = found_primes_at[last_i]
        canvas.draw_text(rx, 285, f"PRIMES FOUND: {len(p_list)}", (255, 215, 100), scale=2)
        recent = p_list[-35:]
        for idx_p, p_val in enumerate(recent):
            col_i = idx_p % 5
            row_i = idx_p // 5
            px_t = rx + col_i * 54
            py_t = 320 + row_i * 30
            col_t = (255, 235, 140) if idx_p == len(recent) - 1 else (165, 190, 225)
            canvas.draw_text(px_t, py_t, str(p_val), col_t, scale=2)

        # Progress bar
        bar_w = int((WIDTH - 160) * progress)
        canvas.draw_line(80, HEIGHT - 28, 80 + bar_w, HEIGHT - 28, (80, 225, 195), 0.95, thick=True)

        proc.stdin.write(canvas.buf)

    proc.stdin.close()
    proc.wait()
    mp4_to_gif(mp4_path, gif_path)
    print(f"    Saved: {mp4_path} & {gif_path}")


def project_3d(x, y, z, yaw, pitch, cx, cy, fov=640.0, dist=4.6):
    cyaw, syaw = math.cos(yaw), math.sin(yaw)
    x1 = x * cyaw + z * syaw
    z1 = -x * syaw + z * cyaw
    cp, sp = math.cos(pitch), math.sin(pitch)
    y2 = y * cp - z1 * sp
    z2 = y * sp + z1 * cp
    z_cam = z2 + dist
    if z_cam <= 0.2:
        return None
    inv = fov / z_cam
    return (cx + x1 * inv, cy - y2 * inv, z_cam)


def generate_video_2_clifford_torus():
    """Video 2: Clifford Torus T^2 — Marked Equator Crossings, Pink -> Red Escape Transition."""
    print("[2/3] Rendering Video 2: Clifford Torus T^2 (Full-Width, Marked Crossings, Pink->Red)...")
    mp4_path = os.path.join(OUT_DIR, "02_clifford_torus_geodesics.mp4")
    gif_path = os.path.join(OUT_DIR, "02_clifford_torus_geodesics.gif")

    proc = open_ffmpeg_mp4(mp4_path, WIDTH, HEIGHT, FPS)
    canvas = Canvas(WIDTH, HEIGHT, bg=(8, 11, 20))

    total_frames = 480  # 16 seconds at 30 fps
    R, r_minor = 1.55, 0.66
    u_steps = 36
    v_steps = 20
    phi_freq = 1.618033988749895

    for f in range(total_frames):
        canvas.clear()
        t = f / float(total_frames)
        # Smooth, slow rotation (calm and cinematic over 16s)
        yaw = 0.55 + t * 1.35 * math.pi
        pitch = 0.50 + 0.06 * math.sin(t * 2.0 * math.pi)

        centers = [(WIDTH * 0.255, HEIGHT * 0.54, 0.50), (WIDTH * 0.745, HEIGHT * 0.54, 0.58)]

        # Center divider & crisp top labels
        canvas.draw_line(WIDTH // 2, 20, WIDTH // 2, HEIGHT - 20, (55, 70, 105), 0.9, thick=True)
        canvas.draw_text(65, 24, "RE(S) = 1/2 : CONFINED EQUATOR", (75, 245, 195), scale=3)
        canvas.draw_text(65, 62, "LAMBDA = 0  |  STABLE GEODESIC", (150, 220, 210), scale=2)

        canvas.draw_text(WIDTH // 2 + 45, 24, "RE(S) != 1/2 : HYPERBOLIC ESCAPE", (255, 95, 115), scale=3)
        canvas.draw_text(WIDTH // 2 + 45, 62, "LAMBDA > 0  |  LEAVES TORUS (RED)", (255, 155, 165), scale=2)

        for cx, cy, beta in centers:
            is_critical = abs(beta - 0.5) < 1e-6

            # Brighter torus wireframe
            for iu in range(0, u_steps, 2):
                u = (iu / u_steps) * 2.0 * math.pi
                prev = None
                for iv in range(v_steps + 1):
                    v = (iv / v_steps) * 2.0 * math.pi
                    x = (R + r_minor * math.cos(v)) * math.cos(u)
                    y = r_minor * math.sin(v)
                    z = (R + r_minor * math.cos(v)) * math.sin(u)
                    p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=500.0, dist=4.9)
                    if prev and p:
                        canvas.draw_line(prev[0], prev[1], p[0], p[1], (75, 102, 155), 0.58)
                    prev = p

            # Highlight the Clifford Equator ring in distinct warm Amber/Gold (contrasts with cyan/pink/red navigator)
            prev_eq = None
            for iu in range(73):
                u = (iu / 72.0) * 2.0 * math.pi
                x = (R + r_minor) * math.cos(u)
                y = 0.0
                z = (R + r_minor) * math.sin(u)
                p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=500.0, dist=4.9)
                if prev_eq and p:
                    canvas.draw_line(prev_eq[0], prev_eq[1], p[0], p[1], (255, 195, 65), 0.72, thick=True)
                prev_eq = p

            # Fixed step size d_tau so every point on the trail stays 100% locked in space (zero jitter!)
            # Faster advance over 16s: phase_head goes up to 34.0 (~8-9 full equatorial crossings!)
            phase_head = t * 34.0
            d_tau = 0.055
            n_steps = int(phase_head / d_tau)
            prev_g = None
            last_p = None
            for s in range(n_steps + 1):
                tau = s * d_tau
                u = tau
                v = tau * phi_freq
                sin_v = math.sin(v)

                if is_critical:
                    rad_scale = 1.0
                    col = (55, 240, 220)
                else:
                    lam = abs(beta - 0.5) * 1.45
                    # Unbounded hyperbolic escape so the off-line trajectory is lost forever
                    rad_scale = 1.0 + 0.12 * (math.exp(min(lam * tau, 4.2)) - 1.0)
                    escape_amt = min(1.0, max(0.0, (rad_scale - 1.08) / 0.25))
                    r_c = 255
                    g_c = int(120 * (1.0 - escape_amt) + 20 * escape_amt)
                    b_c = int(200 * (1.0 - escape_amt) + 25 * escape_amt)
                    col = (r_c, g_c, b_c)

                x = (R * rad_scale + r_minor * math.cos(v)) * math.cos(u)
                y = r_minor * sin_v * rad_scale + (0.0 if is_critical else 0.18 * (rad_scale - 1.0) * math.sin(tau))
                z = (R * rad_scale + r_minor * math.cos(v)) * math.sin(u)
                p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=500.0, dist=4.9)

                if prev_g and p:
                    alpha = 0.35 + 0.65 * (s / float(max(n_steps, 1)))
                    canvas.draw_line(prev_g[0], prev_g[1], p[0], p[1], col, alpha * 0.90, additive=True, thick=True)
                prev_g = p
                last_p = p

            # Exact analytical equatorial crossings: v = 2 * pi * k => tau_k = (2 * pi * k) / phi_freq
            # Zero jitter because each crossing is pinned to its exact mathematical tau_k!
            k_cross = 1
            while True:
                tau_k = (2.0 * math.pi * k_cross) / phi_freq
                if tau_k > phase_head:
                    break
                u_k = tau_k
                if is_critical:
                    rad_k = 1.0
                    escaped = False
                else:
                    lam = abs(beta - 0.5) * 1.45
                    rad_k = 1.0 + 0.12 * (math.exp(min(lam * tau_k, 4.2)) - 1.0)
                    escaped = rad_k > 1.15

                xk = (R * rad_k + r_minor) * math.cos(u_k)
                yk = 0.0 if is_critical else 0.18 * (rad_k - 1.0) * math.sin(tau_k)
                zk = (R * rad_k + r_minor) * math.sin(u_k)
                pk = project_3d(xk, yk, zk, yaw, pitch, cx, cy, fov=500.0, dist=4.9)
                if pk:
                    if is_critical:
                        canvas.draw_circle(pk[0], pk[1], 10, (255, 240, 120), 0.80, glow=True)
                        canvas.draw_circle(pk[0], pk[1], 4, (255, 255, 255), 1.0)
                    elif not escaped:
                        canvas.draw_circle(pk[0], pk[1], 9, (255, 130, 210), 0.70, glow=True)
                        canvas.draw_circle(pk[0], pk[1], 3.5, (255, 225, 245), 0.95)
                    else:
                        canvas.draw_circle(pk[0], pk[1], 11, (255, 25, 25), 0.88, glow=True)
                        canvas.draw_circle(pk[0], pk[1], 4, (255, 160, 160), 1.0)
                k_cross += 1

            # Draw exact smooth head at phase_head
            if phase_head > 0.01:
                u_h = phase_head
                v_h = phase_head * phi_freq
                if is_critical:
                    rad_h = 1.0
                else:
                    lam = abs(beta - 0.5) * 1.45
                    rad_h = 1.0 + 0.12 * (math.exp(min(lam * phase_head, 4.2)) - 1.0)
                xh = (R * rad_h + r_minor * math.cos(v_h)) * math.cos(u_h)
                yh = r_minor * math.sin(v_h) * rad_h + (0.0 if is_critical else 0.18 * (rad_h - 1.0) * math.sin(phase_head))
                zh = (R * rad_h + r_minor * math.cos(v_h)) * math.sin(u_h)
                ph = project_3d(xh, yh, zh, yaw, pitch, cx, cy, fov=500.0, dist=4.9)
                if ph:
                    if last_p:
                        head_col = (55, 240, 220) if is_critical else (255, 45, 45)
                        canvas.draw_line(last_p[0], last_p[1], ph[0], ph[1], head_col, 0.95, additive=True, thick=True)
                    glow_col = (120, 255, 235) if is_critical else (255, 45, 45)
                    canvas.draw_circle(ph[0], ph[1], 16, glow_col, 0.85, glow=True)
                    canvas.draw_circle(ph[0], ph[1], 5, (255, 255, 255), 1.0)

        proc.stdin.write(canvas.buf)

    proc.stdin.close()
    proc.wait()
    mp4_to_gif(mp4_path, gif_path)
    print(f"    Saved: {mp4_path} & {gif_path}")


def _render_single_torus_video(mp4_path, gif_path, is_critical, beta_val):
    """Helper to render a standalone Full-HD (1280x720) Clifford Torus video (Stable vs. Escape)."""
    # First 12 Riemann zeta non-trivial zero imaginary heights gamma_n (Odlyzko / LMFDB)
    ZETA_ZEROS = [
        ("G1", "14.1347"), ("G2", "21.0220"), ("G3", "25.0109"),
        ("G4", "30.4249"), ("G5", "32.9351"), ("G6", "37.5862"),
        ("G7", "40.9187"), ("G8", "43.3271"), ("G9", "48.0052"),
        ("G10", "49.7738"), ("G11", "52.9703"), ("G12", "56.4462"),
    ]
    proc = open_ffmpeg_mp4(mp4_path, WIDTH, HEIGHT, FPS)
    canvas = Canvas(WIDTH, HEIGHT, bg=(8, 11, 20))

    total_frames = 450  # 15 seconds at 30 fps
    R, r_minor = 1.60, 0.68
    u_steps = 40
    v_steps = 22
    phi_freq = 1.618033988749895

    cx, cy = WIDTH * 0.38, HEIGHT * 0.54
    rx = WIDTH - 375  # Right telemetry panel

    for f in range(total_frames):
        canvas.clear()
        t = f / float(total_frames)
        yaw = 0.55 + t * 1.35 * math.pi
        pitch = 0.50 + 0.06 * math.sin(t * 2.0 * math.pi)

        # Top HUD
        if is_critical:
            canvas.draw_text(40, 22, "CLIFFORD TORUS T2 : CRITICAL LINE RE(S) = 1/2", (75, 245, 195), scale=3)
            canvas.draw_text(40, 60, "LAMBDA = 0  |  CONFINED EQUATORIAL RESONANCES (ZETA ZEROS)", (160, 225, 215), scale=2)
        else:
            canvas.draw_text(40, 22, f"CLIFFORD TORUS T2 : OFF-LINE RE(S) = {beta_val:.2f} != 1/2", (255, 95, 115), scale=3)
            canvas.draw_text(40, 60, "LAMBDA > 0  |  HYPERBOLIC ESCAPE: NO EQUATORIAL CROSSINGS", (255, 165, 175), scale=2)

        # Bright torus wireframe
        for iu in range(0, u_steps, 2):
            u = (iu / u_steps) * 2.0 * math.pi
            prev = None
            for iv in range(v_steps + 1):
                v = (iv / v_steps) * 2.0 * math.pi
                x = (R + r_minor * math.cos(v)) * math.cos(u)
                y = r_minor * math.sin(v)
                z = (R + r_minor * math.cos(v)) * math.sin(u)
                p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=580.0, dist=4.8)
                if prev and p:
                    canvas.draw_line(prev[0], prev[1], p[0], p[1], (75, 105, 160), 0.60)
                prev = p

        # Distinct Amber/Gold Clifford Equator ring (v = 0)
        prev_eq = None
        for iu in range(73):
            u = (iu / 72.0) * 2.0 * math.pi
            x = (R + r_minor) * math.cos(u)
            y = 0.0
            z = (R + r_minor) * math.sin(u)
            p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=580.0, dist=4.8)
            if prev_eq and p:
                canvas.draw_line(prev_eq[0], prev_eq[1], p[0], p[1], (255, 195, 65), 0.78, thick=True)
            prev_eq = p

        # Fixed-step geodesic trajectory (zero jitter)
        phase_head = t * 34.0
        d_tau = 0.055
        n_steps = int(phase_head / d_tau)
        prev_g = None
        last_p = None
        escaped_now = False
        for s in range(n_steps + 1):
            tau = s * d_tau
            u = tau
            v = tau * phi_freq
            sin_v = math.sin(v)

            if is_critical:
                rad_scale = 1.0
                col = (55, 240, 220)
            else:
                lam = abs(beta_val - 0.5) * 1.45
                rad_scale = 1.0 + 0.12 * (math.exp(min(lam * tau, 4.2)) - 1.0)
                escape_amt = min(1.0, max(0.0, (rad_scale - 1.08) / 0.25))
                if rad_scale > 1.15:
                    escaped_now = True
                r_c = 255
                g_c = int(120 * (1.0 - escape_amt) + 20 * escape_amt)
                b_c = int(200 * (1.0 - escape_amt) + 25 * escape_amt)
                col = (r_c, g_c, b_c)

            x = (R * rad_scale + r_minor * math.cos(v)) * math.cos(u)
            y = r_minor * sin_v * rad_scale + (0.0 if is_critical else 0.18 * (rad_scale - 1.0) * math.sin(tau))
            z = (R * rad_scale + r_minor * math.cos(v)) * math.sin(u)
            p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=580.0, dist=4.8)

            if prev_g and p:
                alpha = 0.35 + 0.65 * (s / float(max(n_steps, 1)))
                canvas.draw_line(prev_g[0], prev_g[1], p[0], p[1], col, alpha * 0.90, additive=True, thick=True)
            prev_g = p
            last_p = p

        # Exact analytical equatorial crossings: ONLY light up when the trajectory genuinely crosses the equator on T^2!
        crossed_list = []
        k_cross = 1
        while True:
            tau_k = (2.0 * math.pi * k_cross) / phi_freq
            if tau_k > phase_head:
                break
            u_k = tau_k
            if is_critical:
                rad_k = 1.0
                on_equator = True
            else:
                lam = abs(beta_val - 0.5) * 1.45
                rad_k = 1.0 + 0.12 * (math.exp(min(lam * tau_k, 4.2)) - 1.0)
                # Strictly check if still physically touching the torus equator (within tolerance)
                on_equator = rad_k <= 1.12

            if on_equator:
                xk = (R * rad_k + r_minor) * math.cos(u_k)
                yk = 0.0
                zk = (R * rad_k + r_minor) * math.sin(u_k)
                pk = project_3d(xk, yk, zk, yaw, pitch, cx, cy, fov=580.0, dist=4.8)
                if pk:
                    if is_critical:
                        canvas.draw_circle(pk[0], pk[1], 11, (255, 240, 120), 0.85, glow=True)
                        canvas.draw_circle(pk[0], pk[1], 4.5, (255, 255, 255), 1.0)
                    else:
                        canvas.draw_circle(pk[0], pk[1], 9, (255, 130, 210), 0.70, glow=True)
                        canvas.draw_circle(pk[0], pk[1], 3.5, (255, 225, 245), 0.95)
                crossed_list.append(k_cross)
            k_cross += 1

        # Draw smooth head
        if phase_head > 0.01:
            u_h = phase_head
            v_h = phase_head * phi_freq
            if is_critical:
                rad_h = 1.0
            else:
                lam = abs(beta_val - 0.5) * 1.45
                rad_h = 1.0 + 0.12 * (math.exp(min(lam * phase_head, 4.2)) - 1.0)
            xh = (R * rad_h + r_minor * math.cos(v_h)) * math.cos(u_h)
            yh = r_minor * math.sin(v_h) * rad_h + (0.0 if is_critical else 0.18 * (rad_h - 1.0) * math.sin(phase_head))
            zh = (R * rad_h + r_minor * math.cos(v_h)) * math.sin(u_h)
            ph = project_3d(xh, yh, zh, yaw, pitch, cx, cy, fov=580.0, dist=4.8)
            if ph:
                if last_p:
                    head_col = (55, 240, 220) if is_critical else (255, 45, 45)
                    canvas.draw_line(last_p[0], last_p[1], ph[0], ph[1], head_col, 0.95, additive=True, thick=True)
                glow_col = (120, 255, 235) if is_critical else (255, 45, 45)
                canvas.draw_circle(ph[0], ph[1], 16, glow_col, 0.85, glow=True)
                canvas.draw_circle(ph[0], ph[1], 5, (255, 255, 255), 1.0)

        # Right-side telemetry panel listing exact Zeta zeros / crossings
        canvas.draw_line(rx - 20, 95, rx - 20, HEIGHT - 40, (50, 68, 105), 0.9)
        if is_critical:
            canvas.draw_text(rx, 105, "STATUS: CONFINED", (75, 245, 195), scale=2)
            canvas.draw_text(rx, 138, "CURVATURE K = 0.00", (175, 220, 230), scale=2)
            canvas.draw_text(rx, 168, "LYAPUNOV  L = 0.00", (175, 220, 230), scale=2)
            canvas.draw_text(rx, 215, f"EQUATOR CROSSINGS: {len(crossed_list)}", (255, 215, 90), scale=2)
            canvas.draw_text(rx, 248, "ZETA ZEROS (1/2 + I*G):", (180, 200, 235), scale=2)
            for idx_z, k_id in enumerate(crossed_list[:10]):
                if k_id - 1 < len(ZETA_ZEROS):
                    lbl, val = ZETA_ZEROS[k_id - 1]
                    col_z = (255, 245, 140) if idx_z == len(crossed_list) - 1 else (165, 220, 215)
                    canvas.draw_text(rx, 285 + idx_z * 32, f"#{k_id}  {lbl} = {val}", col_z, scale=2)
        else:
            canvas.draw_text(rx, 105, "STATUS: ESCAPED!" if escaped_now else "STATUS: DRIFTING", (255, 75, 85), scale=2)
            canvas.draw_text(rx, 138, "CURVATURE K < 0", (255, 165, 175), scale=2)
            canvas.draw_text(rx, 168, "LYAPUNOV  L > 0", (255, 165, 175), scale=2)
            canvas.draw_text(rx, 215, f"EQUATOR CROSSINGS: {len(crossed_list)}", (255, 140, 180), scale=2)
            if escaped_now:
                canvas.draw_text(rx, 260, "CONFINEMENT LOST!", (255, 65, 65), scale=2)
                canvas.draw_text(rx, 292, "ZERO FURTHER EQUATOR", (255, 150, 150), scale=2)
                canvas.draw_text(rx, 322, "CROSSINGS POSSIBLE.", (255, 150, 150), scale=2)
                canvas.draw_text(rx, 368, "MONOPOLAR DIVERGENCE", (255, 110, 110), scale=2)
                canvas.draw_text(rx, 398, "EXP(LAMBDA * TAU)", (255, 110, 110), scale=2)

        proc.stdin.write(canvas.buf)

    proc.stdin.close()
    proc.wait()
    mp4_to_gif(mp4_path, gif_path)
    print(f"    Saved: {mp4_path} & {gif_path}")


def generate_video_2a_clifford_stable():
    print("[2a] Rendering Standalone HD: Clifford Torus Stable (Re(s) = 1/2)...")
    _render_single_torus_video(
        os.path.join(OUT_DIR, "02a_clifford_torus_stable.mp4"),
        os.path.join(OUT_DIR, "02a_clifford_torus_stable.gif"),
        is_critical=True,
        beta_val=0.50,
    )


def generate_video_2b_clifford_escape():
    print("[2b] Rendering Standalone HD: Clifford Torus Escape (Re(s) != 1/2)...")
    _render_single_torus_video(
        os.path.join(OUT_DIR, "02b_clifford_torus_escape.mp4"),
        os.path.join(OUT_DIR, "02b_clifford_torus_escape.gif"),
        is_critical=False,
        beta_val=0.58,
    )


def generate_video_3_golden_spiral_m5():
    """Video 3: Golden Ratio Spiral & Icosian Gamma_120 Symmetry on S^3 -> R^3 (Full HD)."""
    print("[3/3] Rendering Video 3: Golden Spiral & Icosian Gamma_120...")
    mp4_path = os.path.join(OUT_DIR, "03_golden_spiral_icosian_M5.mp4")
    gif_path = os.path.join(OUT_DIR, "03_golden_spiral_icosian_M5.gif")

    proc = open_ffmpeg_mp4(mp4_path, WIDTH, HEIGHT, FPS)
    canvas = Canvas(WIDTH, HEIGHT, bg=(9, 10, 22))

    phi = (1.0 + math.sqrt(5.0)) / 2.0
    verts = []
    for s1 in (-1, 1):
        for s2 in (-1, 1):
            verts.append((0.0, s1 * 1.0, s2 * phi))
            verts.append((s1 * 1.0, s2 * phi, 0.0))
            verts.append((s2 * phi, 0.0, s1 * 1.0))
    verts = [(x / math.sqrt(x*x+y*y+z*z) * 1.85, y / math.sqrt(x*x+y*y+z*z) * 1.85, z / math.sqrt(x*x+y*y+z*z) * 1.85) for x, y, z in verts]

    edges = []
    for i in range(len(verts)):
        for j in range(i + 1, len(verts)):
            dx = verts[i][0] - verts[j][0]
            dy = verts[i][1] - verts[j][1]
            dz = verts[i][2] - verts[j][2]
            if math.sqrt(dx*dx + dy*dy + dz*dz) < 2.05:
                edges.append((i, j))

    total_frames = 300
    cx, cy = WIDTH * 0.5, HEIGHT * 0.53

    for f in range(total_frames):
        canvas.clear()
        t = f / float(total_frames)
        yaw = t * 2.0 * math.pi
        pitch = 0.35 + 0.25 * math.sin(t * 2.0 * math.pi)

        canvas.draw_text(40, 24, "5D MANIFOLD M5 = (S3 / GAMMA_120) X T2", (235, 240, 255), scale=3)
        canvas.draw_text(40, 62, "GOLDEN RATIO SPIRAL PHI = 1.6180339... (HURWITZ-KAM NON-RESONANCE)", (255, 210, 95), scale=2)

        proj_v = [project_3d(x, y, z, yaw, pitch, cx, cy, fov=660.0, dist=4.8) for x, y, z in verts]
        for i, j in edges:
            p1, p2 = proj_v[i], proj_v[j]
            if p1 and p2:
                canvas.draw_line(p1[0], p1[1], p2[0], p2[1], (90, 120, 195), 0.60, thick=True)

        for p in proj_v:
            if p:
                canvas.draw_circle(p[0], p[1], 10, (130, 175, 255), 0.55, glow=True)
                canvas.draw_circle(p[0], p[1], 3.5, (225, 240, 255), 0.95)

        steps = 420
        max_s = int(steps * (0.15 + 0.85 * t))
        prev = None
        for s in range(max_s):
            theta = (s / float(steps)) * 12.0 * math.pi
            z_norm = -0.92 + 1.84 * (s / float(steps))
            rad = math.sqrt(max(0.0, 1.0 - z_norm * z_norm)) * 1.55
            x = rad * math.cos(theta * phi)
            y = z_norm * 1.55
            z = rad * math.sin(theta * phi)
            p = project_3d(x, y, z, yaw, pitch, cx, cy, fov=660.0, dist=4.8)
            if prev and p:
                alpha = 0.25 + 0.75 * (s / float(max(max_s, 1)))
                canvas.draw_line(prev[0], prev[1], p[0], p[1], (255, 205, 80), alpha * 0.92, additive=True, thick=True)
            prev = p

        if prev:
            canvas.draw_circle(prev[0], prev[1], 18, (255, 225, 110), 0.88, glow=True)
            canvas.draw_circle(prev[0], prev[1], 5, (255, 255, 255), 1.0)

        proc.stdin.write(canvas.buf)

    proc.stdin.close()
    proc.wait()
    mp4_to_gif(mp4_path, gif_path)
    print(f"    Saved: {mp4_path} & {gif_path}")


if __name__ == "__main__":
    os.makedirs(OUT_DIR, exist_ok=True)
    generate_video_1_dipolar_lattice()
    generate_video_2_clifford_torus()
    generate_video_2a_clifford_stable()
    generate_video_2b_clifford_escape()
    generate_video_3_golden_spiral_m5()
    print("\n[OK] All upgraded HD animations (.mp4 & .gif) generated successfully in:", OUT_DIR)
