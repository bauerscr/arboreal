"""Evaluate the O(eps^3) Q-vertex sums on the 4-torus.

Monomial = const * prod G(y+v) * prod G(w+v) * prod G(w-y+v); summed over y, w:
  sum_y Fy(y) * sum_u Fw(y+u) Fyw(u)    (cross-correlation via FFT).
"""
import sys, pickle
import numpy as np

D = 4


def greens(N, m):
    k = 2 * np.pi * np.fft.fftfreq(N)
    K = np.meshgrid(*([k] * D), indexing='ij')
    lam = sum(2 * (1 - np.cos(ki)) for ki in K)
    G = np.real(np.fft.ifftn(1.0 / (lam + m * m)))
    G2 = np.real(np.fft.ifftn(1.0 / (lam + m * m) ** 2))
    G3 = np.real(np.fft.ifftn(1.0 / (lam + m * m) ** 3))
    return G, G2, G3


def shifted(G, v, cache):
    v = tuple(v)
    if v not in cache:
        cache[v] = np.roll(G, shift=tuple(-x for x in v), axis=tuple(range(D)))
    return cache[v]


def evalpoly(poly, G):
    cache = {}
    groups = {}   # (wkeys, ywkeys) -> list of (coeff * const, ykeys)
    for keys, c in poly.items():
        const = c
        yk, wk, ywk = [], [], []
        for kind, v in keys:
            if kind == 'c':
                const *= G[tuple(np.array(v))]
            elif kind == 'y':
                yk.append(v)
            elif kind == 'w':
                wk.append(v)
            else:
                ywk.append(v)
        groups.setdefault((tuple(sorted(wk)), tuple(sorted(ywk))), []).append((const, tuple(yk)))
    total = 0.0
    for (wk, ywk), items in groups.items():
        Fw = np.ones_like(G)
        for v in wk:
            Fw = Fw * shifted(G, v, cache)
        Fyw = np.ones_like(G)
        for v in ywk:
            Fyw = Fyw * shifted(G, v, cache)
        if not wk and not ywk:
            corr = None
        else:
            corr = np.real(np.fft.ifftn(np.fft.fftn(Fw) * np.conj(np.fft.fftn(Fyw))))
        Fy = np.zeros_like(G)
        for const, yk in items:
            arr = np.full_like(G, const)
            for v in yk:
                arr = arr * shifted(G, v, cache)
            Fy = Fy + arr
        if corr is None:
            # no w-dependence: only possible for single-vertex-pair (y-only) sums
            total += Fy.sum() if any(items[i][1] for i in range(len(items))) else Fy.flat[0]
        else:
            total += (Fy * corr).sum()
    return total


if __name__ == '__main__':
    out = pickle.load(open('qvertex3_sym.pkl', 'rb'))
    for N, m in [(int(a), float(b)) for a, b in (s.split(':') for s in sys.argv[1:])]:
        G, G2, G3 = greens(N, m)
        G0, G20, G30 = G.flat[0], G2.flat[0], G3.flat[0]
        T1 = evalpoly(out['T1'], G)
        T2 = evalpoly(out['T2'], G)
        T3 = evalpoly(out['T3'], G)
        T5 = evalpoly(out['T5'], G)
        # mass insertion: d/dm^2 of O(eps^2) internal lines, A + B = -4(1-m^2 G0) + 2 - 4 m^2 G0 + 2 m^4 G2(0)
        # d/dm^2 G0 = -G2(0), d/dm^2 G2(0) = -2 G3(0)
        dAB = 4 * (G0 - m * m * G20) - 4 * (G0 - m * m * G20) + 4 * m * m * G20 - 4 * m ** 4 * G30
        print(f"N={N} m={m}: T1={T1:+.8f} T2={T2:+.8f} T3={T3:+.8f} T5={T5:+.8f}  dAB={dAB:+.3e}", flush=True)
        print(f"         at h=0 (c_Q=2, delta=eps): T1+T2+2*T3+T5+dAB = {T1+T2+2*T3+T5+dAB:+.8f}", flush=True)
