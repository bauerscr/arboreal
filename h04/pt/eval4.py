"""Evaluate sums over y, w, u in the torus of monomials in G(y+v), G(w+v), G(u+v), G(w-y+v), G(u-y+v), G(u-w+v)."""
import numpy as np
D = 4

def shifted(G, v, cache):
    v = tuple(v)
    if v not in cache:
        cache[v] = np.roll(G, shift=tuple(-x for x in v), axis=tuple(range(D)))
    return cache[v]

def evalpoly4(poly, G):
    N = G.shape[0]; V = G.size
    cache = {}
    groups = {}
    for keys, c in poly.items():
        const = c; parts = {k: [] for k in ('y', 'w', 'u', 'yw', 'yu', 'wu')}
        for kind, v in keys:
            if kind == 'c':
                const *= G[tuple(np.array(v))]
            else:
                parts[kind].append(v)
        gk = tuple(tuple(sorted(parts[k])) for k in ('w', 'u', 'yw', 'yu', 'wu'))
        groups.setdefault(gk, []).append((const, tuple(parts['y'])))
    def prod(vs):
        a = np.ones_like(G)
        for v in vs:
            a = a * shifted(G, v, cache)
        return a
    # all y as flat index; translations of arrays by y
    idx = np.indices(G.shape).reshape(D, -1).T          # (V, D) list of y
    total = 0.0
    for (wk, uk, ywk, yuk, wuk), items in groups.items():
        Fw, Fu, Fyw, Fyu, Fwu = prod(wk), prod(uk), prod(ywk), prod(yuk), prod(wuk)
        # a[y, w] = Fw(w) Fyw(w - y);  b[y, u] = Fu(u) Fyu(u - y)
        def translated(F):
            # T[y, z] = F(z - y)
            out = np.empty((V,) + G.shape)
            for i, y in enumerate(idx):
                out[i] = np.roll(F, shift=tuple(y), axis=tuple(range(D)))
            return out
        Tyw = translated(Fyw) if ywk else None
        Tyu = translated(Fyu) if yuk else None
        a = Fw[None] * Tyw if Tyw is not None else np.broadcast_to(Fw[None], (V,) + G.shape)
        b = Fu[None] * Tyu if Tyu is not None else np.broadcast_to(Fu[None], (V,) + G.shape)
        if wuk:
            # C[y, w] = sum_u b[y, u] Fwu(u - w)  (cross-correlation over u, batched over y)
            fb = np.fft.fftn(b, axes=tuple(range(1, D + 1)))
            C = np.real(np.fft.ifftn(fb * np.conj(np.fft.fftn(Fwu))[None], axes=tuple(range(1, D + 1))))
            inner = (a * C).reshape(V, -1).sum(axis=1)
        else:
            inner = a.reshape(V, -1).sum(axis=1) * b.reshape(V, -1).sum(axis=1)
        Fy = np.zeros(V)
        for const, yk in items:
            Fy += const * prod(yk).reshape(-1)
        total += (Fy * inner).sum()
    return total
