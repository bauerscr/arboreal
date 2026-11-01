from grassmann import *
import time
def check(N, edges, beta, h1, h2):
    t=time.time(); M = H04(N, edges, beta, h1, h2)
    # sanity: u.u = -1
    assert all(abs(c - (-1.0 if m == 0 else 0.0)) < 1e-12 for m, c in add(M.dot(0,0), {}).items()) and M.dot(0,0) == {0: -1.0}
    def src(x):  # h1 eta^1_x + 2 h2 (z_x - 1) eta^1_x
        e = M.eta(x, 0)
        return add(scale(h1, e), scale(2*h2, mul(add(M.z(x), const(-1.0)), e)))
    S = add(*[src(x) for x in range(N)])
    w1l = M.avg(M.z(0)); w1r = M.avg(mul(M.xi(0, 0), S))
    F = mul(M.xi(0, 0), mul(M.xi(0, 1), M.eta(0, 1)))
    w2l = M.avg(add(mul(M.xi(0, 1), M.eta(0, 1)), scale(-1, M.q(0)))); w2r = M.avg(mul(F, S))
    print(f"N={N} beta={beta} h1={h1} h2={h2}: Z={M.Z:.4g}  W1: {w1l:.12f} vs {w1r:.12f}   W2: {w2l:.12f} vs {w2r:.12f}  ({time.time()-t:.1f}s)")
check(2, [(0,1)], 1.3, 0.4, 0.0)
check(3, [(0,1),(1,2),(2,0)], 1.3, 0.4, 0.25)
check(3, [(0,1),(1,2)], 0.7, -0.3, 0.6)
check(3, [(0,1),(1,2),(2,0)], 2.0, 0.0, 0.0)
