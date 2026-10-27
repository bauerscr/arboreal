import FRD

/-!
# Audit of the `FRD` library (Section `sec:frd` of `h02rg.tex`)

Run with `lake env lean FRD/Audit.lean` (after `lake build`).  All statements are instantiated
with the constructed family `FRD.stdPt` of polynomials `P_t` (`e:decomp-Pt`), so none of them
depends on an assumption about `P_t`.  Expected axioms: `propext`, `Classical.choice`,
`Quot.sound`.
-/

open FRD Grassmann Filter Topology

/-! ## Definitions -/

#print FRD.PtFamily
#print FRD.negLap      -- `-Δ` on the torus `(ℤ/nℤ)^d`
#print FRD.lam         -- `λ(k)`
#print FRD.fmat        -- Fourier multipliers
#print FRD.uhat
#print FRD.wt
#print FRD.lowEnd
#print FRD.Cj          -- `C_j`
#print FRD.CNN         -- `C_{N,N}`
#print FRD.CN          -- `C_N`
#print FRD.tN          -- `t_N`
#print FRD.QN          -- `Q_N`
#print FRD.WN          -- `W_N`
#print FRD.covZ        -- the covariances on `ℤ^d`
#print FRD.greenZd     -- `(-Δ^{ℤ^d})^{-1}(0, ·)`

/-! ## Statements -/

-- (e:decomp-Pt) polynomials `P_t` exist
example : Nonempty PtFamily := exists_PtFamily

section
variable {d n : ℕ} [NeZero n]

-- (e:C-def)  `(-Δ + m²)^{-1} = C_1 + ⋯ + C_{N-1} + C_{N,N}`
example {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    (negLap + msq • 1 : Matrix (Torus d n) (Torus d n) ℝ)⁻¹ =
      ∑ j ∈ Finset.Ico 1 N, Cj stdPt msq L j + CNN stdPt msq L N :=
  decomposition_inv stdPt hmsq hL hN

-- positive semidefinite
example {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (j : ℕ) :
    (Cj stdPt msq L j : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef := Cj_posSemidef stdPt hmsq hL j
example {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (N : ℕ) :
    (CNN stdPt msq L N : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef :=
  CNN_posSemidef stdPt hmsq hL N
example {msq L : ℝ} (hmsq : 0 ≤ msq) (hL : 0 ≤ L) (N : ℕ) :
    (CN stdPt msq L N : Matrix (Torus d n) (Torus d n) ℝ).PosSemidef := CN_posSemidef stdPt hmsq hL N

-- (e:C-range)  `C_j(x,y) = 0` if `|x - y|_∞ ≥ L^j/2`
example {msq : ℝ} (hmsq : 0 ≤ msq) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) {x y : Torus d n}
    (h : L ^ j / 2 ≤ supNorm (x - y)) : Cj stdPt msq L j x y = 0 := Cj_finiteRange stdPt hmsq hL j h

-- invariance under lattice symmetries (translations, coordinate permutations and reflections)
example (msq L : ℝ) (j : ℕ) (x y a : Torus d n) :
    Cj stdPt msq L j (x + a) (y + a) = Cj stdPt msq L j x y := Cj_translate stdPt msq L j x y a
example (msq L : ℝ) (j : ℕ) (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) (x y : Torus d n) :
    Cj stdPt msq L j (symm π s x) (symm π s y) = Cj stdPt msq L j x y := Cj_symm stdPt msq L j π s x y

-- independence of the torus: `C_j(x,y) = c_j(r(x - y))` with `c_j` defined on `ℤ^d`
example {msq : ℝ} (hmsq : 0 ≤ msq) (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) (hn : L ^ j < n)
    (x y : Torus d n) :
    Cj stdPt msq L j x y = covZ stdPt d msq (Set.Ioc (lowEnd L j) (L ^ j / 2)) (rep (x - y)) :=
  Cj_eq_Zd stdPt hmsq hd hL j hn x y

-- continuity in `m² ≥ 0` (including `m² = 0`)
example (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) (x y : Torus d n) :
    ContinuousOn (fun msq => Cj stdPt msq L j x y) (Set.Ici 0) := Cj_continuousOn stdPt hd hL j x y
example (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (x y : Torus d n) :
    ContinuousOn (fun msq => CN stdPt msq L N x y) (Set.Ici 0) := CN_continuousOn stdPt hd hL N x y

-- (e:CNN-def)  `C_{N,N} = C_N + t_N Q_N`
example (msq L : ℝ) (N : ℕ) :
    (CNN stdPt msq L N : Matrix (Torus d n) (Torus d n) ℝ) = CN stdPt msq L N + tN stdPt d msq L N • QN :=
  CNN_eq stdPt msq L N

-- `W_N = C_1 + ⋯ + C_N`
example {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} (hN : 1 ≤ N) (x : Torus d n) :
    WN stdPt msq L N x = ∑ j ∈ Finset.Ico 1 N, Cj stdPt msq L j 0 x + CN stdPt msq L N 0 x :=
  WN_eq stdPt hmsq hL hN x
end

-- (e:tN)  `t_N > 0`, `t_N` continuous, `0 ≤ 1/m² - t_N ≤ K L^{2N}`
example {d : ℕ} {msq : ℝ} (hmsq : 0 < msq) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) : 0 < tN stdPt d msq L N :=
  tN_pos stdPt hmsq hL N
example {d : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    ContinuousOn (fun msq => tN stdPt d msq L N) (Set.Ioi 0) := tN_continuousOn stdPt hd hL N
example {d : ℕ} (hd : 1 ≤ d) : ∃ K : ℝ, ∀ msq : ℝ, 0 < msq → ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
    0 ≤ 1 / msq - tN stdPt d msq L N ∧ 1 / msq - tN stdPt d msq L N ≤ K * L ^ (2 * N) :=
  tN_sub_inv stdPt hd

-- (e:C-bd)  scaling estimates for `C_{j+1}` and for `C_N`
#check @Cj_bound
#check @CN_bound

-- (e:greenfLambdaZd)
#check @greenf

/-! ## Axioms -/

#print axioms FRD.exists_PtFamily
#print axioms FRD.decomposition_inv
#print axioms FRD.Cj_posSemidef
#print axioms FRD.Cj_finiteRange
#print axioms FRD.Cj_symm
#print axioms FRD.Cj_eq_Zd
#print axioms FRD.Cj_continuousOn
#print axioms FRD.CN_continuousOn
#print axioms FRD.CNN_eq
#print axioms FRD.tN_pos
#print axioms FRD.tN_sub_inv
#print axioms FRD.WN_eq
#print axioms FRD.Cj_bound
#print axioms FRD.CN_bound
#print axioms FRD.hasSum_covZ_green
#print axioms FRD.greenf
