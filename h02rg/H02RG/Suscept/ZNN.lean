import Suscept.Cov

/-!
# `Z_{N,N}` and Proposition `prop:ZNN` (the algebraic part)

For the torus flow `(V_j, K_j) = flowN N m² V₀ j` (started at `K₀ = 0`) we set
* `Z0 N V₀ = Z_0 = e^{-V_0(Λ)}`;
* `ZNN N m² V₀ = Z_{N,N} = 𝔼_C θ Z_0` with `C = (-Δ + m²)^{-1}` (`e:ZNN-def`);
* `uN = u_N = ∑_{j<N} u_{j+1}` and `ZtNN = Z̃_{N,N} = e^{u_N |Λ|} Z_{N,N}`;
* `aN = a_N` (the `a`-coupling of `V_N`), `kN0 = k_N^0 = K_N(Λ)⁰`, `kN2 = k_N^2 = K_N(Λ)²`,
  `atN = ã_{N,N} = a_N - k_N^2/|Λ|`, `utN = ũ_{N,N} = k_N^0 + ã_{N,N} t_N`.

Results:
* `ZNN_eq`: `Z_{N,N} = e^{-u_N|Λ|} 𝔼_{t_N Q_N} θ Z_N` with `Z_N = e^{-V_N(Λ)} + K_N(Λ)`
  (`e:ZNN-def`, `e:P41integrand`); this iterates `ZVK'` along the flow.
* `prop_ZNN` (`e:ZNN`): restricted to constant fields,
  `Z̃_{N,N} = 1 + ũ_{N,N} - |Λ| ã_{N,N} ψψ̄`.
-/

namespace Suscept

noncomputable section

open Finset Grassmann Loc FRD Step Flow

variable {d L : ℕ} [NeZero L]

/-! ### Scale `N` -/

theorem blk_top {N : ℕ} (x : Lam d L N) : blk N x = 0 := by
  funext i
  have := blk_lt (le_refl N) x i
  simp at this
  simpa using this

theorem isPolymer_top {N : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer N X) :
    X = ∅ ∨ X = univ := by
  rcases X.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · exact Or.inr (eq_univ_of_forall fun y => hX x y (by rw [blk_top, blk_top]) hx)

theorem Pj_top (N : ℕ) : Pj N (univ : Finset (Lam d L N)) = {∅, univ} := by
  ext X
  simp only [mem_Pj, subset_univ, true_and, mem_insert, mem_singleton]
  constructor
  · exact isPolymer_top
  · rintro (rfl | rfl)
    · exact isPolymer_empty N
    · exact isPolymer_univ N

theorem isConn_top (N : ℕ) : IsConn N (univ : Finset (Lam d L N)) := by
  refine ⟨isPolymer_univ N, univ_nonempty, fun b hb b' hb' => ?_⟩
  obtain ⟨x, -, rfl⟩ := mem_blocks.1 hb
  obtain ⟨y, -, rfl⟩ := mem_blocks.1 hb'
  rw [blk_top, blk_top]

theorem VE_empty {N : ℕ} (V : Vcoup) : VE V (∅ : Finset (Lam d L N)) = 0 :=
  Subtype.ext (by simp [VE, Vcoup.eval])

/-- `Z_N = e^{-V_N(Λ)} + K_N(Λ)`, since `𝒫_N(Λ) = {∅, Λ}`. -/
theorem Zj_top {N : ℕ} (V : Vcoup) (K : Act d L N) :
    Zj N V K = gexp (-(VE V (univ : Finset (Lam d L N)) : EvR (Lam d L N))) + K univ := by
  have hne : (∅ : Finset (Lam d L N)) ≠ univ := (univ_nonempty.ne_empty).symm
  rw [Zj, Pj_top, sum_pair hne, sdiff_empty, sdiff_self, bot_eq_empty, VE_empty, neg_zero,
    gexp_zero, Kext_empty, Kext, comp_of_isConn (isConn_top N), prod_singleton, mul_one, one_mul]

/-! ### Scale `0` -/

theorem Kext_zero_of_nonempty {j N : ℕ} {X : Finset (Lam d L N)} (hX : X.Nonempty) :
    Kext j (0 : Act d L N) X = 0 := by
  obtain ⟨x, hx⟩ := hX
  refine prod_eq_zero (i := compOf j X (blk j x)) ?_ rfl
  exact mem_image.2 ⟨blk j x, mem_blocks.2 ⟨x, hx, rfl⟩, rfl⟩

/-- `Z_0 = e^{-V_0(Λ)}` for `K_0 = 0`. -/
theorem Zj_zero {N : ℕ} (V : Vcoup) :
    Zj 0 V (0 : Act d L N) = gexp (-(VE V (univ : Finset (Lam d L N)) : EvR (Lam d L N))) := by
  rw [Zj, sum_eq_single ∅]
  · rw [sdiff_empty, Kext_empty, mul_one]
  · intro X _ hX
    rw [Kext_zero_of_nonempty (nonempty_iff_ne_empty.2 hX), mul_zero]
  · intro h; exact absurd (mem_Pj.2 ⟨empty_subset _, isPolymer_empty 0⟩) h

/-! ### The flow -/

theorem Zj_restr {j N : ℕ} (V : Vcoup) (K : Act d L N) : Zj j V (restr j K) = Zj j V K := by
  unfold Zj
  refine sum_congr rfl fun X hX => ?_
  rw [Kext_congr (mem_Pj.1 hX).2 fun Y hY _ => restr_of_conn K hY]

variable (d L) in
/-- `Z_0 = e^{-V_0(Λ)}`. -/
def Z0 (N : ℕ) (V₀ : Vcoup) : Alg d L N := (gexp (-(VE V₀ (univ : Finset (Lam d L N)) : EvR (Lam d L N))) : EvR (Lam d L N))

theorem Z0_mem (N : ℕ) (V₀ : Vcoup) : inv' (Z0 d L N V₀) = Z0 d L N V₀ :=
  mem_Ev.1 (gexp (-(VE V₀ (univ : Finset (Lam d L N)) : EvR (Lam d L N))) : EvR (Lam d L N)).2

/-- The partial sums of the constants `u_{j+1}`. -/
theorem EC_theta_partial (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} {msq ℓ₀ : ℝ}
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    ∀ j ≤ N, EC (∑ i ∈ range j, covAt d L N msq i) (theta (Z0 d L N V₀)) =
      Complex.exp (-((∑ i ∈ range j, uflow d L N msq V₀ i) * (Fintype.card (Lam d L N) : ℂ))) •
        (Zj j (flowN d L N msq V₀ j).1 (flowN d L N msq V₀ j).2 : Alg d L N) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [sum_range_zero, sum_range_zero, zero_mul, neg_zero, Complex.exp_zero, one_smul,
      EC_theta, expL_eq_self _ (by simp [Lop_apply]), flowN_zero, Zj_zero]
    rfl
  | succ j ih =>
    intro hj
    rw [sum_range_succ, ← EC_theta_comp, ih (by omega), map_smul, map_smul]
    have hZ := ZVK' hd hL (by omega : j < N) (hgood j (by omega)) (flowN d L N msq V₀ j).1
      (InK_flowN hd hL hgood V₀ j (by omega))
    have hZ' := congrArg (fun x : EvR (Lam d L N) => (x : Alg d L N)) hZ
    simp only [coe_ECE, coe_thetaE, Subalgebra.coe_smul] at hZ'
    rw [hZ', smul_smul, ← Complex.exp_add, sum_range_succ, flowN_succ, Zj_restr]
    congr 2
    · rw [uflow, card_univ]; ring

variable (d L) in
/-- `Z_{N,N} = 𝔼_C θ Z_0`, `C = (-Δ + m²)^{-1}`. -/
def ZNN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : Alg d L N := EC (Cov d L N msq) (theta (Z0 d L N V₀))

variable (d L) in
/-- `u_N = ∑_{j<N} u_{j+1}`. -/
def uN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℂ := ∑ j ∈ range N, uflow d L N msq V₀ j

variable (d L) in
/-- `Z̃_{N,N} = e^{u_N |Λ|} Z_{N,N}`. -/
def ZtNN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : Alg d L N :=
  Complex.exp (uN d L N msq V₀ * Fintype.card (Lam d L N)) • ZNN d L N msq V₀

variable (d L) in
/-- `V_N`. -/
abbrev VN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : Vcoup := (flowN d L N msq V₀ N).1

variable (d L) in
/-- `K_N(Λ_N)`. -/
abbrev KN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : EvR (Lam d L N) := (flowN d L N msq V₀ N).2 univ

variable (d L) in
/-- `a_N`. -/
abbrev aN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℂ := (VN d L N msq V₀).a

variable (d L) in
/-- `k_N^0`: the constant term of `K_N(Λ)`. -/
def kN0 (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℂ := ε (KN d L N msq V₀ : Alg d L N)

variable (d L) in
/-- `k_N^2 = ∑_{x,y} K_N(Λ)_{(x,+),(y,-)}`: the coefficient of `ψψ̄` of `K_N(Λ)` restricted to
constant fields. -/
def kN2 (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℂ := c2 (KN d L N msq V₀ : Alg d L N)

variable (d L) in
/-- `ã_{N,N} = a_N - k_N^2 / |Λ_N|`. -/
def atN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℂ :=
  aN d L N msq V₀ - kN2 d L N msq V₀ / Fintype.card (Lam d L N)

variable (d L) in
/-- `ũ_{N,N} = k_N^0 + ã_{N,N} t_N`. -/
def utN (N : ℕ) (msq : ℝ) (V₀ : Vcoup) : ℂ :=
  kN0 d L N msq V₀ + atN d L N msq V₀ * (tNN d L N msq : ℂ)

/-- **`e:ZNN-def`, `e:P41integrand`**: `Z_{N,N} = 𝔼_C θ Z_0 = e^{-u_N |Λ|} 𝔼_{t_N Q_N} θ Z_N` with
`Z_N = e^{-V_N(Λ)} + K_N(Λ)`. -/
theorem ZNN_eq (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    ZNN d L N msq V₀ = Complex.exp (-(uN d L N msq V₀ * Fintype.card (Lam d L N))) •
      EC (tNN d L N msq • QN) (theta (((gexp (-(VE (VN d L N msq V₀) (univ : Finset (Lam d L N)) : EvR (Lam d L N))) +
        KN d L N msq V₀ : EvR (Lam d L N))) : Alg d L N)) := by
  rw [ZNN, Cov_eq hmsq hN, ← EC_theta_comp, EC_theta_partial hd hL hgood V₀ N le_rfl, map_smul,
    map_smul, Zj_top]
  rfl

/-- `Z̃_{N,N} = 𝔼_{t_N Q_N} θ (e^{-V_N(Λ)} + K_N(Λ))` (`e:P41integrand`). -/
theorem ZtNN_eq (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N : ℕ} (hN : 1 ≤ N) {msq ℓ₀ : ℝ}
    (hmsq : 0 < msq)
    (hgood : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (covAt d L N msq j)) (V₀ : Vcoup) :
    ZtNN d L N msq V₀ = EC (tNN d L N msq • QN) (theta (((gexp (-(VE (VN d L N msq V₀) (univ : Finset (Lam d L N)) : EvR (Lam d L N))) +
        KN d L N msq V₀ : EvR (Lam d L N))) : Alg d L N)) := by
  rw [ZtNN, ZNN_eq hd hL hN hmsq hgood V₀, smul_smul, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_smul]

end

end Suscept
