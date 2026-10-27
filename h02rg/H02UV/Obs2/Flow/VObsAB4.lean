import Obs2.Flow.VObsAB3

/-!
# Bounds on the sources of the `M₄` flow; the step of the quadratic coefficients

The exact one-step identity `m4Tot_succ` (`M₄' = M₄ − ∑_BM₄(Q(B)_{ab}) − ∑_BM₄(Loc S(B)_{ab})`)
has sources that are quartic coefficients of barycentric localisations
(`cfAB4_locABtX`: `M₄(loc^{ab}_XF) = Mw_X(σ₄; t,t,·,·)(F)`). Here:

* **`supNorm_sq_le_eN2`**: `|a − b|_∞² ≤ |e|²` (the lift difference `e` is a representative of
  `b − a`);
* **`norm_cfAB4_locABt_le`**: `|M₄(loc^{ab,t}_XF)| ≤ K_{M4}ℓ^{-4}(L^j/|a−b|_∞)²‖F‖_{T_j(ℓ)}`
  (`norm_Mw_le`, `eN1_sq_div_le`), and the same for `loc^{ab}_X` and `loc^{ab}_{X,Y}` (`Y ⊆ X`);
* **`norm_cfAB4_Q2O_le`**, **`norm_cfAB4_LSO_le`**: the two sources of one step, by
  `∑_{X⊇B}‖K(X)_{ab}‖_{T_j(ℓ)}` at scale `j` and by `‖S(B_+)_{ab}‖_{T_{j+1}(ℓ')}` at scale `j+1`;
* **`m4_weighted_sum_le`** (pure): from `M_{j_x} = 0` and `|M_{k+1} − M_k| ≤
  ℓ^{-4}(L^{k+1}/s)²σ_k` with `L^{j_x} ≤ 2s`, the second-order seed weights of `PairDefSizesR3`
  are summable: `∑_k|M_k|·2ℓ²(L^{j_x+1}ℓ/L^{k+1})² ≤ 16∑_kσ_k` (the norm-weighted `M₄` decays like
  `L^{-2(k−i)}` from the scale `i` of its source);
* the quadratic coefficients under `e^{ℒ_C}` (**`cfAB2_expLC_of_ab`**): `c_{uv}(e^{ℒ_C}F) =
  c_{uv}(F) + M₄(F)κ_{uv}(C)`, `κ_{uv}(C) = c_{uv}(ℒ_C(ψ̄_aψ_aψ̄_bψ_b))`, and the one-step flow
  **`cfAB2_VpO`** of the gradient coefficients.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD

variable {d L N : ℕ} [NeZero L]

/-! ### The separation and the barycentric weight -/

/-- **`|a − b|_∞² ≤ |e|²`**: the lift difference is a representative of `b − a`. -/
theorem supNorm_sq_le_eN2 (X : Finset (Lam d L N)) (a b : Lam d L N) :
    ((supNorm (a - b) : ℕ) : ℝ) ^ 2 ≤ eN2 X a b := by
  set z : Zd d := rep (b - base X) - rep (a - base X) with hz
  have hp : (prj z : Lam d L N) = b - a := by
    rw [hz, prj_sub, prj_rep, prj_rep]; abel
  have h1 : supNorm (a - b) ≤ supNormZ z := by
    rw [← supNorm_neg, neg_sub, ← hp]; exact supNorm_prj_le z
  have he : ∀ i, eV X a b i = (z i : ℝ) := fun i => by
    simp [eV, lift, hz]
  have hsq : ∀ i, ((z i).natAbs : ℝ) ^ 2 ≤ eN2 X a b := by
    intro i
    have : ((z i).natAbs : ℝ) ^ 2 = eV X a b i ^ 2 := by
      rw [he, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [this]
    exact single_le_sum (f := fun i => eV X a b i ^ 2) (fun i _ => sq_nonneg _) (mem_univ i)
  have h2 : ((supNormZ z : ℕ) : ℝ) ^ 2 ≤ eN2 X a b := by
    rcases (univ : Finset (Fin d)).eq_empty_or_nonempty with he' | hne
    · have : supNormZ z = 0 := by unfold supNormZ; rw [he', sup_empty]; rfl
      rw [this]; simpa using eN2_nonneg X a b
    · obtain ⟨i, -, hi⟩ := exists_mem_eq_sup _ hne (fun i => (z i).natAbs)
      rw [show supNormZ z = (z i).natAbs from hi]; exact hsq i
  have h3 : ((supNorm (a - b) : ℕ) : ℝ) ≤ ((supNormZ z : ℕ) : ℝ) := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ ((supNorm (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  exact (pow_le_pow_left₀ h0 h3 2).trans h2

/-- The constant of `norm_cfAB4_locABt_le`. -/
def KM4 (d : ℕ) (Cc : ℝ) : ℝ := 96 * Cc ^ 4 * d * 4 ^ (d + 1)

theorem KM4_nonneg (d : ℕ) {Cc : ℝ} : 0 ≤ KM4 d Cc := by unfold KM4; positivity

/-- **The quartic coefficient of `loc^{ab,t}`**: `|M₄| ≤ K_{M4}ℓ^{-4}(L^j/|a−b|_∞)²‖F‖`. -/
theorem norm_cfAB4_locABt_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a b : Lam d L N} (ha : a ∈ X) (hab : a ≠ b)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖cfAB4 a b (locABt X a b F)‖ ≤
      KM4 d Cc * ℓ⁻¹ ^ 4 * (((L : ℝ) ^ j) ^ 2 / ((supNorm (a - b) : ℕ) : ℝ) ^ 2) *
        (Tj d (L : ℝ) j ℓ F).toReal := by
  rw [cfAB4_locABt ha hab]
  have m4 := norm_M4_le (norm_Mw_le hCc0 hCc hL hj hX (subset_nbhd hX.1 ha) b hF sg4
    ![true, true, false, false] hℓ)
  refine m4.trans ?_
  set T := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set s : ℝ := ((supNorm (a - b) : ℕ) : ℝ)
  have hs1 : 1 ≤ s := by
    have hne : supNorm (a - b) ≠ 0 := by
      intro h0
      have hz : ∀ i, zabs (((a - b : Lam d L N) : Fin d → ZMod (L ^ N)) i) = 0 := fun i =>
        Nat.le_zero.1 ((Finset.le_sup (f := fun i =>
          zabs (((a - b : Lam d L N) : Fin d → ZMod (L ^ N)) i)) (mem_univ i)).trans h0.le)
      have : a - b = 0 := funext fun i => (zabs_eq_zero_iff _).1 (hz i)
      exact hab (sub_eq_zero.1 this)
    show (1 : ℝ) ≤ ((supNorm (a - b) : ℕ) : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  have hs0 : 0 < s := by linarith
  have hE := supNorm_sq_le_eN2 X a b
  have hE0 : 0 < eN2 X a b := lt_of_lt_of_le (by positivity) hE
  have hq : eN1 X a b ^ 2 * (eN2 X a b)⁻¹ ≤ d := eN1_sq_div_le X a b
  have hR : ((rad d L j : ℕ) : ℝ) = 2 ^ (d + 1) * (L : ℝ) ^ j := by push_cast [rad]; ring
  have hinv : (eN2 X a b)⁻¹ ≤ (s ^ 2)⁻¹ := inv_anti₀ (by positivity) hE
  have hℓ4 : 0 ≤ ℓ⁻¹ ^ 4 := by positivity
  have hAt : (2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹) ^ 2 ≤
      4 * Cc ^ 2 * (4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2) * d * (s ^ 2)⁻¹ := by
    have e : (2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹) ^ 2 =
        4 * Cc ^ 2 * ((rad d L j : ℕ) : ℝ) ^ 2 * (eN1 X a b ^ 2 * (eN2 X a b)⁻¹) *
          (eN2 X a b)⁻¹ := by ring
    have e2 : ((rad d L j : ℕ) : ℝ) ^ 2 = 4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2 := by
      rw [hR, mul_pow, ← pow_mul, show (2 : ℝ) ^ ((d + 1) * 2) = 4 ^ (d + 1) by
        rw [mul_comm, pow_mul]; norm_num]
    rw [e, e2]
    have h4 : 0 ≤ 4 * Cc ^ 2 * (4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2) := by positivity
    have h5 : 0 ≤ eN1 X a b ^ 2 * (eN2 X a b)⁻¹ := by
      have := inv_nonneg.2 hE0.le; positivity
    calc 4 * Cc ^ 2 * (4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2) * (eN1 X a b ^ 2 * (eN2 X a b)⁻¹) *
          (eN2 X a b)⁻¹
        ≤ 4 * Cc ^ 2 * (4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2) * d * (eN2 X a b)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq h4) (inv_nonneg.2 hE0.le)
      _ ≤ 4 * Cc ^ 2 * (4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2) * d * (s ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
  set At := 2 * Cc * (rad d L j : ℝ) * eN1 X a b * (eN2 X a b)⁻¹
  calc 24 * (ℓ⁻¹ ^ 4 * (At * At * (Cc * Cc))) * T
      = 24 * ℓ⁻¹ ^ 4 * At ^ 2 * Cc ^ 2 * T := by ring
    _ ≤ 24 * ℓ⁻¹ ^ 4 * (4 * Cc ^ 2 * (4 ^ (d + 1) * ((L : ℝ) ^ j) ^ 2) * d * (s ^ 2)⁻¹) *
          Cc ^ 2 * T := by
        gcongr
    _ = KM4 d Cc * ℓ⁻¹ ^ 4 * (((L : ℝ) ^ j) ^ 2 / s ^ 2) * T := by
        unfold KM4; rw [div_eq_mul_inv]; ring

/-- **The quartic coefficient of `loc^{ab}_X`** (based at `a` if `a ∈ X`, at `b` otherwise). -/
theorem norm_cfAB4_locABtX_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a b : Lam d L N} (h : a ∈ X ∨ b ∈ X) (hab : a ≠ b)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖cfAB4 a b (locABtX X a b F)‖ ≤
      KM4 d Cc * ℓ⁻¹ ^ 4 * (((L : ℝ) ^ j) ^ 2 / ((supNorm (a - b) : ℕ) : ℝ) ^ 2) *
        (Tj d (L : ℝ) j ℓ F).toReal := by
  unfold locABtX
  split_ifs with ha
  · exact norm_cfAB4_locABt_le hCc0 hCc hL hj hX ha hab hF hℓ
  · rw [cfAB4_comm, show supNorm (a - b) = supNorm (b - a) by rw [← supNorm_neg, neg_sub]]
    exact norm_cfAB4_locABt_le hCc0 hCc hL hj hX (h.resolve_left ha) (Ne.symm hab) hF hℓ

theorem norm_ratio_pts_le (P : ObsPts d L N) {X Y : Finset (Lam d L N)} (hYX : Y ⊆ X) :
    ‖(((Y ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ))‖ ≤ 1 := by
  have hc : (Y ∩ P.pts).card ≤ (X ∩ P.pts).card := card_le_card (inter_subset_inter hYX subset_rfl)
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (X ∩ P.pts).card with h0 | hpos
  · rw [h0]; simp
  · rw [div_le_one (by exact_mod_cast hpos)]; exact_mod_cast hc

/-- **The quartic coefficient of `loc^{ab}_{X,Y}`** for `Y ⊆ X`. -/
theorem norm_cfAB4_locABtXY_le {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) (P : ObsPts d L N) (hab : P.a ≠ P.b)
    {X Y : Finset (Lam d L N)} (hX : IsSmall j X) (hYX : Y ⊆ X)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖cfAB4 P.a P.b (locABtXY P X Y F)‖ ≤
      KM4 d Cc * ℓ⁻¹ ^ 4 * (((L : ℝ) ^ j) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
        (Tj d (L : ℝ) j ℓ F).toReal := by
  have hK := KM4_nonneg d (Cc := Cc)
  have hT : 0 ≤ KM4 d Cc * ℓ⁻¹ ^ 4 * (((L : ℝ) ^ j) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
      (Tj d (L : ℝ) j ℓ F).toReal := by
    have := (ENNReal.toReal_nonneg : 0 ≤ (Tj d (L : ℝ) j ℓ F).toReal); positivity
  rw [locABtXY, cfAB4_smul, norm_mul]
  by_cases hXp : P.a ∈ X ∨ P.b ∈ X
  · calc _ ≤ 1 * (KM4 d Cc * ℓ⁻¹ ^ 4 *
          (((L : ℝ) ^ j) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
            (Tj d (L : ℝ) j ℓ F).toReal) :=
          mul_le_mul (norm_ratio_pts_le P hYX)
            (norm_cfAB4_locABtX_le hCc0 hCc hL hj hX hXp hab hF hℓ) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · have h0 : X ∩ P.pts = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_inter, ObsPts.pts, mem_insert, mem_singleton] at hz
      rcases hz with ⟨hzX, rfl | rfl⟩
      · exact hXp (Or.inl hzX)
      · exact hXp (Or.inr hzX)
    rw [h0, card_empty, Nat.cast_zero, div_zero, norm_zero, zero_mul]
    exact hT

/-! ### The two sources of one step -/

section Sources

variable {Cc : ℝ} (hCc0 : 0 ≤ Cc)
  (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
    Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
    |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
  (hL : 2 ^ (d + 3) + 8 * d < L) (P : ObsPts d L N) (hab : P.a ≠ P.b)

include hCc0 hCc hL hab

/-- **The `Q` source**: `|M₄(Q(B)_{ab})| ≤ K_{M4}ℓ^{-4}(L^j/|a−b|)²∑_{X⊇B}‖K(X)_{ab}‖_{T_j(ℓ)}`. -/
theorem norm_cfAB4_Q2O_le {c : Obs.Case} (j : ℕ) (K : OAct c d L N)
    (hK : ∀ X, IsSmall j X → (K X : SA c (Lam d L N)).ab ∈ NX (nbhd j X : Set (Lam d L N)))
    (b : Fin d → ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖cfAB4 P.a P.b (Q2O P j K b : SA c (Lam d L N)).ab‖ ≤
      KM4 d Cc * ℓ⁻¹ ^ 4 * (((L : ℝ) ^ j) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
        (open Classical in ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
          (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab).toReal) := by
  classical
  have hK0 := KM4_nonneg d (Cc := Cc)
  unfold Q2O
  split_ifs with hjN
  · rw [AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
    have hsum : ∀ (s : Finset (Finset (Lam d L N))) (f : Finset (Lam d L N) → Alg d L N),
        cfAB4 P.a P.b (∑ X ∈ s, f X) = ∑ X ∈ s, cfAB4 P.a P.b (f X) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => rw [sum_empty, sum_empty]; exact coeff_zero _
      | insert x s hx ih => rw [sum_insert hx, sum_insert hx, cfAB4_add, ih]
    rw [hsum, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun X hX => ?_)
    obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    rw [LocO2_ab]
    exact norm_cfAB4_locABtXY_le hCc0 hCc hL (by omega) P hab hs hbX (hK X hs) hℓ
  · rw [show ((0 : OE c (Lam d L N)) : SA c (Lam d L N)).ab = 0 from rfl,
      show cfAB4 P.a P.b (0 : Alg d L N) = 0 from coeff_zero _, norm_zero]
    have : 0 ≤ ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X),
        (Tj d (L : ℝ) j ℓ (K X : SA c (Lam d L N)).ab).toReal :=
      sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    positivity

/-- **The `Loc S` source** (localisation at scale `j + 1`):
`|M₄(Loc_{B_+,B}S(B_+)_{ab})| ≤ K_{M4}ℓ'^{-4}(L^{j+1}/|a−b|)²‖S(B_+)_{ab}‖_{T_{j+1}(ℓ')}`. -/
theorem norm_cfAB4_LSO_le {c : Obs.Case} {j : ℕ} (hj : j + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hS : (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).ab ∈
      NX (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N)))
    {ℓ' : ℝ} (hℓ' : 0 < ℓ') :
    ‖cfAB4 P.a P.b (LSO P j C V W b : SA c (Lam d L N)).ab‖ ≤
      KM4 d Cc * ℓ'⁻¹ ^ 4 *
        (((L : ℝ) ^ (j + 1)) ^ 2 / ((supNorm (P.a - P.b) : ℕ) : ℝ) ^ 2) *
        (Tj d (L : ℝ) (j + 1) ℓ'
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)).ab).toReal := by
  rw [LSO, LocO2_ab]
  exact norm_cfAB4_locABtXY_le hCc0 hCc hL hj P hab
    (isSmall_clo (isSmall_blockSet_of_mem hb)) (subset_clo j _) hS hℓ'

end Sources

/-! ### The weighted sum of the `M₄` sizes (pure) -/

theorem m4_norm_le_sum {M : ℕ → ℂ} {jx n : ℕ} (h0 : M jx = 0) (f : ℕ → ℝ)
    (hstep : ∀ k, jx ≤ k → k < n → ‖M (k + 1) - M k‖ ≤ f k) :
    ∀ k, jx ≤ k → k ≤ n → ‖M k‖ ≤ ∑ i ∈ Ico jx k, f i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; rw [h0, norm_zero, Ico_self, sum_empty]
  | succ k hk ih =>
    intro hkn
    rw [sum_Ico_succ_top hk]
    calc ‖M (k + 1)‖ = ‖(M (k + 1) - M k) + M k‖ := by rw [sub_add_cancel]
      _ ≤ ‖M (k + 1) - M k‖ + ‖M k‖ := norm_add_le _ _
      _ ≤ f k + ∑ i ∈ Ico jx k, f i := add_le_add (hstep k hk (by omega)) (ih (by omega))
      _ = _ := add_comm _ _

/-- One term of the kernel: `ℓ_{i+1}^{-4}(L^{i+1}/s)²·2ℓ_k²(L^{j_x+1}ℓ_k/L^{k+1})² ≤ 8L^{-2(k-1-i)}`. -/
theorem m4_kernel_le (hL : (2 : ℝ) ≤ L) {jx i k : ℕ} (hik : i < k) {s : ℝ} (hs0 : 0 < s)
    (hs : (L : ℝ) ^ jx ≤ 2 * s) {ℓi ℓk : ℝ} (hℓi : 0 < ℓi) (hℓk : 0 < ℓk) (hℓ : ℓk ≤ ℓi) :
    ℓi⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) *
        (2 * ℓk ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓk / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      8 * (((L : ℝ) ^ 2)⁻¹) ^ (k - 1 - i) := by
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = i + 1 + m := ⟨k - (i + 1), by omega⟩
  rw [show i + 1 + m - 1 - i = m by omega]
  set A : ℝ := (L : ℝ) ^ (i + 1)
  set Lj : ℝ := (L : ℝ) ^ jx
  set Lm : ℝ := (L : ℝ) ^ m
  have hA : 0 < A := pow_pos hL0 _
  have hLj : 0 < Lj := pow_pos hL0 _
  have hLm : 0 < Lm := pow_pos hL0 _
  have e1 : (L : ℝ) ^ (i + 1 + m + 1) = A * Lm * L := by
    rw [show i + 1 + m + 1 = (i + 1) + m + 1 by ring, pow_succ, pow_add]
  have e2 : (L : ℝ) ^ (jx + 1) = Lj * L := pow_succ _ _
  have e3 : (((L : ℝ) ^ 2)⁻¹) ^ m = (Lm ^ 2)⁻¹ := by
    rw [inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  rw [e1, e2, e3]
  have e : ℓi⁻¹ ^ 4 * (A ^ 2 / s ^ 2) * (2 * ℓk ^ 2 * (Lj * L * (ℓk / (A * Lm * L))) ^ 2) =
      2 * (ℓk / ℓi) ^ 4 * (Lj / s) ^ 2 * (Lm ^ 2)⁻¹ := by
    field_simp
  rw [e]
  have h1 : (ℓk / ℓi) ^ 4 ≤ 1 := pow_le_one₀ (div_nonneg hℓk.le hℓi.le) ((div_le_one hℓi).2 hℓ)
  have h2 : (Lj / s) ^ 2 ≤ 4 := by
    have : Lj / s ≤ 2 := (div_le_iff₀ hs0).2 (by linarith)
    have h0 : 0 ≤ Lj / s := div_nonneg hLj.le hs0.le
    nlinarith
  have h3 : 0 ≤ (Lm ^ 2)⁻¹ := by positivity
  have h4 : 0 ≤ (ℓk / ℓi) ^ 4 := by positivity
  calc 2 * (ℓk / ℓi) ^ 4 * (Lj / s) ^ 2 * (Lm ^ 2)⁻¹ ≤ 2 * 1 * 4 * (Lm ^ 2)⁻¹ := by gcongr
    _ = 8 * (Lm ^ 2)⁻¹ := by ring

/-- **The second-order seed weights of the `M₄` sizes are summable.** If `M_{j_x} = 0` and
`|M_{k+1} − M_k| ≤ ℓ_{k+1}^{-4}(L^{k+1}/s)²σ_k` (`j_x ≤ k < n`), `L^{j_x} ≤ 2s`, `ℓ` nonincreasing,
then `∑_{j_x≤k<n}|M_k|·2ℓ_k²(L^{j_x+1}ℓ_k/L^{k+1})² ≤ 16∑_{j_x≤k<n}σ_k`. -/
theorem m4_weighted_sum_le (hL : (2 : ℝ) ≤ L) {jx : ℕ} {s : ℝ} (hs0 : 0 < s)
    (hs : (L : ℝ) ^ jx ≤ 2 * s) (ℓ : ℕ → ℝ) (hℓ : ∀ k, 0 < ℓ k)
    (hℓm : ∀ i k, i ≤ k → ℓ k ≤ ℓ i) {M : ℕ → ℂ} (h0 : M jx = 0) (σ : ℕ → ℝ)
    (hσ : ∀ k, 0 ≤ σ k)
    (n : ℕ) (hstep : ∀ k, jx ≤ k → k < n → ‖M (k + 1) - M k‖ ≤
      (ℓ (k + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (k + 1)) ^ 2 / s ^ 2) * σ k) :
    ∑ k ∈ Ico jx n, ‖M k‖ * (2 * ℓ k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2) ≤
      16 * ∑ k ∈ Ico jx n, σ k := by
  have hL0 : (0 : ℝ) < L := by linarith
  set q : ℝ := ((L : ℝ) ^ 2)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 4 := by
    rw [hq, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  set w : ℕ → ℝ := fun k => 2 * ℓ k ^ 2 * ((L : ℝ) ^ (jx + 1) * (ℓ k / (L : ℝ) ^ (k + 1))) ^ 2
  have hw : ∀ k, 0 ≤ w k := fun k => by
    have := hℓ k; have : 0 < (L : ℝ) ^ (k + 1) := pow_pos hL0 _; positivity
  have hM := m4_norm_le_sum h0 _ hstep
  have step1 : ∀ k ∈ Ico jx n, ‖M k‖ * w k ≤ ∑ i ∈ Ico jx k, 8 * q ^ (k - 1 - i) * σ i := by
    intro k hk
    have hjk := (mem_Ico.1 hk).1
    refine (mul_le_mul_of_nonneg_right (hM k hjk (mem_Ico.1 hk).2.le) (hw k)).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun i hi => ?_
    have hik := (mem_Ico.1 hi).2
    have hker := m4_kernel_le hL hik hs0 hs (hℓ (i + 1)) (hℓ k) (hℓm (i + 1) k (by omega))
    calc (ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * σ i * w k
        = ((ℓ (i + 1))⁻¹ ^ 4 * (((L : ℝ) ^ (i + 1)) ^ 2 / s ^ 2) * w k) * σ i := by ring
      _ ≤ (8 * q ^ (k - 1 - i)) * σ i := mul_le_mul_of_nonneg_right hker (hσ i)
  have step2 : ∑ k ∈ Ico jx n, ∑ i ∈ Ico jx k, 8 * q ^ (k - 1 - i) * σ i =
      ∑ i ∈ Ico jx n, ∑ k ∈ Ico (i + 1) n, 8 * q ^ (k - 1 - i) * σ i := by
    refine sum_comm' fun k i => ?_
    simp only [mem_Ico]; omega
  have hgeo : ∀ i, ∑ k ∈ Ico (i + 1) n, q ^ (k - 1 - i) ≤ 4 / 3 := by
    intro i
    rw [sum_Ico_eq_sum_range]
    have e : ∀ k ∈ range (n - (i + 1)), q ^ (i + 1 + k - 1 - i) = q ^ k := fun k _ => by
      rw [show i + 1 + k - 1 - i = k by omega]
    rw [sum_congr rfl e]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n - (i + 1)) hq0 (by linarith)
    rw [← range_eq_Ico, pow_zero] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]; linarith
  calc ∑ k ∈ Ico jx n, ‖M k‖ * w k
      ≤ ∑ k ∈ Ico jx n, ∑ i ∈ Ico jx k, 8 * q ^ (k - 1 - i) * σ i := sum_le_sum step1
    _ = ∑ i ∈ Ico jx n, ∑ k ∈ Ico (i + 1) n, 8 * q ^ (k - 1 - i) * σ i := step2
    _ = ∑ i ∈ Ico jx n, 8 * σ i * ∑ k ∈ Ico (i + 1) n, q ^ (k - 1 - i) := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ ∑ i ∈ Ico jx n, 8 * σ i * (4 / 3) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgeo i) (by have := hσ i; positivity)
    _ ≤ ∑ i ∈ Ico jx n, 16 * σ i := sum_le_sum fun i _ => by have := hσ i; nlinarith
    _ = 16 * ∑ k ∈ Ico jx n, σ k := by rw [mul_sum]

/-! ### The quadratic coefficients under `e^{ℒ_C}` and the gradient flow -/

/-- The quadratic part of `ℒ_C(ψ̄_aψ_aψ̄_bψ_b)`:
`C(b,b)ψ̄_aψ_a + C(a,a)ψ̄_bψ_b − C(a,b)ψ̄_bψ_a − C(b,a)ψ̄_aψ_b`. -/
def LopM4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) : Alg d L N :=
  C b b • m2 a a + C a a • m2 b b - C a b • m2 b a - C b a • m2 a b

theorem pm_evAB (a : Lam d L N) : PM (ev ((a, 1) : Sf (Lam d L N))) (ev (a, -1)) :=
  ⟨fun y => by simp [ev, Prod.ext_iff], fun y => by simp [ev, Prod.ext_iff]⟩

theorem m4_eq_iota (a b : Lam d L N) :
    (m4 a b : Alg d L N) = ψ (a, 1) * (ψ (a, -1) * (ψ (b, 1) * ψ (b, -1))) := by
  unfold m4 psibar psi
  rw [ψ_anticomm (a, -1) (a, 1), ψ_anticomm (b, -1) (b, 1), neg_mul_neg, mul_assoc]

/-- **`ℒ_C(ψ̄_aψ_aψ̄_bψ_b)`** (the quadratic part of `e^{ℒ_C}m₄`). -/
theorem LopC_m4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) :
    LopC C (m4 a b : Alg d L N) = LopM4 C a b := by
  rw [m4_eq_iota]
  simp only [ψ]
  rw [LopC_four C (pm_evAB a) (pm_evAB b), pairC_ev, pairC_ev, pairC_ev, pairC_ev]
  unfold LopM4 m2 psibar psi
  simp only [ψ]
  rw [ι_anticomm (ev ((b, 1) : Sf (Lam d L N))) (ev (b, -1)),
    ι_anticomm (ev ((a, 1) : Sf (Lam d L N))) (ev (b, -1)),
    ι_anticomm (ev ((a, 1) : Sf (Lam d L N))) (ev (a, -1))]
  simp only [smul_neg, neg_smul, neg_neg]
  abel

theorem cfAB2_one (u v : Lam d L N) : cfAB2 u v (1 : Alg d L N) = 0 :=
  coeff_one_of_ne' _ (by decide)

theorem cfAB2_algebraMap (u v : Lam d L N) (r : ℂ) :
    cfAB2 u v (algebraMap ℂ (Alg d L N) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, cfAB2_smul, cfAB2_one, mul_zero]

theorem cfAB2_sub (u v : Lam d L N) (F G : Alg d L N) :
    cfAB2 u v (F - G) = cfAB2 u v F - cfAB2 u v G := by
  rw [sub_eq_add_neg, cfAB2_add, show -G = (-1 : ℂ) • G by simp, cfAB2_smul]; ring

theorem cfAB2_m4 (u v a b : Lam d L N) : cfAB2 u v (m4 a b : Alg d L N) = 0 :=
  isHom_m4 a b 2 _ (by decide)

theorem cfAB2_m2 (u v x y : Lam d L N) :
    cfAB2 u v (m2 x y : Alg d L N) = if u = x ∧ v = y then 1 else 0 :=
  coeff_psibar_psi_mp x y u v

/-- `e^{ℒ_C}(ψ̄_aψ_aψ̄_bψ_b)` has quadratic coefficients those of `LopM4`. -/
theorem cfAB2_expLC_m4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (u v a b : Lam d L N) :
    cfAB2 u v (expLC C (m4 a b : Alg d L N)) = cfAB2 u v (LopM4 C a b) := by
  have h := expLC_four C (pm_evAB a) (pm_evAB b)
  rw [m4_eq_iota]
  simp only [ψ]
  rw [h, cfAB2_add, cfAB2_add, cfAB2_smul, cfAB2_one, mul_zero, add_zero]
  rw [show (ExteriorAlgebra.ι ℂ (ev ((a, 1) : Sf (Lam d L N))) *
      (ExteriorAlgebra.ι ℂ (ev ((a, -1) : Sf (Lam d L N))) *
        (ExteriorAlgebra.ι ℂ (ev ((b, 1) : Sf (Lam d L N))) *
          ExteriorAlgebra.ι ℂ (ev ((b, -1) : Sf (Lam d L N)))))) = (m4 a b : Alg d L N) by
    rw [m4_eq_iota]; rfl, cfAB2_m4, zero_add, LopC_m4]

/-- **The quadratic coefficients under `e^{ℒ_C}`** on `U(1)`-invariant elements of `𝒩({a,b})`:
`c_{uv}(e^{ℒ_C}F) = c_{uv}(F) + M₄(F)c_{uv}(LopM4)`. -/
theorem cfAB2_expLC_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N}
    {F : Alg d L N} (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) {u v : Lam d L N}
    (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) :
    cfAB2 u v (expLC C F) = cfAB2 u v F + cfAB4 a b F * cfAB2 u v (LopM4 C a b) := by
  have hp2 : cfAB2 u v (proj0 a b F) = cfAB2 u v F := coeff_proj0_two a b F hu hv
  conv_lhs => rw [eq_proj0_of_ab hN hS]
  rw [expLC_proj0, cfAB2_add, cfAB2_add, cfAB2_smul, cfAB2_one, mul_zero, add_zero, hp2,
    cfAB2_smul, cfAB2_sub, cfAB2_expLC_m4, cfAB2_m4, sub_zero]

/-- The quadratic coefficients of `LopM4` (`a ≠ b`). -/
theorem cfAB2_LopM4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N} (hab : a ≠ b) :
    cfAB2 a a (LopM4 C a b) = C b b ∧ cfAB2 b b (LopM4 C a b) = C a a ∧
      cfAB2 a b (LopM4 C a b) = -C b a ∧ cfAB2 b a (LopM4 C a b) = -C a b := by
  unfold LopM4
  simp only [cfAB2_sub, cfAB2_add, cfAB2_smul, cfAB2_m2, hab, Ne.symm hab, and_self, and_true,
    and_false, if_true, if_false]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **The gradient coefficients under `e^{ℒ_C}`**: with `M₄ = M₄(F)`,
`c_{ab}+c_{bb} ↦ c_{ab}+c_{bb} + M₄(C(a,a) − C(b,a))`, `c_{ba}+c_{bb} ↦ c_{ba}+c_{bb} +
M₄(C(a,a) − C(a,b))`, `c_{bb} ↦ c_{bb} + M₄C(a,a)` (and `c_{aa} ↦ c_{aa} + M₄C(b,b)`). -/
theorem gradCf_expLC_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N} (hab : a ≠ b)
    {F : Alg d L N} (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    cfAB2 a b (expLC C F) + cfAB2 b b (expLC C F) =
        cfAB2 a b F + cfAB2 b b F + cfAB4 a b F * (C a a - C b a) ∧
      cfAB2 b a (expLC C F) + cfAB2 b b (expLC C F) =
        cfAB2 b a F + cfAB2 b b F + cfAB4 a b F * (C a a - C a b) ∧
      cfAB2 b b (expLC C F) = cfAB2 b b F + cfAB4 a b F * C a a ∧
      cfAB2 a a (expLC C F) = cfAB2 a a F + cfAB4 a b F * C b b := by
  obtain ⟨h1, h2, h3, h4⟩ := cfAB2_LopM4 C hab
  rw [cfAB2_expLC_of_ab C hN hS (Or.inl rfl) (Or.inr rfl),
    cfAB2_expLC_of_ab C hN hS (Or.inr rfl) (Or.inr rfl),
    cfAB2_expLC_of_ab C hN hS (Or.inr rfl) (Or.inl rfl),
    cfAB2_expLC_of_ab C hN hS (Or.inl rfl) (Or.inl rfl), h1, h2, h3, h4]
  refine ⟨by ring, by ring, rfl, rfl⟩

section StepGrad

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- **The one-step flow of the quadratic coefficients of `V'_{ab}`**: for `u, v ∈ {a,b}`,
`c_{uv}(V_{j+1}(B)) = c_{uv}(V(B)) + M₄(V(B))κ_{uv} − c_{uv}(Q(B)) − M₄(Q(B))κ_{uv} −
c_{uv}(Loc_{B_+,B}S(B_+))`, `κ_{uv} = c_{uv}(LopM4 C)` (`cfAB2_LopM4`). -/
theorem cfAB2_VpO (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) {u v : Lam d L N} (hu : u = P.a ∨ u = P.b)
    (hv : v = P.a ∨ v = P.b) (b : Fin d → ℕ) :
    cfAB2 u v (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      cfAB2 u v (V b : SA .two (Lam d L N)).ab +
          cfAB4 P.a P.b (V b : SA .two (Lam d L N)).ab * cfAB2 u v (LopM4 C P.a P.b) -
        (cfAB2 u v (Q2O P j K b : SA .two (Lam d L N)).ab +
          cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab * cfAB2 u v (LopM4 C P.a P.b)) -
        cfAB2 u v (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).ab = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
  rw [h1, halg, upO_ab_eq, sub_zero, cfAB2_sub, cfAB2_algebraMap, sub_zero, uVpO_ab, cfAB2_sub,
    cfAB2_sub, cfAB2_expLC_of_ab C (hV b) (hS b) hu hv,
    cfAB2_expLC_of_ab C (Q2O_ab_mem_pair P j K b) (Q2O_ab_sym P j K b) hu hv]
  rfl

end StepGrad

/-! ### The gradient part of `e^{ℒ_C}`, of `loc^{ab,t}`, and of one step -/

theorem cfAB4_sub (a b : Lam d L N) (F G : Alg d L N) :
    cfAB4 a b (F - G) = cfAB4 a b F - cfAB4 a b G := by
  rw [sub_eq_add_neg, cfAB4_add, show -G = (-1 : ℂ) • G by simp, cfAB4_smul]; ring

theorem cfAB4_m2 (a b u v : Lam d L N) : cfAB4 a b (m2 u v : Alg d L N) = 0 :=
  cfAB4_of_isHom2 a b ((isHom_ι _).mul (isHom_ι _))

theorem cfAB4_LopM4 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) :
    cfAB4 a b (LopM4 C a b) = 0 := by
  unfold LopM4
  simp only [cfAB4_sub, cfAB4_add, cfAB4_smul, cfAB4_m2, mul_zero, sub_zero, add_zero]

theorem gradAB_sub (a b : Lam d L N) (F G : Alg d L N) :
    gradAB a b (F - G) = gradAB a b F - gradAB a b G := by
  rw [sub_eq_add_neg, gradAB_add, show -G = (-1 : ℂ) • G by simp, gradAB_smul]; simp [sub_eq_add_neg]

theorem gradAB_one (a b : Lam d L N) : gradAB a b (1 : Alg d L N) = 0 := by
  unfold gradAB; simp only [cfAB2_one, cfAB4_one, add_zero, zero_smul]

theorem gradAB_algebraMap (a b : Lam d L N) (r : ℂ) :
    gradAB a b (algebraMap ℂ (Alg d L N) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, gradAB_smul, gradAB_one, smul_zero]

/-- **The gradient part of `e^{ℒ_C}F`**: `gradAB(e^{ℒ_C}F) = gradAB F + M₄(F)·gradAB(LopM4)`. -/
theorem gradAB_expLC_of_ab (C : Matrix (Lam d L N) (Lam d L N) ℂ) {a b : Lam d L N}
    {F : Alg d L N} (hN : F ∈ NX ({a, b} : Set (Lam d L N))) (hS : IsSym F) :
    gradAB a b (expLC C F) = gradAB a b F + cfAB4 a b F • gradAB a b (LopM4 C a b) := by
  unfold gradAB
  rw [cfAB2_expLC_of_ab C hN hS (Or.inl rfl) (Or.inr rfl),
    cfAB2_expLC_of_ab C hN hS (Or.inr rfl) (Or.inr rfl),
    cfAB2_expLC_of_ab C hN hS (Or.inr rfl) (Or.inl rfl), cfAB4_expLC_of_ab C hN hS,
    cfAB4_LopM4]
  module

theorem gradAB_pbp {a b : Lam d L N} (hab : a ≠ b) : gradAB a b (pbp a : Alg d L N) = 0 := by
  have e : (pbp a : Alg d L N) = m2 a a := rfl
  unfold gradAB
  rw [e, cfAB2_m2, cfAB2_m2, cfAB2_m2, cfAB4_m2]
  simp [Ne.symm hab]

/-- **`gradAB` reproduces `Dt`** (`a ≠ b`). -/
theorem gradAB_Dt (X : Finset (Lam d L N)) {a b : Lam d L N} (hab : a ≠ b) (F : Alg d L N) :
    gradAB a b (Dt X a b F) = Dt X a b F := by
  have e1 : (dbar a b * psi a : Alg d L N) = m2 b a - m2 a a := by
    unfold dbar m2; rw [sub_mul]
  have e2 : (psibar a * dlt a b : Alg d L N) = m2 a b - m2 a a := by
    unfold dlt m2; rw [mul_sub]
  have e3 : (dbar a b * dlt a b : Alg d L N) = m2 b b - m2 b a - m2 a b + m2 a a := by
    unfold dbar dlt m2; rw [sub_mul, mul_sub, mul_sub]; abel
  have hs : ∀ (u v : Lam d L N), cfAB2 u v (Dt X a b F) =
      Mw X a b sg2 ![true, false] F * (cfAB2 u v (m2 b a) - cfAB2 u v (m2 a a)) +
      Mw X a b sg2 ![false, true] F * (cfAB2 u v (m2 a b) - cfAB2 u v (m2 a a)) +
      Mw X a b sg2 ![true, true] F * (cfAB2 u v (m2 b b) - cfAB2 u v (m2 b a) -
        cfAB2 u v (m2 a b) + cfAB2 u v (m2 a a)) := by
    intro u v
    unfold Dt
    rw [pbp_dbar_dlt, e1, e2, e3]
    simp only [cfAB2_add, cfAB2_sub, cfAB2_smul, cfAB2_m4, mul_zero, add_zero]
  have h4 : cfAB4 a b (Dt X a b F) = Mw X a b sg4 ![true, true, false, false] F := by
    unfold Dt
    rw [pbp_dbar_dlt, e1, e2, e3]
    simp only [cfAB4_add, cfAB4_sub, cfAB4_smul, cfAB4_m2, cfAB4_m4_self hab]
    ring
  unfold gradAB
  rw [hs, hs, hs, h4]
  simp only [cfAB2_m2, hab, Ne.symm hab, and_self, and_true, and_false, if_true, if_false]
  unfold Dt
  rw [pbp_dbar_dlt]
  module

/-- **The gradient part of `loc^{ab,t}_X`** (based at `a ∈ X`, `a ≠ b`) is `Dt`. -/
theorem gradAB_locABt {X : Finset (Lam d L N)} {a b : Lam d L N} (ha : a ∈ X) (hab : a ≠ b)
    (F : Alg d L N) : gradAB a b (locABt X a b F) = Dt X a b F := by
  rw [locABt, locEven_single_eq' ha subset_rfl, gradAB_add, gradAB_add, gradAB_smul, gradAB_smul,
    gradAB_one, gradAB_pbp hab, gradAB_Dt X hab, smul_zero, smul_zero, zero_add, zero_add]

/-- **The gradient source contracts**: `‖gradAB(loc^{ab,t}_XF)‖_{T_h(ℓ')} ≤ K_D(L^j/h)‖F‖_{T_j(ℓ)}`
(at `h = L^{j+1}`: a factor `K_D/L`). -/
theorem tNorm_gradAB_locABt_le (hd : 1 ≤ d) {Cc : ℝ} (hCc0 : 0 ≤ Cc)
    (hCc : ∀ m : Fin d → ℕ, (∀ i, m i ≤ 1) → ∀ R : ℝ, 1 ≤ R → ∀ α : Dir d → ℕ,
      Grassmann.mabs α ≤ pPhi d → ∀ u : Zd d,
      |D1 (fun b v => b +ᵥ v) α (cutP m R) u| ≤ Cc * R ^ (∑ i, m i) / R ^ Grassmann.mabs α)
    (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N) {X : Finset (Lam d L N)}
    (hX : IsSmall j X) {a b : Lam d L N} (ha : a ∈ X) (hab : a ≠ b)
    {F : Alg d L N} (hF : F ∈ NX (nbhd j X : Set (Lam d L N))) {ℓ ℓ' h : ℝ} (hℓ : 0 < ℓ)
    (hℓ' : 0 < ℓ') (hℓℓ : ℓ' ≤ 2 * ℓ) (hh : 0 < h) (hsh : (L : ℝ) ^ j ≤ h) :
    tNorm (Dir d) (pPhi d) h ℓ' (gradAB a b (locABt X a b F)) ≤
      ENNReal.ofReal (KD d Cc * ((L : ℝ) ^ j * h⁻¹) * (Tj d (L : ℝ) j ℓ F).toReal) := by
  rw [gradAB_locABt ha hab]
  exact tNorm_Dt_le hd hCc0 hCc hL hj hX (subset_nbhd hX.1 ha) b hF hℓ hℓ' hℓℓ hh hsh

section StepGradAB

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- **The one-step flow of the gradient part of `V'_{ab}`**:
`gradAB(V_{j+1}(B)) = gradAB(V(B)) + M₄(V(B))gradAB(LopM4) − gradAB(Q(B)) − M₄(Q(B))gradAB(LopM4)
− gradAB(Loc_{B_+,B}S(B_+))`. -/
theorem gradAB_VpO (hV : ∀ b, (V b : SA .two (Lam d L N)).ab ∈ NX ({P.a, P.b} : Set (Lam d L N)))
    (hS : ∀ b, IsSym (V b : SA .two (Lam d L N)).ab) (b : Fin d → ℕ) :
    gradAB P.a P.b (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      gradAB P.a P.b (V b : SA .two (Lam d L N)).ab +
          cfAB4 P.a P.b (V b : SA .two (Lam d L N)).ab • gradAB P.a P.b (LopM4 C P.a P.b) -
        (gradAB P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab +
          cfAB4 P.a P.b (Q2O P j K b : SA .two (Lam d L N)).ab • gradAB P.a P.b (LopM4 C P.a P.b)) -
        gradAB P.a P.b (LSO P j C V W b : SA .two (Lam d L N)).ab := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).ab = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
  rw [h1, halg, upO_ab_eq, sub_zero, gradAB_sub, gradAB_algebraMap, sub_zero, uVpO_ab, gradAB_sub,
    gradAB_sub, gradAB_expLC_of_ab C (hV b) (hS b),
    gradAB_expLC_of_ab C (Q2O_ab_mem_pair P j K b) (Q2O_ab_sym P j K b)]
  rfl

end StepGradAB

end

end Obs2
