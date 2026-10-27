import DressedFRD.LipAux

/-!
# The Lipschitz bound for one step of the construction

For two coupling sequences `ζ` (of `D`) and `ζ'` (of `D' = D.withζ ζ'`):
* `Wn D i r = Z_i R_{i,r}` are the normalised tails, `Wn_succ`: `W_{i+1}(r) = W_i(r) + w^{(i)}_r`.
* `Dlt i = ∑_{r > i} W_{r-i} ‖W_i(r) - W'_i(r)‖_{(r-1)}`.
* `Elt i = ∑_{s > i} W_{s-1-i} ‖w^{(i)}_s - w'^{(i)}_s‖_{(s-1)}`.
* `Dlt_succ_le`: `Dlt (i+1) ≤ θ^{6/256} Dlt i + Elt i`.
* `Elt_le`: `Elt i ≤ 4 K₁ |ζ_i - ζ'_i| + 4 C_ρ K₁ θ Dlt i` (Schwarz lemma for the step map).
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD Metric

variable {d n : ℕ} [NeZero n]

namespace Data

/-- The normalised tails `W_i(r) = Z_i R_{i,r}`. -/
def Wn (D : Data d n) (i r : ℕ) : Sym d n := D.Z i • D.tails i r

variable {D : Data d n}

theorem Wn_succ (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) {i r : ℕ} (hr : i + 2 ≤ r ∧ r ≤ D.N) :
    D.Wn (i + 1) r = D.Wn i r + D.wSc i (D.tails i) r := by
  unfold Wn
  rw [tails]; dsimp only
  rw [if_pos hr, smul_smul, mul_inv_cancel₀ (Z_ne_zero hζ (i + 1)), one_smul]

/-- The step map depends on the tails only through `Z_j R` and on `ζ_j` only through `ζ'_j`. -/
theorem wSc_eq_of_Wn {ζ₁ : ℕ → ℂ} {j : ℕ} {R R' : ℕ → Sym d n}
    (hzp : (D.withζ ζ₁).zp j = D.zp j) (hW : ∀ r, (D.withζ ζ₁).Z j • R' r = D.Z j • R r) :
    (D.withζ ζ₁).wSc j R' = D.wSc j R := by
  have hA : ∀ r, (D.withζ ζ₁).Z j • (Asym D.msq * R' r) = D.Z j • (Asym D.msq * R r) := by
    intro r; rw [← mul_smul_comm, hW, mul_smul_comm]
  have hl : (D.withζ ζ₁).letV j R' = D.letV j R := by
    funext κ ℓ
    rcases ℓ with _ | r
    · fin_cases κ <;> rfl
    · fin_cases κ
      · show -((D.withζ ζ₁).Z j • R' r) = -(D.Z j • R r); rw [hW]
      · show (D.withζ ζ₁).Z j • (Asym D.msq * R' r) = D.Z j • (Asym D.msq * R r); rw [hA]
      · show -((D.withζ ζ₁).Z j • (Asym D.msq * R' r)) = -(D.Z j • (Asym D.msq * R r)); rw [hA]
  have he : (D.withζ ζ₁).eps j R' = D.eps j R := by
    show Ehat D.msq D.C j - ∑ r ∈ Ioc j D.N, (D.withζ ζ₁).Z j • (Asym D.msq * R' r) = _
    rw [sum_congr rfl fun r _ => hA r]; rfl
  have hw : ∀ s k, (D.withζ ζ₁).wLen j R' s k = D.wLen j R s k := fun s k => by
    unfold wLen; rw [hl]; rfl
  have hlow : ∀ s, (D.withζ ζ₁).wLow j R' s = D.wLow j R s := fun s => by
    unfold wLow; simp only [hw, hzp]; rfl
  have htot : (D.withζ ζ₁).wTot j R' = D.wTot j R := by unfold wTot; rw [he, hzp]; rfl
  unfold wSc wTop; simp only [hlow, htot]; rfl

/-- `C'_{j+1} = C_{j+1} + W_j(j+1) + w^{(j)}_{j+1}`. -/
theorem Z_Gint_Wn (hζ : ∀ i, ‖D.ζ i‖ ≤ 1 / 2) {j : ℕ} (hjN : j + 1 < D.N) :
    D.Z (j + 1) • D.Gint j = ofR (D.C (j + 1)) + D.Wn j (j + 1) + D.wSc j (D.tails j) (j + 1) := by
  rw [Z_Gint hζ hjN]; simp [Wn, wSc, hjN]

/-- The standing hypotheses of the Lipschitz estimate. -/
structure LipHyp (D : Data d n) (ζ' : ℕ → ℂ) (q : ℕ) (c₂ θ : ℝ) : Prop where
  good : Good D.L (cexp d q) c₂ (Crho d D.L) θ
  small : Crho d D.L * K1 D.L (cexp d q) c₂ θ * θ ≤ 1 / 32
  std : StdHyp D.L D.N D.msq D.C
  loc : StdLoc D.L D.N q D.msq c₂ D.C
  hL : 7 ≤ D.L
  hn : n = D.L ^ D.N
  hq : 2 ≤ q
  hd : 2 ≤ d
  hmsq : D.msq ≤ (D.L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1)))
  hζ : ∀ i, ‖D.ζ i‖ ≤ θ / 2
  hζ' : ∀ i, ‖ζ' i‖ ≤ θ / 2

variable {ζ' : ℕ → ℂ} {q : ℕ} {c₂ θ : ℝ}

/-- (H_i) and `𝒮_i ≤ K₁ θ` for any data with the same base and couplings `≤ θ/2`. -/
theorem LipHyp.sj_of (h : D.LipHyp ζ' q c₂ θ) (ζ₁ : ℕ → ℂ) (hζ₁ : ∀ i, ‖ζ₁ i‖ ≤ θ / 2)
    {i : ℕ} (hi : i < D.N) :
    (D.withζ ζ₁).StepHyp q c₂ θ i ∧
      (D.withζ ζ₁).Sj q θ i ≤ K1 D.L (cexp d q) c₂ θ * θ := by
  set X := D.withζ ζ₁
  have hθ := h.good.pos
  have hθ1 : θ ≤ 1 := by linarith [h.good.le8]
  have hX : ∀ k, ‖X.ζ k‖ ≤ θ := fun k => by
    show ‖ζ₁ k‖ ≤ θ; linarith [hζ₁ k]
  have hL1 : 1 ≤ D.L := by have := h.hL; omega
  have H0 : X.StepHyp q c₂ θ 0 := ⟨h.std, h.loc, h.hL, h.hn, h.hq, h.hd, h.hmsq, by
    show 0 < D.N; omega, tailRange_zero (D := X) hL1, hθ, hθ1⟩
  obtain ⟨H, hS⟩ := induction (D := X) h.good hX H0 i hi
  refine ⟨H, hS.trans ?_⟩
  have hMz : X.Mz i ≤ θ / 2 := Mz_le (by linarith) fun k _ => hζ₁ k
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg (by exact_mod_cast (by omega : 0 < D.L)) _)
    (h.loc 0 (by omega))
  have hK1 := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) (by positivity) hc₂ hθ.le
  show 2 * K1 D.L (cexp d q) c₂ θ * X.Mz i ≤ K1 D.L (cexp d q) c₂ θ * θ
  nlinarith

/-- `Δ_i = ∑_{r > i} W_{r-i} ‖W_i(r) - W'_i(r)‖_{(r-1)}`. -/
def Dlt (D : Data d n) (ζ' : ℕ → ℂ) (q : ℕ) (θ : ℝ) (i : ℕ) : ℝ :=
  ∑ r ∈ Ioc i D.N, Wt θ D.L (r - i) * snorm D.L q (r - 1) (D.Wn i r - (D.withζ ζ').Wn i r)

/-- `E_i = ∑_{s > i} W_{s-1-i} ‖w^{(i)}_s - w'^{(i)}_s‖_{(s-1)}`. -/
def Elt (D : Data d n) (ζ' : ℕ → ℂ) (q : ℕ) (θ : ℝ) (i : ℕ) : ℝ :=
  ∑ s ∈ Icc (i + 1) D.N, Wt θ D.L (s - 1 - i) *
    snorm D.L q (s - 1) (D.wSc i (D.tails i) s - (D.withζ ζ').wSc i ((D.withζ ζ').tails i) s)

theorem Dlt_nonneg (hθ : 0 < θ) (hL : 1 ≤ D.L) (i : ℕ) : 0 ≤ D.Dlt ζ' q θ i :=
  sum_nonneg fun r _ => mul_nonneg (Wt_pos hθ _ _).le
    (snorm_nonneg (by exact_mod_cast (by omega : 0 < D.L)) _)

theorem Dlt_zero (hL : 1 ≤ D.L) : D.Dlt ζ' q θ 0 = 0 := by
  unfold Dlt
  refine sum_eq_zero fun r _ => ?_
  have h0 : D.Wn 0 r - (D.withζ ζ').Wn 0 r = (0 : ℂ) • (0 : Sym d n) := by simp [Wn, tails]
  rw [h0, snorm_smul (show (0 : ℝ) < D.L by exact_mod_cast (by omega : 0 < D.L))]; simp

/-- `Δ_{i+1} ≤ θ^{6/256} Δ_i + E_i`. -/
theorem Dlt_succ_le (h : D.LipHyp ζ' q c₂ θ) (i : ℕ) :
    D.Dlt ζ' q θ (i + 1) ≤ θ ^ ((6 : ℝ) / 256) * D.Dlt ζ' q θ i + D.Elt ζ' q θ i := by
  have hθ := h.good.pos
  have hθ1 : θ ≤ 1 := by linarith [h.good.le8]
  have hL1 : 1 ≤ D.L := by have := h.hL; omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have h12 : ∀ k, ‖D.ζ k‖ ≤ 1 / 2 := fun k => by linarith [h.hζ k, h.good.le8]
  have h12' : ∀ k, ‖(D.withζ ζ').ζ k‖ ≤ 1 / 2 := fun k => by
    show ‖ζ' k‖ ≤ 1 / 2; linarith [h.hζ' k, h.good.le8]
  have hIoc : Ioc (i + 1) D.N = Icc (i + 2) D.N := by ext r; simp only [mem_Ioc, mem_Icc]; omega
  have hterm : ∀ r ∈ Ioc (i + 1) D.N,
      snorm D.L q (r - 1) (D.Wn (i + 1) r - (D.withζ ζ').Wn (i + 1) r) ≤
        snorm D.L q (r - 1) (D.Wn i r - (D.withζ ζ').Wn i r) +
        snorm D.L q (r - 1) (D.wSc i (D.tails i) r - (D.withζ ζ').wSc i ((D.withζ ζ').tails i) r) := by
    intro r hr
    rw [mem_Ioc] at hr
    rw [Wn_succ h12 ⟨by omega, hr.2⟩, Wn_succ (D := D.withζ ζ') h12' ⟨by omega, hr.2⟩]
    refine le_of_eq_of_le ?_ (snorm_add_le hL0 _ _)
    congr 1; abel
  unfold Dlt Elt
  calc ∑ r ∈ Ioc (i + 1) D.N, Wt θ D.L (r - (i + 1)) *
        snorm D.L q (r - 1) (D.Wn (i + 1) r - (D.withζ ζ').Wn (i + 1) r)
      ≤ ∑ r ∈ Ioc (i + 1) D.N, (θ ^ ((6 : ℝ) / 256) * (Wt θ D.L (r - i) *
          snorm D.L q (r - 1) (D.Wn i r - (D.withζ ζ').Wn i r)) + Wt θ D.L (r - 1 - i) *
          snorm D.L q (r - 1) (D.wSc i (D.tails i) r -
            (D.withζ ζ').wSc i ((D.withζ ζ').tails i) r)) := by
        refine sum_le_sum fun r hr => ?_
        have hr' := mem_Ioc.1 hr
        have hW := Wt_succ_ge hθ hθ1 (by exact_mod_cast h.hL : (7 : ℝ) ≤ D.L) (r - (i + 1))
        rw [show r - (i + 1) + 1 = r - i by omega] at hW
        rw [show r - 1 - i = r - (i + 1) by omega]
        have h1 := hterm r hr
        have hp := (Wt_pos hθ D.L (r - (i + 1))).le
        have hs1 := snorm_nonneg hL0 (q := q) (s := r - 1) (D.Wn i r - (D.withζ ζ').Wn i r)
        calc Wt θ D.L (r - (i + 1)) *
              snorm D.L q (r - 1) (D.Wn (i + 1) r - (D.withζ ζ').Wn (i + 1) r)
            ≤ Wt θ D.L (r - (i + 1)) * (snorm D.L q (r - 1) (D.Wn i r - (D.withζ ζ').Wn i r) +
              snorm D.L q (r - 1) (D.wSc i (D.tails i) r -
                (D.withζ ζ').wSc i ((D.withζ ζ').tails i) r)) := mul_le_mul_of_nonneg_left h1 hp
          _ ≤ _ := by
            rw [mul_add]
            refine add_le_add ?_ le_rfl
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right hW hs1
    _ = θ ^ ((6 : ℝ) / 256) * ∑ r ∈ Ioc (i + 1) D.N, Wt θ D.L (r - i) *
          snorm D.L q (r - 1) (D.Wn i r - (D.withζ ζ').Wn i r) +
        ∑ s ∈ Icc (i + 2) D.N, Wt θ D.L (s - 1 - i) *
          snorm D.L q (s - 1) (D.wSc i (D.tails i) s -
            (D.withζ ζ').wSc i ((D.withζ ζ').tails i) s) := by
        rw [sum_add_distrib, mul_sum, hIoc]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hθ.le _)) ?_
        · exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (by omega)) fun r _ _ =>
            mul_nonneg (Wt_pos hθ _ _).le (snorm_nonneg hL0 _)
        · exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by omega) le_rfl) fun r _ _ =>
            mul_nonneg (Wt_pos hθ _ _).le (snorm_nonneg hL0 _)

/-! ### The complex line through the two states -/

/-- The couplings on the complex line: `ζ_i(t) = ζ'_i + t (ζ_i - ζ'_i)` at position `i`, the
parameter `t` itself at position `i + 1` (it parametrises the tails), `0` elsewhere. -/
def zmap (D : Data d n) (ζ' : ℕ → ℂ) (i : ℕ) (t : ℂ) : Fin (i + 2) → ℂ := fun l =>
  if l.val = i then ζ' i + t * (D.ζ i - ζ' i) else if l.val = i + 1 then t else 0

/-- The tails on the complex line: `W'_i + z_{i+1} (W_i - W'_i)`. -/
def Rz (D : Data d n) (ζ' : ℕ → ℂ) (i : ℕ) (z : Fin (i + 2) → ℂ) : ℕ → Sym d n := fun r =>
  (D.withζ ζ').Wn i r + z ⟨i + 1, by omega⟩ • (D.Wn i r - (D.withζ ζ').Wn i r)

theorem ext_zmap_lt {i k : ℕ} (hk : k < i) (t : ℂ) : ext (D.zmap ζ' i t) k = 0 := by
  simp [ext, zmap, show k < i + 2 by omega, hk.ne, show k ≠ i + 1 by omega]

theorem ext_zmap_self (i : ℕ) (t : ℂ) : ext (D.zmap ζ' i t) i = ζ' i + t * (D.ζ i - ζ' i) := by
  simp [ext, zmap]

theorem Z_zmap (i : ℕ) (t : ℂ) : (D.Dz (D.zmap ζ' i t)).Z i = 1 := by
  unfold Z
  refine prod_eq_one fun k hk => ?_
  show 1 + ext (D.zmap ζ' i t) k = 1
  rw [ext_zmap_lt (mem_range.1 hk)]; simp

theorem Rz_zmap (i : ℕ) (t : ℂ) (r : ℕ) :
    D.Rz ζ' i (D.zmap ζ' i t) r = (D.withζ ζ').Wn i r + t • (D.Wn i r - (D.withζ ζ').Wn i r) := by
  simp [Rz, zmap]

theorem differentiableAt_zmap (i : ℕ) (t : ℂ) : DifferentiableAt ℂ (D.zmap ζ' i) t := by
  refine differentiableAt_pi.2 fun l => ?_
  by_cases h1 : l.val = i
  · simp only [zmap, h1, if_true]; fun_prop
  · by_cases h2 : l.val = i + 1
    · simp only [zmap, h2, show i + 1 ≠ i by omega, if_true, if_false]; fun_prop
    · simp only [zmap, h1, h2, if_false]; fun_prop

theorem holFam_Rz (i : ℕ) (z₀ : Fin (i + 2) → ℂ) : Hol.HolFam (z₀ := z₀) (D.Rz ζ' i) := by
  intro r m
  show (fun z : Fin (i + 2) → ℂ => (D.withζ ζ').Wn i r m +
    z ⟨i + 1, by omega⟩ * (D.Wn i r - (D.withζ ζ').Wn i r) m) ∈ holSub z₀
  exact Subring.add_mem _ (Hol.const_mem _) (Subring.mul_mem _
    (differentiableAt_apply (𝕜 := ℂ) _ _) (Hol.const_mem _))

/-- The step map on the complex line. -/
def Phi (D : Data d n) (ζ' : ℕ → ℂ) (i : ℕ) (t : ℂ) (s : ℕ) : Sym d n :=
  (D.Dz (D.zmap ζ' i t)).wSc i (D.Rz ζ' i (D.zmap ζ' i t)) s

theorem Phi_one (i s : ℕ) : D.Phi ζ' i 1 s = D.wSc i (D.tails i) s := by
  unfold Phi Dz
  rw [wSc_eq_of_Wn (D := D) (R := D.tails i)]
  · unfold zp; show ext (D.zmap ζ' i 1) i / (1 + ext (D.zmap ζ' i 1) i) = _
    rw [ext_zmap_self]; ring_nf
  · intro r
    rw [show (D.withζ (ext (D.zmap ζ' i 1))).Z i = 1 from Z_zmap i 1, one_smul, Rz_zmap, one_smul]
    simp [Wn]

theorem Phi_zero (i s : ℕ) : D.Phi ζ' i 0 s = (D.withζ ζ').wSc i ((D.withζ ζ').tails i) s := by
  show ((D.withζ ζ').withζ (ext (D.zmap ζ' i 0))).wSc i (D.Rz ζ' i (D.zmap ζ' i 0)) s = _
  rw [wSc_eq_of_Wn (D := D.withζ ζ') (R := (D.withζ ζ').tails i)]
  · unfold zp; show ext (D.zmap ζ' i 0) i / (1 + ext (D.zmap ζ' i 0) i) = ζ' i / (1 + ζ' i)
    rw [ext_zmap_self]; ring_nf
  · intro r
    rw [show ((D.withζ ζ').withζ (ext (D.zmap ζ' i 0))).Z i = 1 from Z_zmap (D := D) i 0, one_smul,
      Rz_zmap, zero_smul, add_zero]
    rfl

/-- The range bound on the complex line. -/
theorem rangeR_line (h : D.LipHyp ζ' q c₂ θ) {i : ℕ} (hi : i < D.N) (z : Fin (i + 2) → ℂ) :
    (D.Dz z).RangeR i (D.Rz ζ' i z) := by
  have hL1 : 1 ≤ D.L := by have := h.hL; omega
  have hT := tailRange (D := D) h.std hL1 h.hn i hi.le
  have hT' := tailRange (D := D.withζ ζ') h.std hL1 h.hn i hi.le
  intro r h1 h2
  have e1 : rng (D.Wn i r) ≤ rng (D.tails i r) := rng_smul_le _ _
  have e2 : rng ((D.withζ ζ').Wn i r) ≤ rng ((D.withζ ζ').tails i r) := rng_smul_le _ _
  have e3 := rng_add_le ((D.withζ ζ').Wn i r) (z ⟨i + 1, by omega⟩ • (D.Wn i r - (D.withζ ζ').Wn i r))
  have e4 := rng_smul_le (z ⟨i + 1, by omega⟩) (D.Wn i r - (D.withζ ζ').Wn i r)
  have e5 := rng_sub_le (D.Wn i r) ((D.withζ ζ').Wn i r)
  have a1 := hT r h1 h2
  have a2 := hT' r h1 h2
  show 2 * rng (D.Rz ζ' i z r) < D.L ^ r
  unfold Rz
  have : rng ((D.withζ ζ').Wn i r + z ⟨i + 1, by omega⟩ • (D.Wn i r - (D.withζ ζ').Wn i r)) ≤
      max (rng (D.tails i r)) (rng ((D.withζ ζ').tails i r)) := by
    refine e3.trans (max_le (e2.trans (le_max_right _ _)) (e4.trans (e5.trans ?_)))
    exact max_le (e1.trans (le_max_left _ _)) (e2.trans (le_max_right _ _))
  have : 2 * max (rng (D.tails i r)) (rng ((D.withζ ζ').tails i r)) < D.L ^ r := by
    rcases le_total (rng (D.tails i r)) (rng ((D.withζ ζ').tails i r)) with h | h
    · rw [max_eq_right h]; exact a2
    · rw [max_eq_left h]; exact a1
  omega

/-- `𝒮` on the complex line: `≤ 𝒮'_i + |t| Δ_i`. -/
theorem SjR_line_le (h : D.LipHyp ζ' q c₂ θ) (i : ℕ) (t : ℂ) :
    (D.Dz (D.zmap ζ' i t)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i t)) ≤
      (D.withζ ζ').Sj q θ i + ‖t‖ * D.Dlt ζ' q θ i := by
  have hθ := h.good.pos
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by have := h.hL; omega : 0 < D.L)
  show ∑ r ∈ Ioc i D.N, Wt θ D.L (r - i) * (‖(D.Dz (D.zmap ζ' i t)).Z i‖ *
      snorm D.L q (r - 1) (D.Rz ζ' i (D.zmap ζ' i t) r)) ≤
    ∑ r ∈ Ioc i D.N, Wt θ D.L (r - i) * (‖(D.withζ ζ').Z i‖ *
      snorm D.L q (r - 1) ((D.withζ ζ').tails i r)) + ‖t‖ * ∑ r ∈ Ioc i D.N, Wt θ D.L (r - i) *
      snorm D.L q (r - 1) (D.Wn i r - (D.withζ ζ').Wn i r)
  rw [Z_zmap, norm_one, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun r _ => ?_
  rw [Rz_zmap, one_mul]
  have hW := (Wt_pos hθ D.L (r - i)).le
  have e1 : snorm D.L q (r - 1) ((D.withζ ζ').Wn i r) =
      ‖(D.withζ ζ').Z i‖ * snorm D.L q (r - 1) ((D.withζ ζ').tails i r) := by
    unfold Wn; rw [snorm_smul hL0]
  have := snorm_add_le (q := q) (s := r - 1) hL0 ((D.withζ ζ').Wn i r)
    (t • (D.Wn i r - (D.withζ ζ').Wn i r))
  rw [snorm_smul hL0, e1] at this
  show Wt θ D.L (r - i) * snorm D.L q (r - 1) _ ≤ _
  nlinarith

theorem SjR_line_one (h : D.LipHyp ζ' q c₂ θ) (i : ℕ) :
    (D.Dz (D.zmap ζ' i 1)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i 1)) = D.Sj q θ i := by
  have : ∀ r, D.Rz ζ' i (D.zmap ζ' i 1) r = D.Z i • D.tails i r := fun r => by
    rw [Rz_zmap, one_smul]; simp [Wn]
  show ∑ r ∈ Ioc i D.N, Wt θ D.L (r - i) * (‖(D.Dz (D.zmap ζ' i 1)).Z i‖ *
      snorm D.L q (r - 1) (D.Rz ζ' i (D.zmap ζ' i 1) r)) =
    ∑ r ∈ Ioc i D.N, Wt θ D.L (r - i) * (‖D.Z i‖ * snorm D.L q (r - 1) (D.tails i r))
  refine sum_congr rfl fun r _ => ?_
  rw [Z_zmap, norm_one, one_mul, this,
    snorm_smul (show (0 : ℝ) < D.L by exact_mod_cast (by have := h.hL; omega : 0 < D.L))]

/-- On the good part of the line, the step map is bounded by `K₁ θ` and holomorphic. -/
theorem Phi_bound (h : D.LipHyp ζ' q c₂ θ) {i : ℕ} (hi : i < D.N) {t : ℂ}
    (hu : ‖ζ' i + t * (D.ζ i - ζ' i)‖ ≤ θ)
    (hS : Crho d D.L * (D.Dz (D.zmap ζ' i t)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i t)) ≤ 1) :
    (∑ s ∈ Icc (i + 1) D.N, Wt θ D.L (s - 1 - i) * snorm D.L q (s - 1) (D.Phi ζ' i t s) ≤
      K1 D.L (cexp d q) c₂ θ * θ) ∧
    ∀ s m, DifferentiableAt ℂ (fun t => D.Phi ζ' i t s m) t := by
  set X := D.Dz (D.zmap ζ' i t) with hXdef
  have hθ := h.good.pos
  have hθ1 : θ ≤ 1 := by linarith [h.good.le8]
  have hL1 : 1 ≤ D.L := by have := h.hL; omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hXi : X.ζ i = ζ' i + t * (D.ζ i - ζ' i) := ext_zmap_self i t
  have H : X.StepHyp q c₂ θ i := ⟨h.std, h.loc, h.hL, h.hn, h.hq, h.hd, h.hmsq, hi,
    tailRange (D := X) h.std hL1 h.hn i hi.le, hθ, hθ1⟩
  have hR := rangeR_line h hi (D.zmap ζ' i t)
  have hζX : ‖X.ζ i‖ ≤ θ := by rw [hXi]; exact hu
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (h.loc 0 (by omega))
  have hK1 := K1_nonneg (L := (D.L : ℝ)) (c := cexp d q) hL0.le hc₂ hθ.le
  refine ⟨?_, fun s m => ?_⟩
  · have := word_sum_leR (D := X) h.good hζX H hR hS
    calc ∑ s ∈ Icc (i + 1) D.N, Wt θ D.L (s - 1 - i) * snorm D.L q (s - 1) (D.Phi ζ' i t s)
        ≤ K1 D.L (cexp d q) c₂ θ * ‖X.ζ i‖ := this
      _ ≤ K1 D.L (cexp d q) c₂ θ * θ := mul_le_mul_of_nonneg_left hζX hK1
  · have hden : 1 - X.zp i * X.eps i (D.Rz ζ' i (D.zmap ζ' i t)) m ≠ 0 := by
      have h2 := norm_zp_eps_leR H hR hζX h.good.le8 hS m
      intro h0
      have : X.zp i * X.eps i (D.Rz ζ' i (D.zmap ζ' i t)) m = 1 := by linear_combination -h0
      rw [this, norm_one] at h2; norm_num at h2
    have h1 : 1 + ext (D.zmap ζ' i t) i ≠ 0 := by
      intro h0
      have : ext (D.zmap ζ' i t) i = -1 := by linear_combination h0
      have h3 : ‖X.ζ i‖ = 1 := by
        show ‖ext (D.zmap ζ' i t) i‖ = 1
        rw [this, norm_neg, norm_one]
      linarith [h.good.le8]
    have hG := Hol.wSc_mem (D := D) (z₀ := D.zmap ζ' i t) (k := i) h1 (holFam_Rz i _) s m hden
    exact (Hol.mem_holSub.1 hG).comp t (differentiableAt_zmap i t)

theorem exists_snorm_eq (L : ℝ) (q s : ℕ) (w : Sym d n) :
    ∃ α, Grassmann.mabs α ≤ q ∧ snorm L q s w = wgt d L s α * mom α w := by
  obtain ⟨α, hα, he⟩ := Finset.exists_mem_eq_sup' ⟨0, zero_mem_alphas (d := d) q⟩
    (fun α => wgt d L s α * mom α w)
  exact ⟨α, mem_alphas.1 hα, he⟩

theorem sum_prod_mom (T : Finset ℕ) (a g : ℕ → ℝ) (α : ℕ → Dir d → ℕ) (v : ℕ → Sym d n) :
    ∑ x ∈ T ×ˢ (univ : Finset (Torus d n)),
        (a x.1 * (g x.1 * (((n : ℝ) ^ d)⁻¹ * ‖sigma (α x.1) x.2‖))) * ‖v x.1 x.2‖ =
      ∑ s ∈ T, a s * (g s * mom (α s) (v s)) := by
  rw [sum_product]
  refine sum_congr rfl fun s _ => ?_
  simp only [mom, avg, mul_sum]
  exact sum_congr rfl fun m _ => by ring

/-- **The Lipschitz bound for one step**:
`E_i ≤ 4 K₁ |ζ_i - ζ'_i| + 4 C_ρ K₁ θ Δ_i`. -/
theorem Elt_le (h : D.LipHyp ζ' q c₂ θ) {i : ℕ} (hi : i < D.N) :
    D.Elt ζ' q θ i ≤ 4 * K1 D.L (cexp d q) c₂ θ * ‖D.ζ i - ζ' i‖ +
      4 * (Crho d D.L * K1 D.L (cexp d q) c₂ θ * θ) * D.Dlt ζ' q θ i := by
  have hθ := h.good.pos
  have hL1 : 1 ≤ D.L := by have := h.hL; omega
  have hL0 : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hc₂ : 0 ≤ c₂ := le_trans (snorm_nonneg hL0 _) (h.loc 0 (by omega))
  set K := K1 D.L (cexp d q) c₂ θ with hKdef
  have hK : 0 ≤ K := K1_nonneg hL0.le hc₂ hθ.le
  have hCρ : 0 ≤ Crho d D.L := Crho_nonneg d hL0.le
  have hΔ0 : 0 ≤ D.Dlt ζ' q θ i := Dlt_nonneg hθ hL1 i
  set c := max (2 * ‖D.ζ i - ζ' i‖ / θ) (2 * Crho d D.L * D.Dlt ζ' q θ i) with hcdef
  have hc0 : 0 ≤ c := le_max_of_le_left (by positivity)
  obtain ⟨-, hS'⟩ := h.sj_of ζ' h.hζ' hi
  obtain ⟨-, hS⟩ := h.sj_of D.ζ h.hζ hi
  -- the good part of the line
  have hgood : ∀ t : ℂ, ‖t‖ * c ≤ 1 → ‖ζ' i + t * (D.ζ i - ζ' i)‖ ≤ θ ∧
      Crho d D.L * (D.Dz (D.zmap ζ' i t)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i t)) ≤ 1 := by
    intro t ht
    have ht0 := norm_nonneg t
    have hc1 : ‖t‖ * (2 * ‖D.ζ i - ζ' i‖ / θ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0) ht
    have hc2 : ‖t‖ * (2 * Crho d D.L * D.Dlt ζ' q θ i) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0) ht
    constructor
    · have e1 : ‖t‖ * ‖D.ζ i - ζ' i‖ ≤ θ / 2 := by
        rw [mul_div_assoc', div_le_one hθ] at hc1; linarith
      calc ‖ζ' i + t * (D.ζ i - ζ' i)‖ ≤ ‖ζ' i‖ + ‖t‖ * ‖D.ζ i - ζ' i‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ θ / 2 + θ / 2 := add_le_add (h.hζ' i) e1
        _ = θ := by ring
    · have := SjR_line_le h i t
      have hsm := h.small
      have hS'' : Crho d D.L * (D.withζ ζ').Sj q θ i ≤ 1 / 32 :=
        (mul_le_mul_of_nonneg_left hS' hCρ).trans (by rw [← mul_assoc]; exact hsm)
      calc Crho d D.L * (D.Dz (D.zmap ζ' i t)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i t))
          ≤ Crho d D.L * ((D.withζ ζ').Sj q θ i + ‖t‖ * D.Dlt ζ' q θ i) :=
            mul_le_mul_of_nonneg_left this hCρ
        _ ≤ 1 / 32 + 1 / 2 := by nlinarith
        _ ≤ 1 := by norm_num
  have hgood1 : ‖ζ' i + 1 * (D.ζ i - ζ' i)‖ ≤ θ ∧
      Crho d D.L * (D.Dz (D.zmap ζ' i 1)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i 1)) ≤ 1 := by
    constructor
    · rw [show ζ' i + 1 * (D.ζ i - ζ' i) = D.ζ i by ring]; linarith [h.hζ i]
    · rw [SjR_line_one h i]
      have : Crho d D.L * D.Sj q θ i ≤ 1 / 32 :=
        (mul_le_mul_of_nonneg_left hS hCρ).trans (by rw [← mul_assoc]; exact h.small)
      linarith
  -- the bound `2 K θ` for the differences on the good part
  have hB : ∀ t : ℂ, (‖ζ' i + t * (D.ζ i - ζ' i)‖ ≤ θ ∧
      Crho d D.L * (D.Dz (D.zmap ζ' i t)).SjR q θ i (D.Rz ζ' i (D.zmap ζ' i t)) ≤ 1) →
      ∑ s ∈ Icc (i + 1) D.N, Wt θ D.L (s - 1 - i) *
        snorm D.L q (s - 1) (D.Phi ζ' i t s - D.Phi ζ' i 0 s) ≤ 2 * (K * θ) := by
    intro t ht
    have h1 := (Phi_bound h hi ht.1 ht.2).1
    have h0 := (Phi_bound h hi (hgood 0 (by simp)).1 (hgood 0 (by simp)).2).1
    calc ∑ s ∈ Icc (i + 1) D.N, Wt θ D.L (s - 1 - i) *
          snorm D.L q (s - 1) (D.Phi ζ' i t s - D.Phi ζ' i 0 s)
        ≤ ∑ s ∈ Icc (i + 1) D.N, (Wt θ D.L (s - 1 - i) * snorm D.L q (s - 1) (D.Phi ζ' i t s) +
            Wt θ D.L (s - 1 - i) * snorm D.L q (s - 1) (D.Phi ζ' i 0 s)) := by
          refine sum_le_sum fun s _ => ?_
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (snorm_sub_le hL0 _ _) (Wt_pos hθ _ _).le
      _ ≤ K * θ + K * θ := by rw [sum_add_distrib]; exact add_le_add h1 h0
      _ = 2 * (K * θ) := by ring
  -- the weights attaining the norms at `t = 1`
  choose α hα hαe using fun s => exists_snorm_eq (d := d) (n := n) (D.L : ℝ) q (s - 1)
    (D.Phi ζ' i 1 s - D.Phi ζ' i 0 s)
  set S := Icc (i + 1) D.N ×ˢ (univ : Finset (Torus d n))
  set a : ℕ → ℝ := fun s => Wt θ D.L (s - 1 - i)
  set g : ℕ → ℝ := fun s => wgt d D.L (s - 1) (α s)
  set w : ℕ × Torus d n → ℝ := fun x => a x.1 * (g x.1 * (((n : ℝ) ^ d)⁻¹ * ‖sigma (α x.1) x.2‖))
  have hw : ∀ x ∈ S, 0 ≤ w x := fun x _ => by
    have := (Wt_pos hθ D.L (x.1 - 1 - i)).le
    have := (wgt_pos (d := d) hL0 (x.1 - 1) (α x.1)).le
    simp only [w, a, g]; positivity
  set F : ℂ → ℕ × Torus d n → ℂ := fun t x => D.Phi ζ' i t x.1 x.2
  have hsumF : ∀ t, ∑ x ∈ S, w x * ‖F t x - F 0 x‖ =
      ∑ s ∈ Icc (i + 1) D.N, a s * (g s * mom (α s) (D.Phi ζ' i t s - D.Phi ζ' i 0 s)) :=
    fun t => sum_prod_mom _ a g α (fun s => D.Phi ζ' i t s - D.Phi ζ' i 0 s)
  have hle : ∀ t, ∑ x ∈ S, w x * ‖F t x - F 0 x‖ ≤ ∑ s ∈ Icc (i + 1) D.N, Wt θ D.L (s - 1 - i) *
      snorm D.L q (s - 1) (D.Phi ζ' i t s - D.Phi ζ' i 0 s) := fun t => by
    rw [hsumF]
    exact sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (le_snorm (hα s) _) (Wt_pos hθ _ _).le
  have heq1 : ∑ x ∈ S, w x * ‖F 1 x - F 0 x‖ = D.Elt ζ' q θ i := by
    rw [hsumF]
    unfold Elt
    refine sum_congr rfl fun s _ => ?_
    simp only [a, g]
    rw [← hαe s, Phi_one, Phi_zero]
  have key := sum_lip_of_hol S w hw F hc0
    (fun x _ t ht => (Phi_bound h hi (hgood t ht.le).1 (hgood t ht.le).2).2 x.1 x.2)
    (fun t ht => (hle t).trans (hB t (hgood t ht)))
    ((hle 1).trans (hB 1 hgood1))
  rw [heq1] at key
  have hcle : c ≤ 2 * ‖D.ζ i - ζ' i‖ / θ + 2 * Crho d D.L * D.Dlt ζ' q θ i :=
    max_le_add_of_nonneg (by positivity) (by positivity)
  calc D.Elt ζ' q θ i ≤ 2 * (K * θ) * c := key
    _ ≤ 2 * (K * θ) * (2 * ‖D.ζ i - ζ' i‖ / θ + 2 * Crho d D.L * D.Dlt ζ' q θ i) :=
        mul_le_mul_of_nonneg_left hcle (by positivity)
    _ = 4 * K * ‖D.ζ i - ζ' i‖ + 4 * (Crho d D.L * K * θ) * D.Dlt ζ' q θ i := by
        field_simp; ring

end Data

end

end DressedFRD
