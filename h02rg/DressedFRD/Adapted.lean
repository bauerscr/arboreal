import DressedFRD.Construction

/-!
# `thm:main`(ii): reality and adaptedness

* `realSub`: the subring of symbols that are real-valued and even, i.e. symbols of real symmetric
  operators. If the `C_k` are even and `ζ_0, …, ζ_j` are real, then `R_{j+1,r}`, `Γ_{j+1}` and
  `Γ^int_{j+1}` lie in `realSub` (`tails_mem`, `Gam_mem`, `Gint_mem`).
* Adaptedness: `Γ^int_{j+1}` and `Γ_{j+1}` depend only on `ζ_0, …, ζ_j` (`Gint_congr`,
  `Gam_congr`).
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- Real-valued even symbols. -/
def realSub : Subring (Sym d n) where
  carrier := {w | ∀ m, conj (w m) = w m ∧ w (-m) = w m}
  mul_mem' {a b} ha hb m := by
    simp only [Pi.mul_apply, map_mul, (ha m).1, (hb m).1, (ha m).2, (hb m).2, and_self]
  one_mem' m := by simp
  add_mem' {a b} ha hb m := by
    simp only [Pi.add_apply, map_add, (ha m).1, (hb m).1, (ha m).2, (hb m).2, and_self]
  zero_mem' m := by simp
  neg_mem' {a} ha m := by simp only [Pi.neg_apply, map_neg, (ha m).1, (ha m).2, and_self]

theorem ofR_mem {f : Torus d n → ℝ} (hf : ∀ m, f (-m) = f m) : ofR f ∈ realSub := fun m => by
  simp [ofR, hf]

theorem smul_mem {c : ℂ} (hc : conj c = c) {w : Sym d n} (hw : w ∈ realSub) : c • w ∈ realSub :=
  fun m => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, (hw m).1, (hw m).2, and_self]

/-- Pointwise expressions in real even symbols. -/
theorem div_mem {v w : Sym d n} (hv : v ∈ realSub) (hw : w ∈ realSub) :
    (fun m => v m / w m) ∈ realSub := fun m => by
  simp only [map_div₀, (hv m).1, (hw m).1, (hv m).2, (hw m).2, and_self]

theorem Asym_mem (msq : ℝ) : Asym (d := d) (n := n) msq ∈ realSub := fun m => by
  simp [Asym, lam_neg]

variable {C : ℕ → Torus d n → ℝ}

theorem Cle_mem (hC : ∀ k m, C k (-m) = C k m) (j : ℕ) : Cle C j ∈ realSub :=
  Subring.sum_mem _ fun k _ => ofR_mem (hC k)

theorem Cgt_mem (hC : ∀ k m, C k (-m) = C k m) (N j : ℕ) : Cgt C N j ∈ realSub :=
  Subring.sum_mem _ fun k _ => ofR_mem (hC k)

theorem Ehat_mem (hC : ∀ k m, C k (-m) = C k m) (msq : ℝ) (j : ℕ) : Ehat msq C j ∈ realSub :=
  Subring.mul_mem _ (Asym_mem msq) (Cle_mem hC j)

namespace Data

variable {D : Data d n}

theorem Z_real {j : ℕ} (hζ : ∀ i < j, conj (D.ζ i) = D.ζ i) : conj (D.Z j) = D.Z j := by
  simp only [Z, map_prod, map_add, map_one]
  exact prod_congr rfl fun i hi => by rw [hζ i (mem_range.1 hi)]

theorem zp_real' {j : ℕ} (hζ : conj (D.ζ j) = D.ζ j) : conj (D.zp j) = D.zp j := by
  simp [zp, map_div₀, hζ]

variable (hC : ∀ k m, D.C k (-m) = D.C k m)
include hC

theorem letV_mem {j : ℕ} (hZ : conj (D.Z j) = D.Z j) {R : ℕ → Sym d n}
    (hR : ∀ r, R r ∈ realSub) (κ : Fin 3) (ℓ : Option ℕ) : D.letV j R κ ℓ ∈ realSub := by
  have hA := Asym_mem (d := d) (n := n) D.msq
  rcases ℓ with _ | r <;> fin_cases κ
  · exact Cle_mem hC j
  · exact Subring.sub_mem _ (Subring.one_mem _) (Ehat_mem hC _ j)
  · exact Ehat_mem hC _ j
  · exact Subring.neg_mem _ (smul_mem hZ (hR r))
  · exact smul_mem hZ (Subring.mul_mem _ hA (hR r))
  · exact Subring.neg_mem _ (smul_mem hZ (Subring.mul_mem _ hA (hR r)))

theorem eps_mem {j : ℕ} (hZ : conj (D.Z j) = D.Z j) {R : ℕ → Sym d n}
    (hR : ∀ r, R r ∈ realSub) : D.eps j R ∈ realSub :=
  Subring.sub_mem _ (Ehat_mem hC _ j) (Subring.sum_mem _ fun r _ =>
    smul_mem hZ (Subring.mul_mem _ (Asym_mem _) (hR r)))

theorem wLen_mem {j : ℕ} (hZ : conj (D.Z j) = D.Z j) {R : ℕ → Sym d n}
    (hR : ∀ r, R r ∈ realSub) (s k : ℕ) : D.wLen j R s k ∈ realSub :=
  Subring.sum_mem _ fun w _ => Subring.prod_mem _ fun i _ => letV_mem hC hZ hR _ _

theorem wLow_mem {j : ℕ} (hZ : conj (D.Z j) = D.Z j) (hzp : conj (D.zp j) = D.zp j)
    {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ realSub) (s : ℕ) : D.wLow j R s ∈ realSub :=
  Subring.sum_mem _ fun k _ => smul_mem (by rw [map_pow, hzp]) (wLen_mem hC hZ hR s k)

theorem wTot_mem {j : ℕ} (hZ : conj (D.Z j) = D.Z j) (hzp : conj (D.zp j) = D.zp j)
    {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ realSub) : D.wTot j R ∈ realSub := by
  have he := eps_mem hC hZ hR
  have hc : (fun _ => D.zp j : Sym d n) ∈ realSub := fun m => ⟨hzp, rfl⟩
  have hA := Asym_mem (d := d) (n := n) D.msq
  have hAi : (fun m => (Asym D.msq m)⁻¹ : Sym d n) ∈ realSub := by
    have := div_mem (Subring.one_mem realSub) hA
    simpa only [Pi.one_apply, one_div] using this
  have hnum := Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hc hAi) he)
    (Subring.sub_mem _ (Subring.one_mem _) he)
  have hden := Subring.sub_mem _ (Subring.one_mem _) (Subring.mul_mem _ hc he)
  exact div_mem hnum hden

theorem wSc_mem {j : ℕ} (hZ : conj (D.Z j) = D.Z j) (hzp : conj (D.zp j) = D.zp j)
    {R : ℕ → Sym d n} (hR : ∀ r, R r ∈ realSub) (s : ℕ) : D.wSc j R s ∈ realSub := by
  unfold wSc wTop
  split_ifs
  · exact wLow_mem hC hZ hzp hR s
  · exact Subring.sub_mem _ (wTot_mem hC hZ hzp hR)
      (Subring.sum_mem _ fun s _ => wLow_mem hC hZ hzp hR s)

/-- The tails `R_{j,r}` are real and even if `ζ_0, …, ζ_{j-1}` are real. -/
theorem tails_mem : ∀ j, (∀ i < j, conj (D.ζ i) = D.ζ i) → ∀ r, D.tails j r ∈ realSub
  | 0, _, _ => Subring.zero_mem _
  | j + 1, hζ, r => by
    have hZ := Z_real (D := D) (j := j) fun i hi => hζ i (by omega)
    have hZ1 := Z_real (D := D) (j := j + 1) hζ
    have hzp := zp_real' (D := D) (hζ j (by omega))
    have ih := tails_mem j fun i hi => hζ i (by omega)
    unfold tails
    split_ifs
    · exact smul_mem (by rw [map_inv₀, hZ1]) (Subring.add_mem _ (smul_mem hZ (ih r))
        (wSc_mem hC hZ hzp ih r))
    · exact Subring.zero_mem _

theorem Gam_mem {j : ℕ} (hζ : ∀ i < j, conj (D.ζ i) = D.ζ i) : D.Gam j ∈ realSub :=
  Subring.add_mem _ (smul_mem (by rw [map_inv₀, Z_real hζ]) (Cgt_mem hC _ j))
    (Subring.sum_mem _ fun r _ => tails_mem hC j hζ r)

/-- `thm:main`(ii), reality: `Γ^int_{j+1}` is real and even if `ζ_0, …, ζ_j` are real. -/
theorem Gint_mem {j : ℕ} (hζ : ∀ i ≤ j, conj (D.ζ i) = D.ζ i) : D.Gint j ∈ realSub := by
  have hζ' : ∀ i < j, conj (D.ζ i) = D.ζ i := fun i hi => hζ i hi.le
  have hZ := Z_real hζ'
  have hZ1 := Z_real (D := D) (j := j + 1) fun i hi => hζ i (by omega)
  have hzp := zp_real' (hζ j le_rfl)
  have hR := tails_mem hC j hζ'
  unfold Gint
  split_ifs
  · exact smul_mem (by rw [map_inv₀, hZ1]) (Subring.add_mem _ (Subring.add_mem _
      (ofR_mem (hC _)) (smul_mem hZ (hR _))) (wSc_mem hC hZ hzp hR _))
  · have hG := Gam_mem hC hζ'
    have hz : (fun _ => D.ζ j * D.Z j : Sym d n) ∈ realSub := fun m =>
      ⟨by rw [map_mul, hζ j le_rfl, hZ], rfl⟩
    exact div_mem hG (Subring.add_mem _ (Subring.one_mem _)
      (Subring.mul_mem _ (Subring.mul_mem _ hz (Asym_mem _)) hG))

end Data

/-! ### Adaptedness -/

namespace Data

variable (D : Data d n) (ζ' : ℕ → ℂ)

/-- `D` with the couplings replaced by `ζ'`. -/
def withζ : Data d n := { D with ζ := ζ' }

variable {D ζ'}

theorem Z_congr {j : ℕ} (h : ∀ i < j, D.ζ i = ζ' i) : (D.withζ ζ').Z j = D.Z j :=
  prod_congr rfl fun i hi => by simp [withζ, h i (mem_range.1 hi)]

theorem zp_congr {j : ℕ} (h : D.ζ j = ζ' j) : (D.withζ ζ').zp j = D.zp j := by
  simp [zp, withζ, h]

theorem wSc_congr {j : ℕ} (hZ : (D.withζ ζ').Z j = D.Z j) (hzp : (D.withζ ζ').zp j = D.zp j)
    (R : ℕ → Sym d n) : (D.withζ ζ').wSc j R = D.wSc j R := by
  have hl : (D.withζ ζ').letV j R = D.letV j R := by
    funext κ ℓ; unfold letV; rw [hZ]; rfl
  have he : (D.withζ ζ').eps j R = D.eps j R := by unfold eps; rw [hZ]; rfl
  have hw : ∀ s k, (D.withζ ζ').wLen j R s k = D.wLen j R s k := fun s k => by
    unfold wLen; rw [hl]; rfl
  have hlow : ∀ s, (D.withζ ζ').wLow j R s = D.wLow j R s := fun s => by
    unfold wLow; simp only [hw, hzp]; rfl
  have htot : (D.withζ ζ').wTot j R = D.wTot j R := by unfold wTot; rw [he, hzp]; rfl
  unfold wSc wTop; simp only [hlow, htot]; rfl

theorem tails_congr : ∀ j, (∀ i < j, D.ζ i = ζ' i) → (D.withζ ζ').tails j = D.tails j
  | 0, _ => rfl
  | j + 1, h => by
    have ih := tails_congr j fun i hi => h i (by omega)
    funext r
    have hZ := Z_congr (D := D) (j := j) fun i hi => h i (by omega)
    have hZ1 := Z_congr (D := D) (j := j + 1) h
    have hzp := zp_congr (D := D) (h j (by omega))
    simp only [tails]
    rw [ih, hZ, hZ1, wSc_congr hZ hzp]; rfl

theorem Gam_congr {j : ℕ} (h : ∀ i < j, D.ζ i = ζ' i) : (D.withζ ζ').Gam j = D.Gam j := by
  unfold Gam; rw [Z_congr h, tails_congr j h]; rfl

/-- `thm:main`(ii), adaptedness: `Γ^int_{j+1}` depends only on `ζ_0, …, ζ_j`. -/
theorem Gint_congr {j : ℕ} (h : ∀ i ≤ j, D.ζ i = ζ' i) : (D.withζ ζ').Gint j = D.Gint j := by
  have h' : ∀ i < j, D.ζ i = ζ' i := fun i hi => h i hi.le
  have hZ := Z_congr h'
  have hZ1 := Z_congr (D := D) (j := j + 1) fun i hi => h i (by omega)
  have hzp := zp_congr (h j le_rfl)
  unfold Gint absorbed
  rw [hZ, hZ1, tails_congr j h', wSc_congr hZ hzp, Gam_congr h']
  have : (D.withζ ζ').ζ j = D.ζ j := by simp [withζ, h j le_rfl]
  rw [this]; rfl

end Data

end

end DressedFRD
