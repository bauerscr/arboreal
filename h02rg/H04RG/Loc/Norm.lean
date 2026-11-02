import H04RG.Loc.Restr

/-!
# Norms on the two-species algebra and the restriction to one species

The lattice directions act on the sites `Λ × Fin 2` through the first factor, so the norms
`Φ_j(ℓ)`, `T_j(ℓ)` of `Grassmann.Norms` (and `Tj`) are defined on `𝒩(Λ × Fin 2)`.

* `liftT a g` extends a single-species test function to the two-species sites, by zero off
  sequences of species `a`; `phiNorm_liftT_le`: `‖liftT a g‖_Φ ≤ ‖g‖_Φ`;
* `pair_res`: `⟨res a F, g⟩ = ⟨F, liftT a g⟩`;
* `tNorm_res_le`: `‖res a F‖_T ≤ ‖F‖_T` (restriction to one species is a contraction).
-/

namespace H04RG.LocS

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

instance : AddAction (Dir d → ℕ) (LamS d L N) where
  vadd α p := (α +ᵥ p.1, p.2)
  zero_vadd p := by
    show ((0 : Dir d → ℕ) +ᵥ p.1, p.2) = p
    rw [zero_vadd]
  add_vadd α β p := by
    show ((α + β) +ᵥ p.1, p.2) = (α +ᵥ (β +ᵥ p.1), p.2)
    rw [add_vadd]

theorem vaddS_def (α : Dir d → ℕ) (p : LamS d L N) : α +ᵥ p = (α +ᵥ p.1, p.2) := rfl

/-- Forget the species label. -/
def unl (w : Sf (LamS d L N)) : Sf (Lam d L N) := (w.1.1, w.2)

theorem unl_lab (a : Fin 2) (z : Sf (Lam d L N)) : unl (lab a z) = z := rfl

theorem sh_species (b : Dir d → ℕ) (w : Sf (LamS d L N)) : (sh b w).1.2 = w.1.2 := rfl

theorem unl_sh (b : Dir d → ℕ) (w : Sf (LamS d L N)) : unl (sh b w) = sh b (unl w) := rfl

open Classical in
/-- Extension of a single-species test function by zero off species-`a` sequences. -/
def liftT (a : Fin 2) (g : TestFn (Lam d L N)) : TestFn (LamS d L N) :=
  fun n z => if ∀ i, (z i).1.2 = a then g n (unl ∘ z) else 0

theorem liftT_of_all {a : Fin 2} (g : TestFn (Lam d L N)) {n : ℕ} {z : Fin n → Sf (LamS d L N)}
    (h : ∀ i, (z i).1.2 = a) : liftT a g n z = g n (unl ∘ z) := by
  classical
  simp [liftT, h]

theorem liftT_of_not {a : Fin 2} (g : TestFn (Lam d L N)) {n : ℕ} {z : Fin n → Sf (LamS d L N)}
    (h : ¬∀ i, (z i).1.2 = a) : liftT a g n z = 0 := by
  classical
  simp [liftT, h]

theorem liftT_lab (a : Fin 2) (g : TestFn (Lam d L N)) {n : ℕ} (w : Fin n → Sf (Lam d L N)) :
    liftT a g n (lab a ∘ w) = g n w :=
  liftT_of_all g (fun _ => rfl)

/-- Derivatives of the lifted test function. -/
theorem nab_liftT (a : Fin 2) (g : TestFn (Lam d L N)) {n : ℕ} (α : Fin n → Dir d → ℕ)
    (z : Fin n → Sf (LamS d L N)) :
    nab α (liftT a g n) z = if ∀ i, (z i).1.2 = a then nab α (g n) (unl ∘ z) else 0 := by
  classical
  split_ifs with h
  · have h1 : nab α (liftT a g n) z = nab α (fun w => g n fun i => unl (w i)) z := by
      refine nabla_congr sh α z fun β => ?_
      exact liftT_of_all g (fun i => by rw [sh_species]; exact h i)
    rw [h1]
    exact nabla_comp_pi sh sh (fun _ => unl) (fun _ b w => unl_sh b w) α (g n) z
  · have h1 : nab α (liftT a g n) z = nab α (fun _ => (0 : ℂ)) z := by
      refine nabla_congr sh α z fun β => ?_
      refine liftT_of_not g fun hall => h fun i => ?_
      have := hall i
      rwa [sh_species] at this
    rw [h1]
    exact congrFun (map_zero (nab (W := ℂ) (X := LamS d L N) α)) z

theorem phiNorm_liftT_le (a : Fin 2) (p : ℕ) (h ℓ : ℝ) (hh : 0 ≤ h) (hℓ : 0 < ℓ)
    (g : TestFn (Lam d L N)) :
    phiNorm (Dir d) p h ℓ (liftT a g) ≤ phiNorm (Dir d) p h ℓ g := by
  classical
  refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
  by_cases hz : ∀ i, (z i).1.2 = a
  · refine le_trans (le_of_eq ?_) (phiTerm_le g (unl ∘ z) α hα)
    simp only [phiTerm, nab_liftT, if_pos hz]
  · simp [phiTerm, nab_liftT, hz]

/-- Pairing with the restriction is pairing with the lifted test function. -/
theorem pair_res (a : Fin 2) (F : AlgS d L N) (g : TestFn (Lam d L N)) :
    pair (res a F) g = pair F (liftT a g) := by
  classical
  have hN : Nf (Lam d L N) ≤ Nf (LamS d L N) := by
    simp only [Nf, Fintype.card_prod, Fintype.card_fin]
    nlinarith [Fintype.card_pos (α := Lam d L N), Fintype.card_pos (α := ℤˣ)]
  -- inner sums agree for every length
  have hin : ∀ n, (∑ z : Fin n → Sf (LamS d L N), coeff F z * liftT a g n z) =
      ∑ w : Fin n → Sf (Lam d L N), coeff (res a F) w * g n w := by
    intro n
    rw [← sum_filter_add_sum_filter_not univ (fun z : Fin n → Sf (LamS d L N) => ∀ i, (z i).1.2 = a)]
    rw [sum_eq_zero (s := univ.filter fun z : Fin n → Sf (LamS d L N) => ¬∀ i, (z i).1.2 = a)
      (fun z hz => by rw [liftT_of_not g (mem_filter.1 hz).2, mul_zero]), add_zero]
    symm
    refine sum_bij' (fun w _ => lab a ∘ w) (fun z _ => unl ∘ z) (fun w _ => ?_) (fun z _ => ?_)
      (fun w _ => ?_) (fun z hz => ?_) (fun w _ => ?_)
    · simp [lab]
    · simp
    · rfl
    · funext i
      have h := (mem_filter.1 hz).2 i
      simp only [Function.comp_apply, lab, unl]
      rw [← h]
    · rw [coeff_res, liftT_lab]
  rw [pair, pair]
  simp only [hin]
  -- extend the range of lengths
  rw [← sum_range_add_sum_Ico _ (Nat.succ_le_succ hN)]
  rw [sum_eq_zero (s := Ico (Nf (Lam d L N) + 1) (Nf (LamS d L N) + 1)), add_zero]
  intro n hn
  have hn' : Nf (Lam d L N) < n := by have := (mem_Ico.1 hn).1; omega
  rw [sum_eq_zero fun w _ => by rw [coeff_eq_zero_of_lt _ w hn', zero_mul], mul_zero]

/-- Restriction to one species does not increase the `T` norm. -/
theorem tNorm_res_le (a : Fin 2) (p : ℕ) (h ℓ : ℝ) (hh : 0 ≤ h) (hℓ : 0 < ℓ)
    (F : AlgS d L N) :
    tNorm (Dir d) p h ℓ (res a F) ≤ tNorm (Dir d) p h ℓ F := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  rw [pair_res]
  exact le_iSup₂_of_le (liftT a g) ((phiNorm_liftT_le a p h ℓ hh hℓ g).trans hg) le_rfl

theorem Tj_res_le (a : Fin 2) (Lr : ℝ) (hL : 0 ≤ Lr) (j : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (F : AlgS d L N) : Tj d Lr j ℓ (res a F) ≤ Tj d Lr j ℓ F :=
  tNorm_res_le a _ _ ℓ (pow_nonneg hL j) hℓ F

end

end H04RG.LocS
