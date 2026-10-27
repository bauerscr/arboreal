module

public import ArborealDecay.SimonLieb.Poly

/-!
# Incident-edge negative correlation, unconditional case

For distinct `a, b ≠ ρ`, `μ(ρa, ρb ∈ F) ≤ μ(ρa ∈ F) μ(ρb ∈ F)` (`prop:incident-NC`, first part),
assuming real stability of forest polynomials (`hstab`).

Proof.  Replace the weights of the two edges `ρa`, `ρb` by variables `s`, `t` (`modW`).  On the one
hand, `Z(s, t) = S₀₀ + s S₁₀ + t S₀₁ + s t S₁₁`, where `S_{xy}` sums the weights (with `ρa`, `ρb`
of weight `1`) of the forests with the prescribed status of `ρa`, `ρb`.  On the other hand, by the
cone identity (`Surgery.Zforest_cone`), `Z(s, t) = P_H(h)` with `h_a = s`, `h_b = t`, and `P_H` is
multi-affine; comparing coefficients, the Rayleigh inequality gives `S₀₀ S₁₁ ≤ S₁₀ S₀₁`, which is
the claim.
-/

@[expose] public section

namespace ArborealDecay.SimonLieb

universe u

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- Weights `m` with the weights of the edges `ρa`, `ρb` replaced by `s`, `t`. -/
def modW (m : Λ → Λ → ℝ) (ρ a b : Λ) (s t : ℝ) (x y : Λ) : ℝ :=
  if s(x, y) = s(ρ, a) then s else if s(x, y) = s(ρ, b) then t else m x y

theorem modW_symm {m : Λ → Λ → ℝ} (hm : ∀ i j, m i j = m j i) (ρ a b : Λ) (s t : ℝ) :
    ∀ x y, modW m ρ a b s t x y = modW m ρ a b s t y x := by
  intro x y
  simp only [modW, Sym2.eq_swap (a := x) (b := y), hm x y]

theorem forestWeight_congr {β β' : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ' : ∀ i j, β' i j = β' j i) (h : ∀ x y, β x y = β' x y) (F : SimpleGraph Λ) :
    H02.forestWeight β hβ F = H02.forestWeight β' hβ' F := by
  unfold H02.forestWeight
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | h x y => exact h x y

theorem forestWeight_modW {m : Λ → Λ → ℝ} (hm : ∀ i j, m i j = m j i) {ρ a b : Λ}
    (hab : a ≠ b) (s t : ℝ) (F : SimpleGraph Λ) :
    H02.forestWeight (modW m ρ a b s t) (modW_symm hm ρ a b s t) F =
      H02.forestWeight (modW m ρ a b 1 1) (modW_symm hm ρ a b 1 1) F *
        (if F.Adj ρ a then s else 1) * (if F.Adj ρ b then t else 1) := by
  have hne : s(ρ, a) ≠ s(ρ, b) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact hab h
    · exact hab (h2.trans h1)
  have key : ∀ e : Sym2 Λ, Sym2.lift ⟨modW m ρ a b s t, modW_symm hm ρ a b s t⟩ e =
      Sym2.lift ⟨modW m ρ a b 1 1, modW_symm hm ρ a b 1 1⟩ e *
        (if e = s(ρ, a) then s else 1) * (if e = s(ρ, b) then t else 1) := by
    intro e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Sym2.lift_mk, modW]
      by_cases h1 : s(x, y) = s(ρ, a)
      · have h2 : s(x, y) ≠ s(ρ, b) := h1 ▸ hne
        simp [h1, hne]
      · by_cases h2 : s(x, y) = s(ρ, b)
        · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, ite_eq_right h1,
            ite_eq_left h2]
          ring
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2, ite_eq_right h1,
            ite_eq_right h2]
          ring
  unfold H02.forestWeight
  rw [Finset.prod_congr rfl fun e _ => key e, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

theorem modW_self {m : Λ → Λ → ℝ} (hm : ∀ i j, m i j = m j i) (ρ a b : Λ) :
    ∀ x y, m x y = modW m ρ a b (m ρ a) (m ρ b) x y := by
  intro x y
  unfold modW
  split_ifs with h1 h2
  · rcases Sym2.eq_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hm _ _
  · rcases Sym2.eq_iff.1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hm _ _
  · rfl

/-- The cone identity for the modified weights: `Z(s, t) = P_H(h)` with `h_v = m ρ v`, updated
at `a` and `b`. -/
theorem Zforest_modW {m : Λ → Λ → ℝ} (hm : ∀ i j, m i j = m j i) {ρ a b : Λ}
    (hab : a ≠ b) (ha : a ≠ ρ) (hb : b ≠ ρ) (s t : ℝ) :
    H02.Zforest (modW m ρ a b s t) (modW_symm hm ρ a b s t) =
      MvPolynomial.eval (Function.update (Function.update (fun v : {v : Λ // v ≠ ρ} => m ρ v)
          ⟨a, ha⟩ s) ⟨b, hb⟩ t)
        (forestPolynomial (fun x y : {v : Λ // v ≠ ρ} => m x y) (fun x y => hm x y)) := by
  rw [Surgery.Zforest_cone (ρ := ρ), eval_forestPolynomial]
  refine Finset.sum_congr rfl fun B _ => ?_
  congr 1
  · refine forestWeight_congr _ _ (fun x y => ?_) B
    have hx := x.2
    have hy := y.2
    simp only [modW]
    rw [ite_eq_right, ite_eq_right]
    · intro h
      rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hx h1
      · exact hy h2
    · intro h
      rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hx h1
      · exact hy h2
  · refine Finset.prod_congr rfl fun T _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    have hv := v.2
    have hva : (v = ⟨a, ha⟩) ↔ s(ρ, v.1) = s(ρ, a) := by
      rw [Subtype.ext_iff]
      constructor
      · intro h; rw [h]
      · intro h
        rcases Sym2.eq_iff.1 h with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact absurd h2 hv
    have hvb : (v = ⟨b, hb⟩) ↔ s(ρ, v.1) = s(ρ, b) := by
      rw [Subtype.ext_iff]
      constructor
      · intro h; rw [h]
      · intro h
        rcases Sym2.eq_iff.1 h with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · exact absurd h2 hv
    simp only [modW, Function.update_apply]
    by_cases h2 : v = ⟨b, hb⟩
    · by_cases h1 : v = ⟨a, ha⟩
      · rw [ite_eq_left h2, ite_eq_left (hva.1 h1)]
        have := h1.symm.trans h2
        simp only [Subtype.mk.injEq] at this
        exact absurd this hab
      · rw [ite_eq_left h2, ite_eq_right (fun h => h1 (hva.2 h)), ite_eq_left (hvb.1 h2)]
    · rw [ite_eq_right h2]
      by_cases h1 : v = ⟨a, ha⟩
      · rw [ite_eq_left h1, ite_eq_left (hva.1 h1)]
      · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hva.2 h)), ite_eq_right (fun h => h2 (hvb.2 h))]

theorem arborealProb_eq_sum_ite {β : Λ → Λ → ℝ} (hβ : ∀ i j, β i j = β j i)
    (P : SimpleGraph Λ → Prop) [DecidablePred P] :
    H02.arborealProb β hβ P = (∑ F : SimpleGraph Λ with F.IsAcyclic,
      if P F then H02.forestWeight β hβ F else 0) / H02.Zforest β hβ := by
  unfold H02.arborealProb
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases h1 : F.IsAcyclic <;> by_cases h2 : P F <;> simp [h1, h2]

/-- **Incident-edge negative correlation, unconditional case** (conditional on `hstab`):
for distinct `a, b`, both different from `ρ`, `μ(ρa, ρb ∈ F) ≤ μ(ρa ∈ F) μ(ρb ∈ F)`. -/
theorem uncond_NC_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    {m : Λ → Λ → ℝ} (hm : ∀ i j, m i j = m j i) (hm0 : ∀ i j, 0 ≤ m i j) {ρ a b : Λ}
    (hab : a ≠ b) (ha : a ≠ ρ) (hb : b ≠ ρ) :
    H02.arborealProb m hm (fun F => F.Adj ρ a ∧ F.Adj ρ b) ≤
      H02.arborealProb m hm (fun F => F.Adj ρ a) * H02.arborealProb m hm (fun F => F.Adj ρ b) := by
  have hab' : (⟨a, ha⟩ : {v : Λ // v ≠ ρ}) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  obtain ⟨c₀₀, c₁₀, c₀₁, c₁₁, hR, hev⟩ := rayleigh_forestPolynomial_of_stable hstab
    (fun x y : {v : Λ // v ≠ ρ} => m x y) (fun x y => hm x y) (fun x y => hm0 x y) hab'
    (fun v : {v : Λ // v ≠ ρ} => m ρ v)
  set c : SimpleGraph Λ → ℝ := fun F => H02.forestWeight (modW m ρ a b 1 1)
    (modW_symm hm ρ a b 1 1) F with hc
  set S₀₀ := ∑ F : SimpleGraph Λ with F.IsAcyclic,
    if ¬ F.Adj ρ a ∧ ¬ F.Adj ρ b then c F else 0 with hS₀₀
  set S₁₀ := ∑ F : SimpleGraph Λ with F.IsAcyclic,
    if F.Adj ρ a ∧ ¬ F.Adj ρ b then c F else 0 with hS₁₀
  set S₀₁ := ∑ F : SimpleGraph Λ with F.IsAcyclic,
    if ¬ F.Adj ρ a ∧ F.Adj ρ b then c F else 0 with hS₀₁
  set S₁₁ := ∑ F : SimpleGraph Λ with F.IsAcyclic,
    if F.Adj ρ a ∧ F.Adj ρ b then c F else 0 with hS₁₁
  have hw : ∀ (s t : ℝ) (F : SimpleGraph Λ), H02.forestWeight (modW m ρ a b s t)
      (modW_symm hm ρ a b s t) F = c F * (if F.Adj ρ a then s else 1) *
        (if F.Adj ρ b then t else 1) := fun s t F => forestWeight_modW hm hab s t F
  have hZ : ∀ s t : ℝ, H02.Zforest (modW m ρ a b s t) (modW_symm hm ρ a b s t) =
      S₀₀ + s * S₁₀ + t * S₀₁ + s * t * S₁₁ := by
    intro s t
    unfold H02.Zforest
    simp only [hw, hS₀₀, hS₁₀, hS₀₁, hS₁₁, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h1 : F.Adj ρ a <;> by_cases h2 : F.Adj ρ b <;> simp [h1, h2] <;> ring
  have hpoly : ∀ s t : ℝ, H02.Zforest (modW m ρ a b s t) (modW_symm hm ρ a b s t) =
      c₀₀ + c₁₀ * s + c₀₁ * t + c₁₁ * s * t := fun s t => by
    rw [Zforest_modW hm hab ha hb, hev]
  have e00 := (hZ 0 0).symm.trans (hpoly 0 0)
  have e10 := (hZ 1 0).symm.trans (hpoly 1 0)
  have e01 := (hZ 0 1).symm.trans (hpoly 0 1)
  have e11 := (hZ 1 1).symm.trans (hpoly 1 1)
  have h00 : S₀₀ = c₀₀ := by linarith
  have h10 : S₁₀ = c₁₀ := by linarith
  have h01 : S₀₁ = c₀₁ := by linarith
  have h11 : S₁₁ = c₁₁ := by linarith
  -- the original weights
  set ha' := m ρ a
  set hb' := m ρ b
  have hwm : ∀ F, H02.forestWeight m hm F = c F * (if F.Adj ρ a then ha' else 1) *
      (if F.Adj ρ b then hb' else 1) := fun F =>
    (forestWeight_congr hm _ (modW_self hm ρ a b) F).trans (hw _ _ F)
  have hZm : H02.Zforest m hm = S₀₀ + ha' * S₁₀ + hb' * S₀₁ + ha' * hb' * S₁₁ := by
    rw [← hZ]
    unfold H02.Zforest
    exact Finset.sum_congr rfl fun F _ => (forestWeight_congr hm _ (modW_self hm ρ a b) F)
  have hNab : (∑ F : SimpleGraph Λ with F.IsAcyclic,
      if F.Adj ρ a ∧ F.Adj ρ b then H02.forestWeight m hm F else 0) = ha' * hb' * S₁₁ := by
    rw [hS₁₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [hwm]
    by_cases h1 : F.Adj ρ a <;> by_cases h2 : F.Adj ρ b <;> simp [h1, h2]; ring
  have hNa : (∑ F : SimpleGraph Λ with F.IsAcyclic,
      if F.Adj ρ a then H02.forestWeight m hm F else 0) = ha' * S₁₀ + ha' * hb' * S₁₁ := by
    rw [hS₁₀, hS₁₁, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [hwm]
    by_cases h1 : F.Adj ρ a <;> by_cases h2 : F.Adj ρ b <;> simp [h1, h2] <;> ring
  have hNb : (∑ F : SimpleGraph Λ with F.IsAcyclic,
      if F.Adj ρ b then H02.forestWeight m hm F else 0) = hb' * S₀₁ + ha' * hb' * S₁₁ := by
    rw [hS₀₁, hS₁₁, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [hwm]
    by_cases h1 : F.Adj ρ a <;> by_cases h2 : F.Adj ρ b <;> simp [h1, h2] <;> ring
  have hZpos := H02.Zforest_pos hm hm0
  have hha : 0 ≤ ha' := hm0 _ _
  have hhb : 0 ≤ hb' := hm0 _ _
  rw [arborealProb_eq_sum_ite, arborealProb_eq_sum_ite, arborealProb_eq_sum_ite,
    hNab, hNa, hNb, div_mul_div_comm, div_le_div_iff₀ hZpos (mul_pos hZpos hZpos)]
  have key : ha' * hb' * S₁₁ * H02.Zforest m hm ≤
      (ha' * S₁₀ + ha' * hb' * S₁₁) * (hb' * S₀₁ + ha' * hb' * S₁₁) := by
    have h1 : (ha' * S₁₀ + ha' * hb' * S₁₁) * (hb' * S₀₁ + ha' * hb' * S₁₁) -
        ha' * hb' * S₁₁ * H02.Zforest m hm = ha' * hb' * (S₁₀ * S₀₁ - S₀₀ * S₁₁) := by
      rw [hZm]; ring
    have h2 : 0 ≤ ha' * hb' * (S₁₀ * S₀₁ - S₀₀ * S₁₁) := by
      refine mul_nonneg (mul_nonneg hha hhb) ?_
      rw [h00, h10, h01, h11]; linarith
    linarith
  calc ha' * hb' * S₁₁ * (H02.Zforest m hm * H02.Zforest m hm)
      = (ha' * hb' * S₁₁ * H02.Zforest m hm) * H02.Zforest m hm := by ring
    _ ≤ (ha' * S₁₀ + ha' * hb' * S₁₁) * (hb' * S₀₁ + ha' * hb' * S₁₁) * H02.Zforest m hm :=
        mul_le_mul_of_nonneg_right key hZpos.le

end

end ArborealDecay.SimonLieb
