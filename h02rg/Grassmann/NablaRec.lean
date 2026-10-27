import Grassmann.Nabla

/-!
# The recursion for discrete derivatives

We show that `nabla` (defined by the binomial formula) is the product of the elementary
differences `∇_{i,e} f(z) = f(z with z_i ↦ z_i + e) - f(z)`, for a translation `s` with
`s (b + b') = s b ∘ s b'` (and `s 0 = id` for `nabla_single`):
`∇^{α + δ_{i,e}} = ∇^α ∇_{i,e}` (`nabla_succ`), and in particular `∇^{δ_{i,e}} = ∇_{i,e}`
(`nabla_single`).
-/

namespace Grassmann

noncomputable section

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {Y W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The elementary difference `∇_{i,e} f(z) = f(z with z_i ↦ z_i + e) - f(z)` in direction `e`
at the point `i`. -/
def ediff {κ : Type*} [DecidableEq κ] (s : (E → ℕ) → Y → Y) (i : κ) (e : E)
    (f : (κ → Y) → W) : (κ → Y) → W :=
  fun z => f (Function.update z i (s (Pi.single e 1) (z i))) - f z

theorem cf_eq_zero_of_lt {a b : E → ℕ} {e : E} (h : a e < b e) : cf a b = 0 := by
  unfold cf
  exact Finset.prod_eq_zero (mem_univ e) (by rw [Nat.choose_eq_zero_of_lt h]; simp)

/-- Pascal's rule for the coefficients. -/
theorem cf_succ (a b : E → ℕ) (e : E) :
    cf (a + Pi.single e 1) b =
      (if 1 ≤ b e then cf a (b - Pi.single e 1) else 0) - cf a b := by
  unfold cf
  rw [Fintype.prod_eq_mul_prod_compl e,
    Fintype.prod_eq_mul_prod_compl e (fun e' => (-1 : ℝ) ^ (a e' - b e') * _)]
  have h1 : ∏ e' ∈ {e}ᶜ, (-1 : ℝ) ^ ((a + Pi.single e 1 : E → ℕ) e' - b e') *
        ((a + Pi.single e 1 : E → ℕ) e').choose (b e') =
      ∏ e' ∈ {e}ᶜ, (-1 : ℝ) ^ (a e' - b e') * (a e').choose (b e') := by
    refine prod_congr rfl fun e' he' => ?_
    have : e' ≠ e := by simpa using he'
    simp [this]
  rw [h1]
  split_ifs with hb
  · rw [Fintype.prod_eq_mul_prod_compl e]
    have h2 : ∏ e' ∈ {e}ᶜ, (-1 : ℝ) ^ (a e' - (b - Pi.single e 1 : E → ℕ) e') *
          (a e').choose ((b - Pi.single e 1 : E → ℕ) e') =
        ∏ e' ∈ {e}ᶜ, (-1 : ℝ) ^ (a e' - b e') * (a e').choose (b e') := by
      refine prod_congr rfl fun e' he' => ?_
      have : e' ≠ e := by simpa using he'
      simp [this]
    rw [h2]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
    obtain ⟨c, hc⟩ : ∃ c, b e = c + 1 := ⟨b e - 1, by omega⟩
    rw [hc, Nat.add_sub_cancel, Nat.choose_succ_succ, Nat.add_sub_add_right]
    rcases Nat.lt_or_ge (a e) (c + 1) with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; push_cast; ring
    · have : a e - c = (a e - (c + 1)) + 1 := by omega
      rw [this, pow_succ]; push_cast; ring
  · have hb0 : b e = 0 := by omega
    simp only [Pi.add_apply, Pi.single_eq_same, hb0, Nat.sub_zero, Nat.choose_zero_right]
    rw [pow_succ]; push_cast; ring

section
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The coefficient `∏_i cf (α i) (β i)` of `nabla`. -/
def mcf (α β : κ → E → ℕ) : ℝ := ∏ j, cf (α j) (β j)

theorem mcf_succ (α γ : κ → E → ℕ) (i : κ) (e : E) :
    mcf (α + Pi.single i (Pi.single e 1)) γ =
      (if 1 ≤ γ i e then mcf α (γ - Pi.single i (Pi.single e 1)) else 0) - mcf α γ := by
  unfold mcf
  rw [Fintype.prod_eq_mul_prod_compl i,
    Fintype.prod_eq_mul_prod_compl i (fun j => cf (α j) (γ j))]
  have h1 : ∏ j ∈ {i}ᶜ, cf ((α + Pi.single i (Pi.single e 1) : κ → E → ℕ) j) (γ j) =
      ∏ j ∈ {i}ᶜ, cf (α j) (γ j) := by
    refine prod_congr rfl fun j hj => ?_
    have : j ≠ i := by simpa using hj
    simp [this]
  rw [h1]
  simp only [Pi.add_apply, Pi.single_eq_same, cf_succ]
  split_ifs with hb
  · rw [Fintype.prod_eq_mul_prod_compl i]
    have h2 : ∏ j ∈ {i}ᶜ, cf (α j) ((γ - Pi.single i (Pi.single e 1) : κ → E → ℕ) j) =
        ∏ j ∈ {i}ᶜ, cf (α j) (γ j) := by
      refine prod_congr rfl fun j hj => ?_
      have : j ≠ i := by simpa using hj
      simp [this]
    rw [h2]
    simp only [Pi.sub_apply, Pi.single_eq_same]
    ring
  · ring

theorem sum_mcf_extend (α : κ → E → ℕ) (S : Finset (κ → E → ℕ))
    (hS : Fintype.piFinset (fun j => Iic (α j)) ⊆ S) (F : (κ → E → ℕ) → W) :
    ∑ β ∈ Fintype.piFinset (fun j => Iic (α j)), mcf α β • F β =
      ∑ β ∈ S, mcf α β • F β := by
  refine sum_subset hS fun β _ hβ => ?_
  simp only [Fintype.mem_piFinset, mem_Iic, not_forall] at hβ
  obtain ⟨j, hj⟩ := hβ
  simp only [Pi.le_def, not_forall, not_le] at hj
  obtain ⟨e', he'⟩ := hj
  rw [mcf, prod_eq_zero (mem_univ j) (cf_eq_zero_of_lt he'), zero_smul]

/-- `∇^{α + δ_{i,e}} = ∇^α ∇_{i,e}`. -/
theorem nabla_succ (s : (E → ℕ) → Y → Y) (hsa : ∀ b b' y, s (b + b') y = s b (s b' y))
    (α : κ → E → ℕ) (i : κ) (e : E) (f : (κ → Y) → W) :
    nabla s (α + Pi.single i (Pi.single e 1)) f = nabla s α (ediff s i e f) := by
  ext z
  set D : κ → E → ℕ := Pi.single i (Pi.single e 1) with hD
  have hDapp : ∀ j e', D j e' = if j = i ∧ e' = e then 1 else 0 := by
    intro j e'
    by_cases hj : j = i
    · subst hj; by_cases he : e' = e
      · subst he; simp [D]
      · simp [D, he]
    · simp [D, hj]
  set A := Fintype.piFinset (fun j => Iic (α j))
  set B := Fintype.piFinset (fun j => Iic ((α + D) j))
  have hAB : A ⊆ B := by
    intro β hβ
    simp only [A, B, Fintype.mem_piFinset, mem_Iic, Pi.le_def] at hβ ⊢
    intro j e'
    have := hβ j e'
    simp only [Pi.add_apply]
    omega
  simp only [nabla_apply, ediff]
  change ∑ β ∈ B, mcf (α + D) β • _ = ∑ β ∈ A, mcf α β • _
  have hupd : ∀ β : κ → E → ℕ, Function.update (fun j => s (β j) (z j)) i
      (s (Pi.single e 1) (s (β i) (z i))) = fun j => s ((β + D) j) (z j) := by
    intro β
    ext j
    by_cases hj : j = i
    · subst hj; simp [D, ← hsa, add_comm]
    · simp [D, hj]
  have hm : ∀ γ, mcf (α + D) γ = (if 1 ≤ γ i e then mcf α (γ - D) else 0) - mcf α γ :=
    fun γ => mcf_succ α γ i e
  simp_rw [hupd, smul_sub, sum_sub_distrib, hm, sub_smul, sum_sub_distrib]
  rw [← sum_mcf_extend α B hAB]
  congr 1
  simp_rw [ite_smul, zero_smul]
  rw [← sum_filter]
  symm
  refine Finset.sum_nbij' (fun β => β + D) (fun γ => γ - D) ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [A, B, mem_filter, Fintype.mem_piFinset, mem_Iic, Pi.le_def]
      at hβ ⊢
    refine ⟨fun j e' => ?_, ?_⟩
    · have := hβ j e'
      simp only [Pi.add_apply, hDapp]
      omega
    · simp [Pi.add_apply, hDapp]
  · intro γ hγ
    simp only [A, B, mem_filter, Fintype.mem_piFinset, mem_Iic, Pi.le_def]
      at hγ ⊢
    intro j e'
    have := hγ.1 j e'
    simp only [Pi.add_apply, Pi.sub_apply, hDapp] at this ⊢
    omega
  · intro β _
    ext j e'
    simp
  · intro γ hγ
    simp only [B, mem_filter] at hγ
    ext j e'
    have := hγ.2
    simp only [Pi.add_apply, Pi.sub_apply, hDapp]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; omega
    · omega
  · intro β _
    simp only [add_tsub_cancel_right]

/-- In particular a single first-order derivative is the elementary difference. -/
theorem nabla_single (s : (E → ℕ) → Y → Y) (hs0 : ∀ y, s 0 y = y)
    (hsa : ∀ b b' y, s (b + b') y = s b (s b' y)) (i : κ) (e : E) (f : (κ → Y) → W) :
    nabla s (Pi.single i (Pi.single e 1)) f = ediff s i e f := by
  have := nabla_succ s hsa (0 : κ → E → ℕ) i e f
  rw [zero_add] at this
  rw [this, nabla_zero s hs0]

end

end

end Grassmann
