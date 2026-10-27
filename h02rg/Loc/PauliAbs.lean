import Loc.PauliSum

/-!
# Lemma `lem:pauli`, abstract form

Let `(χ_B)_{B ∈ Bk}` be cut-offs on `X` with centres `c_B` and path lengths `Dst_B`, such that at
scale `h₀` (`h₀ = L^j`):
* (PU1) `∑_B |∇^b χ_B(y)| ≤ C_χ h₀^{-|b|}`,
* (PU2) `∑_B |∇^b χ_B(y)| Dst_B(y + b) ≤ C_χ h₀^{1-|b|}`, for `|b| ≤ p`,
* (PU3) `∑_B χ_B = 1` on `Y`,
and the path property `PathH` holds. If `L ≥ 4 · 2^p (p+1)^{|E|} C_χ`, then for `F ∈ 𝒩(Y)`
(`pauli_abstract`)

  `‖F‖_{T(h₀ L, 2ℓ)} ≤ (2^{p+2} C_χ)^{2|Bk|} ‖F‖_{T(h₀, ℓ)}`.

The test function of `T(h₀, ℓ)` is `hfun g`: the doubling `2^n` of the field scale is paid by
the gain `L^{-1}` of each remainder variable, except for at most `2|Bk|` frozen variables
(the Pauli principle).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X]
variable {Bk : Type*} [Fintype Bk] [DecidableEq Bk] {χ : Bk → X → ℝ} {cB : Bk → X}

theorem mabs_sub_add {b γ : E → ℕ} (h : γ ≤ b) : mabs (b - γ) + mabs γ = mabs b := by
  simp only [Grassmann.mabs, ← sum_add_distrib]
  exact sum_congr rfl fun e _ => by
    simp only [Pi.sub_apply]; have h' : γ e ≤ b e := h e; omega

theorem one_le_mabs_sub {b γ : E → ℕ} (h : γ ≤ b) (hne : γ ≠ b) : 1 ≤ mabs (b - γ) := by
  by_contra h0
  push Not at h0
  have hz : mabs (b - γ) = 0 := by omega
  apply hne
  funext e
  have := (sum_eq_zero_iff.1 hz) e (mem_univ e)
  simp only [Pi.sub_apply] at this
  have h' : γ e ≤ b e := h e
  omega

theorem card_Iic_le {b : E → ℕ} {p : ℕ} (hb : mabs b ≤ p) :
    ((Iic b).card : ℝ) ≤ ((p + 1 : ℕ) : ℝ) ^ Fintype.card E := by
  have hIic : Iic b = Fintype.piFinset fun e => Iic (b e) := rfl
  rw [hIic, Fintype.card_piFinset]
  push_cast
  rw [← Finset.card_univ, ← prod_const]
  refine prod_le_prod (fun e _ => by positivity) fun e _ => ?_
  rw [Nat.card_Iic]
  have : b e ≤ mabs b := single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (mem_univ e)
  exact_mod_cast (by omega : b e + 1 ≤ p + 1)

variable {p : ℕ} {h₀ L Cχ : ℝ} {Dst : Bk → Sf X → ℝ}

/-- The frozen weights in one variable. -/
theorem sum_wt_true (hh : 0 < h₀)
    (hPU1 : ∀ y (b : E → ℕ), mabs b ≤ p →
      ∑ B, |D1 sh b (fun a => χ B a.1) y| ≤ Cχ * (h₀ ^ mabs b)⁻¹)
    (τ : ℝ) (y : Sf X) {b : E → ℕ} (hb : mabs b ≤ p) :
    ∑ B, wt χ Dst τ (B, true) y b * h₀ ^ mabs b ≤ 2 ^ p * Cχ := by
  simp only [wt, if_true]
  rw [← sum_mul, ← mul_sum]
  have h1 := hPU1 y b hb
  have hC : 0 ≤ Cχ := by
    have : 0 ≤ ∑ B, |D1 sh b (fun a => χ B a.1) y| := sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 < (h₀ ^ mabs b)⁻¹ := by positivity
    by_contra hc; push Not at hc; nlinarith
  calc (2 ^ mabs b * ∑ B, |D1 sh b (fun a => χ B a.1) y|) * h₀ ^ mabs b
      ≤ 2 ^ mabs b * (Cχ * (h₀ ^ mabs b)⁻¹) * h₀ ^ mabs b := by gcongr
    _ = 2 ^ mabs b * Cχ := by field_simp
    _ ≤ 2 ^ p * Cχ := by gcongr; norm_num

/-- The remainder weights in one variable gain `L^{-1}`. -/
theorem sum_wt_false (hh : 0 < h₀) (hL : 1 ≤ L)
    (hPU1 : ∀ y (b : E → ℕ), mabs b ≤ p →
      ∑ B, |D1 sh b (fun a => χ B a.1) y| ≤ Cχ * (h₀ ^ mabs b)⁻¹)
    (hPU2 : ∀ y (b : E → ℕ), mabs b ≤ p →
      ∑ B, |D1 sh b (fun a => χ B a.1) y| * Dst B (sh b y) ≤ Cχ * h₀ * (h₀ ^ mabs b)⁻¹)
    (y : Sf X) {b : E → ℕ} (hb : mabs b ≤ p) :
    ∑ B, wt χ Dst (h₀ * L)⁻¹ (B, false) y b * h₀ ^ mabs b ≤
      2 ^ p * ((p + 1 : ℕ) : ℝ) ^ Fintype.card E * Cχ / L := by
  have hL0 : 0 < L := by linarith
  set τ := (h₀ * L)⁻¹
  simp only [wt, Bool.false_eq_true, if_false, wR]
  have hC : 0 ≤ Cχ := by
    have h1 := hPU1 y 0 (by simp [Grassmann.mabs])
    have : 0 ≤ ∑ B, |D1 sh (0 : E → ℕ) (fun a => χ B a.1) y| := sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 < (h₀ ^ mabs (0 : E → ℕ))⁻¹ := by positivity
    by_contra hc; push Not at hc; nlinarith
  -- each `γ ≤ b` contributes at most `C_χ h₀^{-|b|} / L`
  have hγ : ∀ γ ∈ Iic b, ∑ B, |D1 sh γ (fun a => χ B a.1) y| *
      (if γ = b then Dst B (sh b y) * τ else τ ^ mabs (b - γ)) ≤ Cχ * (h₀ ^ mabs b)⁻¹ / L := by
    intro γ hγb
    rw [mem_Iic] at hγb
    by_cases hγe : γ = b
    · subst hγe
      simp only [if_true]
      calc ∑ B, |D1 sh γ (fun a => χ B a.1) y| * (Dst B (sh γ y) * τ)
          = (∑ B, |D1 sh γ (fun a => χ B a.1) y| * Dst B (sh γ y)) * τ := by
            rw [sum_mul]; exact sum_congr rfl fun B _ => by ring
        _ ≤ Cχ * h₀ * (h₀ ^ mabs γ)⁻¹ * τ := by
            gcongr
            exact hPU2 y γ hb
        _ = _ := by simp only [τ]; field_simp
    · simp only [if_neg hγe]
      have hk := one_le_mabs_sub hγb hγe
      have hsplit := mabs_sub_add hγb
      have hγp : mabs γ ≤ p := by omega
      rw [← sum_mul]
      have hτk : τ ^ mabs (b - γ) ≤ (h₀ ^ mabs (b - γ))⁻¹ / L := by
        simp only [τ]
        rw [inv_pow, mul_pow, mul_inv, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_anti₀ hL0 (le_self_pow₀ hL (by omega))
      calc (∑ B, |D1 sh γ (fun a => χ B a.1) y|) * τ ^ mabs (b - γ)
          ≤ (Cχ * (h₀ ^ mabs γ)⁻¹) * ((h₀ ^ mabs (b - γ))⁻¹ / L) :=
            mul_le_mul (hPU1 y γ hγp) hτk (by positivity) (by positivity)
        _ = Cχ * (h₀ ^ mabs b)⁻¹ / L := by
            rw [← hsplit, pow_add]; field_simp
  calc ∑ B, (2 ^ mabs b * ∑ γ ∈ Iic b, |D1 sh γ (fun a => χ B a.1) y| *
        (if γ = b then Dst B (sh b y) * τ else τ ^ mabs (b - γ))) * h₀ ^ mabs b
      = 2 ^ mabs b * (∑ γ ∈ Iic b, ∑ B, |D1 sh γ (fun a => χ B a.1) y| *
          (if γ = b then Dst B (sh b y) * τ else τ ^ mabs (b - γ))) * h₀ ^ mabs b := by
        rw [← sum_mul, ← mul_sum, sum_comm]
    _ ≤ 2 ^ mabs b * (∑ γ ∈ Iic b, Cχ * (h₀ ^ mabs b)⁻¹ / L) * h₀ ^ mabs b := by
        gcongr with γ hγb
        exact hγ γ hγb
    _ = 2 ^ mabs b * (Iic b).card * Cχ / L := by
        rw [sum_const, nsmul_eq_mul]; field_simp
    _ ≤ 2 ^ p * ((p + 1 : ℕ) : ℝ) ^ Fintype.card E * Cχ / L := by
        gcongr
        · norm_num
        · exact card_Iic_le hb


open Classical in
/-- **Lemma `lem:pauli`, abstract form.** -/
theorem pauli_abstract [Fintype X] (hp : 1 ≤ p) (hh : 0 < h₀) (hL : 1 ≤ L) (hC : 1 ≤ Cχ)
    (hLC : 4 * (2 ^ p * ((p + 1 : ℕ) : ℝ) ^ Fintype.card E * Cχ) ≤ L)
    (hDst : ∀ B y, 0 ≤ Dst B y) (hpath : ∀ B, PathH (E := E) (cenAt (cB B)) (Dst B))
    (hPU1 : ∀ y (b : E → ℕ), mabs b ≤ p →
      ∑ B, |D1 sh b (fun a => χ B a.1) y| ≤ Cχ * (h₀ ^ mabs b)⁻¹)
    (hPU2 : ∀ y (b : E → ℕ), mabs b ≤ p →
      ∑ B, |D1 sh b (fun a => χ B a.1) y| * Dst B (sh b y) ≤ Cχ * h₀ * (h₀ ^ mabs b)⁻¹)
    {Y : Set X} (hPU3 : ∀ x ∈ Y, ∑ B, χ B x = 1) {F : N X} (hF : F ∈ NX Y) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    tNorm E p (h₀ * L) (2 * ℓ) F ≤
      ENNReal.ofReal ((4 * (2 ^ p * Cχ)) ^ (2 * Fintype.card Bk)) * tNorm E p h₀ ℓ F := by
  have hL0 : 0 < L := by linarith
  have hhL : 0 < h₀ * L := by positivity
  set τ := (h₀ * L)⁻¹ with hτdef
  have hτ : 0 ≤ τ := by positivity
  set AP := 2 ^ p * Cχ
  set AR := 2 ^ p * ((p + 1 : ℕ) : ℝ) ^ Fintype.card E * Cχ / L
  have hAP : 1 ≤ AP := by
    have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    nlinarith
  have hAR0 : 0 ≤ AR := by positivity
  have hAR : 4 * AR ≤ 1 := by
    simp only [AR]; rw [mul_div_assoc', div_le_one hL0]; linarith
  set C := (4 * AP) ^ (2 * Fintype.card Bk)
  have hC0 : 0 ≤ C := by positivity
  set T := (tNorm E p h₀ ℓ F).toReal
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F), ← ENNReal.ofReal_mul hC0]
  refine tNorm_le fun g hg => ?_
  set hg' : TestFn X := fun n => hfun χ cB (g n)
  -- the pairings agree
  have hpair : pair F g = pair F hg' := by
    unfold pair
    refine sum_congr rfl fun n _ => ?_
    rw [sum_coeff_hfun hPU3 hF (g n)]
  -- the norm of the admissible test function
  have hbd : phiNorm E p h₀ ℓ hg' ≤ ENNReal.ofReal C := by
    refine phiNorm_le fun n z β hβ => ?_
    -- the bound on `g`
    have hgb : Bd p ((2 * ℓ) ^ n) (fun _ _ (b : E → ℕ) => τ ^ mabs b) (g n) := by
      intro w β' hβ'
      have := abs_nab_le hhL (by positivity : 0 < 2 * ℓ) zero_le_one
        (by rwa [ENNReal.ofReal_one]) (g := g) w β' hβ'
      rw [one_mul] at this
      refine this.trans (le_of_eq ?_)
      rw [hτdef, ← inv_pow, prod_pow_eq_pow_sum, ord]
    have hGb : ∀ α : Fin n → Bk × Bool, Bd p ((2 * ℓ) ^ n) (ρm χ Dst τ n α)
        (G χ cB (g n) n le_rfl α) := fun α =>
      bd_G hDst hpath hp hτ (by positivity) hgb n le_rfl α
    set f : Fin n → Bk × Bool → ℝ := fun k o => wt χ Dst τ o (z k) (β k) * h₀ ^ mabs (β k)
    have hf : ∀ k o, 0 ≤ f k o := fun k o =>
      mul_nonneg (wt_nonneg hDst hτ o _ _) (by positivity)
    have hsum := sum_adm_le f hf hAP hAR0 hAR
      (fun k => sum_wt_true hh hPU1 τ (z k) (hβ k))
      (fun k => sum_wt_false hh hL hPU1 hPU2 (z k) (hβ k)) (spins z)
    have hprod : ∀ α : Fin n → Bk × Bool,
        ∏ k, ρm χ Dst τ n α k (z k) (β k) = (∏ k, f k (α k)) * (h₀ ^ ord β)⁻¹ := by
      intro α
      simp only [f, prod_mul_distrib, ρm, Fin.is_lt, dif_pos]
      rw [prod_pow_eq_pow_sum, ← ord, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
    have hnab : ‖nab β (hg' n) z‖ ≤ (2 * ℓ) ^ n * (h₀ ^ ord β)⁻¹ *
        ∑ α : Fin n → Bk × Bool, (if Inadm α (spins z) then 0 else ∏ k, f k (α k)) := by
      rw [show hg' n = hfun χ cB (g n) from rfl, nab_hfun, mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun α _ => ?_)
      split_ifs
      · simp
      · refine (hGb α z β hβ).trans (le_of_eq ?_)
        rw [hprod]; ring
    unfold phiTerm
    calc ℓ⁻¹ ^ n * h₀ ^ ord β * ‖nab β (hg' n) z‖
        ≤ ℓ⁻¹ ^ n * h₀ ^ ord β * ((2 * ℓ) ^ n * (h₀ ^ ord β)⁻¹ *
          ∑ α : Fin n → Bk × Bool, (if Inadm α (spins z) then 0 else ∏ k, f k (α k))) :=
          mul_le_mul_of_nonneg_left hnab (by positivity)
      _ = 2 ^ n * ∑ α : Fin n → Bk × Bool, (if Inadm α (spins z) then 0 else ∏ k, f k (α k)) := by
          have h1 : ℓ ^ n ≠ 0 := by positivity
          have h2 : h₀ ^ ord β ≠ 0 := by positivity
          rw [mul_pow, inv_pow]
          field_simp
      _ ≤ C := hsum
  rw [hpair]
  calc ‖pair F hg'‖ ≤ T * C := abs_pair_le hh hℓ F hC0 hbd
    _ = C * T := mul_comm _ _

end

end Loc
