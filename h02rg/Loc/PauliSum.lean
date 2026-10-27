import Loc.PauliComp
import Loc.EstBasic

/-!
# The Pauli cancellation and the admissible sum (Lemma `lem:pauli`)

An assignment `α : Fin n → Bk × Bool` is *admissible* for the spins `s` if no two variables of
equal spin are frozen in the same block. For inadmissible `α`, the factorisation `G_fact` and
the antisymmetry of the coefficients give `∑_z F_z G g n α (z) = 0` (`sum_inadm_eq_zero`).

* `hfun g` is the sum of `G g n α` over the admissible `α`; `pair_hfun` shows
  `⟨F, g⟩ = ⟨F, hfun g⟩` for `F ∈ 𝒩(Y)` when the cut-offs sum to one on `Y`.
* `sum_adm_le`: `2^n ∑_{α adm} ∏_k f_k(α_k) ≤ (4 A_P)^{2|Bk|}` if the frozen weights sum to
  `≤ A_P` and the remainder weights to `≤ A_R ≤ 1/4` in each variable; `sum_adm_le_gain` keeps
  the factor `(4 A_R)^{n - 2|Bk|}` of the remainders.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {n : ℕ}
variable {Bk : Type*} [Fintype Bk] [DecidableEq Bk] {χ : Bk → X → ℝ} {cB : Bk → X}

/-! ### Swapping two frozen variables of the same block -/

theorem swap_apply_eq_of_eq {α : Fin n → Bk × Bool} {i k : Fin n} (hα : α i = α k) (q : Fin n) :
    α (Equiv.swap i k q) = α q := by
  by_cases hqi : q = i
  · subst hqi; rw [Equiv.swap_apply_left, hα]
  · by_cases hqk : q = k
    · subst hqk; rw [Equiv.swap_apply_right, hα]
    · rw [Equiv.swap_apply_of_ne_of_ne hqi hqk]

theorem G_swap (g : (Fin n → Sf X) → ℂ) (α : Fin n → Bk × Bool) {i k : Fin n} (hik : i ≠ k)
    (hα : α i = α k) (hP : (α i).2 = true) (w : Fin n → Sf X) (hs : (w i).2 = (w k).2) :
    G χ cB g n le_rfl α (w ∘ Equiv.swap i k) = G χ cB g n le_rfl α w := by
  obtain ⟨K, hK⟩ := G_fact (χ := χ) (cB := cB) g n le_rfl α
  rw [hK, hK]
  have hcast : ∀ q : Fin n, Fin.castLE (le_refl n) q = q := fun q => Fin.ext rfl
  have h1 : frozenProd χ n le_rfl α (w ∘ Equiv.swap i k) = frozenProd χ n le_rfl α w := by
    unfold frozenProd
    simp only [hcast, Function.comp_apply]
    rw [← Equiv.prod_comp (Equiv.swap i k) (fun q => if (α q).2 then χ (α q).1 (w q).1 else 1)]
    refine prod_congr rfl fun q _ => ?_
    rw [swap_apply_eq_of_eq hα]
  have h2 : updF cB n α (w ∘ Equiv.swap i k) = updF cB n α w := by
    funext q
    unfold updF
    rw [dif_pos q.isLt, dif_pos q.isLt]
    have hq : (⟨q.val, q.isLt⟩ : Fin n) = q := Fin.ext rfl
    rw [hq]
    by_cases hPq : (α q).2 = true
    · rw [if_pos hPq, if_pos hPq]
      simp only [cenAt, Function.comp_apply]
      congr 1
      by_cases hqi : q = i
      · subst hqi; rw [Equiv.swap_apply_left, hs]
      · by_cases hqk : q = k
        · subst hqk; rw [Equiv.swap_apply_right, hs]
        · rw [Equiv.swap_apply_of_ne_of_ne hqi hqk]
    · rw [if_neg hPq, if_neg hPq, Function.comp_apply]
      have hqi : q ≠ i := by rintro rfl; exact hPq hP
      have hqk : q ≠ k := by rintro rfl; exact hPq (hα ▸ hP)
      rw [Equiv.swap_apply_of_ne_of_ne hqi hqk]
  rw [h1, h2]

/-! ### Admissible assignments -/

/-- Two variables of equal spin frozen in the same block. -/
def Inadm (α : Fin n → Bk × Bool) (s : Fin n → ℤˣ) : Prop :=
  ∃ i k, i ≠ k ∧ α i = α k ∧ (α i).2 = true ∧ s i = s k

open Classical in
/-- A canonical pair witnessing inadmissibility. -/
def pk (α : Fin n → Bk × Bool) (s : Fin n → ℤˣ) (h : Inadm α s) : Fin n × Fin n :=
  (h.choose, h.choose_spec.choose)

theorem pk_spec (α : Fin n → Bk × Bool) (s : Fin n → ℤˣ) (h : Inadm α s) :
    (pk α s h).1 ≠ (pk α s h).2 ∧ α (pk α s h).1 = α (pk α s h).2 ∧ (α (pk α s h).1).2 = true ∧
      s (pk α s h).1 = s (pk α s h).2 :=
  h.choose_spec.choose_spec

theorem pk_congr (α : Fin n → Bk × Bool) {s s' : Fin n → ℤˣ} (e : s = s') (h : Inadm α s)
    (h' : Inadm α s') : pk α s h = pk α s' h' := by
  subst e; rfl

open Classical in
/-- The involution exchanging the canonical pair. -/
def invl (α : Fin n → Bk × Bool) (z : Fin n → Sf X) : Fin n → Sf X :=
  if h : Inadm α (spins z) then z ∘ Equiv.swap (pk α _ h).1 (pk α _ h).2 else z

theorem spins_comp_swap {z : Fin n → Sf X} {i k : Fin n} (hs : (z i).2 = (z k).2) :
    spins (z ∘ Equiv.swap i k) = spins z := by
  funext q
  simp only [spins, Function.comp_apply]
  by_cases hqi : q = i
  · subst hqi; rw [Equiv.swap_apply_left, hs]
  · by_cases hqk : q = k
    · subst hqk; rw [Equiv.swap_apply_right, hs]
    · rw [Equiv.swap_apply_of_ne_of_ne hqi hqk]

theorem spins_invl (α : Fin n → Bk × Bool) (z : Fin n → Sf X) : spins (invl α z) = spins z := by
  unfold invl
  split_ifs with h
  · exact spins_comp_swap (pk_spec α _ h).2.2.2
  · rfl

theorem invl_invl (α : Fin n → Bk × Bool) : Function.Involutive (invl (X := X) α) := by
  intro z
  have hs := spins_invl α z
  by_cases h : Inadm α (spins z)
  · have h' : Inadm α (spins (invl α z)) := hs ▸ h
    have hz : invl α z = z ∘ Equiv.swap (pk α _ h).1 (pk α _ h).2 := by simp [invl, h]
    conv_lhs => rw [invl, dif_pos h']
    rw [pk_congr α hs h' h, hz]
    funext q
    simp [Equiv.swap_apply_self]
  · have : invl α z = z := by simp [invl, h]
    rw [this, this]

open Classical in
/-- The Pauli cancellation: inadmissible assignments do not contribute. -/
theorem sum_inadm_eq_zero [Fintype X] (g : (Fin n → Sf X) → ℂ) (α : Fin n → Bk × Bool)
    (c : (Fin n → Sf X) → ℂ) (hc : ∀ z (i k : Fin n), i ≠ k → c (z ∘ Equiv.swap i k) = -c z) :
    ∑ z, (if Inadm α (spins z) then c z * G χ cB g n le_rfl α z else 0) = 0 := by
  set f : (Fin n → Sf X) → ℂ := fun z =>
    if Inadm α (spins z) then c z * G χ cB g n le_rfl α z else 0
  have hf : ∀ z, f (invl α z) = -f z := by
    intro z
    simp only [f, spins_invl]
    split_ifs with h
    · have hz : invl α z = z ∘ Equiv.swap (pk α _ h).1 (pk α _ h).2 := by simp [invl, h]
      obtain ⟨hne, hα, hP, hs⟩ := pk_spec α _ h
      rw [hz, hc z _ _ hne, G_swap g α hne hα hP z hs]
      ring
    · simp
  have hsum : ∑ z, f z = ∑ z, f (invl α z) :=
    (Equiv.sum_comp ((invl_invl α).toPerm _) f).symm
  simp only [hf, sum_neg_distrib] at hsum
  change ∑ z, f z = 0
  linear_combination hsum / 2


/-! ### The admissible part of a test function -/

variable (χ cB) in
open Classical in
/-- The sum of the admissible pieces. -/
def hfun (g : (Fin n → Sf X) → ℂ) : (Fin n → Sf X) → ℂ :=
  fun z => ∑ α : Fin n → Bk × Bool, if Inadm α (spins z) then 0 else G χ cB g n le_rfl α z

open Classical in
theorem nab_hfun (g : (Fin n → Sf X) → ℂ) (β : Fin n → E → ℕ) (z : Fin n → Sf X) :
    nab β (hfun χ cB g) z =
      ∑ α : Fin n → Bk × Bool, if Inadm α (spins z) then 0 else nab β (G χ cB g n le_rfl α) z := by
  unfold hfun
  rw [nabla_sum]
  refine sum_congr rfl fun α _ => ?_
  have := nab_ite_spins (X := X) (E := E) (fun s => ¬Inadm α s) β (G χ cB g n le_rfl α) z
  simp only [ite_not] at this
  exact this

open Classical in
/-- `⟨F, g⟩ = ⟨F, hfun g⟩` for `F ∈ 𝒩(Y)` if the cut-offs sum to one on `Y`. -/
theorem sum_coeff_hfun [Fintype X] {Y : Set X} (hY : ∀ x ∈ Y, ∑ B, χ B x = 1) {F : N X}
    (hF : F ∈ NX Y) (g : (Fin n → Sf X) → ℂ) :
    ∑ z, coeff F z * g z = ∑ z, coeff F z * hfun χ cB g z := by
  have h1 : ∀ z, coeff F z * g z = coeff F z * ∑ α : Fin n → Bk × Bool, G χ cB g n le_rfl α z := by
    intro z
    by_cases hz : ∀ k, (z k).1 ∈ Y
    · rw [sum_G g n le_rfl z fun k _ => hY _ (hz k)]
    · push Not at hz
      obtain ⟨k, hk⟩ := hz
      rw [coeff_eq_zero_of_mem_NX hF z k hk, zero_mul, zero_mul]
  have h2 : ∀ z, coeff F z * ∑ α : Fin n → Bk × Bool, G χ cB g n le_rfl α z =
      coeff F z * hfun χ cB g z + ∑ α : Fin n → Bk × Bool,
        (if Inadm α (spins z) then coeff F z * G χ cB g n le_rfl α z else 0) := by
    intro z
    unfold hfun
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun α _ => ?_
    split_ifs <;> ring
  simp only [h1, h2, sum_add_distrib]
  rw [sum_comm (s := univ) (t := univ)]
  rw [sum_eq_zero fun α _ => sum_inadm_eq_zero g α (coeff F) fun z i k hik => by
    rw [coeff_perm, Perm.sign_swap hik]; push_cast; ring, add_zero]

/-! ### The admissible sum -/

theorem card_frozen_le {α : Fin n → Bk × Bool} {s : Fin n → ℤˣ} (h : ¬Inadm α s) :
    (univ.filter fun k => (α k).2 = true).card ≤ 2 * Fintype.card Bk := by
  have hinj : Set.InjOn (fun k => ((α k).1, s k)) (univ.filter fun k => (α k).2 = true : Finset (Fin n)) := by
    intro k hk k' hk' he
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk hk'
    simp only [Prod.mk.injEq] at he
    by_contra hne
    exact h ⟨k, k', hne, Prod.ext he.1 (hk.trans hk'.symm), hk, he.2⟩
  have := Finset.card_le_card_of_injOn _ (fun k _ => mem_univ ((α k).1, s k)) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_units_int] at this
  linarith

open Classical in
/-- The admissible sum with the gain of the remainders: at least `n - 2|Bk|` variables are not
frozen. -/
theorem sum_adm_le_gain (f : Fin n → Bk × Bool → ℝ) (hf : ∀ k o, 0 ≤ f k o) {AP AR : ℝ}
    (hAP : 1 ≤ AP) (hAR0 : 0 ≤ AR) (hAR : 4 * AR ≤ 1)
    (hP : ∀ k, ∑ B, f k (B, true) ≤ AP) (hR : ∀ k, ∑ B, f k (B, false) ≤ AR)
    (s : Fin n → ℤˣ) :
    2 ^ n * ∑ α : Fin n → Bk × Bool, (if Inadm α s then 0 else ∏ k, f k (α k)) ≤
      (4 * AP) ^ (2 * Fintype.card Bk) * (4 * AR) ^ (n - 2 * Fintype.card Bk) := by
  set m := 2 * Fintype.card Bk
  have hAR1 : AR ≤ 1 := by linarith
  -- drop admissibility, keep the bound on the number of frozen variables
  have h1 : ∑ α : Fin n → Bk × Bool, (if Inadm α s then 0 else ∏ k, f k (α k)) ≤
      ∑ α : Fin n → Bk × Bool,
        (if (univ.filter fun k => (α k).2 = true).card ≤ m then ∏ k, f k (α k) else 0) := by
    refine sum_le_sum fun α _ => ?_
    by_cases h : Inadm α s
    · rw [if_pos h]; split_ifs
      · exact prod_nonneg fun k _ => hf k _
      · exact le_rfl
    · rw [if_neg h, if_pos (card_frozen_le h)]
  -- split blocks and flags
  have h2 : ∑ α : Fin n → Bk × Bool,
        (if (univ.filter fun k => (α k).2 = true).card ≤ m then ∏ k, f k (α k) else 0) =
      ∑ t : Fin n → Bool, (if (univ.filter fun k => t k = true).card ≤ m then
        ∏ k, ∑ B, f k (B, t k) else 0) := by
    let e : (Fin n → Bk) × (Fin n → Bool) ≃ (Fin n → Bk × Bool) :=
      { toFun := fun q k => (q.1 k, q.2 k)
        invFun := fun α => (fun k => (α k).1, fun k => (α k).2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun t _ => ?_
    simp only [e, Equiv.coe_fn_mk]
    split_ifs
    · rw [Fintype.prod_sum]
    · simp
  -- each flag pattern
  have h3 : ∀ t : Fin n → Bool, (if (univ.filter fun k => t k = true).card ≤ m then
      ∏ k, ∑ B, f k (B, t k) else 0) ≤ AP ^ m * AR ^ (n - m) := by
    intro t
    split_ifs with ht
    · have hle : ∏ k, ∑ B, f k (B, t k) ≤ ∏ k, (if t k = true then AP else AR) :=
        prod_le_prod (fun k _ => sum_nonneg fun B _ => hf k _) fun k _ => by
          split_ifs with htk
          · rw [htk]; exact hP k
          · rw [show t k = false by simpa using htk]; exact hR k
      refine hle.trans ?_
      rw [prod_ite, prod_const, prod_const]
      set a := (univ.filter fun k => t k = true).card
      have hb : (univ.filter fun k => ¬t k = true).card = n - a := by
        have := Finset.filter_card_add_filter_neg_card_eq_card (s := univ) (fun k => t k = true)
        rw [card_univ, Fintype.card_fin] at this
        omega
      rw [hb]
      have e1 : AP ^ a ≤ AP ^ m := pow_le_pow_right₀ hAP ht
      have e2 : AR ^ (n - a) ≤ AR ^ (n - m) := pow_le_pow_of_le_one hAR0 hAR1 (by omega)
      exact mul_le_mul e1 e2 (by positivity) (by positivity)
    · positivity
  have h4 : ∑ t : Fin n → Bool, (if (univ.filter fun k => t k = true).card ≤ m then
      ∏ k, ∑ B, f k (B, t k) else 0) ≤ 2 ^ n * (AP ^ m * AR ^ (n - m)) := by
    refine (sum_le_sum fun t _ => h3 t).trans (le_of_eq ?_)
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [h2] at h1
  have h5 : (2 : ℝ) ^ n * (2 ^ n * (AP ^ m * AR ^ (n - m))) ≤
      (4 * AP) ^ m * (4 * AR) ^ (n - m) := by
    have e : (2 : ℝ) ^ n * (2 ^ n * (AP ^ m * AR ^ (n - m))) = AP ^ m * (4 ^ n * AR ^ (n - m)) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
    rw [e, mul_pow, mul_comm (4 ^ m), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    by_cases hnm : n ≤ m
    · rw [Nat.sub_eq_zero_of_le hnm, pow_zero, mul_one, pow_zero, mul_one]
      exact pow_le_pow_right₀ (by norm_num) hnm
    · push Not at hnm
      have : (4 : ℝ) ^ n * AR ^ (n - m) = 4 ^ m * (4 * AR) ^ (n - m) := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm.le]
      rw [this]
  calc _ ≤ 2 ^ n * (2 ^ n * (AP ^ m * AR ^ (n - m))) :=
        mul_le_mul_of_nonneg_left (h1.trans h4) (by positivity)
    _ ≤ _ := h5

open Classical in
theorem sum_adm_le (f : Fin n → Bk × Bool → ℝ) (hf : ∀ k o, 0 ≤ f k o) {AP AR : ℝ}
    (hAP : 1 ≤ AP) (hAR0 : 0 ≤ AR) (hAR : 4 * AR ≤ 1)
    (hP : ∀ k, ∑ B, f k (B, true) ≤ AP) (hR : ∀ k, ∑ B, f k (B, false) ≤ AR)
    (s : Fin n → ℤˣ) :
    2 ^ n * ∑ α : Fin n → Bk × Bool, (if Inadm α s then 0 else ∏ k, f k (α k)) ≤
      (4 * AP) ^ (2 * Fintype.card Bk) :=
  (sum_adm_le_gain f hf hAP hAR0 hAR hP hR s).trans
    (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) hAR))

end

end Loc
