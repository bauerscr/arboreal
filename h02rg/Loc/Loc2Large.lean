import Loc.Loc2Four
import Loc.PauliSum

/-!
# The contraction bound on sequences of length `≥ 5` (Lemma `lem:loc2`)

The decomposition of Lemma `lem:pauli` with a *single* block: cut-off `χ ≡ 1` and centre the
base point `b` of the small set `X`. A variable is either frozen at `b` or replaced by its
remainder `H - H(x_i ↦ b)`. By the Pauli principle at most one variable of each spin is frozen
(`card_frozen_le` with one block), so at least `n - 2` variables carry a remainder. On `X^□`
(diameter `O(L^j)`) each remainder gains `O(L^{-1})` against the scale `L^{j+1}` of the test
function. After the localisation of `exists_localized_bound`, the per-variable constant `C` and
the factor `2` of the field scale `ℓ' ≤ 2ℓ` are absorbed for `L ≥ L₀`, and for `n ≥ 5` the bound
is `O(L^{-3})`, uniformly in `n` (`exists_large_bound`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Equiv

variable {d L N : ℕ} [NeZero L]

/-! ### The single block -/

/-- The distance from the centre `b`: the `ℓ¹` norm of the centred representative. -/
def dstB (b : Lam d L N) (y : Sf (Lam d L N)) : ℝ := norm1 (rep (y.1 - b))

omit [NeZero L] in
theorem dstB_nonneg (b : Lam d L N) (y : Sf (Lam d L N)) : 0 ≤ dstB b y := norm1_nonneg _

theorem pathH_dstB (b : Lam d L N) : PathH (E := Dir d) (cenAt b) (dstB b) := by
  intro φ K hK y
  set f : Zd d → ℂ := fun u => φ (ιZ b u, y.2)
  have hM : ∀ t i, ‖f (t + Pi.single i 1) - f t‖ ≤ K := by
    intro t i
    have e : ((ιZ b (t + Pi.single i 1), y.2) : Sf (Lam d L N)) =
        sh (Pi.single (Sum.inl i) 1 : Dir d → ℕ) ((ιZ b t, y.2) : Sf (Lam d L N)) := by
      rw [MonoEst.sh_single_T]
      change ((b + prj (t + ez i), y.2) : Sf (Lam d L N)) = (b + prj t + dirVec (Sum.inl i), y.2)
      rw [prj_add, MonoEst.prj_ez, add_assoc]
    simp only [f]
    rw [e]
    exact hK _ _
  have h := path_bound f hM (rep (y.1 - b)) 0
  rw [sub_zero] at h
  have e1 : f (rep (y.1 - b)) = φ y := by
    simp only [f, ιZ, prj_rep, add_sub_cancel]
  have e2 : f 0 = φ (cenAt b y) := by
    simp only [f, ιZ, MonoEst.prj_zero', add_zero, cenAt]
  rw [e1, e2] at h
  exact h

theorem norm1_rep_prj_le (u : Zd d) : norm1 (rep (prj u : Lam d L N)) ≤ norm1 u := by
  unfold norm1
  refine sum_le_sum fun i _ => ?_
  rw [natAbs_rep]
  exact_mod_cast zabs_le_natAbs (u i)

theorem dstB_ιS_le (b : Lam d L N) (a : Sf (Zd d)) :
    dstB b (ιS b a) ≤ d * supNormZ a.1 := by
  unfold dstB ιS ιZ
  rw [add_sub_cancel_left]
  exact (norm1_rep_prj_le a.1).trans (norm1_le a.1)

theorem D1_one {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
    [AddAction (E → ℕ) X] (a : E → ℕ) (y : Sf X) :
    D1 sh a (fun _ : Sf X => (1 : ℝ)) y = if a = 0 then 1 else 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [D1_zero _ (fun _ => sh_zero _), if_pos rfl]
  · rw [D1_eq_sum, if_neg ha]
    simp only [mul_one]
    exact sum_cf_eq_zero ha

section Weights

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X]

theorem wt_one_true (Dst : Unit → Sf X → ℝ) (τ : ℝ) {s : ℝ} (y : Sf X) (b : E → ℕ) :
    wt (fun _ _ => (1 : ℝ)) Dst τ ((), true) y b * s ^ Grassmann.mabs b ≤ 1 := by
  simp only [wt, if_true]
  rw [D1_one]
  split_ifs with hb
  · subst hb; simp [Grassmann.mabs]
  · simp

theorem wt_one_false (Dst : Unit → Sf X → ℝ) (hDst : ∀ y, 0 ≤ Dst () y) {τ s : ℝ} (hτ : 0 ≤ τ)
    (hs : 0 ≤ s) (h2 : 2 * τ * s ≤ 1) (y : Sf X) (b : E → ℕ) :
    wt (fun _ _ => (1 : ℝ)) Dst τ ((), false) y b * s ^ Grassmann.mabs b ≤
      Dst () y * τ + 2 * τ * s := by
  simp only [wt, Bool.false_eq_true, if_false, wR]
  rw [sum_eq_single (0 : E → ℕ) (fun γ _ hγ => by rw [D1_one, if_neg hγ]; simp)
    (fun h => absurd (mem_Iic.2 fun _ => Nat.zero_le _) h)]
  rw [D1_one, if_pos rfl, abs_one, one_mul]
  by_cases hb : (0 : E → ℕ) = b
  · subst hb
    simp only [if_true, sh_zero, Grassmann.mabs]
    simp only [Pi.zero_apply, sum_const_zero, pow_zero, one_mul, mul_one]
    nlinarith [hDst y]
  · rw [if_neg hb, tsub_zero]
    have hb' : Grassmann.mabs b ≠ 0 := fun h => hb (mabs_eq_zero h).symm
    have e : (2 : ℝ) ^ Grassmann.mabs b * τ ^ Grassmann.mabs b * s ^ Grassmann.mabs b =
        (2 * τ * s) ^ Grassmann.mabs b := by rw [mul_pow, mul_pow]
    rw [e]
    have := pow_le_of_le_one (by positivity) h2 hb'
    nlinarith [hDst y, mul_nonneg (hDst y) hτ]

end Weights

/-! ### The bound -/

open Classical in
theorem exists_large_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ,
    ∀ (L : ℕ) [NeZero L], 2 ^ (d + 3) + 8 * d < L → L₀ ≤ L → ∀ N j : ℕ, j < N →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)),
    ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ 2 * ℓ → ∀ g : TestFn (Lam d L N),
    phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' g ≤ 1 →
    ‖pair F (restr (fun n => 5 ≤ n) g)‖ ≤ (Tj d (L : ℝ) j ℓ F).toReal * (C / (L : ℝ) ^ 3) := by
  obtain ⟨Cl, hCl0, hCl⟩ := exists_localized_bound d
  set A : ℝ := d * (2 ^ (d + 2) + 4 * d) + 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K : ℝ := 4 * (Cl + 1) * A
  refine ⟨(4 * (Cl + 1)) ^ 2 * K ^ 3, by positivity, ⌈K⌉₊, ?_⟩
  intro L _ hL hL₀ N j hj X hX F hF ℓ ℓ' hℓ hℓ' hℓℓ g hg
  set b := base X
  set R : ℝ := (rad d L j : ℝ)
  set s : ℝ := (L : ℝ) ^ j
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hs0 : 0 < s := by linarith
  have hh' : (L : ℝ) ^ (j + 1) = L * s := by rw [pow_succ, mul_comm]
  have hhL : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hKL : K ≤ L := (Nat.le_ceil K).trans (by exact_mod_cast hL₀)
  have hp : 1 ≤ pPhi d := by simp [pPhi]; omega
  set τ : ℝ := ((L : ℝ) ^ (j + 1))⁻¹ with hτdef
  have hτ : 0 ≤ τ := by positivity
  have hτs : τ * s = 1 / L := by rw [hτdef, hh']; field_simp
  have h2τs : 2 * τ * s ≤ 1 := by
    rw [mul_assoc, hτs]
    have : (2 : ℝ) ≤ L := by
      have : (2 : ℝ) ≤ K := by
        simp only [K, hAdef]
        nlinarith [hCl0, (by positivity : (0 : ℝ) ≤ d * (2 ^ (d + 2) + 4 * d))]
      linarith
    rw [mul_one_div, div_le_one hL0]; exact this
  set χ : Unit → Lam d L N → ℝ := fun _ _ => 1
  set cB : Unit → Lam d L N := fun _ => b
  set Dst : Unit → Sf (Lam d L N) → ℝ := fun _ => dstB b
  set U : ∀ n, (Fin n → Sf (Zd d)) → ℂ := fun n w => hfun χ cB (g n) (ιS b ∘ w)
  set h : TestFn (Lam d L N) :=
    fun n z => if 5 ≤ n then locH (fun _ => True) (U n) R (ρS b ∘ z) else 0
  -- the pairings agree
  have hpair : pair F (restr (fun n => 5 ≤ n) g) = pair F h := by
    unfold pair
    refine sum_congr rfl fun n _ => ?_
    congr 1
    by_cases hn : 5 ≤ n
    · simp only [restr, h, if_pos hn]
      rw [sum_coeff_hfun (χ := χ) (cB := cB) (Y := (nbhd j X : Set (Lam d L N)))
        (fun x _ => by simp [χ]) hF (g n)]
      refine sum_congr rfl fun z _ => ?_
      by_cases hz : ∀ i, (z i).1 ∈ nbhd j X
      · congr 1
        simp only [locH, if_true]
        rw [cutS_ρS_eq_one hX z hz, Complex.ofReal_one, one_mul]
        simp only [U]
        congr 1
        funext i
        exact (ιS_ρS b (z i)).symm
      · push Not at hz
        obtain ⟨i, hi⟩ := hz
        rw [coeff_eq_zero_of_mem_NX hF z i hi]; ring
    · simp [restr, h, hn]
  -- the norm of `h`
  set M : ℝ := (4 * (Cl + 1)) ^ 2 * K ^ 3 / (L : ℝ) ^ 3
  have hM0 : 0 ≤ M := by positivity
  have hbd : phiNorm (Dir d) (pPhi d) s ℓ h ≤ ENNReal.ofReal M := by
    refine phiNorm_le fun n z β hβ => ?_
    by_cases hn : 5 ≤ n
    · set B : ℝ := ℓ' ^ n * (2 ^ n)⁻¹ * ((4 * 1) ^ 2 * (4 * (A / L)) ^ (n - 2))
      have hB0 : 0 ≤ B := by positivity
      have hU : ∀ w : Fin n → Sf (Zd d), (fun _ => True) (spins w) →
          (∀ k, supNormZ (w k).1 ≤ 2 * rad d L j + 2 * pPhi d) →
          ∀ δ : Fin n → Dir d → ℕ, (∀ k, mabs (δ k) ≤ pPhi d) →
            ‖nab δ (U n) w‖ * s ^ ord δ ≤ B := by
        intro w _ hr δ hδ
        set z' := ιS b ∘ w
        have e1 : nab δ (U n) w = nab δ (hfun χ cB (g n)) z' := nab_comp_ιS b δ _ w
        rw [e1, nab_hfun]
        have hgb : Bd (pPhi d) (ℓ' ^ n) (fun _ _ (b : Dir d → ℕ) => τ ^ Grassmann.mabs b)
            (g n) := by
          intro w' β' hβ'
          have := abs_nab_le hhL hℓ' zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) w' β' hβ'
          rw [one_mul] at this
          refine this.trans (le_of_eq ?_)
          rw [hτdef, ← inv_pow, prod_pow_eq_pow_sum, ord]
        have hGb : ∀ α : Fin n → Unit × Bool, Bd (pPhi d) (ℓ' ^ n) (ρm χ Dst τ n α)
            (G χ cB (g n) n le_rfl α) := fun α =>
          bd_G (fun _ y => dstB_nonneg b y) (fun _ => pathH_dstB b) hp hτ (by positivity) hgb
            n le_rfl α
        set f : Fin n → Unit × Bool → ℝ := fun k o => wt χ Dst τ o (z' k) (δ k) * s ^ mabs (δ k)
        have hf : ∀ k o, 0 ≤ f k o := fun k o =>
          mul_nonneg (wt_nonneg (fun _ y => dstB_nonneg b y) hτ o _ _) (by positivity)
        have hDz : ∀ k, Dst () (z' k) * τ + 2 * τ * s ≤ A / L := by
          intro k
          have h1 : Dst () (z' k) ≤ d * supNormZ (w k).1 := dstB_ιS_le b (w k)
          have h2 : (d : ℝ) * supNormZ (w k).1 ≤ (d * (2 ^ (d + 2) + 4 * d)) * s := by
            have := radius_le (d := d) (L := L) j
            have h3 : (supNormZ (w k).1 : ℝ) ≤ ((2 * rad d L j + 2 * pPhi d : ℕ) : ℝ) := by
              exact_mod_cast hr k
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (h3.trans this) (Nat.cast_nonneg _)
          have h4 : Dst () (z' k) * τ ≤ (d * (2 ^ (d + 2) + 4 * d)) * s * τ :=
            mul_le_mul_of_nonneg_right (h1.trans h2) hτ
          have h5 : 2 * τ * s = 2 / L := by rw [mul_assoc, hτs]; ring
          have h6 : (d * (2 ^ (d + 2) + 4 * d)) * s * τ = (d * (2 ^ (d + 2) + 4 * d)) / L := by
            rw [mul_assoc, mul_comm s τ, hτs]; ring
          rw [h5]
          rw [h6] at h4
          calc Dst () (z' k) * τ + 2 / L ≤ (d * (2 ^ (d + 2) + 4 * d)) / L + 2 / L := by linarith
            _ = A / L := by rw [hAdef]; ring
        have hP : ∀ k, ∑ B : Unit, f k (B, true) ≤ 1 := fun k => by
          simp only [Fintype.univ_unit, sum_singleton, f]
          exact wt_one_true Dst τ (z' k) (δ k)
        have hR : ∀ k, ∑ B : Unit, f k (B, false) ≤ A / L := fun k => by
          simp only [Fintype.univ_unit, sum_singleton, f]
          exact (wt_one_false Dst (fun y => dstB_nonneg b y) hτ hs0.le h2τs (z' k) (δ k)).trans
            (hDz k)
        have hAL : 4 * (A / L) ≤ 1 := by
          rw [mul_div_assoc', div_le_one hL0]
          have : 4 * A ≤ K := by
            simp only [K]; nlinarith [hCl0]
          linarith
        have hsum := sum_adm_le_gain f hf le_rfl (by positivity) hAL hP hR (spins z')
        rw [show Fintype.card Unit = 1 from rfl, show 2 * 1 = 2 from rfl] at hsum
        have hprod : ∀ α : Fin n → Unit × Bool,
            ∏ k, ρm χ Dst τ n α k (z' k) (δ k) = (∏ k, f k (α k)) * (s ^ ord δ)⁻¹ := by
          intro α
          simp only [f, prod_mul_distrib, ρm, Fin.is_lt, dif_pos]
          rw [prod_pow_eq_pow_sum, ← ord, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
        have hnab : ‖∑ α : Fin n → Unit × Bool, (if Inadm α (spins z') then 0 else
            nab δ (G χ cB (g n) n le_rfl α) z')‖ ≤ ℓ' ^ n * (s ^ ord δ)⁻¹ *
            ∑ α : Fin n → Unit × Bool, (if Inadm α (spins z') then 0 else ∏ k, f k (α k)) := by
          rw [mul_sum]
          refine (norm_sum_le _ _).trans (sum_le_sum fun α _ => ?_)
          split_ifs
          · simp
          · refine (hGb α z' δ hδ).trans (le_of_eq ?_)
            rw [hprod]; ring
        have hsum' : ∑ α : Fin n → Unit × Bool, (if Inadm α (spins z') then 0 else
            ∏ k, f k (α k)) ≤ (2 ^ n)⁻¹ * ((4 * 1) ^ 2 * (4 * (A / L)) ^ (n - 2)) := by
          rw [le_inv_mul_iff₀ (by positivity)]; exact hsum
        calc ‖∑ α : Fin n → Unit × Bool, (if Inadm α (spins z') then 0 else
              nab δ (G χ cB (g n) n le_rfl α) z')‖ * s ^ ord δ
            ≤ (ℓ' ^ n * (s ^ ord δ)⁻¹ * ∑ α : Fin n → Unit × Bool,
                (if Inadm α (spins z') then 0 else ∏ k, f k (α k))) * s ^ ord δ :=
              mul_le_mul_of_nonneg_right hnab (by positivity)
          _ = ℓ' ^ n * ∑ α : Fin n → Unit × Bool,
                (if Inadm α (spins z') then 0 else ∏ k, f k (α k)) := by
              have : s ^ ord δ ≠ 0 := by positivity
              field_simp
          _ ≤ ℓ' ^ n * ((2 ^ n)⁻¹ * ((4 * 1) ^ 2 * (4 * (A / L)) ^ (n - 2))) :=
              mul_le_mul_of_nonneg_left hsum' (by positivity)
          _ = B := by simp only [B]; ring
      have hloc := hCl n L hL N j hj b (fun _ => True) (U n) B hB0 hU ℓ hℓ
      have ht := phiTerm_le_of_phiNorm_le hs0.le hℓ (by positivity) hloc z β hβ
      have e : phiTerm s ℓ h z β =
          phiTerm s ℓ (single n (fun z => locH (fun _ => True) (U n) R (ρS b ∘ z))) z β := by
        unfold phiTerm
        rw [single_self]
        have : h n = fun z => locH (fun _ => True) (U n) R (ρS b ∘ z) := by
          funext z; simp only [h, if_pos hn]
        rw [this]
      rw [e]
      refine ht.trans ?_
      have hKL1 : K / L ≤ 1 := (div_le_one hL0).2 hKL
      have hKL0 : 0 ≤ K / L := by positivity
      have hr : ℓ' ^ n * (2 ^ n)⁻¹ * ℓ⁻¹ ^ n ≤ 1 := by
        have e1 : ℓ' ^ n * (2 ^ n)⁻¹ * ℓ⁻¹ ^ n = (ℓ' / (2 * ℓ)) ^ n := by
          rw [div_pow, mul_pow, inv_pow]; field_simp
        rw [e1]
        exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 hℓℓ)
      have hC : Cl ^ n ≤ (Cl + 1) ^ n := pow_le_pow_left₀ hCl0 (by linarith) n
      have e2 : (Cl + 1) ^ n = (Cl + 1) ^ 2 * (Cl + 1) ^ (n - 2) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega : 2 ≤ n)]
      have hq : 0 ≤ 16 * (4 * (A / L)) ^ (n - 2) := by positivity
      calc Cl ^ n * B * ℓ⁻¹ ^ n
          = Cl ^ n * (ℓ' ^ n * (2 ^ n)⁻¹ * ℓ⁻¹ ^ n) * (16 * (4 * (A / L)) ^ (n - 2)) := by
            simp only [B]; ring
        _ ≤ (Cl + 1) ^ n * 1 * (16 * (4 * (A / L)) ^ (n - 2)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul hC hr (by positivity) (by positivity)) hq
        _ = (4 * (Cl + 1)) ^ 2 * (K / L) ^ (n - 2) := by
            rw [e2, show K / L = (Cl + 1) * (4 * (A / L)) by simp only [K]; ring,
              mul_pow (Cl + 1) (4 * (A / L)) (n - 2)]
            ring
        _ ≤ (4 * (Cl + 1)) ^ 2 * (K / L) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hKL0 hKL1 (by omega)) (by positivity)
        _ = M := by simp only [M]; rw [div_pow]; ring
    · have h0 : h n = 0 := by funext z; simp [h, hn]
      unfold phiTerm
      rw [h0, map_zero]
      simp only [Pi.zero_apply, norm_zero, mul_zero]
      exact hM0
  rw [hpair]
  refine (abs_pair_le hs0 hℓ F hM0 hbd).trans (le_of_eq ?_)
  simp only [Tj, M, s]

end

end Loc
