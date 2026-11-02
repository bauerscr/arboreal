import H04RG.Loc.Norm
import Loc.EstContractGen

/-!
# The localisation contraction bound for two species (`prop:Loc`(ii), `d ≥ 5`)

For `F ∈ 𝒩((nbhd X) × Fin 2)` with the species-wise `U(1)` symmetry (`IsSymS`), and field scales
`ℓ' ≤ ℓ`, `r = ℓ'/ℓ`:

`‖F - LocS_X F‖_{T_{j+1}(ℓ')} ≤ C (r²/L³ + r⁴) ‖F‖_{T_j(ℓ)}`  (`exists_contract_bound_S`).

Proof. Split the test function by length.
* Length `0` and odd lengths: the coefficients of `F - LocS_X F` vanish.
* Length `2`: by symmetry only species-diagonal `(ψ^a, ψ̄^a)` sequences contribute; on them the
  pairing is the single-species pairing of `res a (F - LocS_X F) = res a F - Loc_X (res a F)`
  (`res_LocSXY`), which is bounded by `Loc.exists_two_bound` and `Loc.exists_LocXY_bound`
  together with `Tj_res_le`.
* Length `≥ 4`: `LocS_X F` has no such coefficients, and `Loc.phiNorm_restr_ge_le` gives `r⁴`.

With `ℓ = ℓ_j`, `ℓ' = 2 ℓ_{j+1}`, `r = 2 L^{-(d-2)/2}`, the RG step needs `L^d` times the bound to
be small: `L^d r²/L³ = 4/L` and `L^d r⁴ = 16 L^{4-d}`. So no quartic localisation is needed for
`d ≥ 5`. (In `d = 4` the quartic `Q` is marginal and in `d = 3` relevant, and the length-`4`
part must be localised as in `Loc.Loc4Def`.)
-/

namespace H04RG.LocS

noncomputable section

open Finset Matrix Grassmann Loc FRD Equiv

variable {d L N : ℕ} [NeZero L]

/-! ### Supports -/

/-- The sites above a set of lattice points. -/
def above (Y : Set (Lam d L N)) : Set (LamS d L N) := {p | p.1 ∈ Y}

theorem res_mem {Y : Set (Lam d L N)} (a : Fin 2) {F : AlgS d L N} (hF : F ∈ NX (above Y)) :
    res a F ∈ NX Y := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨w, hw⟩, rfl⟩ := hx
    obtain ⟨⟨x, b⟩, σ⟩ := w
    by_cases hb : b = a
    · subst hb
      have : res b (ψ (((x, b), σ) : Sf (LamS d L N))) = ψ (x, σ) := by
        rw [show (((x, b), σ) : Sf (LamS d L N)) = lab b (x, σ) from rfl, ← emb_ψ, res_emb]
      rw [this]
      exact ψ_mem_NX hw
    · have : res a (ψ (((x, b), σ) : Sf (LamS d L N))) = 0 := by
        rw [show (((x, b), σ) : Sf (LamS d L N)) = lab b (x, σ) from rfl, ← emb_ψ, res_emb_ne hb]
        simp [ψ, ExteriorAlgebra.algebraMapInv]
      rw [this]
      exact zero_mem _
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-! ### Symmetry -/

/-- The species-wise `U(1)` symmetry: coefficients vanish unless every species carries as many
`ψ` as `ψ̄`. -/
def IsSymS (F : AlgS d L N) : Prop :=
  ∀ (n : ℕ) (z : Fin n → Sf (LamS d L N)) (a : Fin 2),
    (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = 1).card ≠
      (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = -1).card → coeff F z = 0

theorem isSym_res {F : AlgS d L N} (hF : IsSymS F) (a : Fin 2) : IsSym (res a F) := by
  intro n w hw
  rw [coeff_res]
  refine hF n (lab a ∘ w) a ?_
  simpa [lab] using hw

theorem card_spinsS_add {n : ℕ} (z : Fin n → Sf (LamS d L N)) :
    ∑ a : Fin 2, ((univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = 1).card +
      (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = -1).card) = n := by
  have h : ∀ a : Fin 2, (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = 1).card +
      (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = -1).card =
        (univ.filter fun i => (z i).1.2 = a).card := by
    intro a
    rw [← card_union_of_disjoint]
    · congr 1
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases Int.units_eq_one_or (z i).2 with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
    · rw [disjoint_filter]
      rintro i _ ⟨_, h1⟩ ⟨_, h2⟩
      exact absurd (h1.symm.trans h2) (by decide)
  simp only [h]
  rw [← card_eq_sum_card_fiberwise (f := fun i => (z i).1.2) (fun _ _ => mem_univ _)]
  simp

theorem coeff_eq_zero_of_oddS {F : AlgS d L N} (hF : IsSymS F) {n : ℕ} (hn : Odd n)
    (z : Fin n → Sf (LamS d L N)) : coeff F z = 0 := by
  by_contra hne
  have h0 : ∀ a : Fin 2, (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = 1).card =
      (univ.filter fun i => (z i).1.2 = a ∧ (z i).2 = -1).card :=
    fun a => by by_contra h; exact hne (hF n z a h)
  have := card_spinsS_add z
  simp only [h0, Fin.sum_univ_two] at this
  obtain ⟨k, hk⟩ := hn
  omega

/-! ### Coefficients of `emb` and of the localisation -/

open Classical in
theorem coeff_emb_gen (a : Fin 2) (H : Alg d L N) {n : ℕ} (z : Fin n → Sf (LamS d L N)) :
    coeff (emb a H) z = if ∀ i, (z i).1.2 = a then coeff H (unl ∘ z) else 0 := by
  split_ifs with hz
  · have : z = lab a ∘ (unl ∘ z) := by
      funext i
      have h := hz i
      simp only [Function.comp_apply, lab, unl]
      rw [← h]
    conv_lhs => rw [this]
    exact coeff_emb a H _
  · push Not at hz
    obtain ⟨i₀, hi₀⟩ := hz
    induction H using induction_ιMulti with
    | hzero => simp
    | hadd F G hF hG => rw [map_add, coeff_add, hF, hG, add_zero]
    | hsmul r F hF => rw [map_smul, coeff_smul, hF, mul_zero]
    | hι m v =>
      rw [emb, ExteriorAlgebra.map_apply_ιMulti]
      by_cases h : n = m
      · subst h
        rw [coeff_ιMulti]
        refine Matrix.det_eq_zero_of_row_eq_zero i₀ fun j => ?_
        rw [Matrix.of_apply, Function.comp_apply]
        show (if (z i₀).1.2 = a then v j ((z i₀).1.1, (z i₀).2) else 0) = 0
        rw [if_neg hi₀]
      · rw [coeff_ιMulti_of_ne _ _ h]

/-- The quadratic part of the localisation on species `a`. -/
theorem LocSXY_eq (X Y : Finset (Lam d L N)) (F : AlgS d L N) :
    LocSXY X Y F = (ε F * Y.card / X.card) • (1 : AlgS d L N) +
      ∑ a, emb a (∑ M, locCoef X (res a F) M • monoSet M Y) := by
  rw [LocSXY]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun M _ => ?_
  rw [map_smul, monoSets, locCoefs_eq]

theorem coeff_quad_eq_zero (X Y : Finset (Lam d L N)) (G : Alg d L N) {n : ℕ}
    (w : Fin n → Sf (Lam d L N)) (hn : n ≠ 0)
    (hw : ∀ u v : Lam d L N, coeff (psi u * psibar v) w = 0) :
    coeff (∑ M, locCoef X G M • monoSet M Y) w = 0 := by
  have h := coeff_LocXY_eq_zero X Y G w hn hw
  rw [LocXY, coeff_add, coeff_smul, coeff_one_of_ne w hn, mul_zero, zero_add] at h
  exact h

/-- Coefficients of `LocS_{X,Y} F` vanish unless the length is `0` or `2`. -/
theorem coeff_LocSXY_of_ne (X Y : Finset (Lam d L N)) (F : AlgS d L N) {n : ℕ}
    (z : Fin n → Sf (LamS d L N)) (hn0 : n ≠ 0) (hn2 : n ≠ 2) : coeff (LocSXY X Y F) z = 0 := by
  classical
  rw [LocSXY_eq, coeff_add, coeff_smul, coeff_one_of_ne z hn0, mul_zero, zero_add, coeff_sum]
  refine sum_eq_zero fun a _ => ?_
  rw [coeff_emb_gen]
  split_ifs
  · exact coeff_quad_eq_zero X Y _ _ hn0 fun u v => coeff_psi_psibar_of_ne u v _ hn2
  · rfl

theorem coeff_sub_LocSX_of_ne (X : Finset (Lam d L N)) (F : AlgS d L N) {n : ℕ}
    (z : Fin n → Sf (LamS d L N)) (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    coeff (F - LocSX X F) z = coeff F z := by
  rw [sub_eq_add_neg, coeff_add, show -LocSX X F = (-1 : ℂ) • LocSX X F by simp, coeff_smul,
    LocSX, coeff_LocSXY_of_ne X X F z hn0 hn2]
  ring

/-- On length-`2` sequences that are not of a single species, the coefficients of `LocS` and of
symmetric `F` vanish. -/
theorem coeff_sub_LocSX_mixed (X : Finset (Lam d L N)) {F : AlgS d L N} (hF : IsSymS F)
    (z : Fin 2 → Sf (LamS d L N)) (hz : ∀ a : Fin 2, ¬∀ i, (z i).1.2 = a) :
    coeff (F - LocSX X F) z = 0 := by
  classical
  have hL : coeff (LocSX X F) z = 0 := by
    rw [LocSX, LocSXY_eq, coeff_add, coeff_smul, coeff_one_of_ne z (by norm_num), mul_zero,
      zero_add, coeff_sum]
    refine sum_eq_zero fun a _ => ?_
    rw [coeff_emb_gen, if_neg (hz a)]
  have hFz : coeff F z = 0 := by
    -- the two entries have different species, so each species carries one field
    have h01 : (z 0).1.2 ≠ (z 1).1.2 := by
      intro h
      refine hz (z 0).1.2 fun i => ?_
      fin_cases i
      · rfl
      · exact h.symm
    refine hF 2 z (z 0).1.2 fun hc => ?_
    rcases Int.units_eq_one_or (z 0).2 with hs | hs
    · have h1 : (univ.filter fun i => (z i).1.2 = (z 0).1.2 ∧ (z i).2 = 1) = {0} := by
        ext i; fin_cases i <;> simp [hs, h01.symm]
      have h2 : (univ.filter fun i => (z i).1.2 = (z 0).1.2 ∧ (z i).2 = -1) = ∅ := by
        ext i; fin_cases i <;> simp [hs, h01.symm]
      rw [h1, h2] at hc
      simp at hc
    · have h1 : (univ.filter fun i => (z i).1.2 = (z 0).1.2 ∧ (z i).2 = 1) = ∅ := by
        ext i; fin_cases i <;> simp [hs, h01.symm]
      have h2 : (univ.filter fun i => (z i).1.2 = (z 0).1.2 ∧ (z i).2 = -1) = {0} := by
        ext i; fin_cases i <;> simp [hs, h01.symm]
      rw [h1, h2] at hc
      simp at hc
  rw [sub_eq_add_neg, coeff_add, show -LocSX X F = (-1 : ℂ) • LocSX X F by simp, coeff_smul, hFz,
    hL]
  ring

/-! ### Pairing on length `2` -/

/-- The species-`a` part of a two-species test function on length `2`. -/
def part (a : Fin 2) (g : (Fin 2 → Sf (LamS d L N)) → ℂ) : (Fin 2 → Sf (Lam d L N)) → ℂ :=
  fun w => g (lab a ∘ w)

theorem pair_congr_of_coeff {X : Type*} [DecidableEq X] [Fintype X] (F : Grassmann.N X)
    {g₁ g₂ : TestFn X} (h : ∀ n (z : Fin n → Sf X), coeff F z ≠ 0 → g₁ n z = g₂ n z) :
    pair F g₁ = pair F g₂ := by
  unfold pair
  refine sum_congr rfl fun n _ => ?_
  congr 1
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : coeff F z = 0
  · simp [hz]
  · rw [h n z hz]

theorem pair_two_eq (X : Finset (Lam d L N)) {F : AlgS d L N} (hF : IsSymS F)
    (g : (Fin 2 → Sf (LamS d L N)) → ℂ) :
    pair (F - LocSX X F) (single 2 g) =
      ∑ a : Fin 2, pair (res a (F - LocSX X F)) (single 2 (part a g)) := by
  classical
  simp only [pair_res]
  rw [show (∑ a : Fin 2, pair (F - LocSX X F) (liftT a (single 2 (part a g)))) =
      pair (F - LocSX X F) (∑ a : Fin 2, liftT a (single 2 (part a g))) from
    (map_sum (pairR (F - LocSX X F)) _ univ).symm]
  refine pair_congr_of_coeff _ fun n z hz => ?_
  rw [Fin.sum_univ_two]
  show Loc.single 2 g n z = liftT 0 (Loc.single 2 (part 0 g)) n z +
    liftT 1 (Loc.single 2 (part 1 g)) n z
  have hback : ∀ a : Fin 2, (∀ i, (z i).1.2 = a) → lab a ∘ (unl ∘ z) = z := by
    intro a ha
    funext i
    simp only [Function.comp_apply, lab, unl]
    rw [← ha i]
  by_cases hn : n = 2
  · subst hn
    by_cases h0 : ∀ i, (z i).1.2 = 0
    · have h1 : ¬∀ i, (z i).1.2 = 1 := fun h1 => absurd ((h0 0).symm.trans (h1 0)) (by decide)
      rw [liftT_of_all _ h0, liftT_of_not _ h1, add_zero, single_self, single_self, part,
        hback 0 h0]
    · by_cases h1 : ∀ i, (z i).1.2 = 1
      · rw [liftT_of_not _ h0, liftT_of_all _ h1, zero_add, single_self, single_self, part,
          hback 1 h1]
      · exact absurd (coeff_sub_LocSX_mixed X hF z fun a => by
          fin_cases a
          · exact h0
          · exact h1) hz
  · have hz0 : ∀ a : Fin 2, liftT a (Loc.single 2 (part a g)) n z = 0 := by
      intro a
      by_cases ha : ∀ i, (z i).1.2 = a
      · rw [liftT_of_all _ ha, single_ne _ hn]; rfl
      · exact liftT_of_not _ ha
    rw [single_ne _ hn, hz0, hz0, add_zero]
    rfl

/-! ### Derivatives of the species parts -/

theorem lab_sh (a : Fin 2) (b : Dir d → ℕ) (z : Sf (Lam d L N)) :
    lab a (sh b z) = sh b (lab a z) := rfl

theorem nab_part (a : Fin 2) (g : (Fin 2 → Sf (LamS d L N)) → ℂ) (γ : Fin 2 → Dir d → ℕ)
    (w : Fin 2 → Sf (Lam d L N)) : nab γ (part a g) w = nab γ g (lab a ∘ w) :=
  nabla_comp_pi sh sh (fun _ => lab a) (fun _ b z => lab_sh a b z) γ g w

/-! ### The contraction bound -/

theorem restr_decomp3 {X : Type*} (g : TestFn X) :
    g = Loc.restr (fun n => n = 2) g + Loc.restr (fun n => 4 ≤ n) g +
      Loc.restr (fun n => n ≠ 2 ∧ n < 4) g := by
  funext n z
  simp only [Loc.restr, Pi.add_apply]
  by_cases h2 : n = 2
  · subst h2; simp
  by_cases h4 : 4 ≤ n
  · simp [h2, h4]
  · simp [h2, h4, show n < 4 by omega]

theorem exists_contract_bound_S (d : ℕ) (hd : 2 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ ℓ' : ℝ, 0 < ℓ → 0 < ℓ' → ℓ' ≤ ℓ →
    ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (above (nbhd j X : Set (Lam d L N))), IsSymS F →
      Tj d (L : ℝ) (j + 1) ℓ' (F - LocSX X F) ≤
        ENNReal.ofReal (C * ((ℓ' / ℓ) ^ 2 / (L : ℝ) ^ 3 + (ℓ' / ℓ) ^ 4)) *
          Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C2, hC2, hC2b⟩ := exists_two_bound d hd
  obtain ⟨Cb, hCb, hCbb⟩ := exists_LocXY_bound d (by omega)
  refine ⟨1 + 2 * ((1 + Cb) * C2), by positivity, ?_⟩
  intro L _ hL N j hj ℓ ℓ' hℓ hℓ' hℓ'ℓ X hX F hF hsym
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set r : ℝ := ℓ' / ℓ with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hratio : ℓ' * ℓ⁻¹ = r := by rw [hrdef, div_eq_mul_inv]
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hss : s ≤ (L : ℝ) ^ (j + 1) := by
    rw [pow_succ]; exact le_mul_of_one_le_right hs.le hL1
  set T : ℝ := (Tj d (L : ℝ) j ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hTF : Tj d (L : ℝ) j ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  have hne : X.Nonempty := hX.2.1.1
  have hpatch := patch_of_small hL hj hX
  set G := F - LocSX X F with hGdef
  -- the single-species restrictions
  have hGa : ∀ a : Fin 2, res a G = res a F - LocX X (res a F) := fun a => by
    rw [hGdef, map_sub, LocSX, res_LocSXY, LocX]
  have hFa : ∀ a : Fin 2, res a F ∈ NX (nbhd j X : Set (Lam d L N)) := fun a => res_mem a hF
  have hTa : ∀ a : Fin 2, (Tj d (L : ℝ) j ℓ (res a G)).toReal ≤ (1 + Cb) * T := by
    intro a
    have hTra : Tj d (L : ℝ) j ℓ (res a F) ≤ ENNReal.ofReal T := by
      rw [← hTF]; exact Tj_res_le a _ (by positivity) j ℓ hℓ F
    have h1 := tNorm_sub_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ j) (ℓ := ℓ) (res a F)
      (LocX X (res a F))
    have h2 := hCbb L hL N j hj X X hX subset_rfl (res a F) (hFa a) ℓ hℓ
    have h3 : Tj d (L : ℝ) j ℓ (res a G) ≤ ENNReal.ofReal ((1 + Cb) * T) := by
      rw [hGa a]
      refine h1.trans ?_
      calc tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (res a F) +
            tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (LocX X (res a F))
          ≤ ENNReal.ofReal T + ENNReal.ofReal Cb * ENNReal.ofReal T :=
            add_le_add hTra (h2.trans (mul_le_mul_right hTra _))
        _ = ENNReal.ofReal ((1 + Cb) * T) := by
            rw [← ENNReal.ofReal_mul hCb, ← ENNReal.ofReal_add hT (by positivity)]
            congr 1; ring
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3
  -- reduce to test functions
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  refine tNorm_le fun g hg => ?_
  set g' := asym g
  have hg' : phiNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' g' ≤ 1 :=
    (phiNorm_asym_le hh'.le hℓ' g).trans hg
  have hgb : ∀ (n : ℕ) (z : Fin n → Sf (LamS d L N)) (γ : Fin n → Dir d → ℕ),
      (∀ k, mabs (γ k) ≤ pPhi d) → ‖nab γ (g' n) z‖ ≤ ℓ' ^ n * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹ :=
    fun n z γ hγ => by
      have := abs_nab_le hh' hℓ' zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g') z γ hγ
      rwa [one_mul] at this
  have hga : ∀ a a' : Sf (LamS d L N), g' 2 ![a', a] = -g' 2 ![a, a'] := fun a a' => by
    have := asym_perm g ![a, a'] (Equiv.swap 0 1)
    have e : (![a, a'] ∘ Equiv.swap (0 : Fin 2) 1) = ![a', a] := by
      funext i; fin_cases i <;> rfl
    rw [e, Perm.sign_swap (by decide)] at this
    simpa using this
  have hdec : pair G g' = pair G (Loc.restr (fun n => n = 2) g') +
      pair G (Loc.restr (fun n => 4 ≤ n) g') + pair G (Loc.restr (fun n => n ≠ 2 ∧ n < 4) g') := by
    have hadd : ∀ g₁ g₂ : TestFn (LamS d L N), pair G (g₁ + g₂) = pair G g₁ + pair G g₂ :=
      fun g₁ g₂ => map_add (pairR G) g₁ g₂
    conv_lhs => rw [restr_decomp3 g']
    simp only [hadd]
  rw [← pair_asym, hdec]
  -- the rest: lengths 0, 1, 3
  have hrest : pair G (Loc.restr (fun n => n ≠ 2 ∧ n < 4) g') = 0 := by
    refine pair_restr_eq_zero _ _ fun n z hn => ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [coeff_elim0, hGdef, map_sub, LocSX, ← LocSX, ε_LocSX hne, sub_self]
    · rw [hGdef, coeff_sub_LocSX_of_ne X F z (by omega) hn.1]
      exact coeff_eq_zero_of_oddS hsym (Nat.odd_iff.2 (by omega)) z
  -- lengths ≥ 4
  have h4 : ‖pair G (Loc.restr (fun n => 4 ≤ n) g')‖ ≤ T * r ^ 4 := by
    rw [pair_restr_congr (G := F) _ _ fun n z hn =>
      coeff_sub_LocSX_of_ne X F z (by omega) (by omega)]
    have hn := phiNorm_restr_ge_le hs hss hℓ hℓ' hℓ'ℓ hg' 4
    exact abs_pair_le hs hℓ F (by positivity) hn
  -- length 2, one species at a time
  have hpa : ∀ a : Fin 2, ‖pair (res a G) (single 2 (part a (g' 2)))‖ ≤
      (1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3) := by
    intro a
    have hmem : res a G ∈ NX (nbhd j X : Set (Lam d L N)) := by
      rw [hGa a]; exact sub_mem (hFa a) (LocXY_mem (by omega) hX.1 X (res a F))
    have hsame : ∀ (u u' : Lam d L N) (σ : ℤˣ), coeff (res a G) ![(u, σ), (u', σ)] = 0 := by
      intro u u' σ; rw [hGa a]; exact coeff_sub_LocX_same X (isSym_res hsym a) u u' σ
    have hmu : ∀ β : Mono d, mu (base X) β (res a G) = 0 := by
      intro β; rw [hGa a]; exact mu_sub_LocX hpatch hne (res a F) β
    have hanti : ∀ u u' : Sf (Lam d L N), part a (g' 2) ![u', u] = -part a (g' 2) ![u, u'] := by
      intro u u'
      have e : ∀ v v' : Sf (Lam d L N), (lab a ∘ ![v, v'] : Fin 2 → Sf (LamS d L N)) =
          ![lab a v, lab a v'] := fun v v' => by funext i; fin_cases i <;> rfl
      simp only [part, e]
      exact hga (lab a u) (lab a u')
    have hder : ∀ (w : Fin 2 → Sf (Lam d L N)) (γ : Fin 2 → Dir d → ℕ), (∀ k, mabs (γ k) ≤ pPhi d) →
        ‖nab γ (part a (g' 2)) w‖ ≤ ℓ' ^ 2 * (((L : ℝ) ^ (j + 1)) ^ ord γ)⁻¹ := by
      intro w γ hγ; rw [nab_part]; exact hgb 2 _ γ hγ
    have := hC2b L hL N j hj X hX (res a G) hmem hsame hmu ℓ ℓ' hℓ hℓ' _ hanti hder
    refine this.trans ?_
    have hq : 0 ≤ C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3 := by positivity
    calc (Tj d (L : ℝ) j ℓ (res a G)).toReal * (C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3)
        ≤ (1 + Cb) * T * (C2 * ℓ' ^ 2 * ℓ⁻¹ ^ 2 / (L : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right (hTa a) hq
      _ = (1 + Cb) * T * (C2 * (ℓ' * ℓ⁻¹) ^ 2 / (L : ℝ) ^ 3) := by ring
      _ = _ := by rw [hratio]
  have h2 : ‖pair G (Loc.restr (fun n => n = 2) g')‖ ≤
      2 * ((1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3)) := by
    rw [pair_restr_eq_single, pair_two_eq X hsym, Fin.sum_univ_two, two_mul]
    exact (norm_add_le _ _).trans (add_le_add (hpa 0) (hpa 1))
  rw [hrest, add_zero]
  refine (norm_add_le _ _).trans ((add_le_add h2 h4).trans ?_)
  have a2 : 0 ≤ r ^ 2 / (L : ℝ) ^ 3 := by positivity
  have a4 : 0 ≤ r ^ 4 := by positivity
  have hCb0 : 0 ≤ (1 + Cb) * C2 := by positivity
  calc 2 * ((1 + Cb) * T * (C2 * r ^ 2 / (L : ℝ) ^ 3)) + T * r ^ 4
      = T * ((2 * ((1 + Cb) * C2)) * (r ^ 2 / (L : ℝ) ^ 3) + r ^ 4) := by ring
    _ ≤ T * ((1 + 2 * ((1 + Cb) * C2)) * (r ^ 2 / (L : ℝ) ^ 3 + r ^ 4)) := by
        refine mul_le_mul_of_nonneg_left ?_ hT
        nlinarith [mul_nonneg hCb0 a4]
    _ = _ := by ring

end

end H04RG.LocS
