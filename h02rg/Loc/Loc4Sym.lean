import Loc.Loc4Est

/-!
# The symmetric quartic localisation (`h02uv-outline.tex`, Lemma `lem:C0`)

`Loc.Loc4Def` uses the quartic monomials `M^{ik}_x = (∇_i ψ)(∇_k ψ̄) ψ ψ̄` with *forward*
differences, while the quadratic basis of `Loc` uses central differences. Here the quartic
basis is replaced by the lattice-symmetric one, the `m2` stencil times `ψ_x ψ̄_x`:

  `M̂^{ik}_x = (∂_i ψ)(∂_k ψ̄) ψ ψ̄` (`i ≠ k`),  `M̂^{ii}_x = ½ ∑_{s=±} (∇_{s e_i} ψ)(∇_{s e_i} ψ̄) ψ ψ̄`.

Both are combinations of `gmono4 e e' x = (∇_e ψ)(∇_{e'} ψ̄) ψ ψ̄` with `e, e' ∈ 𝓔_d` (forward and
backward unit directions); `mono4 i k = gmono4 (inl i) (inl k)`.

* `mu4_mono4s_patch`: `μ⁽⁴⁾_{κκ'}(M̂^{ik}_x) = δ_{iκ} δ_{kκ'}` for `x` in a patch;
* `coeff_mono4s_of_ne`, `coeff_mono4s_eq_zero`: only sequences of length `4` with pattern `U(1)`;
* `mono4s_mem`: locality; `tNorm_mono4s_le`: `‖M̂^{ik}_x‖_{T(h,ℓ)} ≤ ℓ⁴ h^{-2}`;
* `Loc4sXY`, `Loc2sXY = LocXY + Loc4sXY` and their basic properties;
* `exists_Loc4sXY_bound`, `exists_Loc2sXY_bound`: `prop:Loc`(i).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-! ### The general quartic monomials -/

/-- The four vectors of `(∇_e ψ)(∇_{e'} ψ̄) ψ ψ̄` at `x`. -/
def v4g (e e' : Dir d) (x : Lam d L N) : Fin 4 → V (Lam d L N) :=
  ![ev (x + dirVec e, 1) - ev (x, 1), ev (x + dirVec e', -1) - ev (x, -1), ev (x, 1), ev (x, -1)]

/-- `(∇_e ψ)(∇_{e'} ψ̄) ψ ψ̄` at `x`. -/
def gmono4 (e e' : Dir d) (x : Lam d L N) : Alg d L N := ExteriorAlgebra.ιMulti ℂ 4 (v4g e e' x)

theorem gmono4_eq (e e' : Dir d) (x : Lam d L N) :
    gmono4 e e' x = (ψ (x + dirVec e, 1) - ψ (x, 1)) *
      ((ψ (x + dirVec e', -1) - ψ (x, -1)) * (ψ (x, 1) * ψ (x, -1))) := by
  simp [gmono4, v4g, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, ψ,
    Matrix.vecTail]

theorem coeff_gmono4_of_ne (e e' : Dir d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hn : n ≠ 4) : coeff (gmono4 e e' x) z = 0 :=
  coeff_ιMulti_of_ne _ _ hn

omit [NeZero L] in
theorem v4g_apply_eq_zero (e e' : Dir d) (x : Lam d L N) (r : Fin 4) (y : Sf (Lam d L N))
    (hy : y.2 ≠ pat4 r) : v4g e e' x r y = 0 := by
  obtain ⟨y₁, y₂⟩ := y
  fin_cases r <;> simp_all [v4g, ev, Pi.single_apply, pat4]

/-- The general quartic monomials are `U(1)`-invariant. -/
theorem coeff_gmono4_eq_zero (e e' : Dir d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hz : (univ.filter fun i => (z i).2 = 1).card ≠ (univ.filter fun i => (z i).2 = -1).card) :
    coeff (gmono4 e e' x) z = 0 := by
  by_cases hn : n = 4
  · subst hn
    rw [gmono4, coeff_ιMulti, det_apply]
    refine sum_eq_zero fun σ _ => ?_
    suffices h : ∏ r, (of fun a c => v4g e e' x c (z a)) (σ r) r = 0 by rw [h, smul_zero]
    by_contra hne
    have hall : ∀ r, (z (σ r)).2 = pat4 r := by
      intro r
      by_contra hr
      exact hne (prod_eq_zero (mem_univ r) (by simp [v4g_apply_eq_zero e e' x r _ hr]))
    have e1 : (univ.filter fun i => (z i).2 = 1).card = 2 := by
      rw [← card_filter_comp_perm σ]
      have : (univ.filter fun r => (z (σ r)).2 = 1) = univ.filter fun r => pat4 r = 1 := by
        ext r; simp [hall r]
      rw [this]; decide
    have e2 : (univ.filter fun i => (z i).2 = -1).card = 2 := by
      rw [← card_filter_comp_perm σ]
      have : (univ.filter fun r => (z (σ r)).2 = -1) = univ.filter fun r => pat4 r = -1 := by
        ext r; simp [hall r]
      rw [this]; decide
    exact hz (e1.trans e2.symm)
  · exact coeff_gmono4_of_ne e e' x z hn

theorem mu4_gmono4 (b : Lam d L N) (e e' : Dir d) (κ κ' : Fin d) (x : Lam d L N) :
    mu4 b κ κ' (gmono4 e e' x) =
      (((lift b (x + dirVec e) κ - lift b x κ) *
        (lift b (x + dirVec e') κ' - lift b x κ') : ℝ) : ℂ) := by
  set φ : Fin 4 → Lam d L N → ℂ :=
    ![fun y => (lift b y κ : ℂ), fun y => (lift b y κ' : ℂ), fun _ => 1, fun _ => 1]
  have hφ : ∀ x' : Fin 4 → Lam d L N,
      ((lift b (x' 0) κ * lift b (x' 1) κ' : ℝ) : ℂ) = ∏ r, φ r (x' r) := by
    intro x'
    simp [φ, Fin.prod_univ_four]
  simp only [mu4, cf4, gmono4, coeff_ιMulti, hφ]
  rw [sum_det_rows φ (v4g e e' x)]
  rw [det_of_upperTriangular]
  · simp [Fin.prod_univ_four, φ, v4g, ev, Pi.single_apply, pat4, mul_sub, sum_sub_distrib]
  · intro a c hac
    fin_cases a <;> fin_cases c <;> simp_all [φ, v4g, ev, Pi.single_apply, pat4, mul_sub,
      sum_sub_distrib]

theorem lift_add_dirVec' {X : Finset (Lam d L N)} (hX : Patch X) {x : Lam d L N} (hx : x ∈ X)
    (e : Dir d) (κ : Fin d) :
    lift (base X) (x + dirVec e) κ - lift (base X) x κ = ((dirZ e) κ : ℝ) := by
  have h1 := hX x hx
  have h2 := supNormZ_dirZ (d := d) e
  rw [← prj_dirZ e, lift_add (by omega)]
  simp

theorem mu4_gmono4_patch {X : Finset (Lam d L N)} (hX : Patch X) {x : Lam d L N} (hx : x ∈ X)
    (e e' : Dir d) (κ κ' : Fin d) :
    mu4 (base X) κ κ' (gmono4 e e' x) = (((dirZ e) κ * (dirZ e') κ' : ℤ) : ℂ) := by
  rw [mu4_gmono4, lift_add_dirVec' hX hx, lift_add_dirVec' hX hx]
  push_cast; ring

/-! ### The symmetric basis -/

/-- The symmetric quartic monomial `M̂^{ik}_x`. -/
def mono4s (i k : Fin d) (x : Lam d L N) : Alg d L N :=
  if i = k then
    (1 / 2 : ℂ) • (gmono4 (Sum.inl i) (Sum.inl i) x + gmono4 (Sum.inr i) (Sum.inr i) x)
  else
    (1 / 4 : ℂ) • (gmono4 (Sum.inl i) (Sum.inl k) x - gmono4 (Sum.inl i) (Sum.inr k) x -
      gmono4 (Sum.inr i) (Sum.inl k) x + gmono4 (Sum.inr i) (Sum.inr k) x)

/-- `∑_{x ∈ Y} M̂^{ik}_x`. -/
def mono4sSet (i k : Fin d) (Y : Finset (Lam d L N)) : Alg d L N := ∑ x ∈ Y, mono4s i k x

/-- The symmetric quartic part of the localisation. -/
def Loc4sXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  ∑ i, ∑ k, (mu4 (base X) i k F / X.card) • mono4sSet i k Y

/-- `Loc4sX X = Loc4sXY X X`. -/
def Loc4sX (X : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N := Loc4sXY X X F

/-- The symmetric localisation in `d = 2`: `Loc_{X,Y}` plus the symmetric quartic part. -/
def Loc2sXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  LocXY X Y F + Loc4sXY X Y F

/-- `Loc2sX X = Loc2sXY X X`. -/
def Loc2sX (X : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N := Loc2sXY X X F

theorem coeff_sub' {X : Type*} [DecidableEq X] (a b : Grassmann.N X) {n : ℕ}
    (z : Fin n → Sf X) : coeff (a - b) z = coeff a z - coeff b z := by
  rw [sub_eq_add_neg, coeff_add, show -b = (-1 : ℂ) • b by simp, coeff_smul]; ring

theorem mono4s_cases (i k : Fin d) (x : Lam d L N) (P : Alg d L N → Prop)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hsub : ∀ a b, P a → P b → P (a - b))
    (hsmul : ∀ (c : ℂ) a, P a → P (c • a)) (hg : ∀ e e', P (gmono4 e e' x)) :
    P (mono4s i k x) := by
  unfold mono4s
  split_ifs
  · exact hsmul _ _ (hadd _ _ (hg _ _) (hg _ _))
  · exact hsmul _ _ (hadd _ _ (hsub _ _ (hsub _ _ (hg _ _) (hg _ _)) (hg _ _)) (hg _ _))

theorem coeff_mono4s_of_ne (i k : Fin d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hn : n ≠ 4) : coeff (mono4s i k x) z = 0 :=
  mono4s_cases i k x (fun a => coeff a z = 0)
    (fun a b ha hb => by rw [coeff_add, ha, hb, add_zero])
    (fun a b ha hb => by rw [coeff_sub', ha, hb, sub_zero])
    (fun c a ha => by rw [coeff_smul, ha, mul_zero])
    (fun e e' => coeff_gmono4_of_ne e e' x z hn)

theorem coeff_mono4s_eq_zero (i k : Fin d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hz : (univ.filter fun i => (z i).2 = 1).card ≠ (univ.filter fun i => (z i).2 = -1).card) :
    coeff (mono4s i k x) z = 0 :=
  mono4s_cases i k x (fun a => coeff a z = 0)
    (fun a b ha hb => by rw [coeff_add, ha, hb, add_zero])
    (fun a b ha hb => by rw [coeff_sub', ha, hb, sub_zero])
    (fun c a ha => by rw [coeff_smul, ha, mul_zero])
    (fun e e' => coeff_gmono4_eq_zero e e' x z hz)

theorem mu4_mono4s_patch {X : Finset (Lam d L N)} (hX : Patch X) {x : Lam d L N} (hx : x ∈ X)
    (i k κ κ' : Fin d) :
    mu4 (base X) κ κ' (mono4s i k x) = (if κ = i then 1 else 0) * (if κ' = k then 1 else 0) := by
  unfold mono4s
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, mu4_smul, mu4_add, mu4_gmono4_patch hX hx, mu4_gmono4_patch hX hx]
    simp only [dirZ, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  · rw [if_neg hik, mu4_smul, mu4_add, mu4_sub, mu4_sub, mu4_gmono4_patch hX hx,
      mu4_gmono4_patch hX hx, mu4_gmono4_patch hX hx, mu4_gmono4_patch hX hx]
    simp only [dirZ, Pi.neg_apply, Pi.single_apply]
    split_ifs <;> push_cast <;> ring

/-! ### Coefficients and symmetry of `Loc4s` -/

theorem coeff_Loc4sXY_of_ne (X Y : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn : n ≠ 4) : coeff (Loc4sXY X Y F) z = 0 := by
  simp only [Loc4sXY, mono4sSet, coeff_sum, coeff_smul, coeff_mono4s_of_ne _ _ _ z hn, mul_zero,
    sum_const_zero]

theorem eps_Loc4sXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : ε (Loc4sXY X Y F) = 0 := by
  rw [← coeff_elim0 _ (Fin.elim0 : Fin 0 → Sf (Lam d L N))]
  exact coeff_Loc4sXY_of_ne X Y F _ (by decide)

theorem isSym_Loc4sXY (X Y : Finset (Lam d L N)) (F : Alg d L N) : IsSym (Loc4sXY X Y F) := by
  intro n z hz
  simp only [Loc4sXY, mono4sSet, coeff_sum, coeff_smul, coeff_mono4s_eq_zero _ _ _ z hz, mul_zero,
    sum_const_zero]

theorem mu4_Loc4sXY {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (F : Alg d L N)
    (κ κ' : Fin d) : mu4 (base X) κ κ' (Loc4sX X F) = mu4 (base X) κ κ' F := by
  have hX0 : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  simp only [Loc4sX, Loc4sXY, mono4sSet, mu4_sum, mu4_smul]
  simp only [sum_congr rfl fun x hx => mu4_mono4s_patch hX hx _ _ κ κ', sum_const, nsmul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  field_simp

/-- `F - Loc2s_X F` has vanishing quartic pairings. -/
theorem mu4_sub_Loc2sX {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (F : Alg d L N) (κ κ' : Fin d) : mu4 (base X) κ κ' (F - Loc2sX X F) = 0 := by
  rw [Loc2sX, Loc2sXY, mu4_sub, mu4_add, mu4_LocXY, show Loc4sXY X X F = Loc4sX X F from rfl,
    mu4_Loc4sXY hX hne]
  ring

/-! ### Locality -/

theorem gmono4_mem (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (e e' : Dir d) {x : Lam d L N} (hx : x ∈ Y) :
    gmono4 e e' x ∈ NX (nbhd j Y : Set (Lam d L N)) := by
  have hx' : x ∈ (nbhd j Y : Set (Lam d L N)) := subset_nbhd hY hx
  have hn : ∀ e : Dir d, x + dirVec e ∈ (nbhd j Y : Set (Lam d L N)) := fun e => by
    refine mem_nbhd_of_near hd hY hx ?_
    rw [add_sub_cancel_left, ← prj_dirZ e]
    exact (supNorm_prj_le _).trans (supNormZ_dirZ e)
  rw [gmono4_eq]
  refine Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (ψ_mem_NX (hn e)) (ψ_mem_NX hx'))
    (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (ψ_mem_NX (hn e')) (ψ_mem_NX hx'))
      (Subalgebra.mul_mem _ (ψ_mem_NX hx') (ψ_mem_NX hx')))

theorem mono4s_mem (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (i k : Fin d) {x : Lam d L N} (hx : x ∈ Y) :
    mono4s i k x ∈ NX (nbhd j Y : Set (Lam d L N)) :=
  mono4s_cases i k x (· ∈ NX (nbhd j Y : Set (Lam d L N))) (fun _ _ => add_mem)
    (fun _ _ => sub_mem) (fun c _ h => Subalgebra.smul_mem _ h c)
    (fun e e' => gmono4_mem hd hY e e' hx)

theorem Loc4sXY_mem (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (X : Finset (Lam d L N)) (F : Alg d L N) :
    Loc4sXY X Y F ∈ NX (nbhd j Y : Set (Lam d L N)) :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _
    (Subalgebra.sum_mem _ fun _ hx => mono4s_mem hd hY i k hx) _

/-! ### Norms -/

theorem tNorm_gmono4_le {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (e e' : Dir d)
    (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (gmono4 e e' x) ≤ ENNReal.ofReal (ℓ ^ 4 * (h ^ 2)⁻¹) := by
  have e1 : ψ (x + dirVec e, 1) - ψ (x, 1) =
      MonoEst.Dψ (Pi.single e 1 : Dir d → ℕ) ((x, 1) : Sf (Lam d L N)) :=
    (MonoEst.Dψ_one_T _ x 1).symm
  have e2 : ψ (x + dirVec e', -1) - ψ (x, -1) =
      MonoEst.Dψ (Pi.single e' 1 : Dir d → ℕ) ((x, -1) : Sf (Lam d L N)) :=
    (MonoEst.Dψ_one_T _ x (-1)).symm
  have e3 : ∀ σ : ℤˣ, ψ ((x, σ) : Sf (Lam d L N)) =
      MonoEst.Dψ (0 : Dir d → ℕ) ((x, σ) : Sf (Lam d L N)) := fun σ =>
    (MonoEst.Dψ_zero _).symm
  rw [gmono4_eq, e1, e2, e3 1, e3 (-1)]
  have h0 : Grassmann.mabs (0 : Dir d → ℕ) = 0 := by simp [Grassmann.mabs]
  have b1 := tNorm_Dψ_le (p := p) hh hℓ (a := (Pi.single e 1 : Dir d → ℕ))
    (by rw [mabs_single]; exact hp) ((x, 1) : Sf (Lam d L N))
  have b2 := tNorm_Dψ_le (p := p) hh hℓ (a := (Pi.single e' 1 : Dir d → ℕ))
    (by rw [mabs_single]; exact hp) ((x, -1) : Sf (Lam d L N))
  have b3 := tNorm_Dψ_le (p := p) hh hℓ (a := (0 : Dir d → ℕ)) (by rw [h0]; omega)
    ((x, 1) : Sf (Lam d L N))
  have b4 := tNorm_Dψ_le (p := p) hh hℓ (a := (0 : Dir d → ℕ)) (by rw [h0]; omega)
    ((x, -1) : Sf (Lam d L N))
  rw [mabs_single] at b1 b2
  rw [h0] at b3 b4
  refine (tNorm_mul_le hh hℓ _ _).trans ?_
  refine (mul_le_mul' b1 ((tNorm_mul_le hh hℓ _ _).trans (mul_le_mul' b2
    ((tNorm_mul_le hh hℓ _ _).trans (mul_le_mul' b3 b4))))).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem tNorm_mono4s_le {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (i k : Fin d)
    (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (mono4s i k x) ≤ ENNReal.ofReal (ℓ ^ 4 * (h ^ 2)⁻¹) := by
  set c := ℓ ^ 4 * (h ^ 2)⁻¹
  have hc : 0 ≤ c := by positivity
  have hg := fun e e' => tNorm_gmono4_le (p := p) hp hh hℓ e e' x
  have hT : ∀ a b : Alg d L N, tNorm (Dir d) p h ℓ (a - b) ≤ tNorm (Dir d) p h ℓ a +
      tNorm (Dir d) p h ℓ b := fun a b => tNorm_sub_le a b
  unfold mono4s
  split_ifs
  · refine (tNorm_smul_le _ _).trans ?_
    refine (mul_le_mul_left' ((tNorm_add_le _ _).trans (add_le_add (hg _ _) (hg _ _))) _).trans
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_add hc hc, ← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1; norm_num; ring
  · refine (tNorm_smul_le _ _).trans ?_
    refine (mul_le_mul_left' ((tNorm_add_le _ _).trans (add_le_add ((hT _ _).trans
      (add_le_add ((hT _ _).trans (add_le_add (hg _ _) (hg _ _))) (hg _ _))) (hg _ _))) _).trans
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_add hc hc, ← ENNReal.ofReal_add (by positivity) hc,
      ← ENNReal.ofReal_add (by positivity) hc, ← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1; norm_num; ring

theorem toReal_tNorm_mono4sSet_le {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ)
    (i k : Fin d) (Y : Finset (Lam d L N)) :
    (tNorm (Dir d) p h ℓ (mono4sSet i k Y)).toReal ≤ Y.card * (ℓ ^ 4 * (h ^ 2)⁻¹) := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((tNorm_sum_le _ _).trans ?_)
  calc ∑ x ∈ Y, tNorm (Dir d) p h ℓ (mono4s i k x)
      ≤ ∑ _x ∈ Y, ENNReal.ofReal (ℓ ^ 4 * (h ^ 2)⁻¹) :=
        sum_le_sum fun x _ => tNorm_mono4s_le hp hh hℓ i k x
    _ = ENNReal.ofReal (Y.card * (ℓ ^ 4 * (h ^ 2)⁻¹)) := by
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-! ### `prop:Loc`(i) -/

theorem exists_Loc4sXY_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (Loc4sXY X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨K, hK0, hK⟩ := exists_mu4_bound d
  refine ⟨(d : ℝ) ^ 2 * K, by positivity, ?_⟩
  intro L _ hL N j hj X Y hX hYX F hF ℓ hℓ
  have hne : X.Nonempty := hX.2.1.1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold Tj
  rw [Loc4sXY]
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  set T : ℝ := (tNorm (Dir d) (pPhi d) s ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
  have hYX' : (Y.card : ℝ) ≤ X.card := by exact_mod_cast card_le_card hYX
  have hp : 1 ≤ pPhi d := by simp [pPhi]; omega
  have hTF : tNorm (Dir d) (pPhi d) s ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  have hmu : ∀ i k : Fin d, ‖mu4 (base X) i k F‖ ≤ K * (ℓ ^ 4)⁻¹ * s ^ 2 * T := fun i k =>
    hK L hL N j hj X hX F hF i k ℓ hℓ
  have hmono : ∀ i k : Fin d, (tNorm (Dir d) (pPhi d) s ℓ (mono4sSet i k Y)).toReal ≤
      Y.card * (ℓ ^ 4 * (s ^ 2)⁻¹) := fun i k => toReal_tNorm_mono4sSet_le hp hs hℓ i k Y
  clear_value s T
  have hterm : ∀ i k : Fin d, (tNorm (Dir d) (pPhi d) s ℓ
      ((mu4 (base X) i k F / X.card) • mono4sSet i k Y)).toReal ≤ K * T := by
    intro i k
    have hsm := tNorm_smul_le (E := Dir d) (p := pPhi d) (h := s) (ℓ := ℓ)
      (mu4 (base X) i k F / X.card) (mono4sSet i k Y)
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tNorm_ne_top hs hℓ _)) hsm).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), norm_div,
      Complex.norm_natCast]
    have h1 := hmu i k
    have h2 := hmono i k
    calc ‖mu4 (base X) i k F‖ / X.card * (tNorm (Dir d) (pPhi d) s ℓ (mono4sSet i k Y)).toReal
        ≤ (K * (ℓ ^ 4)⁻¹ * s ^ 2 * T) / X.card * (Y.card * (ℓ ^ 4 * (s ^ 2)⁻¹)) := by
          gcongr
      _ = K * T * (Y.card / X.card) := by field_simp
      _ ≤ K * T * 1 := by
          gcongr
          exact (div_le_one hX0).2 hYX'
      _ = K * T := mul_one _
  refine (tNorm_sum_le _ _).trans ?_
  calc ∑ i, tNorm (Dir d) (pPhi d) s ℓ (∑ k, (mu4 (base X) i k F / X.card) • mono4sSet i k Y)
      ≤ ∑ _i : Fin d, ∑ _k : Fin d, ENNReal.ofReal (K * T) := by
        refine sum_le_sum fun i _ => (tNorm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
        rw [← ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ _)]
        exact ENNReal.ofReal_le_ofReal (hterm i k)
    _ = ENNReal.ofReal ((d : ℝ) ^ 2 * K * T) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

/-- `prop:Loc`(i) for the localisation `Loc2sXY = LocXY + Loc4sXY` of `d = 2`. -/
theorem exists_Loc2sXY_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (Loc2sXY X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C2, hC2, h2⟩ := exists_LocXY_bound d hd
  obtain ⟨C4, hC4, h4⟩ := exists_Loc4sXY_bound d hd
  refine ⟨C2 + C4, by positivity, fun L _ hL N j hj X Y hX hYX F hF ℓ hℓ => ?_⟩
  refine (tNorm_add_le _ _).trans ?_
  rw [ENNReal.ofReal_add hC2 hC4, add_mul]
  exact add_le_add (h2 L hL N j hj X Y hX hYX F hF ℓ hℓ) (h4 L hL N j hj X Y hX hYX F hF ℓ hℓ)

end

end Loc
