import Loc.EstLocCoeffs

/-!
# The quartic marginal localisation (`d = 2`)

In `d = 2` the field has dimension `[ψ] = 0`, and the quartic local monomials with two
derivatives, `ψ ψ̄ (∇_i ψ)(∇_k ψ̄)`, are marginal (`M` of `h02uv-outline.tex`,
Section `sec:loc`). `Loc_X` (`Loc.LocDef`) only reproduces the constant and the quadratic part.
Here we add the projection of the quartic part onto these monomials:

* `mu4 b i k F = ∑_x F_{(x₀,+)(x₁,-)(x₂,+)(x₃,-)} ℓ(x₀)_i ℓ(x₁)_k`, the pairing with the quartic
  test polynomial `ℓ(x₀)_i ℓ(x₁)_k`;
* `mono4 i k x = (ψ_{x+e_i} - ψ_x)(ψ̄_{x+e_k} - ψ̄_x) ψ_x ψ̄_x`;
* `Loc4XY X Y F = ∑_{i,k} (mu4 i k F / |X|) ∑_{x ∈ Y} mono4 i k x`, `Loc4X X = Loc4XY X X`;
* `Loc2XY = LocXY + Loc4XY`, the localisation in `d = 2`.

Main facts: `mu4 (base X) κ κ' (mono4 i k x) = δ_{iκ} δ_{kκ'}` for `x ∈ X` (patch condition), so
`mu4 (Loc4X X F) = mu4 F` (`mu4_Loc4X`); `Loc4XY` only has coefficients on sequences of length
`4` with two fields of each spin; and `Loc4XY X Y F ∈ 𝒩(Y^□)`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The spin pattern `(+, -, +, -)`. -/
def pat4 : Fin 4 → ℤˣ := ![1, -1, 1, -1]

/-- The coefficient `F_{(x₀,+)(x₁,-)(x₂,+)(x₃,-)}`. -/
def cf4 (F : Alg d L N) (x : Fin 4 → Lam d L N) : ℂ := coeff F fun r => (x r, pat4 r)

/-- The pairing of the quartic part of `F` with the test polynomial `ℓ(x₀)_i ℓ(x₁)_k`. -/
def mu4 (b : Lam d L N) (i k : Fin d) (F : Alg d L N) : ℂ :=
  ∑ x : Fin 4 → Lam d L N, cf4 F x * ((lift b (x 0) i * lift b (x 1) k : ℝ) : ℂ)

/-- The four vectors of the quartic monomial. -/
def v4 (i k : Fin d) (x : Lam d L N) : Fin 4 → V (Lam d L N) :=
  ![ev (x + dirVec (Sum.inl i), 1) - ev (x, 1), ev (x + dirVec (Sum.inl k), -1) - ev (x, -1),
    ev (x, 1), ev (x, -1)]

/-- The quartic local monomial `(∇_i ψ)(∇_k ψ̄) ψ ψ̄` at `x`. -/
def mono4 (i k : Fin d) (x : Lam d L N) : Alg d L N := ExteriorAlgebra.ιMulti ℂ 4 (v4 i k x)

/-- `∑_{x ∈ Y} mono4 i k x`. -/
def mono4Set (i k : Fin d) (Y : Finset (Lam d L N)) : Alg d L N := ∑ x ∈ Y, mono4 i k x

/-- The quartic part of the localisation. -/
def Loc4XY (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N :=
  ∑ i, ∑ k, (mu4 (base X) i k F / X.card) • mono4Set i k Y

/-- `Loc4X X = Loc4XY X X`. -/
def Loc4X (X : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N := Loc4XY X X F

/-- The localisation in `d = 2`: `Loc_{X,Y}` plus the quartic marginal part. -/
def Loc2XY (X Y : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N := LocXY X Y F + Loc4XY X Y F

/-- `Loc2X X = Loc2XY X X`. -/
def Loc2X (X : Finset (Lam d L N)) (F : Alg d L N) : Alg d L N := Loc2XY X X F

theorem mono4_eq (i k : Fin d) (x : Lam d L N) :
    mono4 i k x = (ψ (x + dirVec (Sum.inl i), 1) - ψ (x, 1)) *
      ((ψ (x + dirVec (Sum.inl k), -1) - ψ (x, -1)) * (ψ (x, 1) * ψ (x, -1))) := by
  simp [mono4, v4, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, ψ,
    Matrix.vecTail]

/-! ### Linearity of `mu4` -/

theorem mu4_add (b : Lam d L N) (i k : Fin d) (F G : Alg d L N) :
    mu4 b i k (F + G) = mu4 b i k F + mu4 b i k G := by
  simp only [mu4, cf4, coeff_add, add_mul, sum_add_distrib]

theorem mu4_smul (b : Lam d L N) (i k : Fin d) (r : ℂ) (F : Alg d L N) :
    mu4 b i k (r • F) = r * mu4 b i k F := by
  simp only [mu4, cf4, coeff_smul, mul_sum, mul_assoc]

theorem mu4_sub (b : Lam d L N) (i k : Fin d) (F G : Alg d L N) :
    mu4 b i k (F - G) = mu4 b i k F - mu4 b i k G := by
  rw [sub_eq_add_neg, mu4_add, show -G = (-1 : ℂ) • G by simp, mu4_smul]; ring

theorem mu4_sum {ι : Type*} (s : Finset ι) (b : Lam d L N) (i k : Fin d) (F : ι → Alg d L N) :
    mu4 b i k (∑ a ∈ s, F a) = ∑ a ∈ s, mu4 b i k (F a) := by
  simp only [mu4, cf4, coeff_sum, sum_mul]
  exact sum_comm

/-! ### Coefficients -/

theorem coeff_mono4_of_ne (i k : Fin d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hn : n ≠ 4) : coeff (mono4 i k x) z = 0 :=
  coeff_ιMulti_of_ne _ _ hn

theorem coeff_Loc4XY_of_ne (X Y : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (hn : n ≠ 4) : coeff (Loc4XY X Y F) z = 0 := by
  simp only [Loc4XY, mono4Set, coeff_sum, coeff_smul, coeff_mono4_of_ne _ _ _ z hn, mul_zero,
    sum_const_zero]

theorem eps_Loc4XY (X Y : Finset (Lam d L N)) (F : Alg d L N) : ε (Loc4XY X Y F) = 0 := by
  rw [← coeff_elim0 _ (Fin.elim0 : Fin 0 → Sf (Lam d L N))]
  exact coeff_Loc4XY_of_ne X Y F _ (by decide)

omit [NeZero L] in
theorem v4_apply_eq_zero (i k : Fin d) (x : Lam d L N) (r : Fin 4) (y : Sf (Lam d L N))
    (hy : y.2 ≠ pat4 r) : v4 i k x r y = 0 := by
  obtain ⟨y₁, y₂⟩ := y
  fin_cases r <;> simp_all [v4, ev, Pi.single_apply, pat4]

theorem card_filter_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Fin n → Prop)
    [DecidablePred P] : (univ.filter fun i => P (σ i)).card = (univ.filter P).card := by
  refine Finset.card_bij (fun i _ => σ i) (fun i hi => by simpa using hi)
    (fun a _ b _ h => σ.injective h) fun b hb => ⟨σ.symm b, by simpa using hb, by simp⟩

/-- The quartic monomials are `U(1)`-invariant. -/
theorem coeff_mono4_eq_zero (i k : Fin d) (x : Lam d L N) {n : ℕ} (z : Fin n → Sf (Lam d L N))
    (hz : (univ.filter fun i => (z i).2 = 1).card ≠ (univ.filter fun i => (z i).2 = -1).card) :
    coeff (mono4 i k x) z = 0 := by
  by_cases hn : n = 4
  · subst hn
    rw [mono4, coeff_ιMulti, det_apply]
    refine sum_eq_zero fun σ _ => ?_
    suffices h : ∏ r, (of fun a c => v4 i k x c (z a)) (σ r) r = 0 by rw [h, smul_zero]
    by_contra hne
    have hall : ∀ r, (z (σ r)).2 = pat4 r := by
      intro r
      by_contra hr
      exact hne (prod_eq_zero (mem_univ r) (by simp [v4_apply_eq_zero i k x r _ hr]))
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
  · exact coeff_mono4_of_ne i k x z hn

theorem isSym_Loc4XY (X Y : Finset (Lam d L N)) (F : Alg d L N) : IsSym (Loc4XY X Y F) := by
  intro n z hz
  simp only [Loc4XY, mono4Set, coeff_sum, coeff_smul, coeff_mono4_eq_zero _ _ _ z hz, mul_zero,
    sum_const_zero]

/-! ### The pairing of `mono4` with the test polynomials -/

theorem sum_det_rows (φ : Fin 4 → Lam d L N → ℂ) (v : Fin 4 → V (Lam d L N)) :
    ∑ x : Fin 4 → Lam d L N, (of fun a c => v c (x a, pat4 a)).det * ∏ r, φ r (x r) =
      (of fun a c => ∑ y, φ a y * v c (y, pat4 a)).det := by
  have h1 : ∀ x : Fin 4 → Lam d L N, (of fun a c => v c (x a, pat4 a)).det * ∏ r, φ r (x r) =
      detRowAlternating (fun a c => φ a (x a) * v c (x a, pat4 a)) := by
    intro x
    have := det_mul_column (fun a => φ a (x a)) (of fun a c => v c (x a, pat4 a))
    rw [mul_comm]
    exact this.symm
  simp only [h1]
  have h2 := (detRowAlternating (R := ℂ) (n := Fin 4)).toMultilinearMap.map_sum
    (fun a (y : Lam d L N) c => φ a y * v c (y, pat4 a))
  simp only [AlternatingMap.coe_multilinearMap] at h2
  rw [← h2]
  show _ = detRowAlternating _
  congr 1
  funext a c
  simp [Finset.sum_apply]

theorem mu4_mono4 (b : Lam d L N) (i k κ κ' : Fin d) (x : Lam d L N) :
    mu4 b κ κ' (mono4 i k x) =
      (((lift b (x + dirVec (Sum.inl i)) κ - lift b x κ) *
        (lift b (x + dirVec (Sum.inl k)) κ' - lift b x κ') : ℝ) : ℂ) := by
  set φ : Fin 4 → Lam d L N → ℂ :=
    ![fun y => (lift b y κ : ℂ), fun y => (lift b y κ' : ℂ), fun _ => 1, fun _ => 1]
  have hφ : ∀ x' : Fin 4 → Lam d L N,
      ((lift b (x' 0) κ * lift b (x' 1) κ' : ℝ) : ℂ) = ∏ r, φ r (x' r) := by
    intro x'
    simp [φ, Fin.prod_univ_four]
  simp only [mu4, cf4, mono4, coeff_ιMulti, hφ]
  rw [sum_det_rows φ (v4 i k x)]
  rw [det_of_upperTriangular]
  · simp [Fin.prod_univ_four, φ, v4, ev, Pi.single_apply, pat4, mul_sub, sum_sub_distrib]
  · intro a c hac
    fin_cases a <;> fin_cases c <;> simp_all [φ, v4, ev, Pi.single_apply, pat4, mul_sub,
      sum_sub_distrib]

theorem lift_add_dirVec {X : Finset (Lam d L N)} (hX : Patch X) {x : Lam d L N} (hx : x ∈ X)
    (i κ : Fin d) :
    lift (base X) (x + dirVec (Sum.inl i)) κ - lift (base X) x κ = if κ = i then 1 else 0 := by
  have h1 := hX x hx
  have h2 := supNormZ_ez (d := d) i
  rw [← MonoEst.prj_ez, lift_add (by omega)]
  simp [ez, Pi.single_apply]

theorem mu4_mono4_patch {X : Finset (Lam d L N)} (hX : Patch X) {x : Lam d L N} (hx : x ∈ X)
    (i k κ κ' : Fin d) :
    mu4 (base X) κ κ' (mono4 i k x) = (if κ = i then 1 else 0) * (if κ' = k then 1 else 0) := by
  rw [mu4_mono4, lift_add_dirVec hX hx, lift_add_dirVec hX hx]
  split_ifs <;> simp

theorem mu4_Loc4XY {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty) (F : Alg d L N)
    (κ κ' : Fin d) : mu4 (base X) κ κ' (Loc4X X F) = mu4 (base X) κ κ' F := by
  have hX0 : (X.card : ℂ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  simp only [Loc4X, Loc4XY, mono4Set, mu4_sum, mu4_smul]
  simp only [sum_congr rfl fun x hx => mu4_mono4_patch hX hx _ _ κ κ', sum_const, nsmul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  field_simp

theorem mu4_LocXY (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) (κ κ' : Fin d) :
    mu4 b κ κ' (LocXY X Y F) = 0 := by
  refine sum_eq_zero fun x _ => ?_
  rw [cf4, coeff_LocXY_eq_zero X Y F _ (by decide) fun u v =>
    coeff_psi_psibar_of_ne u v _ (by decide), zero_mul]

/-- `F - Loc2_X F` has vanishing quartic pairings. -/
theorem mu4_sub_Loc2X {X : Finset (Lam d L N)} (hX : Patch X) (hne : X.Nonempty)
    (F : Alg d L N) (κ κ' : Fin d) : mu4 (base X) κ κ' (F - Loc2X X F) = 0 := by
  rw [Loc2X, Loc2XY, mu4_sub, mu4_add, mu4_LocXY, show Loc4XY X X F = Loc4X X F from rfl,
    mu4_Loc4XY hX hne]
  ring

/-! ### Locality -/

theorem mono4_mem (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (i k : Fin d) {x : Lam d L N} (hx : x ∈ Y) :
    mono4 i k x ∈ NX (nbhd j Y : Set (Lam d L N)) := by
  have hx' : x ∈ (nbhd j Y : Set (Lam d L N)) := subset_nbhd hY hx
  have hn : ∀ i : Fin d, x + dirVec (Sum.inl i) ∈ (nbhd j Y : Set (Lam d L N)) := fun i => by
    refine mem_nbhd_of_near hd hY hx ?_
    rw [add_sub_cancel_left, ← MonoEst.prj_ez]
    exact (supNorm_prj_le _).trans (supNormZ_ez i)
  rw [mono4_eq]
  refine Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (ψ_mem_NX (hn i)) (ψ_mem_NX hx'))
    (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (ψ_mem_NX (hn k)) (ψ_mem_NX hx'))
      (Subalgebra.mul_mem _ (ψ_mem_NX hx') (ψ_mem_NX hx')))

theorem Loc4XY_mem (hd : 1 ≤ d) {j : ℕ} {Y : Finset (Lam d L N)} (hY : IsPolymer j Y)
    (X : Finset (Lam d L N)) (F : Alg d L N) :
    Loc4XY X Y F ∈ NX (nbhd j Y : Set (Lam d L N)) :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _
    (Subalgebra.sum_mem _ fun _ hx => mono4_mem hd hY i k hx) _

end

end Loc
