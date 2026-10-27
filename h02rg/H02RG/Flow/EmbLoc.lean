import Flow.EmbAlg
import Flow.EmbGeom

/-!
# `emb` and the local polynomials, `Loc` and the covariances

* `embA ψ_x = ψ_{emb x}` (`embA_psi`), `embA V(X) = V(emb X)` (`embA_eval`),
  `embA M_x = M_{emb x}` (`embA_monoAt`);
* `embA Loc_{X,Y} F = Loc_{emb X, emb Y} embA F` for `F` supported in a region near the origin
  (`LocXY_emb`), the analogue of `LocXY_aut`;
* the covariances of the finite range decomposition are compatible with `emb`
  (`Cfrd_emb_of`).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Matrix

variable {d L : ℕ} [NeZero L] {N M : ℕ}

theorem embA_eq : embA (d := d) (L := L) N M = pushA (emb N M) := rfl

@[simp] theorem coe_embE (F : EvR (Lam d L N)) : (embE N M F : Alg d L M) = embA N M F := rfl

/-- `emb` on the doubled algebra. -/
abbrev embA2 (N M : ℕ) : Alg2 d L N →ₐ[ℂ] Alg2 d L M := pushA (Sum.map (emb N M) (emb N M))

/-- `emb` on even elements of the doubled algebra. -/
def embE2 (N M : ℕ) : EvR (Lam d L N ⊕ Lam d L N) →ₐ[ℂ] EvR (Lam d L M ⊕ Lam d L M) :=
  mapE (pushV (Sum.map (emb N M) (emb N M)))

@[simp] theorem coe_embE2 (F : EvR (Lam d L N ⊕ Lam d L N)) :
    (embE2 N M F : Alg2 d L M) = embA2 N M F := rfl

variable (hNM : N ≤ M)
include hNM

theorem embA_ψ (a : Sf (Lam d L N)) : embA N M (ψ a) = ψ (emb N M a.1, a.2) :=
  pushA_ψ (emb_injective' hNM) a

theorem embA_psi' (x : Lam d L N) : embA N M (psi x) = psi (emb N M x) := embA_ψ hNM _

theorem embA_psibar' (x : Lam d L N) : embA N M (psibar x) = psibar (emb N M x) := embA_ψ hNM _

theorem embE2_thetaE (F : EvR (Lam d L N)) : embE2 N M (thetaE F) = thetaE (embE N M F) :=
  Subtype.ext (by
    rw [coe_embE2, coe_thetaE, coe_thetaE, coe_embE]
    exact (theta_pushA (emb_injective' hNM) (F : Alg d L N)).symm)

theorem embE2_inclE (F : EvR (Lam d L N)) : embE2 N M (inclE F) = inclE (embE N M F) :=
  Subtype.ext (by
    rw [coe_embE2, coe_inclE, coe_inclE, coe_embE]
    exact (incl_pushA (emb_injective' hNM) (F : Alg d L N)).symm)

theorem ε_embA (F : Alg d L N) : ε (embA N M F) = ε F := ε_pushA F

theorem embA_mem_NX {X : Set (Lam d L N)} {F : Alg d L N} (hF : F ∈ NX X) :
    embA N M F ∈ NX (emb N M '' X) := pushA_mem_NX (emb_injective' hNM) hF

theorem cf2_embA (F : Alg d L N) (x y : Lam d L N) :
    cf2 (embA N M F) (emb N M x) (emb N M y) = cf2 F x y := by
  rw [cf2, cf2, ← coeff_pushA (emb_injective' hNM) F]
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ### Neighbours -/

theorem emb_add_prj {x : Lam d L N} {a : Zd d} (ha : supNormZ a ≤ 1)
    (hx : 2 * supNorm x + 2 < L ^ N) : emb N M (x + prj a) = emb N M x + prj a := by
  have hz : rep (x + prj a) = rep x + a := by
    symm
    refine eq_rep ?_ ?_
    · rw [prj_add, prj_rep]
    · have := supNormZ_add_le (rep x) a
      rw [supNormZ_rep_eq] at this
      omega
  rw [emb, hz, prj_add]; rfl

theorem emb_add_dir {x : Lam d L N} (e : Dir d) (hx : 2 * supNorm x + 2 < L ^ N) :
    emb N M (x + dirVec e) = emb N M x + dirVec e := by
  rw [← prj_dirZ (n := L ^ N), emb_add_prj hNM (supNormZ_dirZ e) hx, prj_dirZ]

theorem emb_sub_dir {x : Lam d L N} (e : Dir d) (hx : 2 * supNorm x + 2 < L ^ N) :
    emb N M (x - dirVec e) = emb N M x - dirVec e := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← prj_dirZ (n := L ^ N), ← prj_neg,
    emb_add_prj hNM (by rw [supNormZ_neg]; exact supNormZ_dirZ e) hx, prj_neg, prj_dirZ]

theorem embA_grad (e : Dir d) {x : Lam d L N} (hx : 2 * supNorm x + 2 < L ^ N) :
    embA N M (grad e x) = grad e (emb N M x) := by
  rw [grad, grad, map_sub, embA_psi' hNM, embA_psi' hNM, emb_add_dir hNM e hx]

theorem embA_gradbar (e : Dir d) {x : Lam d L N} (hx : 2 * supNorm x + 2 < L ^ N) :
    embA N M (gradbar e x) = gradbar e (emb N M x) := by
  rw [gradbar, gradbar, map_sub, embA_psibar' hNM, embA_psibar' hNM, emb_add_dir hNM e hx]

theorem embA_gradSq {x : Lam d L N} (hx : 2 * supNorm x + 2 < L ^ N) :
    embA N M (gradSq x) = gradSq (emb N M x) := by
  simp only [gradSq, map_smul, map_sum, map_mul, embA_grad hNM _ hx, embA_gradbar hNM _ hx]

omit hNM in
theorem grad_sub_dir (e : Dir d) (x : Lam d L N) :
    grad e (x - dirVec e) = psi x - psi (x - dirVec e) := by
  rw [grad, sub_add_cancel]

omit hNM in
theorem gradbar_sub_dir (e : Dir d) (x : Lam d L N) :
    gradbar e (x - dirVec e) = psibar x - psibar (x - dirVec e) := by
  rw [gradbar, sub_add_cancel]

theorem embA_lapPsi {x : Lam d L N} (hx : 2 * supNorm x + 2 < L ^ N) :
    embA N M (lapPsi x) = lapPsi (emb N M x) := by
  rw [lapPsi, lapPsi, _root_.map_smul, _root_.map_sum]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [grad_sub_dir, grad_sub_dir, _root_.map_sub, _root_.map_sub, embA_psi' hNM, embA_psi' hNM,
    emb_sub_dir hNM _ hx, embA_grad hNM _ hx]

theorem embA_lapPsibar {x : Lam d L N} (hx : 2 * supNorm x + 2 < L ^ N) :
    embA N M (lapPsibar x) = lapPsibar (emb N M x) := by
  rw [lapPsibar, lapPsibar, _root_.map_smul, _root_.map_sum]
  congr 1
  refine sum_congr rfl fun e _ => ?_
  rw [gradbar_sub_dir, gradbar_sub_dir, _root_.map_sub, _root_.map_sub, embA_psibar' hNM,
    embA_psibar' hNM, emb_sub_dir hNM _ hx, embA_gradbar hNM _ hx]

theorem embA_eval (V : Vcoup) {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 2 * supNorm x + 2 < L ^ N) :
    embA N M (V.eval X) = V.eval (X.image (emb N M)) := by
  rw [Vcoup.eval, _root_.map_sum, Vcoup.eval, sum_image fun x _ y _ h => emb_injective' hNM h]
  refine sum_congr rfl fun x hx => ?_
  simp only [_root_.map_add, _root_.map_smul, _root_.map_mul, _root_.map_neg, embA_psi' hNM,
    embA_psibar' hNM,
    embA_gradSq hNM (hX x hx), embA_lapPsi hNM (hX x hx), embA_lapPsibar hNM (hX x hx)]

theorem embE_VE (V : Vcoup) {X : Finset (Lam d L N)} (hX : ∀ x ∈ X, 2 * supNorm x + 2 < L ^ N) :
    embE N M (VE V X) = VE V (X.image (emb N M)) :=
  Subtype.ext (embA_eval hNM V hX)

theorem embA_monoAt (Mo : Mono d) {x : Lam d L N} (hx : 2 * supNorm x + 2 < L ^ N) :
    embA N M (monoAt Mo x) = monoAt Mo (emb N M x) := by
  rw [monoAt, monoAt, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hb := stencil_offsets Mo p hp
  show embA N M ((p.1 : ℂ) • (psi (x + prj p.2.1) * psibar (x + prj p.2.2))) = _
  rw [_root_.map_smul, _root_.map_mul, embA_psi' hNM, embA_psibar' hNM,
    emb_add_prj hNM hb.1 hx, emb_add_prj hNM hb.2 hx]

theorem embA_monoSet (Mo : Mono d) {X : Finset (Lam d L N)}
    (hX : ∀ x ∈ X, 2 * supNorm x + 2 < L ^ N) :
    embA N M (monoSet Mo X) = monoSet Mo (X.image (emb N M)) := by
  rw [monoSet, _root_.map_sum, monoSet, sum_image fun x _ y _ h => emb_injective' hNM h]
  exact sum_congr rfl fun x hx => embA_monoAt hNM Mo (hX x hx)

/-! ### `Loc` -/

section LocEmb

variable {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
  (hRn : ∀ x ∈ R, ∀ y ∈ R, supNorm x + supNorm y + supNorm (x - y) < L ^ N)
include hR hRn

theorem lift_emb {x₀ b x : Lam d L N} (hx₀ : x₀ ∈ R) (hb : b ∈ R) (hx : x ∈ R) :
    lift (emb N M x₀) (emb N M x) = lift b x + lift (emb N M x₀) (emb N M b) := by
  have e1 : rep (emb N M x - emb N M x₀) = rep x - rep x₀ := by
    rw [← emb_sub (hRn x hx x₀ hx₀), rep_emb hNM, rep_sub_of (hRn x hx x₀ hx₀)]
  have e2 : rep (emb N M b - emb N M x₀) = rep b - rep x₀ := by
    rw [← emb_sub (hRn b hb x₀ hx₀), rep_emb hNM, rep_sub_of (hRn b hb x₀ hx₀)]
  have e3 : rep (x - b) = rep x - rep b := rep_sub_of (hRn x hx b hb)
  funext i
  simp only [lift, e1, e2, e3, Pi.add_apply, Pi.sub_apply]
  push_cast; ring

theorem mu_emb (hne : X.Nonempty) {x₀ : Lam d L N} (hx₀ : x₀ ∈ R) (β : Mono d) :
    ∃ Tc : Mono d → ℝ, ∀ G ∈ NX R,
      mu (emb N M x₀) β (embA N M G) = ∑ β', (Tc β' : ℂ) * mu (base X) β' G := by
  obtain ⟨Tc, hTc⟩ := exists_Qfun_comp LinearMap.id (lift (emb N M x₀) (emb N M (base X))) β
  refine ⟨Tc, fun G hG => ?_⟩
  have hbR := hR.mem (base_mem hne)
  have hG' := embA_mem_NX hNM hG
  have hinj := emb_injective' (d := d) (L := L) hNM
  have h1 : ∀ x y, cf2 G x y *
      (Qpoly β (lift (emb N M x₀) (emb N M x)) (lift (emb N M x₀) (emb N M y)) : ℂ) =
      ∑ β', (Tc β' : ℂ) * (cf2 G x y * (Qpoly β' (lift (base X) x) (lift (base X) y) : ℂ)) := by
    intro x y
    by_cases hx : x ∈ R
    · by_cases hy : y ∈ R
      · rw [lift_emb hNM hR hRn hx₀ hbR hx, lift_emb hNM hR hRn hx₀ hbR hy]
        have := hTc (lift (base X) x) (lift (base X) y)
        simp only [LinearMap.id_apply] at this
        rw [this]
        push_cast
        rw [Finset.mul_sum]
        refine sum_congr rfl fun β' _ => by ring
      · simp [cf2_eq_zero_right hG x hy]
    · simp [cf2_eq_zero_left hG hx y]
  have hsum : mu (emb N M x₀) β (embA N M G) = ∑ x, ∑ y, cf2 G x y *
      (Qpoly β (lift (emb N M x₀) (emb N M x)) (lift (emb N M x₀) (emb N M y)) : ℂ) := by
    rw [mu]
    refine Eq.symm (Fintype.sum_of_injective (emb N M) hinj _ _ (fun x' hx' => ?_) (fun x => ?_))
    · refine sum_eq_zero fun y' _ => ?_
      rw [cf2_eq_zero_left hG' (fun ⟨x, _, e⟩ => hx' ⟨x, e⟩), zero_mul]
    · refine Fintype.sum_of_injective (emb N M) hinj _ _ (fun y' hy' => ?_) (fun y => ?_)
      · rw [cf2_eq_zero_right hG' _ (fun ⟨y, _, e⟩ => hy' ⟨y, e⟩), zero_mul]
      · rw [cf2_embA hNM]
  rw [hsum]
  simp only [h1, mu, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  exact Finset.sum_comm

theorem patch_emb (hne : X.Nonempty) : Patch (X.image (emb N M)) := by
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
  obtain ⟨y, hy, hy'⟩ := mem_image.1 (base_mem (hne.image (emb N M)))
  rw [← hy', supNorm_emb_sub hNM (hRn x (hR.mem hx) y (hR.mem hy))]
  have := hR.diam x (hR.mem hx) y (hR.mem hy)
  have := pow_le_pow_NM (L := L) hNM
  omega

/-- **`Loc` commutes with `emb`** (the analogue of `LocXY_aut`). -/
theorem LocXY_emb (hne : X.Nonempty) (hXn : ∀ x ∈ X, 2 * supNorm x + 2 < L ^ N)
    (Y : Finset (Lam d L N))
    (hY : ∀ y ∈ Y, 2 * supNorm y + 2 < L ^ N) (F : Alg d L N) (hF : F ∈ NX R) :
    embA N M (LocXY X Y F) = LocXY (X.image (emb N M)) (Y.image (emb N M)) (embA N M F) := by
  set c := locCoef X F
  have hpX := hR.patch hne
  have hpEX := patch_emb hNM hR hRn hne
  have hneE := hne.image (emb N M)
  have hinj := emb_injective' (d := d) (L := L) hNM
  have key : locCoef (X.image (emb N M)) (embA N M F) = c := by
    obtain ⟨x₁, hx₁, hb'⟩ := mem_image.1 (base_mem hneE)
    have hz : (locCoef (X.image (emb N M)) (embA N M F) - c) ᵥ* Amat (X.image (emb N M)) = 0 := by
      funext β
      obtain ⟨Tc, hTc⟩ := mu_emb hNM hR hRn hne (hR.mem hx₁) β
      have hLX : LocX X F ∈ NX R := LocXY_mem_of hR.nbr F
      have e1 : ((locCoef (X.image (emb N M)) (embA N M F) - c) ᵥ* Amat (X.image (emb N M))) β =
          mu (base (X.image (emb N M))) β (LocX (X.image (emb N M)) (embA N M F)) -
            mu (base (X.image (emb N M))) β (embA N M (LocX X F)) := by
        rw [LocX, LocXY, LocX, LocXY, _root_.map_add, _root_.map_smul, _root_.map_one,
          _root_.map_sum]
        simp only [_root_.map_smul, embA_monoSet hNM _ hXn, mu_add, mu_smul, mu_one, mul_zero,
          zero_add, mu_monoSet_vecMul]
        simp only [Pi.sub_apply, vecMul, dotProduct, Loc.Amat, sub_mul, Finset.sum_sub_distrib]
        rfl
      rw [e1, mu_LocX hpEX hneE, ← hb', hTc _ hF, hTc _ hLX]
      simp only [mu_LocX hpX hne, sub_self, Pi.zero_apply]
    have := (vecMul_injective_iff_isUnit.2 (Amat_isUnit hpEX hneE))
      (show (locCoef (X.image (emb N M)) (embA N M F) - c) ᵥ* Amat (X.image (emb N M)) =
        0 ᵥ* Amat (X.image (emb N M)) by rw [hz, zero_vecMul])
    exact sub_eq_zero.1 this
  rw [LocXY, _root_.map_add, _root_.map_smul, _root_.map_one, _root_.map_sum, LocXY, key,
    ε_embA hNM, card_image_emb hNM, card_image_emb hNM]
  simp only [_root_.map_smul, embA_monoSet hNM _ hY]
  rfl

end LocEmb

/-! ### `𝔼_C` -/

theorem image_sumMap_NXd (R : Set (Lam d L N)) :
    Sum.map (emb N M) (emb N M) '' (Sum.inl '' R ∪ Sum.inr '' R) =
      (Sum.inl '' (emb N M '' R) ∪ Sum.inr '' (emb N M '' R) : Set (Lam d L M ⊕ Lam d L M)) := by
  rw [Set.image_union, Set.image_image, Set.image_image, Set.image_image, Set.image_image]
  rfl

/-- **`𝔼_C` commutes with `emb`** for elements supported where the covariances agree. -/
theorem EC_emb {C : Matrix (Lam d L N) (Lam d L N) ℝ} {C' : Matrix (Lam d L M) (Lam d L M) ℝ}
    {R : Set (Lam d L N)} (hC : ∀ x ∈ R, ∀ y ∈ R, C' (emb N M x) (emb N M y) = C x y)
    {F : Alg2 d L N} (hF : F ∈ NX2 R) : EC C' (embA2 N M F) = embA N M (EC C F) := by
  classical
  have hinj := emb_injective' (d := d) (L := L) hNM
  have hF' : embA2 N M F ∈ NXd (emb N M '' R) := by
    have := pushA_mem_NX (sumMap_injective hinj) hF
    rwa [image_sumMap_NXd hNM] at this
  rw [EC_restr C (X := R) hF, EC_restr C' hF', embA_eq]
  refine EC_pushA hinj (fun x y => ?_) (fun x' y' h => ?_) F
  · simp only [restr, hinj.mem_set_image]
    split_ifs with h1
    · exact hC x h1.1 y h1.2
    · rfl
  · simp only [restr]
    rw [if_neg]
    rintro ⟨⟨x, -, rfl⟩, ⟨y, -, rfl⟩⟩
    rcases h with h | h
    · exact h x rfl
    · exact h y rfl

theorem ECE_emb {C : Matrix (Lam d L N) (Lam d L N) ℝ} {C' : Matrix (Lam d L M) (Lam d L M) ℝ}
    {R : Set (Lam d L N)} (hC : ∀ x ∈ R, ∀ y ∈ R, C' (emb N M x) (emb N M y) = C x y)
    {F : EvR (Lam d L N ⊕ Lam d L N)} (hF : (F : Alg2 d L N) ∈ NX2 R) :
    embE N M (ECE C F) = ECE C' (embE2 N M F) :=
  Subtype.ext (EC_emb hNM hC hF).symm

/-! ### Covariances -/

/-- The covariance `C_{j+1}` of `sec:frd` is compatible with `emb` for pairs of points not too
far from the origin. -/
theorem Cfrd_emb_of {j : ℕ} (hj : j + 1 < N) {msq : ℝ} (hmsq : 0 ≤ msq) (hd : 1 ≤ d)
    {x y : Lam d L N} (h : supNorm x + supNorm y + supNorm (x - y) < L ^ N) :
    Cfrd d L M msq j (emb N M x) (emb N M y) = Cfrd d L N msq j x y := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  rcases Nat.lt_or_ge 1 L with hL2 | hL2
  · have hN : (L : ℝ) ^ (j + 1) < ((L ^ N : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_lt_pow_right hL2 hj
    have hM : (L : ℝ) ^ (j + 1) < ((L ^ M : ℕ) : ℝ) :=
      hN.trans_le (by exact_mod_cast pow_le_pow_NM hNM)
    rw [Cfrd, Cfrd, Cj_eq_Zd stdPt hmsq hd hL0 (j + 1) hM, Cj_eq_Zd stdPt hmsq hd hL0 (j + 1) hN,
      ← emb_sub h, rep_emb hNM]
  · have hL : L = 1 := le_antisymm hL2 hL1
    have key : ∀ (n n' : ℕ) [NeZero n] [NeZero n'], n = n' → ∀ u v : Torus d n,
        Cj stdPt msq (L : ℝ) (j + 1) (prj (rep u) : Torus d n') (prj (rep v)) =
          Cj stdPt msq (L : ℝ) (j + 1) u v := by
      intro n n' _ _ e u v
      subst e
      rw [prj_rep, prj_rep]
    exact key (L ^ N) (L ^ M) (by rw [hL, one_pow, one_pow]) x y

end

end Flow
