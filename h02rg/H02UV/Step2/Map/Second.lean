import Step2.Map.Defs
import Step2.Map.Exp
import Step.Decomp
import Step.DerivAux

/-!
# The second-order part of `K_{j+1}` (`h02uv-outline.tex`, `e:K2`)

For `K_j = 0` and the scaled coordinates `(t V, t² 𝒲, 0)`,

  `K_{j+1}(t V, t² 𝒲, 0)(U) = t² K^{(2)}(U) + O(t³)`     (`Knext2_expansion`),

for every nonempty `U`, with `K^{(2)}` given by `e:K2` (`Step2.K2`). In particular the first-order
part vanishes and the `𝒲`-dependence cancels at second order.

The proof:
* for `K = 0`, `Q = J = 0` and `K_{j+1}(U) = e^{u(U)} ∑_{\bar X = U} I_{j+1}^{U∖X} 𝔼[(δI)^X]`
  (`gKnext_zero`);
* `I_j(B) = 1 - t V(B) + t² (V(B)²/2 + 𝒲(B)) + O(t³)` and, because
  `-V^{(2)}_{j+1}(B) + 𝒲_{j+1}(B) = S(B)` exactly,
  `I_{j+1}(B) = 1 - t V'_B + t² (V'_B²/2 + S(B)) + O(t³)` (`Ip_exp`);
* `𝔼 δI(B) = -½ t² F(V'_B, V'(Λ ∖ B)) + O(t³)` and
  `𝔼 [δI(B) δI(B')] = t² F(V'_B, V'_{B'}) + O(t³)`, by `𝔼θ(AB) = 𝔼θA 𝔼θB + F(𝔼θA, 𝔼θB)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Linearity -/

section Lin

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)

theorem EthE_smul (c : ℂ) (F : EvR Λ) : EthE C (c • F) = c • EthE C F := by
  simp [EthE, map_smul]

theorem EthE_add (F G : EvR Λ) : EthE C (F + G) = EthE C F + EthE C G := by
  simp [EthE, map_add]

theorem EthE_sub (F G : EvR Λ) : EthE C (F - G) = EthE C F - EthE C G := by
  simp [EthE, map_sub]

theorem EthE_zero : EthE C (0 : EvR Λ) = 0 := by simp [EthE]

theorem FCE_smul_left (c : ℂ) (A B : EvR Λ) : FCE C (c • A) B = c • FCE C A B :=
  Subtype.ext (by simp [FC_smul_left])

theorem FCE_smul_right (c : ℂ) (A B : EvR Λ) : FCE C A (c • B) = c • FCE C A B :=
  Subtype.ext (by simp [FC_smul_right])

theorem FCE_sub_right (A B B' : EvR Λ) : FCE C A (B - B') = FCE C A B - FCE C A B' := by
  refine Subtype.ext ?_
  simp only [coe_FCE, Subalgebra.coe_sub]
  rw [sub_eq_add_neg, FC_add_right, show -(B' : Grassmann.N Λ) = (-1 : ℂ) • (B' : Grassmann.N Λ)
    by simp, FC_smul_right]
  simp [sub_eq_add_neg]

theorem ECCE_thetaE (F : EvR Λ) : ECCE C (thetaE F) = EthE C F := rfl

end Lin

theorem Loc2E_smul (X Y : Finset (Lam d L N)) (c : ℂ) (F : EvR (Lam d L N)) :
    Loc2E X Y (c • F) = c • Loc2E X Y F := by
  refine Subtype.ext ?_
  simp only [coe_Loc2E, Loc2sXY, SetLike.val_smul, smul_add]
  congr 1
  · exact congrArg Subtype.val (LocE_smul X Y c F)
  · simp only [Loc4sXY, mu4_smul, smul_sum, smul_smul]
    refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
    congr 1; ring

theorem Loc2E_zero (X Y : Finset (Lam d L N)) : Loc2E X Y 0 = 0 := by
  simpa using Loc2E_smul X Y 0 0

/-! ### `K = 0` -/

section Zero

variable (j : ℕ)

theorem Q2_zero (b : Fin d → ℕ) : Q2 j (0 : Act d L N) b = 0 := by
  unfold Q2
  split_ifs
  · exact sum_eq_zero fun X _ => by simpa using Loc2E_zero X (blockSet j b)
  · rfl

theorem J2_zero (b : Fin d → ℕ) (X : Finset (Lam d L N)) : J2 j (0 : Act d L N) b X = 0 := by
  unfold J2
  split_ifs
  · rw [neg_eq_zero]
    exact sum_eq_zero fun Y _ => by simpa using Loc2E_zero Y (blockSet j b)
  · simpa using Loc2E_zero X (blockSet j b)
  · rfl

theorem Kext_zero {Z : Finset (Lam d L N)} (hZ : Z.Nonempty) : Kext j (0 : Act d L N) Z = 0 := by
  rw [Kext]
  obtain ⟨x, hx⟩ := hZ
  have : (Comp j Z).Nonempty := ⟨compOf j Z (blk j x), mem_image.2 ⟨_, blk_mem_blocks hx, rfl⟩⟩
  obtain ⟨c, hc⟩ := this
  exact prod_eq_zero hc rfl

variable (Ib Ip : Fam d L N)

theorem gKtil_zero {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    gKtil j Ib Ip 0 W = gdIPow j Ib Ip W := by
  rw [gKtil, sum_eq_single W]
  · rw [sdiff_self, show (⊥ : Finset (Lam d L N)) = ∅ from rfl, Kext_empty, map_one, one_mul]
  · intro Y hY hYW
    have hsub := (mem_Pj.1 hY).1
    have hne : (W \ Y).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h
      exact hYW (subset_antisymm hsub h)
    rw [Kext_zero j hne, map_zero, zero_mul]
  · intro h
    exact absurd (mem_Pj.2 ⟨subset_rfl, hW⟩) h

theorem gdIPow_eq_prod_comp {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    gdIPow j Ib Ip Z = ∏ Y ∈ Comp j Z, gdIPow j Ib Ip Y :=
  eq_prod_comp_of_mul _ (gdIPow_empty j Ib Ip)
    (fun _ _ hA hB h => prod_blocks_union _ hA hB (disjoint_of_not_touch h)) hZ

theorem gKchk_zero {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    gKchk j Ib Ip 0 (J2 j 0) X = gdIPow j Ib Ip X := by
  rw [gKchk, gdIPow_eq_prod_comp j Ib Ip hX]
  refine prod_congr rfl fun c hc => ?_
  have hcp : IsPolymer j c := (isConn_of_mem_comp hX hc).1
  rw [gKchkC, gKtil_zero j Ib Ip hcp]
  simp [J2_zero]

open Classical in
/-- For `K = 0`: `K_{j+1}(U) = ∑_{\bar X = U} I_{j+1}^{U∖X} 𝔼[(δI)^X]` (before normalisation). -/
theorem gKnext_zero (C : Matrix (Lam d L N) (Lam d L N) ℂ) (U : Finset (Lam d L N)) :
    gKnext j C Ib Ip 0 (J2 j 0) U =
      ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U),
        bpow j Ip (U \ X) * ECCE C (gdIPow j Ib Ip X) := by
  rw [gKnext]
  have h1 : ∀ g ∈ Gset j U, g.1 ≠ ∅ →
      bpow j Ip (U \ (g.2 ∪ Xcal g.1)) *
        ECCE C (gKchk j Ib Ip 0 (J2 j 0) g.2 * ∏ p ∈ g.1, thetaE (J2 j 0 p.1 p.2)) = 0 := by
    intro g _ hg
    obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hg
    rw [prod_eq_zero hp (by rw [J2_zero, map_zero]), mul_zero, map_zero, mul_zero]
  rw [← sum_filter_add_sum_filter_not (Gset j U) (fun g => g.1 = ∅),
    sum_eq_zero (s := (Gset j U).filter fun g => ¬ g.1 = ∅) fun g hg =>
      h1 g (mem_filter.1 hg).1 (mem_filter.1 hg).2, add_zero]
  refine sum_nbij' (fun g => g.2) (fun X => (∅, X)) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨hg, h0⟩ := mem_filter.1 hg
    rw [eq_empty_left_of_mem_Gset h0] at hg
    obtain ⟨hp, hc⟩ := mem_Gset_empty.1 hg
    exact mem_filter.2 ⟨mem_Pj.2 ⟨subset_univ _, hp⟩, hc⟩
  · intro X hX
    obtain ⟨hX, hc⟩ := mem_filter.1 hX
    exact mem_filter.2 ⟨mem_Gset_empty.2 ⟨(mem_Pj.1 hX).2, hc⟩, rfl⟩
  · intro g hg
    exact (eq_empty_left_of_mem_Gset (mem_filter.1 hg).2).symm
  · intro X _; rfl
  · intro g hg
    obtain ⟨hg, h0⟩ := mem_filter.1 hg
    rw [eq_empty_left_of_mem_Gset h0] at hg
    obtain ⟨hp, -⟩ := mem_Gset_empty.1 hg
    rw [h0]
    simp only [Xcal_empty, union_empty, prod_empty, mul_one]
    rw [gKchk_zero j Ib Ip hp]

end Zero

/-! ### The scaled coordinates -/

section Scale

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)

/-- `t V`. -/
def Vt (t : ℂ) : Fam d L N := fun b => t • V b

/-- `t² 𝒲`. -/
def Wt (t : ℂ) : Fam d L N := fun b => t ^ 2 • W b

theorem Vpr_scale (t : ℂ) (b : Fin d → ℕ) : Vpr C (Vt V t) b = t • Vpr C V b :=
  EthE_smul C t (V b)

theorem VprL_scale (t : ℂ) : VprL j C (Vt V t) = t • VprL j C V := by
  simp only [VprL, Vpr_scale, smul_sum]

theorem Sb_scale (t : ℂ) (b : Fin d → ℕ) :
    Sb j C (Vt V t) (Wt W t) b = t ^ 2 • Sb j C V W b := by
  simp only [Sb, Vpr_scale, VprL_scale, FCE_smul_left, FCE_smul_right, Wt, EthE_smul, smul_add,
    smul_smul, pow_two]
  congr 1
  congr 1
  ring

theorem SX_scale (t : ℂ) (X : Finset (Lam d L N)) :
    SX j C (Vt V t) (Wt W t) X = t ^ 2 • SX j C V W X := by
  simp only [SX, Sb_scale, smul_sum]

theorem LS_scale (t : ℂ) (b : Fin d → ℕ) :
    LS j C (Vt V t) (Wt W t) b = t ^ 2 • LS j C V W b := by
  simp only [LS, SX_scale, Loc2E_smul]

theorem uVp_scale (t : ℂ) (b : Fin d → ℕ) :
    uVp j C (Vt V t) (Wt W t) 0 b = t • Vpr C V b - t ^ 2 • LS j C V W b := by
  simp only [uVp, Vpr_scale, LS_scale, Q2_zero, EthE_zero, sub_zero]

theorem ε_smulE {Λ : Type*} [DecidableEq Λ] (c : ℂ) (F : EvR Λ) :
    ε ((c • F : EvR Λ) : Grassmann.N Λ) = c * ε (F : Grassmann.N Λ) := by
  simp [map_smul]

theorem up_scale (t : ℂ) (b : Fin d → ℕ) :
    up j C (Vt V t) (Wt W t) 0 b =
      t * ε (Vpr C V b : Alg d L N) - t ^ 2 * ε (LS j C V W b : Alg d L N) := by
  rw [up, uVp_scale, Subalgebra.coe_sub, map_sub, ε_smulE, ε_smulE]

theorem ε_Vp (U W' : Fam d L N) (K : Act d L N) (b : Fin d → ℕ) :
    ε (Vp j C U W' K b : Alg d L N) = 0 := by
  simp [Vp, up]

/-- The first- and second-order parts of `δI(B)`. -/
def D1 (V : Fam d L N) (b : Fin d → ℕ) : EvR (Lam d L N ⊕ Lam d L N) :=
  -thetaE (V b) + inclE (Vpr C V b)

def D2 (V W : Fam d L N) (b : Fin d → ℕ) : EvR (Lam d L N ⊕ Lam d L N) :=
  thetaE ((1 / 2 : ℂ) • V b ^ 2 + W b) - inclE ((1 / 2 : ℂ) • Vpr C V b ^ 2 + Sb j C V W b)

/-! ### Expansions of the block factors -/

variable {V}

theorem Ib_exp (hV : ∀ b, ε (V b : Alg d L N) = 0) (b : Fin d → ℕ) :
    ExpE2 (fun t => Ib (Vt V t) (Wt W t) b) 1 (-V b) ((1 / 2 : ℂ) • V b ^ 2 + W b) := by
  have h1 : ExpE2 (fun t => -(Vt V t b)) 0 (-V b) 0 :=
    (ExpE2.lin (-V b)).congr fun t => by simp [Vt]
  have h2 := ExpE2.gexp h1 (fun t => by simp [Vt, hV b])
  have h3 : ExpE2 (fun t => 1 + Wt W t b) 1 0 (W b) :=
    ((ExpE2.const 1).add (ExpE2.quad (W b))).coeffs (by simp) (by simp) (by simp)
  exact (h2.mul h3).coeffs (by simp) (by simp) (by simp; abel)

theorem Ip_exp (b : Fin d → ℕ) :
    ExpE2 (fun t => Ip j C (Vt V t) (Wt W t) 0 b) 1 (-Vpr C V b)
      ((1 / 2 : ℂ) • Vpr C V b ^ 2 + Sb j C V W b) := by
  set a : ℂ := ε (Vpr C V b : Alg d L N)
  set β : ℂ := ε (LS j C V W b : Alg d L N)
  set V' := Vpr C V b
  set S := LS j C V W b
  have hVp : ∀ t, -Vp j C (Vt V t) (Wt W t) 0 b =
      t • (-(V' - algebraMap ℂ _ a)) + t ^ 2 • (S - algebraMap ℂ _ β) := by
    intro t
    rw [Vp, uVp_scale, up_scale]
    simp only [smul_eq_alg, map_sub, map_mul, map_pow]
    ring
  have h1 : ExpE2 (fun t => -Vp j C (Vt V t) (Wt W t) 0 b) 0 (-(V' - algebraMap ℂ _ a))
      (S - algebraMap ℂ _ β) :=
    ((ExpE2.lin _).add (ExpE2.quad _)).congr hVp |>.coeffs (by simp) (by simp) (by simp)
  have h2 := ExpE2.gexp h1 (fun t => by
    have := ε_Vp j C (Vt V t) (Wt W t) 0 b
    simp [this])
  have h3 : ExpE2 (fun t => 1 + Wp j C (Vt V t) (Wt W t) b) 1 0 (Sb j C V W b - S) :=
    (((ExpE2.const 1).add (ExpE2.quad (Sb j C V W b - S))).congr fun t => by
      simp [Wp, Sb_scale, LS_scale, smul_sub, S]).coeffs (by simp) (by simp) (by simp)
  have h4 : ExpS2 (fun t => -up j C (Vt V t) (Wt W t) 0 b) 0 (-a) β :=
    OrdS.congr (OrdS.zero 3) fun t => by beta_reduce; rw [up_scale]; ring
  have h5 := (ExpS2.exp h4).congr (ψ := fun t => Complex.exp (-up j C (Vt V t) (Wt W t) 0 b))
    fun t => rfl
  have := ExpE2.smulS h5 (h2.mul h3)
  refine (this.congr fun t => rfl).coeffs ?_ ?_ ?_
  · simp
  · simp only [smul_eq_alg, map_neg, map_one, one_mul, mul_one, mul_zero, add_zero]
    ring
  · have hh : algebraMap ℂ (EvR (Lam d L N)) (1 / 2) * 2 = 1 := by
      rw [show (2 : EvR (Lam d L N)) = algebraMap ℂ _ 2 from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    simp only [show ((-a) ^ 2 / 2 : ℂ) = a ^ 2 * (1 / 2) by ring]
    simp only [smul_eq_alg, map_neg, map_one, one_mul, mul_one, mul_zero, add_zero, zero_add,
      map_add, map_pow, map_mul]
    linear_combination (V' * algebraMap ℂ (EvR (Lam d L N)) a -
      algebraMap ℂ (EvR (Lam d L N)) a ^ 2) * hh

theorem dI_exp (hV : ∀ b, ε (V b : Alg d L N) = 0) (b : Fin d → ℕ) :
    ExpE2 (fun t => gdI (Ib (Vt V t) (Wt W t)) (Ip j C (Vt V t) (Wt W t) 0) b) 0
      (D1 C V b) (D2 j C V W b) := by
  have h1 := (Ib_exp W hV b).mapA thetaE
  have h2 := (Ip_exp j C (V := V) W b).mapA inclE
  exact ((h1.sub h2).congr fun t => rfl).coeffs (by simp) (by simp [D1]) (by simp [D2])

theorem ECCE_D1 (b : Fin d → ℕ) : ECCE C (D1 C V b) = 0 := by
  simp [D1, ECCE_thetaE, ECCE_inclE, Vpr]

theorem ECCE_D1_mul (b b' : Fin d → ℕ) :
    ECCE C (D1 C V b * D1 C V b') = FCE C (Vpr C V b) (Vpr C V b') := by
  have e : D1 C V b * D1 C V b' = thetaE (V b * V b') - inclE (Vpr C V b) * thetaE (V b') -
      inclE (Vpr C V b') * thetaE (V b) + inclE (Vpr C V b * Vpr C V b') := by
    simp only [D1, map_mul]; ring
  rw [e, map_add, map_sub, map_sub, ECCE_inclE_mul, ECCE_inclE_mul, ECCE_inclE, ECCE_thetaE,
    ECCE_thetaE, ECCE_thetaE, EthE_mul]
  simp only [Vpr]
  ring

theorem ECCE_D2 (b : Fin d → ℕ) :
    ECCE C (D2 j C V W b) =
      (-(1 / 2 : ℂ)) • FCE C (Vpr C V b) (VprL j C V - Vpr C V b) := by
  rw [D2, map_sub, ECCE_inclE, ECCE_thetaE, EthE_add, EthE_smul]
  simp only [pow_two]
  rw [EthE_mul, Sb, FCE_sub_right]
  simp only [Vpr]
  module

theorem ExpE2.prod_one {I : Type*} [DecidableEq I] [Fintype I] {ι : Type*} (s : Finset ι)
    {f : ι → ℂ → EvR I} (h : ∀ i ∈ s, ∃ F₁ F₂, ExpE2 (f i) 1 F₁ F₂) :
    ∃ F₁ F₂, ExpE2 (fun t => ∏ i ∈ s, f i t) 1 F₁ F₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, (ExpE2.const 1).congr fun t => by simp⟩
  | insert a s ha ih =>
    obtain ⟨F₁, F₂, hF⟩ := h a (mem_insert_self _ _)
    obtain ⟨G₁, G₂, hG⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    refine ⟨_, _, ((hF.mul hG).congr fun t => by rw [prod_insert ha]).coeffs (by simp) rfl rfl⟩

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {V : Fam d L N} (W : Fam d L N)

theorem uX_exp (U : Finset (Lam d L N)) :
    ∃ a₁ a₂, ExpS2 (fun t => Complex.exp (uX j C (Vt V t) (Wt W t) 0 U)) 1 a₁ a₂ := by
  have h : ExpS2 (fun t => uX j C (Vt V t) (Wt W t) 0 U)
      (∑ b ∈ blocks j U, (0 : ℂ))
      (∑ b ∈ blocks j U, ε (Vpr C V b : Alg d L N))
      (∑ b ∈ blocks j U, -ε (LS j C V W b : Alg d L N)) := by
    refine (ExpS2.sum _ fun b _ => ?_).congr fun t => rfl
    exact OrdS.congr (OrdS.zero 3) fun t => by beta_reduce; rw [up_scale]; ring
  rw [sum_const_zero] at h
  exact ⟨_, _, ExpS2.exp h⟩

theorem pref_exp (hV : ∀ b, ε (V b : Alg d L N) = 0) (U X : Finset (Lam d L N)) :
    ∃ P₁ P₂, ExpE2 (fun t => Complex.exp (uX j C (Vt V t) (Wt W t) 0 U) •
      bpow j (Ip j C (Vt V t) (Wt W t) 0) (U \ X)) 1 P₁ P₂ := by
  obtain ⟨a₁, a₂, ha⟩ := uX_exp j C (V := V) W U
  obtain ⟨P₁, P₂, hP⟩ := ExpE2.prod_one (blocks j (U \ X))
    (f := fun b t => Ip j C (Vt V t) (Wt W t) 0 b) fun b _ => ⟨_, _, Ip_exp j C W b⟩
  exact ⟨_, _, ((ExpE2.smulS ha hP).congr fun t => rfl).coeffs (by simp) rfl rfl⟩

theorem E_dIPow_exp (hV : ∀ b, ε (V b : Alg d L N) = 0) {X : Finset (Lam d L N)}
    (hX : X.Nonempty) :
    ExpE2 (fun t => ECCE C (gdIPow j (Ib (Vt V t) (Wt W t)) (Ip j C (Vt V t) (Wt W t) 0) X))
      0 0 (k2 j C V X) := by
  have hb : ∀ b, ExpE2 (fun t => gdI (Ib (Vt V t) (Wt W t)) (Ip j C (Vt V t) (Wt W t) 0) b) 0
      (D1 C V b) (D2 j C V W b) := dI_exp j C W hV
  have hne : nb j X ≠ 0 := by
    intro h
    rw [nb, card_eq_zero] at h
    obtain ⟨x, hx⟩ := hX
    exact notMem_empty _ (h ▸ blk_mem_blocks hx)
  by_cases h1 : nb j X = 1
  · obtain ⟨b, hbX⟩ := card_eq_one.1 h1
    have := (hb b).map (ECCE C)
    refine (this.congr fun t => by rw [gdIPow, hbX, prod_singleton]).coeffs (by simp)
      (ECCE_D1 C b).symm ?_
    rw [k2, if_pos h1, hbX, sum_singleton, ECCE_D2]
  by_cases h2 : nb j X = 2
  · obtain ⟨b, b', hbb', hbX⟩ := card_eq_two.1 h2
    have := ((hb b).mul (hb b')).map (ECCE C)
    refine (this.congr fun t => by rw [gdIPow, hbX, prod_pair hbb']).coeffs (by simp)
      (by simp) ?_
    have e1 : ({b, b'} : Finset (Fin d → ℕ)).erase b = {b'} := by
      ext c; simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hc, hc' | hc'⟩
        · exact absurd hc' hc
        · exact hc'
      · rintro rfl; exact ⟨fun h => hbb' h.symm, Or.inr rfl⟩
    have e2 : ({b, b'} : Finset (Fin d → ℕ)).erase b' = {b} := by
      ext c; simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hc, hc' | hc'⟩
        · exact hc'
        · exact absurd hc' hc
      · rintro rfl; exact ⟨hbb', Or.inl rfl⟩
    rw [k2, if_neg h1, if_pos h2, hbX, sum_pair hbb', e1, e2, sum_singleton, sum_singleton,
      FCE_comm C (Vpr C V b')]
    simp only [mul_zero, zero_mul, add_zero, zero_add, ECCE_D1_mul]
    module
  · have h3 : 3 ≤ nb j X := by omega
    have hO : OrdE 3 (fun t => gdIPow j (Ib (Vt V t) (Wt W t)) (Ip j C (Vt V t) (Wt W t) 0) X) :=
      OrdE.mono h3 (OrdE.prod (blocks j X) fun b _ => (hb b).ord1)
    refine ((ExpE2.of_ord3 hO).map (ECCE C)).coeffs (by simp) (by simp) ?_
    rw [k2, if_neg h1, if_neg h2, map_zero]

/-- **The second-order part of `K_{j+1}`** (`e:K2`): for `K_j = 0` and the coordinates
`(t V, t² 𝒲)`, `K_{j+1}(U) = t² K^{(2)}(U) + O(t³)` for every nonempty `U`. -/
theorem Knext2_expansion (hV : ∀ b, ε (V b : Alg d L N) = 0) {U : Finset (Lam d L N)}
    (hU : U.Nonempty) :
    ExpE2 (fun t => Knext2 j C (Vt V t) (Wt W t) 0 U) 0 0 (K2 j C V U) := by
  classical
  have hterm : ∀ X ∈ (Pj j univ).filter (fun X => clo j X = U),
      ExpE2 (fun t => (Complex.exp (uX j C (Vt V t) (Wt W t) 0 U) •
          bpow j (Ip j C (Vt V t) (Wt W t) 0) (U \ X)) *
        ECCE C (gdIPow j (Ib (Vt V t) (Wt W t)) (Ip j C (Vt V t) (Wt W t) 0) X))
        0 0 (k2 j C V X) := by
    intro X hX
    have hXne : X.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      rw [(mem_filter.1 hX).2.symm, clo_empty] at hU
      exact not_nonempty_empty hU
    obtain ⟨P₁, P₂, hP⟩ := pref_exp j C W hV U X
    exact (hP.mul (E_dIPow_exp j C W hV hXne)).coeffs (by simp) (by simp) (by simp)
  have := ExpE2.sum _ hterm
  refine (this.congr fun t => ?_).coeffs (by simp) (by simp) (by rw [K2])
  rw [Knext2, gKnext_zero, smul_sum]
  refine sum_congr rfl fun X _ => ?_
  rw [smul_mul_assoc]

end Scale

end

end Step2
