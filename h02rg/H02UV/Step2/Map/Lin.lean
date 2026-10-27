import Step2.Map.Second
import Step2.Map.Norm

/-!
# The linear part of `K_{j+1}` at `V = 𝒲 = 0`

For the coordinates `(0, 0, s K)`,

  `K_{j+1}(0, 0, s K)(U) = s 𝓛(K)(U) + O(s²)`     (`Knext2_lin`),

for nonempty `U`, with the explicit linear map `𝓛 = Llin2`:
`𝓛(K)(U) = ∑_{X ∈ 𝒞_j, \bar X = U} 𝔼θ[K(X) - ∑_B J(B, X) - 1_{X = B} Q(B)]
  + ∑_{(B,X): \overline{B^□} = U} 𝔼θ J(B, X)`.
At `V = 𝒲 = 0`: `I_j(B) = 1`, and `I_{j+1}(B) = 1 + s 𝔼θ Q(B) + O(s²)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Linearity in `K` -/

section LinK

variable (j : ℕ)

theorem Loc2E_add (X Y : Finset (Lam d L N)) (F G : EvR (Lam d L N)) :
    Loc2E X Y (F + G) = Loc2E X Y F + Loc2E X Y G := by
  refine Subtype.ext ?_
  simp only [coe_Loc2E, Loc2sXY, Subalgebra.coe_add]
  have h1 := congrArg Subtype.val (LocE_add X Y F G)
  simp only [coe_LocE, Subalgebra.coe_add] at h1
  rw [h1]
  have h2 : Loc4sXY X Y ((F : Alg d L N) + (G : Alg d L N)) =
      Loc4sXY X Y (F : Alg d L N) + Loc4sXY X Y (G : Alg d L N) := by
    simp only [Loc4sXY, mu4_add, add_div, add_smul, sum_add_distrib]
  rw [h2]; abel

theorem Q2_smul (s : ℂ) (K : Act d L N) (b : Fin d → ℕ) : Q2 j (s • K) b = s • Q2 j K b := by
  unfold Q2
  split_ifs
  · rw [smul_sum]
    exact sum_congr rfl fun X _ => by rw [Pi.smul_apply, Loc2E_smul]
  · rw [smul_zero]

theorem J2_smul (s : ℂ) (K : Act d L N) (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    J2 j (s • K) b X = s • J2 j K b X := by
  unfold J2
  split_ifs
  · rw [smul_neg, smul_sum]
    exact congrArg _ (sum_congr rfl fun Y _ => by rw [Pi.smul_apply, Loc2E_smul])
  · rw [Pi.smul_apply, Loc2E_smul]
  · rw [smul_zero]

theorem Kext_smul (s : ℂ) (K : Act d L N) (Z : Finset (Lam d L N)) :
    Kext j (s • K) Z = s ^ (Comp j Z).card • Kext j K Z := by
  simp only [Kext, Pi.smul_apply]
  exact (Finset.smul_prod _ s _).symm

end LinK

/-! ### The map at `V = 𝒲 = 0` -/

section Zero

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : Act d L N)

theorem FCE_zero_left (B : EvR (Lam d L N)) : FCE C 0 B = 0 := by
  simpa using FCE_smul_left C 0 0 B

theorem Vpr_zero (b : Fin d → ℕ) : Vpr C (0 : Fam d L N) b = 0 := EthE_zero C

theorem Sb_zero (b : Fin d → ℕ) : Sb j C (0 : Fam d L N) 0 b = 0 := by
  simp [Sb, Vpr_zero, FCE_zero_left, EthE_zero]

theorem LS_zero (b : Fin d → ℕ) : LS j C (0 : Fam d L N) 0 b = 0 := by
  simp [LS, SX, Sb_zero, Loc2E_zero]

theorem Wp_zero (b : Fin d → ℕ) : Wp j C (0 : Fam d L N) 0 b = 0 := by
  simp [Wp, Sb_zero, LS_zero]

theorem uVp_zeroVW (s : ℂ) (b : Fin d → ℕ) :
    uVp j C (0 : Fam d L N) 0 (s • K) b = -(s • EthE C (Q2 j K b)) := by
  simp [uVp, Vpr_zero, LS_zero, Q2_smul, EthE_smul]

theorem Ib_zero (b : Fin d → ℕ) : Ib (0 : Fam d L N) 0 b = 1 := by
  simp [Ib, gexp, IsNilpotent.exp_zero]

/-- `I_{j+1}(B) = 1 + s 𝔼θ Q(B) + O(s²)` at `V = 𝒲 = 0`. -/
theorem Ip_lin (b : Fin d → ℕ) :
    ExpE1 (fun s : ℂ => Ip j C (0 : Fam d L N) 0 (s • K) b) 1 (EthE C (Q2 j K b)) := by
  set F := EthE C (Q2 j K b)
  set c : ℂ := ε (F : Alg d L N)
  have hVp : ∀ s : ℂ, -Vp j C (0 : Fam d L N) 0 (s • K) b = s • (F - algebraMap ℂ _ c) := by
    intro s
    rw [Vp, up, uVp_zeroVW]
    simp only [Subalgebra.coe_neg, map_neg, ε_smulE]
    simp only [smul_eq_alg, map_mul, map_neg, F, c]
    ring
  have hup : ∀ s : ℂ, -up j C (0 : Fam d L N) 0 (s • K) b = s * c := by
    intro s
    rw [up, uVp_zeroVW]
    simp only [Subalgebra.coe_neg, map_neg, ε_smulE, neg_neg, F, c]
  have h1 : ExpE2 (fun s : ℂ => -Vp j C (0 : Fam d L N) 0 (s • K) b) 0 (F - algebraMap ℂ _ c) 0 :=
    (ExpE2.lin _).congr hVp
  have h2 := ExpE2.gexp h1 (fun s => by have := ε_Vp j C 0 0 (s • K) b; simp [this])
  have h3 : ExpS2 (fun s : ℂ => -up j C (0 : Fam d L N) 0 (s • K) b) 0 c 0 :=
    (ExpS2.lin c).congr fun s => by rw [hup]
  have h4 := ExpS2.exp h3
  have h5 := ExpE1.smulS h4 (ExpE1.of_exp2 h2)
  refine (h5.congr fun s => ?_).coeffs (by simp) ?_
  · simp [Ip, Wp_zero]
  · simp [smul_eq_alg]

/-- `δI(B) = -s 𝔼θ Q(B) + O(s²)` at `V = 𝒲 = 0`. -/
theorem dI_lin (b : Fin d → ℕ) :
    ExpE1 (fun s : ℂ => gdI (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) b) 0
      (-inclE (EthE C (Q2 j K b))) := by
  have := ((ExpE1.const (thetaE (1 : EvR (Lam d L N)))).sub ((Ip_lin j C K b).mapA inclE))
  refine (this.congr fun s => by simp [gdI, Ib_zero]).coeffs (by simp) (by simp)

theorem dIPow_ord (Y : Finset (Lam d L N)) :
    OrdE (nb j Y) (fun s : ℂ => gdIPow j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) Y) :=
  OrdE.prod (blocks j Y) fun b _ => (dI_lin j C K b).ord1

theorem thetaKext_ord (Z : Finset (Lam d L N)) :
    OrdE (Comp j Z).card (fun s : ℂ => thetaE (Kext j (s • K) Z)) := by
  refine ⟨fun _ => thetaE (Kext j K Z), HolE.const _, fun s => ?_⟩
  beta_reduce
  rw [Kext_smul, map_smul]

/-- The first-order part of `(δI)^W`: `-𝔼θQ(B)` if `W = B` is a block, `0` otherwise. -/
def dIlin (W : Finset (Lam d L N)) : EvR (Lam d L N ⊕ Lam d L N) :=
  if nb j W = 1 then ∑ b ∈ blocks j W, -inclE (EthE C (Q2 j K b)) else 0

theorem dIPow_lin {W : Finset (Lam d L N)} (hW : W.Nonempty) :
    ExpE1 (fun s : ℂ => gdIPow j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) W) 0
      (dIlin j C K W) := by
  by_cases h1 : nb j W = 1
  · obtain ⟨b, hb⟩ := card_eq_one.1 h1
    refine ((dI_lin j C K b).congr fun s => by rw [gdIPow, hb, prod_singleton]).coeffs rfl ?_
    rw [dIlin, if_pos h1, hb, sum_singleton]
  · have hne : nb j W ≠ 0 := by
      intro h
      rw [nb, card_eq_zero] at h
      obtain ⟨x, hx⟩ := hW
      exact notMem_empty _ (h ▸ blk_mem_blocks hx)
    refine (ExpE1.of_ord2 (OrdE.mono (by omega) (dIPow_ord j C K W))).coeffs rfl ?_
    rw [dIlin, if_neg h1]

theorem gKtil_lin {W : Finset (Lam d L N)} (hW : IsConn j W) :
    ExpE1 (fun s : ℂ => gKtil j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K) W) 0
      (thetaE (K W) + dIlin j C K W) := by
  have hWp := hW.1
  have hWne : W.Nonempty := hW.2.1
  have hWm : W ∈ Pj j W := mem_Pj.2 ⟨subset_rfl, hWp⟩
  have h0ne : (∅ : Finset (Lam d L N)) ≠ W := fun h => not_nonempty_empty (h ▸ hWne)
  have h0m : (∅ : Finset (Lam d L N)) ∈ (Pj j W).erase W :=
    mem_erase.2 ⟨h0ne, mem_Pj.2 ⟨empty_subset _, isPolymer_empty j⟩⟩
  have e : ∀ s : ℂ, gKtil j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K) W =
      gdIPow j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) W +
        (thetaE (Kext j (s • K) W) +
          ∑ Y ∈ ((Pj j W).erase W).erase ∅,
            thetaE (Kext j (s • K) (W \ Y)) * gdIPow j (Ib 0 0) (Ip j C 0 0 (s • K)) Y) := by
    intro s
    rw [gKtil, ← add_sum_erase _ _ hWm, ← add_sum_erase _ _ h0m, sdiff_self,
      show (⊥ : Finset (Lam d L N)) = ∅ from rfl, Kext_empty, map_one, one_mul, sdiff_empty,
      gdIPow_empty, mul_one]
  have hK : ExpE1 (fun s : ℂ => thetaE (Kext j (s • K) W)) 0 (thetaE (K W)) := by
    refine (ExpE1.lin (thetaE (K W))).congr fun s => ?_
    rw [Kext_smul, Kext, comp_of_isConn hW, card_singleton, pow_one, prod_singleton, map_smul]
  have hrest : OrdE 2 (fun s : ℂ => ∑ Y ∈ ((Pj j W).erase W).erase ∅,
      thetaE (Kext j (s • K) (W \ Y)) * gdIPow j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) Y) := by
    refine OrdE.sum _ fun Y hY => ?_
    have hY1 : Y ≠ ∅ := ne_of_mem_erase hY
    have hY2 : Y ≠ W := ne_of_mem_erase (mem_of_mem_erase hY)
    obtain ⟨hYW, hYp⟩ := mem_Pj.1 (mem_of_mem_erase (mem_of_mem_erase hY))
    have hc : 1 ≤ (Comp j (W \ Y)).card := by
      have hne : W \ Y ≠ ∅ := fun h => hY2 (subset_antisymm hYW (sdiff_eq_empty_iff_subset.1 h))
      have := (comp_card_eq_zero_iff (IsPolymer.sdiff hWp hYp)).not.2 hne
      omega
    have hn : 1 ≤ nb j Y := by
      by_contra h; push Not at h
      have h0 : blocks j Y = ∅ := card_eq_zero.1 (by rw [← nb]; omega)
      exact hY1 (image_eq_empty.1 h0)
    exact OrdE.mono (by omega) ((OrdE.mono hc (thetaKext_ord j K (W \ Y))).mul
      (OrdE.mono hn (dIPow_ord j C K Y)))
  exact (((dIPow_lin j C K hWne).add (hK.add (ExpE1.of_ord2 hrest))).congr e).coeffs
    (by simp) (by simp; abel)

theorem thetaJ_lin (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    ExpE1 (fun s : ℂ => thetaE (J2 j (s • K) b X)) 0 (thetaE (J2 j K b X)) :=
  (ExpE1.lin _).congr fun s => by rw [J2_smul, map_smul]

theorem gKchkC_lin {W : Finset (Lam d L N)} (hW : IsConn j W) :
    ExpE1 (fun s : ℂ => gKchkC j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K)
        (J2 j (s • K)) W) 0
      (thetaE (K W) + dIlin j C K W - ∑ b ∈ blocks j W, thetaE (J2 j K b W)) :=
  ((gKtil_lin j C K hW).sub (ExpE1.sum _ fun b _ => thetaJ_lin j K b W)).coeffs (by simp) rfl

theorem gKchk_ord {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    OrdE (Comp j X).card (fun s : ℂ => gKchk j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K)
      (J2 j (s • K)) X) :=
  OrdE.prod (Comp j X) fun c hc => (gKchkC_lin j C K (isConn_of_mem_comp hX hc)).ord1

theorem Jprod2_ord (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    OrdE 𝒳.card (fun s : ℂ => ∏ p ∈ 𝒳, thetaE (J2 j (s • K) p.1 p.2)) :=
  OrdE.prod 𝒳 fun p _ => (thetaJ_lin j K p.1 p.2).ord1

/-- **The linear part** `𝓛(K)(U)` of `K_{j+1}` at `V = 𝒲 = 0`. -/
def Llin2 (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ECCE C (thetaE (K g.2) + dIlin j C K g.2 - ∑ b ∈ blocks j g.2, thetaE (J2 j K b g.2)) +
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ECCE C (∏ p ∈ g.1, thetaE (J2 j K p.1 p.2))

theorem Gset_nonempty_part {U : Finset (Lam d L N)} (hU : U.Nonempty)
    {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)} (hg : g ∈ Gset j U) :
    ¬ (g.1 = ∅ ∧ g.2 = ∅) := by
  rintro ⟨h1, h2⟩
  have := (mem_Gset.1 hg).2.2.2.2.2
  rw [h1, h2, Bbox_empty, union_empty, clo_empty] at this
  rw [← this] at hU
  exact not_nonempty_empty hU

theorem uX_lin (U : Finset (Lam d L N)) :
    ∃ a₁ a₂, ExpS2 (fun s : ℂ => Complex.exp (uX j C (0 : Fam d L N) 0 (s • K) U)) 1 a₁ a₂ := by
  have h : ExpS2 (fun s : ℂ => uX j C (0 : Fam d L N) 0 (s • K) U)
      (∑ b ∈ blocks j U, (0 : ℂ)) (∑ b ∈ blocks j U, -ε (EthE C (Q2 j K b) : Alg d L N))
      (∑ b ∈ blocks j U, (0 : ℂ)) := by
    refine (ExpS2.sum _ fun b _ => ?_).congr fun s => rfl
    refine OrdS.congr (OrdS.zero 3) fun s => ?_
    beta_reduce
    rw [up, uVp_zeroVW]
    simp only [Subalgebra.coe_neg, map_neg, ε_smulE]
    ring
  simp only [sum_const_zero] at h
  exact ⟨_, _, ExpS2.exp h⟩

/-- **`K_{j+1}(0, 0, s K)(U) = s 𝓛(K)(U) + O(s²)`** for nonempty `U`. -/
theorem Knext2_lin {U : Finset (Lam d L N)} (hU : U.Nonempty) :
    ExpE1 (fun s : ℂ => Knext2 j C (0 : Fam d L N) 0 (s • K) U) 0 (Llin2 j C K U) := by
  classical
  -- the summands
  set T : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N) → ℂ →
      EvR (Lam d L N) := fun g s =>
    bpow j (Ip j C (0 : Fam d L N) 0 (s • K)) (U \ (g.2 ∪ Xcal g.1)) *
      ECCE C (gKchk j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K) (J2 j (s • K)) g.2 *
        ∏ p ∈ g.1, thetaE (J2 j (s • K) p.1 p.2)) with hT
  have hpref : ∀ Z : Finset (Lam d L N), ∃ P₁, ExpE1 (fun s : ℂ =>
      bpow j (Ip j C (0 : Fam d L N) 0 (s • K)) Z) 1 P₁ :=
    fun Z => ExpE1.prod_one (blocks j Z) fun b _ => ⟨_, Ip_lin j C K b⟩
  have hA : ∀ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ExpE1 (T g) 0 (ECCE C (thetaE (K g.2) + dIlin j C K g.2 -
        ∑ b ∈ blocks j g.2, thetaE (J2 j K b g.2))) := by
    intro g hg
    obtain ⟨-, h1, hc⟩ := mem_filter.1 hg
    obtain ⟨P₁, hP⟩ := hpref (U \ (g.2 ∪ Xcal g.1))
    have hE := ((gKchkC_lin j C K hc).map (ECCE C)).congr (g := fun s : ℂ =>
      ECCE C (gKchk j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K) (J2 j (s • K)) g.2 *
        ∏ p ∈ g.1, thetaE (J2 j (s • K) p.1 p.2))) fun s => by
      rw [h1, prod_empty, mul_one, gKchk, comp_of_isConn hc, prod_singleton]
    exact (hP.mul hE).coeffs (by simp) (by simp)
  have hB : ∀ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ExpE1 (T g) 0 (ECCE C (∏ p ∈ g.1, thetaE (J2 j K p.1 p.2))) := by
    intro g hg
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hg
    obtain ⟨p, hp⟩ := card_eq_one.1 h1
    obtain ⟨P₁, hP⟩ := hpref (U \ (g.2 ∪ Xcal g.1))
    have hE := ((thetaJ_lin j K p.1 p.2).map (ECCE C)).congr (g := fun s : ℂ =>
      ECCE C (gKchk j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K) (J2 j (s • K)) g.2 *
        ∏ p ∈ g.1, thetaE (J2 j (s • K) p.1 p.2))) fun s => by
      rw [h2, hp, gKchk, comp_empty, prod_empty, one_mul, prod_singleton]
    refine (hP.mul hE).coeffs (by simp) ?_
    rw [hp, prod_singleton]; simp
  have hR : ∀ g ∈ ((Gset j U).filter (fun g => ¬ (g.1 = ∅ ∧ IsConn j g.2))).filter
      (fun g => ¬ (g.1.card = 1 ∧ g.2 = ∅)), ExpE1 (T g) 0 0 := by
    intro g hg
    obtain ⟨hg', hnB⟩ := mem_filter.1 hg
    obtain ⟨hgG, hnA⟩ := mem_filter.1 hg'
    obtain ⟨f1, -, -, -⟩ := Gset_facts hgG
    have hnE := Gset_nonempty_part j hU hgG
    have hm : 2 ≤ g.1.card + (Comp j g.2).card := by
      by_cases h1 : g.1 = ∅
      · have h2 : g.2 ≠ ∅ := fun h2 => hnE ⟨h1, h2⟩
        have hc0 : (Comp j g.2).card ≠ 0 := fun h => h2 ((comp_card_eq_zero_iff f1).1 h)
        have hc1 : (Comp j g.2).card ≠ 1 := fun h => hnA ⟨h1, (comp_card_eq_one_iff f1).1 h⟩
        rw [h1, card_empty]; omega
      · have hc1 : 1 ≤ g.1.card := card_pos.2 (nonempty_iff_ne_empty.2 h1)
        by_cases h1' : g.1.card = 1
        · have h2 : g.2 ≠ ∅ := fun h2 => hnB ⟨h1', h2⟩
          have hc0 : (Comp j g.2).card ≠ 0 := fun h => h2 ((comp_card_eq_zero_iff f1).1 h)
          omega
        · omega
    have hO : OrdE 2 (fun s : ℂ =>
        ECCE C (gKchk j (Ib (0 : Fam d L N) 0) (Ip j C 0 0 (s • K)) (s • K) (J2 j (s • K)) g.2 *
          ∏ p ∈ g.1, thetaE (J2 j (s • K) p.1 p.2))) :=
      OrdE.map (OrdE.mono (by omega) ((gKchk_ord j C K f1).mul (Jprod2_ord j K g.1))) (ECCE C)
    exact ExpE1.of_ord2 (OrdE.congr ((OrdE.of_hol (ExpE1.hol (hpref _).choose_spec)).mul hO
      |>.mono (by norm_num)) fun s => rfl) |>.congr fun s => rfl
  -- assemble
  have hsum : ExpE1 (fun s => ∑ g ∈ Gset j U, T g s) 0 (Llin2 j C K U) := by
    have e : ∀ s, ∑ g ∈ Gset j U, T g s =
        ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2), T g s +
          (∑ g ∈ ((Gset j U).filter (fun g => ¬ (g.1 = ∅ ∧ IsConn j g.2))).filter
              (fun g => g.1.card = 1 ∧ g.2 = ∅), T g s +
            ∑ g ∈ ((Gset j U).filter (fun g => ¬ (g.1 = ∅ ∧ IsConn j g.2))).filter
              (fun g => ¬ (g.1.card = 1 ∧ g.2 = ∅)), T g s) := by
      intro s
      rw [sum_filter_add_sum_filter_not, sum_filter_add_sum_filter_not]
    have hBf : ((Gset j U).filter (fun g => ¬ (g.1 = ∅ ∧ IsConn j g.2))).filter
        (fun g => g.1.card = 1 ∧ g.2 = ∅) = (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅) := by
      ext g
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h1, h2⟩
        refine ⟨⟨h, fun h' => ?_⟩, h1, h2⟩
        rw [h'.1, card_empty] at h1; exact absurd h1 (by decide)
    have := (ExpE1.sum _ hA).add ((ExpE1.sum _ (hBf ▸ hB)).add (ExpE1.sum _ hR))
    refine (this.congr e).coeffs (by simp) ?_
    rw [Llin2, sum_const_zero, add_zero, hBf]
  obtain ⟨a₁, a₂, hu⟩ := uX_lin j C K U
  have := ExpE1.smulS hu hsum
  refine (this.congr fun s => ?_).coeffs (by simp) (by simp)
  rw [Knext2, gKnext]

end Zero

end

end Step2
