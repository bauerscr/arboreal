import Obs2.Map.OrdW
import Obs2.Map.HolO

/-!
# The second-order part of `K_{j+1}` with sources (`Step2.Map.Second` on `OE`)

For `K_j = 0` and the scaled coordinates `(t V, t² 𝒲)` (`VtO`, `WtO`; bulk plus observable
parts), the activity of the map with sources is
`K_{j+1}(U) = t² K^{(2)}(U) + O(t³)` for nonempty `U` (`Knext2O_expansion`), with `K^{(2)} = K2O`
of `Obs2.Map.Map`. Same proof as `Step2.Knext2_expansion`; the observable constant `u^{obs}` is
combined with `V_{j+1}` in the exponential (`oexp_add`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### `K = 0` -/

section Zero

variable (P : ObsPts d L N) (j : ℕ)

theorem Q2O_zero (b : Fin d → ℕ) : Q2O P j (0 : OAct c d L N) b = 0 := by
  unfold Q2O
  split_ifs
  · exact sum_eq_zero fun X _ => by simp
  · rfl

theorem J2O_zero (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    J2O P j (0 : OAct c d L N) b X = 0 := by
  unfold J2O
  split_ifs <;> simp

theorem KextO_zero {Z : Finset (Lam d L N)} (hZ : Z.Nonempty) : KextO j (0 : OAct c d L N) Z = 0 := by
  rw [KextO]
  obtain ⟨x, hx⟩ := hZ
  have : (Comp j Z).Nonempty := ⟨compOf j Z (blk j x), mem_image.2 ⟨_, blk_mem_blocks hx, rfl⟩⟩
  obtain ⟨c, hc⟩ := this
  exact prod_eq_zero hc rfl

variable (Ib Ip : OFam c d L N)

theorem gKtilO_zero {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    gKtilO j Ib Ip 0 W = gdIPowO j Ib Ip W := by
  rw [gKtilO, sum_eq_single W]
  · rw [sdiff_self, show (⊥ : Finset (Lam d L N)) = ∅ from rfl]
    simp [KextO, comp_empty]
  · intro Y hY hYW
    have hsub := (mem_Pj.1 hY).1
    have hne : (W \ Y).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h
      exact hYW (subset_antisymm hsub h)
    rw [KextO_zero j hne, map_zero, zero_mul]
  · intro h
    exact absurd (mem_Pj.2 ⟨subset_rfl, hW⟩) h

theorem gdIPowO_eq_prod_comp {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    gdIPowO j Ib Ip Z = ∏ Y ∈ Comp j Z, gdIPowO j Ib Ip Y :=
  eq_prod_comp_of_mul _ (by simp [gdIPowO, blocks])
    (fun _ _ hA hB h => prod_blocks_union _ hA hB (disjoint_of_not_touch h)) hZ

theorem gKchkO_zero {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    gKchkO j Ib Ip 0 (J2O P j 0) X = gdIPowO j Ib Ip X := by
  rw [gKchkO, gdIPowO_eq_prod_comp j Ib Ip hX]
  refine prod_congr rfl fun c hc => ?_
  have hcp : IsPolymer j c := (isConn_of_mem_comp hX hc).1
  rw [gKchkCO, gKtilO_zero j Ib Ip hcp]
  simp [J2O_zero]

open Classical in
/-- For `K = 0`: `K_{j+1}(U) = ∑_{\bar X = U} I_{j+1}^{U∖X} 𝔼[(δI)^X]` (before normalisation). -/
theorem gKnextO_zero (C : Matrix (Lam d L N) (Lam d L N) ℂ) (U : Finset (Lam d L N)) :
    gKnextO j C Ib Ip 0 (J2O P j 0) U =
      ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U),
        bpowO j Ip (U \ X) * ECCO C (gdIPowO j Ib Ip X) := by
  rw [gKnextO]
  have h1 : ∀ g ∈ Gset j U, g.1 ≠ ∅ →
      bpowO j Ip (U \ (g.2 ∪ Xcal g.1)) *
        ECCO C (gKchkO j Ib Ip 0 (J2O P j 0) g.2 * ∏ p ∈ g.1, thetaO (J2O P j 0 p.1 p.2)) = 0 := by
    intro g _ hg
    obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hg
    rw [prod_eq_zero hp (by rw [J2O_zero, map_zero]), mul_zero, map_zero, mul_zero]
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
    rw [gKchkO_zero P j Ib Ip hp]

end Zero

/-! ### The scaled coordinates -/

section Scale

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : OFam c d L N)

/-- `t V`. -/
def VtO (t : ℂ) : OFam c d L N := fun b => t • V b

/-- `t² 𝒲`. -/
def WtO (t : ℂ) : OFam c d L N := fun b => t ^ 2 • W b

theorem EthO_zero' (F : OE c (Lam d L N)) (hF : F = 0) : EthO C F = 0 := by
  subst hF; show EthOL C 0 = 0; exact map_zero _

theorem VprO_scale (t : ℂ) (b : Fin d → ℕ) : VprO C (VtO V t) b = t • VprO C V b :=
  EthO_smul C t (V b)

theorem VprLO_scale (t : ℂ) : VprLO j C (VtO V t) = t • VprLO j C V := by
  simp only [VprLO, VprO_scale, smul_sum]

theorem SCorO_scale (t : ℂ) (b : Fin d → ℕ) :
    SCorO j C (VtO V t) b = t ^ 2 • SCorO j C V b := by
  simp only [SCorO, VprO_scale, VprLO_scale, map_smul, FCO_smul_left, FCO_smul_right, smul_sub,
    smul_smul, pow_two]
  module

theorem SbO_scale (t : ℂ) (b : Fin d → ℕ) :
    SbO j C (VtO V t) (WtO W t) b = t ^ 2 • SbO j C V W b := by
  simp only [SbO, SFO, SCorO_scale, VprO_scale, VprLO_scale, FCO_smul_left, FCO_smul_right, WtO,
    EthO_smul, smul_add, smul_smul, pow_two]
  congr 2
  ring

theorem SXO_scale (t : ℂ) (X : Finset (Lam d L N)) :
    SXO j C (VtO V t) (WtO W t) X = t ^ 2 • SXO j C V W X := by
  simp only [SXO, SbO_scale, smul_sum]

theorem LSO_scale (t : ℂ) (b : Fin d → ℕ) :
    LSO P j C (VtO V t) (WtO W t) b = t ^ 2 • LSO P j C V W b := by
  simp only [LSO, SXO_scale, map_smul]

theorem uVpO_scale (t : ℂ) (b : Fin d → ℕ) :
    uVpO P j C (VtO V t) (WtO W t) 0 b = t • VprO C V b - t ^ 2 • LSO P j C V W b := by
  rw [uVpO, VprO_scale, LSO_scale, EthO_zero' C _ (Q2O_zero P j b), sub_zero]

theorem eps_e_smul {Λ : Type*} [DecidableEq Λ] (r : ℂ) (F : OE c Λ) :
    ε (((r • F : OE c Λ) : SA c Λ).e) = r * ε ((F : SA c Λ).e) := by
  show ε (r • (F : SA c Λ).e) = _
  rw [map_smul, smul_eq_mul]

theorem upB_scale (t : ℂ) (b : Fin d → ℕ) :
    upB P j C (VtO V t) (WtO W t) 0 b =
      t * ε ((VprO C V b : SA c (Lam d L N)).e) - t ^ 2 * ε ((LSO P j C V W b : SA c (Lam d L N)).e) := by
  rw [upB, uVpO_scale, coe_bulk]
  show ε (((t • VprO C V b - t ^ 2 • LSO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).e) = _
  rw [show (((t • VprO C V b - t ^ 2 • LSO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).e) =
    ((t • VprO C V b : OE c (Lam d L N)) : SA c (Lam d L N)).e -
      ((t ^ 2 • LSO P j C V W b : OE c (Lam d L N)) : SA c (Lam d L N)).e from rfl, map_sub,
    eps_e_smul, eps_e_smul]

theorem upO_scale (t : ℂ) (b : Fin d → ℕ) :
    upO P j C (VtO V t) (WtO W t) 0 b =
      t • πobs (epsO (VprO C V b)) - t ^ 2 • πobs (epsO (LSO P j C V W b)) := by
  rw [upO, uVpO_scale, map_sub, map_smul, map_smul, map_sub, map_smul, map_smul]

/-- The first- and second-order parts of `δI(B)`. -/
def D1O (V : OFam c d L N) (b : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  -thetaO (V b) + inclO (VprO C V b)

def D2O (V W : OFam c d L N) (b : Fin d → ℕ) : OE c (Lam d L N ⊕ Lam d L N) :=
  thetaO ((1 / 2 : ℂ) • V b ^ 2 + W b) - inclO ((1 / 2 : ℂ) • VprO C V b ^ 2 + SbO j C V W b)

/-! ### Expansions of the block factors -/

variable {V}

theorem IbO_exp (hV : ∀ b, ε ((V b : SA c (Lam d L N)).e) = 0) (b : Fin d → ℕ) :
    ExpW2 (fun t => IbO (VtO V t) (WtO W t) b) 1 (-V b) ((1 / 2 : ℂ) • V b ^ 2 + W b) := by
  have h1 : ExpW2 (fun t => -(VtO V t b)) 0 (-V b) 0 :=
    (ExpW2.lin (-V b)).congr fun t => by simp [VtO]
  have h2 := ExpW2.oexp h1 (fun t => by
    show ε (-(t • (V b : SA c (Lam d L N)))).e = 0
    rw [neg_e]; show ε (-(t • (V b : SA c (Lam d L N)).e)) = 0
    rw [map_neg, map_smul, hV b, smul_zero, neg_zero])
  have h3 : ExpW2 (fun t => 1 + WtO W t b) 1 0 (W b) :=
    ((ExpW2.const 1).add (ExpW2.quad (W b))).coeffs (by simp) (by simp) (by simp)
  exact (h2.mul h3).coeffs (by simp) (by simp) (by simp; abel)

theorem IpO_exp (b : Fin d → ℕ) :
    ExpW2 (fun t => IpO P j C (VtO V t) (WtO W t) 0 b) 1 (-VprO C V b)
      ((1 / 2 : ℂ) • VprO C V b ^ 2 + SbO j C V W b) := by
  set a : ℂ := ε ((VprO C V b : SA c (Lam d L N)).e)
  set β : ℂ := ε ((LSO P j C V W b : SA c (Lam d L N)).e)
  set V' := VprO C V b
  set S := LSO P j C V W b
  -- the exponent `-u^{obs} - V_{j+1} = -(u+V)_{j+1} + u^∅`
  have hG : ∀ t, -upO P j C (VtO V t) (WtO W t) 0 b + -VpO P j C (VtO V t) (WtO W t) 0 b =
      t • (-(V' - algebraMap ℂ _ a)) + t ^ 2 • (S - algebraMap ℂ _ β) := by
    intro t
    rw [VpO, uVpO_scale, upB_scale]
    simp only [smul_eq_algW, map_sub, map_mul, map_pow]
    ring
  have h1 : ExpW2 (fun t => -upO P j C (VtO V t) (WtO W t) 0 b + -VpO P j C (VtO V t) (WtO W t) 0 b)
      0 (-(V' - algebraMap ℂ _ a)) (S - algebraMap ℂ _ β) :=
    ((ExpW2.lin _).add (ExpW2.quad _)).congr hG |>.coeffs (by simp) (by simp) (by simp)
  have h2 := ExpW2.oexp h1 (fun t => by
    show ε ((-upO P j C (VtO V t) (WtO W t) 0 b : SA c (Lam d L N)).e +
      (-VpO P j C (VtO V t) (WtO W t) 0 b : SA c (Lam d L N)).e) = 0
    rw [map_add, neg_e, neg_e, map_neg, map_neg, eps_VpO,
      ε_bulk_eq_zero_of_obs (bulk_upO P j C _ _ _ b), neg_zero, add_zero])
  have h3 : ExpW2 (fun t => 1 + WpO P j C (VtO V t) (WtO W t) b) 1 0 (SbO j C V W b - S) :=
    (((ExpW2.const 1).add (ExpW2.quad (SbO j C V W b - S))).congr fun t => by
      simp [WpO, SbO_scale, LSO_scale, smul_sub, S]).coeffs (by simp) (by simp) (by simp)
  have h4 : ExpS2 (fun t => -upB P j C (VtO V t) (WtO W t) 0 b) 0 (-a) β :=
    OrdS.congr (OrdS.zero 3) fun t => by beta_reduce; rw [upB_scale]; ring
  have h5 := ExpS2.exp h4
  have := ExpW2.smulS h5 (h2.mul h3)
  refine (this.congr fun t => ?_).coeffs ?_ ?_ ?_
  · rw [IpO, GpO, expU, smul_mul_assoc, ← mul_assoc,
      ← oexp_add (isNilpotent_of_ε (eps_neg_upO P j C _ _ _ b))
        (isNilpotent_of_ε (by
          show ε (-(VpO P j C (VtO V t) (WtO W t) 0 b : SA c (Lam d L N)).e) = 0
          rw [map_neg, eps_VpO, neg_zero]))]
  · simp
  · simp only [smul_eq_algW, map_neg, map_one, one_mul, mul_one, mul_zero, add_zero]
    ring
  · have hh : algebraMap ℂ (OE c (Lam d L N)) (1 / 2) * 2 = 1 := by
      rw [show (2 : OE c (Lam d L N)) = algebraMap ℂ _ 2 from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    simp only [show ((-a) ^ 2 / 2 : ℂ) = a ^ 2 * (1 / 2) by ring]
    simp only [smul_eq_algW, map_neg, map_one, one_mul, mul_one, mul_zero, add_zero, zero_add,
      map_add, map_pow, map_mul, map_sub]
    linear_combination (V' * algebraMap ℂ (OE c (Lam d L N)) a -
      algebraMap ℂ (OE c (Lam d L N)) a ^ 2) * hh

theorem dIO_exp (hV : ∀ b, ε ((V b : SA c (Lam d L N)).e) = 0) (b : Fin d → ℕ) :
    ExpW2 (fun t => gdIO (IbO (VtO V t) (WtO W t)) (IpO P j C (VtO V t) (WtO W t) 0) b) 0
      (D1O C V b) (D2O j C V W b) := by
  have h1 := (IbO_exp W hV b).map (thetaO (c := c) (Λ := Lam d L N)).toLinearMap
  have h2 := (IpO_exp P j C (V := V) W b).map (inclO (c := c) (Λ := Lam d L N)).toLinearMap
  exact ((h1.sub h2).congr fun t => rfl).coeffs (by simp) (by simp [D1O]) (by simp [D2O])

theorem FCO_sub_rightS (A B B' : OE c (Lam d L N)) :
    FCO C A (B - B') = FCO C A B - FCO C A B' := by
  rw [sub_eq_add_neg, FCO_add_right, ← neg_one_smul ℂ B', FCO_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

theorem ECCO_thetaO (F : OE c (Lam d L N)) : ECCO C (thetaO F) = EthO C F := rfl

theorem ECCO_D1O (b : Fin d → ℕ) : ECCO C (D1O C V b) = 0 := by
  rw [D1O, map_add, map_neg, ECCO_inclO, ECCO_thetaO, VprO, neg_add_cancel]

theorem ECCO_D1O_mul (b b' : Fin d → ℕ) :
    ECCO C (D1O C V b * D1O C V b') = FCO C (VprO C V b) (VprO C V b') := by
  have e : D1O C V b * D1O C V b' = thetaO (V b * V b') - inclO (VprO C V b) * thetaO (V b') -
      inclO (VprO C V b') * thetaO (V b) + inclO (VprO C V b * VprO C V b') := by
    simp only [D1O, map_mul]; ring
  rw [e, map_add, map_sub, map_sub, ECCO_inclO_mul, ECCO_inclO_mul, ECCO_inclO, ECCO_thetaO,
    ECCO_thetaO, ECCO_thetaO, EthO_mul]
  simp only [VprO]
  ring

theorem ECCO_D2O (b : Fin d → ℕ) :
    ECCO C (D2O j C V W b) =
      (-(1 / 2 : ℂ)) • FCO C (VprO C V b) (VprLO j C V - VprO C V b) - SCorO j C V b := by
  rw [D2O, map_sub, ECCO_inclO, ECCO_thetaO, EthO_add, EthO_smul]
  simp only [pow_two]
  rw [EthO_mul, SbO, SFO, FCO_sub_rightS]
  simp only [VprO]
  module


theorem uXO_exp (U : Finset (Lam d L N)) :
    ∃ a₁ a₂, ExpS2 (fun t => Complex.exp (uXB P j C (VtO V t) (WtO W t) 0 U)) 1 a₁ a₂ := by
  have h : ExpS2 (fun t => uXB P j C (VtO V t) (WtO W t) 0 U)
      (∑ b ∈ blocks j U, (0 : ℂ))
      (∑ b ∈ blocks j U, ε ((VprO C V b : SA c (Lam d L N)).e))
      (∑ b ∈ blocks j U, -ε ((LSO P j C V W b : SA c (Lam d L N)).e)) := by
    refine (ExpS2.sum _ fun b _ => ?_).congr fun t => rfl
    exact OrdS.congr (OrdS.zero 3) fun t => by beta_reduce; rw [upB_scale]; ring
  rw [sum_const_zero] at h
  exact ⟨_, _, ExpS2.exp h⟩

theorem prefO_exp (U X : Finset (Lam d L N)) :
    ∃ P₁ P₂, ExpW2 (fun t => expU (uXB P j C (VtO V t) (WtO W t) 0 U)
      (uXO P j C (VtO V t) (WtO W t) 0 U) * bpowO j (IpO P j C (VtO V t) (WtO W t) 0) (U \ X))
      1 P₁ P₂ := by
  obtain ⟨a₁, a₂, ha⟩ := uXO_exp P j C (V := V) W U
  have hu : ExpW2 (fun t => uXO P j C (VtO V t) (WtO W t) 0 U) 0
      (∑ b ∈ blocks j U, πobs (epsO (VprO C V b)))
      (∑ b ∈ blocks j U, -πobs (epsO (LSO P j C V W b))) := by
    refine ((ExpW2.sum _ fun b _ => ((ExpW2.lin (πobs (epsO (VprO C V b)))).add
      (ExpW2.quad (-πobs (epsO (LSO P j C V W b))))).coeffs (zero_add 0).symm (add_zero _).symm
        (zero_add _).symm).congr fun t => ?_).coeffs (by simp) rfl rfl
    rw [uXO]
    refine sum_congr rfl fun b _ => ?_
    rw [upO_scale, smul_neg, sub_eq_add_neg]
  have he := (ExpW2.smulS ha (ExpW2.oexp hu fun t => eps_uXO P j C _ _ _ U))
  obtain ⟨P₁, P₂, hP⟩ := ExpW2.prod_one (blocks j (U \ X))
    (f := fun b t => IpO P j C (VtO V t) (WtO W t) 0 b) fun b _ => ⟨_, _, IpO_exp P j C W b⟩
  exact ⟨_, _, ((he.mul hP).congr fun t => by rw [expU]; rfl).coeffs (by simp) rfl rfl⟩

theorem E_dIPowO_exp (hV : ∀ b, ε ((V b : SA c (Lam d L N)).e) = 0) {X : Finset (Lam d L N)}
    (hX : X.Nonempty) :
    ExpW2 (fun t => ECCO C (gdIPowO j (IbO (VtO V t) (WtO W t)) (IpO P j C (VtO V t) (WtO W t) 0) X))
      0 0 (k2O j C V X) := by
  have hb : ∀ b, ExpW2 (fun t => gdIO (IbO (VtO V t) (WtO W t)) (IpO P j C (VtO V t) (WtO W t) 0) b) 0
      (D1O C V b) (D2O j C V W b) := dIO_exp P j C W hV
  have hne : nb j X ≠ 0 := by
    intro h
    rw [nb, card_eq_zero] at h
    obtain ⟨x, hx⟩ := hX
    exact notMem_empty _ (h ▸ blk_mem_blocks hx)
  by_cases h1 : nb j X = 1
  · obtain ⟨b, hbX⟩ := card_eq_one.1 h1
    have := (hb b).map (ECCO C)
    refine (this.congr fun t => by rw [gdIPowO, hbX, prod_singleton]).coeffs (by simp)
      (ECCO_D1O C b).symm ?_
    rw [k2O, if_pos h1, hbX, sum_singleton, ECCO_D2O]
  by_cases h2 : nb j X = 2
  · obtain ⟨b, b', hbb', hbX⟩ := card_eq_two.1 h2
    have := ((hb b).mul (hb b')).map (ECCO C)
    refine (this.congr fun t => by rw [gdIPowO, hbX, prod_pair hbb']).coeffs (by simp)
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
    rw [k2O, if_neg h1, if_pos h2, hbX, sum_pair hbb', e1, e2, sum_singleton, sum_singleton,
      FCO_comm C (VprO C V b')]
    simp only [mul_zero, zero_mul, add_zero, zero_add, ECCO_D1O_mul, map_add]
    module
  · have h3 : 3 ≤ nb j X := by omega
    have hO : OrdW 3 (fun t => gdIPowO j (IbO (VtO V t) (WtO W t)) (IpO P j C (VtO V t) (WtO W t) 0) X) :=
      OrdW.mono h3 (OrdW.prod (blocks j X) fun b _ => (hb b).ord1)
    refine ((ExpW2.of_ord3 hO).map (ECCO C)).coeffs (by simp) (by simp) ?_
    rw [k2O, if_neg h1, if_neg h2, map_zero]

/-- **The second-order part of `K_{j+1}` with sources** (`e:K2`): for `K_j = 0` and the
coordinates `(t V, t² 𝒲)`, `K_{j+1}(U) = t² K^{(2)}(U) + O(t³)` for every nonempty `U`. -/
theorem Knext2O_expansion (hV : ∀ b, ε ((V b : SA c (Lam d L N)).e) = 0) {U : Finset (Lam d L N)}
    (hU : U.Nonempty) :
    ExpW2 (fun t => Knext2O P j C (VtO V t) (WtO W t) 0 U) 0 0 (K2O j C V U) := by
  classical
  have hterm : ∀ X ∈ (Pj j univ).filter (fun X => clo j X = U),
      ExpW2 (fun t => (expU (uXB P j C (VtO V t) (WtO W t) 0 U)
          (uXO P j C (VtO V t) (WtO W t) 0 U) * bpowO j (IpO P j C (VtO V t) (WtO W t) 0) (U \ X)) *
        ECCO C (gdIPowO j (IbO (VtO V t) (WtO W t)) (IpO P j C (VtO V t) (WtO W t) 0) X))
        0 0 (k2O j C V X) := by
    intro X hX
    have hXne : X.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      rw [(mem_filter.1 hX).2.symm, clo_empty] at hU
      exact not_nonempty_empty hU
    obtain ⟨P₁, P₂, hP⟩ := prefO_exp P j C W U X
    exact (hP.mul (E_dIPowO_exp P j C W hV hXne)).coeffs (by simp) (by simp) (by simp)
  have := ExpW2.sum _ hterm
  refine (this.congr fun t => ?_).coeffs (by simp) (by simp) (by rw [K2O])
  rw [Knext2O, gKnextO_zero, mul_sum]
  refine sum_congr rfl fun X _ => ?_
  rw [mul_assoc]

end Scale

end

end Obs2
