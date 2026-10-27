import Obs2.Est.SecondO

/-!
# The linear part of `K_{j+1}` with sources at `V = 𝒲 = 0` (`Step2.Map.Lin` on `OE`)

For the coordinates `(0, 0, s K)` (bulk plus observable activity),
`K_{j+1}(0, 0, s K)(U) = s 𝓛(K)(U) + O(s²)` for nonempty `U` (`Knext2O_lin`), with the explicit
linear map `𝓛 = Llin2O`:
`𝓛(K)(U) = ∑_{X ∈ 𝒞_j, \bar X = U} 𝔼θ[K(X) - ∑_B J(B, X) - 1_{X = B} Q(B)]
  + ∑_{(B,X): \overline{B^□} = U} 𝔼θ J(B, X)`.
Same proof as `Step2.Knext2_lin`; `Q`, `J` use the pointed localisation `LocO2`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

section LinK

variable (P : ObsPts d L N) (j : ℕ)

theorem Q2O_smul (s : ℂ) (K : OAct c d L N) (b : Fin d → ℕ) : Q2O P j (s • K) b = s • Q2O P j K b := by
  unfold Q2O
  split_ifs
  · rw [smul_sum]
    exact sum_congr rfl fun X _ => by rw [Pi.smul_apply, map_smul]
  · rw [smul_zero]

theorem J2O_smul (s : ℂ) (K : OAct c d L N) (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    J2O P j (s • K) b X = s • J2O P j K b X := by
  unfold J2O
  split_ifs
  · rw [smul_neg, smul_sum]
    exact congrArg _ (sum_congr rfl fun Y _ => by rw [Pi.smul_apply, map_smul])
  · rw [Pi.smul_apply, map_smul]
  · rw [smul_zero]

theorem KextO_smul (s : ℂ) (K : OAct c d L N) (Z : Finset (Lam d L N)) :
    KextO j (s • K) Z = s ^ (Comp j Z).card • KextO j K Z := by
  simp only [KextO, Pi.smul_apply]
  exact (Finset.smul_prod _ s _).symm

end LinK

section Zero

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : OAct c d L N)

theorem FCO_zero_left (B : OE c (Lam d L N)) : FCO C 0 B = 0 := by
  simpa using FCO_smul_left C 0 0 B

theorem VprO_zero (b : Fin d → ℕ) : VprO C (0 : OFam c d L N) b = 0 := EthO_zero' C _ rfl

theorem VprLO_zero : VprLO j C (0 : OFam c d L N) = 0 := by
  simp [VprLO, VprO_zero]

theorem SbO_zero (b : Fin d → ℕ) : SbO j C (0 : OFam c d L N) 0 b = 0 := by
  simp [SbO, SFO, SCorO, VprO_zero, VprLO_zero, FCO_zero_left, FCO_comm C _ (0 : OE c (Lam d L N)),
    EthO_zero' C (0 : OE c (Lam d L N)) rfl]

theorem LSO_zero (b : Fin d → ℕ) : LSO P j C (0 : OFam c d L N) 0 b = 0 := by
  simp [LSO, SXO, SbO_zero]

theorem WpO_zero (b : Fin d → ℕ) : WpO P j C (0 : OFam c d L N) 0 b = 0 := by
  simp [WpO, SbO_zero, LSO_zero]

theorem uVpO_zeroVW (s : ℂ) (b : Fin d → ℕ) :
    uVpO P j C (0 : OFam c d L N) 0 (s • K) b = -(s • EthO C (Q2O P j K b)) := by
  rw [uVpO, VprO_zero, LSO_zero, Q2O_smul, EthO_smul]; abel

theorem IbO_zero (b : Fin d → ℕ) : IbO (0 : OFam c d L N) 0 b = 1 := by
  simp [IbO, oexp_zero]

/-- `I_{j+1}(B) = 1 + s 𝔼θ Q(B) + O(s²)` at `V = 𝒲 = 0`. -/
theorem IpO_lin (b : Fin d → ℕ) :
    ExpW1 (fun s : ℂ => IpO P j C (0 : OFam c d L N) 0 (s • K) b) 1 (EthO C (Q2O P j K b)) := by
  set F := EthO C (Q2O P j K b)
  set a : ℂ := ε ((F : SA c (Lam d L N)).e)
  have hG : ∀ s : ℂ, -upO P j C (0 : OFam c d L N) 0 (s • K) b +
      -VpO P j C (0 : OFam c d L N) 0 (s • K) b = s • (F - algebraMap ℂ _ a) := by
    intro s
    have hu : upB P j C (0 : OFam c d L N) 0 (s • K) b = -(s * a) := by
      rw [upB, uVpO_zeroVW, coe_bulk]
      show ε (-(s • (F : SA c (Lam d L N)).e)) = _
      rw [map_neg, map_smul, smul_eq_mul]
    rw [VpO, hu, uVpO_zeroVW]
    simp only [smul_eq_algW, map_neg, map_mul]
    ring
  have h1 : ExpW2 (fun s : ℂ => -upO P j C (0 : OFam c d L N) 0 (s • K) b +
      -VpO P j C (0 : OFam c d L N) 0 (s • K) b) 0 (F - algebraMap ℂ _ a) 0 :=
    (ExpW2.lin _).congr hG
  have h2 := ExpW2.oexp h1 (fun s => by
    show ε ((-upO P j C (0 : OFam c d L N) 0 (s • K) b : SA c (Lam d L N)).e +
      (-VpO P j C (0 : OFam c d L N) 0 (s • K) b : SA c (Lam d L N)).e) = 0
    rw [map_add, neg_e, neg_e, map_neg, map_neg, eps_VpO,
      ε_bulk_eq_zero_of_obs (bulk_upO P j C _ _ _ b), neg_zero, add_zero])
  have hup : ∀ s : ℂ, -upB P j C (0 : OFam c d L N) 0 (s • K) b = s * a := by
    intro s
    rw [upB, uVpO_zeroVW, coe_bulk]
    show -ε (-(s • (F : SA c (Lam d L N)).e)) = _
    rw [map_neg, map_smul, smul_eq_mul, neg_neg]
  have h3 : ExpS2 (fun s : ℂ => -upB P j C (0 : OFam c d L N) 0 (s • K) b) 0 a 0 :=
    (ExpS2.lin a).congr fun s => by rw [hup]
  have h4 := ExpS2.exp h3
  have h5 := ExpW1.smulS h4 (ExpW1.of_exp2 h2)
  refine (h5.congr fun s => ?_).coeffs (by simp) ?_
  · rw [IpO, GpO, WpO_zero, add_zero, mul_one, expU, smul_mul_assoc,
      ← oexp_add (isNilpotent_of_ε (eps_neg_upO P j C _ _ _ b))
        (isNilpotent_of_ε (by
          show ε (-(VpO P j C (0 : OFam c d L N) 0 (s • K) b : SA c (Lam d L N)).e) = 0
          rw [map_neg, eps_VpO, neg_zero]))]
  · simp [smul_eq_algW]

/-- `δI(B) = -s 𝔼θ Q(B) + O(s²)` at `V = 𝒲 = 0`. -/
theorem dIO_lin (b : Fin d → ℕ) :
    ExpW1 (fun s : ℂ => gdIO (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) b) 0
      (-inclO (EthO C (Q2O P j K b))) := by
  have := ((ExpW1.const (thetaO (1 : OE c (Lam d L N)))).sub
    ((IpO_lin P j C K b).map (inclO (c := c) (Λ := Lam d L N)).toLinearMap))
  refine (this.congr fun s => by simp [gdIO, IbO_zero]).coeffs (by simp) (by simp)

theorem dIPowO_ord (Y : Finset (Lam d L N)) :
    OrdW (nb j Y) (fun s : ℂ => gdIPowO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) Y) :=
  OrdW.prod (blocks j Y) fun b _ => (dIO_lin P j C K b).ord1

theorem thetaKextO_ord (Z : Finset (Lam d L N)) :
    OrdW (Comp j Z).card (fun s : ℂ => thetaO (KextO j (s • K) Z)) := by
  refine ⟨fun _ => thetaO (KextO j K Z), HolW.const _, fun s => ?_⟩
  beta_reduce
  rw [KextO_smul, map_smul]

/-- The first-order part of `(δI)^W`: `-𝔼θQ(B)` if `W = B` is a block, `0` otherwise. -/
def dIlinO (W : Finset (Lam d L N)) : OE c (Lam d L N ⊕ Lam d L N) :=
  if nb j W = 1 then ∑ b ∈ blocks j W, -inclO (EthO C (Q2O P j K b)) else 0

theorem dIPowO_lin {W : Finset (Lam d L N)} (hW : W.Nonempty) :
    ExpW1 (fun s : ℂ => gdIPowO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) W) 0
      (dIlinO P j C K W) := by
  by_cases h1 : nb j W = 1
  · obtain ⟨b, hb⟩ := card_eq_one.1 h1
    refine ((dIO_lin P j C K b).congr fun s => by rw [gdIPowO, hb, prod_singleton]).coeffs rfl ?_
    rw [dIlinO, if_pos h1, hb, sum_singleton]
  · have hne : nb j W ≠ 0 := by
      intro h
      rw [nb, card_eq_zero] at h
      obtain ⟨x, hx⟩ := hW
      exact notMem_empty _ (h ▸ blk_mem_blocks hx)
    refine (ExpW1.of_ord2 (OrdW.mono (by omega) (dIPowO_ord P j C K W))).coeffs rfl ?_
    rw [dIlinO, if_neg h1]

theorem gKtilO_lin {W : Finset (Lam d L N)} (hW : IsConn j W) :
    ExpW1 (fun s : ℂ => gKtilO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) (s • K) W) 0
      (thetaO (K W) + dIlinO P j C K W) := by
  have hWp := hW.1
  have hWne : W.Nonempty := hW.2.1
  have hWm : W ∈ Pj j W := mem_Pj.2 ⟨subset_rfl, hWp⟩
  have h0ne : (∅ : Finset (Lam d L N)) ≠ W := fun h => not_nonempty_empty (h ▸ hWne)
  have h0m : (∅ : Finset (Lam d L N)) ∈ (Pj j W).erase W :=
    mem_erase.2 ⟨h0ne, mem_Pj.2 ⟨empty_subset _, isPolymer_empty j⟩⟩
  have e : ∀ s : ℂ, gKtilO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) (s • K) W =
      gdIPowO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) W +
        (thetaO (KextO j (s • K) W) +
          ∑ Y ∈ ((Pj j W).erase W).erase ∅,
            thetaO (KextO j (s • K) (W \ Y)) * gdIPowO j (IbO 0 0) (IpO P j C 0 0 (s • K)) Y) := by
    intro s
    rw [gKtilO, ← add_sum_erase _ _ hWm, ← add_sum_erase _ _ h0m, sdiff_self,
      show (⊥ : Finset (Lam d L N)) = ∅ from rfl, sdiff_empty]
    simp only [KextO, comp_empty, prod_empty, map_one, one_mul]
    rw [show gdIPowO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) ∅ = 1 by
      simp [gdIPowO, blocks], mul_one]
  have hK : ExpW1 (fun s : ℂ => thetaO (KextO j (s • K) W)) 0 (thetaO (K W)) := by
    refine (ExpW1.lin (thetaO (K W))).congr fun s => ?_
    rw [KextO_smul, KextO, comp_of_isConn hW, card_singleton, pow_one, prod_singleton, map_smul]
  have hrest : OrdW 2 (fun s : ℂ => ∑ Y ∈ ((Pj j W).erase W).erase ∅,
      thetaO (KextO j (s • K) (W \ Y)) *
        gdIPowO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) Y) := by
    refine OrdW.sum _ fun Y hY => ?_
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
    exact OrdW.mono (by omega) ((OrdW.mono hc (thetaKextO_ord j K (W \ Y))).mul
      (OrdW.mono hn (dIPowO_ord P j C K Y)))
  exact (((dIPowO_lin P j C K hWne).add (hK.add (ExpW1.of_ord2 hrest))).congr e).coeffs
    (by simp) (by simp; abel)

theorem thetaJO_lin (b : Fin d → ℕ) (X : Finset (Lam d L N)) :
    ExpW1 (fun s : ℂ => thetaO (J2O P j (s • K) b X)) 0 (thetaO (J2O P j K b X)) :=
  (ExpW1.lin _).congr fun s => by rw [J2O_smul, map_smul]

theorem gKchkCO_lin {W : Finset (Lam d L N)} (hW : IsConn j W) :
    ExpW1 (fun s : ℂ => gKchkCO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) (s • K)
        (J2O P j (s • K)) W) 0
      (thetaO (K W) + dIlinO P j C K W - ∑ b ∈ blocks j W, thetaO (J2O P j K b W)) :=
  ((gKtilO_lin P j C K hW).sub (ExpW1.sum _ fun b _ => thetaJO_lin P j K b W)).coeffs (by simp) rfl

theorem gKchkO_ord {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    OrdW (Comp j X).card (fun s : ℂ => gKchkO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K))
      (s • K) (J2O P j (s • K)) X) :=
  OrdW.prod (Comp j X) fun c hc => (gKchkCO_lin P j C K (isConn_of_mem_comp hX hc)).ord1

theorem Jprod2O_ord (𝒳 : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    OrdW 𝒳.card (fun s : ℂ => ∏ p ∈ 𝒳, thetaO (J2O P j (s • K) p.1 p.2)) :=
  OrdW.prod 𝒳 fun p _ => (thetaJO_lin P j K p.1 p.2).ord1

/-- **The linear part** `𝓛(K)(U)` of `K_{j+1}` with sources at `V = 𝒲 = 0`. -/
def Llin2O (U : Finset (Lam d L N)) : OE c (Lam d L N) :=
  open Classical in
  ∑ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ECCO C (thetaO (K g.2) + dIlinO P j C K g.2 - ∑ b ∈ blocks j g.2, thetaO (J2O P j K b g.2)) +
    ∑ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ECCO C (∏ p ∈ g.1, thetaO (J2O P j K p.1 p.2))

theorem uXO_lin (U : Finset (Lam d L N)) :
    ∃ a₁ a₂, ExpS2 (fun s : ℂ => Complex.exp (uXB P j C (0 : OFam c d L N) 0 (s • K) U)) 1 a₁ a₂ := by
  have h : ExpS2 (fun s : ℂ => uXB P j C (0 : OFam c d L N) 0 (s • K) U)
      (∑ b ∈ blocks j U, (0 : ℂ))
      (∑ b ∈ blocks j U, -ε ((EthO C (Q2O P j K b) : SA c (Lam d L N)).e))
      (∑ b ∈ blocks j U, (0 : ℂ)) := by
    refine (ExpS2.sum _ fun b _ => ?_).congr fun s => rfl
    refine OrdS.congr (OrdS.zero 3) fun s => ?_
    beta_reduce
    rw [upB, uVpO_zeroVW, coe_bulk]
    show ε (-(s • (EthO C (Q2O P j K b) : SA c (Lam d L N)).e)) - _ = _
    rw [map_neg, map_smul, smul_eq_mul]
    ring
  simp only [sum_const_zero] at h
  exact ⟨_, _, ExpS2.exp h⟩

theorem prefO_lin (U Z : Finset (Lam d L N)) :
    ∃ P₁, ExpW1 (fun s : ℂ => expU (uXB P j C (0 : OFam c d L N) 0 (s • K) U)
      (uXO P j C (0 : OFam c d L N) 0 (s • K) U) *
        bpowO j (IpO P j C (0 : OFam c d L N) 0 (s • K)) Z) 1 P₁ := by
  obtain ⟨a₁, a₂, ha⟩ := uXO_lin P j C K U
  have hu : ExpW2 (fun s : ℂ => uXO P j C (0 : OFam c d L N) 0 (s • K) U) 0
      (∑ b ∈ blocks j U, -πobs (epsO (EthO C (Q2O P j K b)))) 0 := by
    refine ((ExpW2.sum _ fun b _ => ExpW2.lin (-πobs (epsO (EthO C (Q2O P j K b))))).congr
      fun s => ?_).coeffs (by simp) rfl (by simp)
    rw [uXO]
    refine sum_congr rfl fun b _ => ?_
    rw [upO, uVpO_zeroVW, map_neg, map_neg, map_smul, map_smul, smul_neg]
  have he := ExpW1.smulS ha (ExpW1.of_exp2 (ExpW2.oexp hu fun s => eps_uXO P j C _ _ _ U))
  obtain ⟨P₁, hP⟩ := ExpW1.prod_one (blocks j Z)
    (f := fun b s => IpO P j C (0 : OFam c d L N) 0 (s • K) b) fun b _ => ⟨_, IpO_lin P j C K b⟩
  exact ⟨_, ((he.mul hP).congr fun s => by rw [expU]; rfl).coeffs (by simp) rfl⟩

/-- The summand of `K_{j+1}(0, 0, s K)(U)` for `g ∈ 𝒢(U)`. -/
def TtermO (U : Finset (Lam d L N))
    (g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)) (s : ℂ) :
    OE c (Lam d L N) :=
  (expU (uXB P j C (0 : OFam c d L N) 0 (s • K) U) (uXO P j C (0 : OFam c d L N) 0 (s • K) U) *
    bpowO j (IpO P j C (0 : OFam c d L N) 0 (s • K)) (U \ (g.2 ∪ Xcal g.1))) *
    ECCO C (gKchkO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) (s • K)
      (J2O P j (s • K)) g.2 * ∏ p ∈ g.1, thetaO (J2O P j (s • K) p.1 p.2))

open Classical in
theorem TtermO_A {U : Finset (Lam d L N)} (hU : U.Nonempty)
    (g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N))
    (hg : g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2)) :
    ExpW1 (TtermO P j C K U g) 0 (ECCO C (thetaO (K g.2) + dIlinO P j C K g.2 -
        ∑ b ∈ blocks j g.2, thetaO (J2O P j K b g.2))) := by
  obtain ⟨-, h1, hc⟩ := mem_filter.1 hg
  obtain ⟨P₁, hP⟩ := prefO_lin P j C K U (U \ (g.2 ∪ Xcal g.1))
  have hE := (gKchkCO_lin P j C K hc).map (ECCO C)
  have hTe : ∀ s, TtermO P j C K U g s = (expU (uXB P j C (0 : OFam c d L N) 0 (s • K) U)
      (uXO P j C (0 : OFam c d L N) 0 (s • K) U) *
        bpowO j (IpO P j C (0 : OFam c d L N) 0 (s • K)) (U \ (g.2 ∪ Xcal g.1))) *
      ECCO C (gKchkCO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) (s • K)
        (J2O P j (s • K)) g.2) := by
    intro s
    rw [TtermO, h1, prod_empty, mul_one, gKchkO, comp_of_isConn hc, prod_singleton]
  exact ((hP.mul hE).congr hTe).coeffs (by rw [map_zero, mul_zero])
    (by rw [map_zero, mul_zero, add_zero, one_mul])

open Classical in
theorem TtermO_B {U : Finset (Lam d L N)} (hU : U.Nonempty)
    (g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N))
    (hg : g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅)) :
    ExpW1 (TtermO P j C K U g) 0 (ECCO C (∏ p ∈ g.1, thetaO (J2O P j K p.1 p.2))) := by
  obtain ⟨-, h1, h2⟩ := mem_filter.1 hg
  obtain ⟨p, hp⟩ := card_eq_one.1 h1
  obtain ⟨P₁, hP⟩ := prefO_lin P j C K U (U \ (g.2 ∪ Xcal g.1))
  have hE := (thetaJO_lin P j K p.1 p.2).map (ECCO C)
  have hTe : ∀ s, TtermO P j C K U g s = (expU (uXB P j C (0 : OFam c d L N) 0 (s • K) U)
      (uXO P j C (0 : OFam c d L N) 0 (s • K) U) *
        bpowO j (IpO P j C (0 : OFam c d L N) 0 (s • K)) (U \ (g.2 ∪ Xcal g.1))) *
      ECCO C (thetaO (J2O P j (s • K) p.1 p.2)) := by
    intro s
    rw [TtermO, h2, hp, gKchkO, comp_empty, prod_empty, one_mul, prod_singleton]
  refine ((hP.mul hE).congr hTe).coeffs (by rw [map_zero, mul_zero]) ?_
  rw [hp, prod_singleton, map_zero, mul_zero, add_zero, one_mul]

open Classical in
theorem TtermO_R {U : Finset (Lam d L N)} (hU : U.Nonempty)
    (g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N))
    (hg : g ∈ ((Gset j U).filter (fun g => ¬ (g.1 = ∅ ∧ IsConn j g.2))).filter
      (fun g => ¬ (g.1.card = 1 ∧ g.2 = ∅))) :
    ExpW1 (TtermO P j C K U g) 0 0 := by
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
  have hO : OrdW 2 (fun s : ℂ =>
      ECCO C (gKchkO j (IbO (0 : OFam c d L N) 0) (IpO P j C 0 0 (s • K)) (s • K)
        (J2O P j (s • K)) g.2 * ∏ p ∈ g.1, thetaO (J2O P j (s • K) p.1 p.2))) :=
    OrdW.map (OrdW.mono (by omega) ((gKchkO_ord P j C K f1).mul (Jprod2O_ord P j K g.1))) (ECCO C)
  exact ExpW1.of_ord2 (OrdW.congr ((OrdW.of_hol (ExpW1.hol
    (prefO_lin P j C K U (U \ (g.2 ∪ Xcal g.1))).choose_spec)).mul hO
    |>.mono (by norm_num)) fun s => rfl) |>.congr fun s => rfl

/-- **`K_{j+1}(0, 0, s K)(U) = s 𝓛(K)(U) + O(s²)`** with sources, for nonempty `U`. -/
theorem Knext2O_lin {U : Finset (Lam d L N)} (hU : U.Nonempty) :
    ExpW1 (fun s : ℂ => Knext2O P j C (0 : OFam c d L N) 0 (s • K) U) 0 (Llin2O P j C K U) := by
  classical
  set T := TtermO P j C K U with hT
  have hA : ∀ g ∈ (Gset j U).filter (fun g => g.1 = ∅ ∧ IsConn j g.2),
      ExpW1 (T g) 0 (ECCO C (thetaO (K g.2) + dIlinO P j C K g.2 -
        ∑ b ∈ blocks j g.2, thetaO (J2O P j K b g.2))) :=
    fun g hg => TtermO_A P j C K hU g hg
  have hB : ∀ g ∈ (Gset j U).filter (fun g => g.1.card = 1 ∧ g.2 = ∅),
      ExpW1 (T g) 0 (ECCO C (∏ p ∈ g.1, thetaO (J2O P j K p.1 p.2))) :=
    fun g hg => TtermO_B P j C K hU g hg
  have hR : ∀ g ∈ ((Gset j U).filter (fun g => ¬ (g.1 = ∅ ∧ IsConn j g.2))).filter
      (fun g => ¬ (g.1.card = 1 ∧ g.2 = ∅)),
      ExpW1 (T g) 0 0 :=
    fun g hg => TtermO_R P j C K hU g hg
  have hsum : ExpW1 (fun s => ∑ g ∈ Gset j U, T g s) 0 (Llin2O P j C K U) := by
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
    have := (ExpW1.sum _ hA).add ((ExpW1.sum _ (hBf ▸ hB)).add (ExpW1.sum _ hR))
    refine (this.congr e).coeffs (by simp) ?_
    rw [Llin2O, sum_const_zero, add_zero, hBf]
  refine hsum.congr fun s => ?_
  rw [Knext2O, gKnextO, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [hT, TtermO, mul_assoc]

end Zero

end

end Obs2
