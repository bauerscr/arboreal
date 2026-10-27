import Obs2.Est.SecondO
import Obs2.Flow.BlockFlow
import Obs2.Flow.Hist

/-!
# Exact decoupling of observable constants from the second-order map

An observable constant `G` (`ε G = G`, `G_∅ = 0`, e.g. `−γ_aσ_a`) is a scalar of the field
algebra. Shifting the block family `V ↦ V + κ` by observable constants `κ(B)`:

* `𝔼_Cθ` fixes constants and is linear over them (`EthO_cst_mul`), so `V'_B ↦ V'_B + κ(B)`;
* `F_C(G, ·) = 0` for constants (`FCO_cst_left`), so `S^♯`, `𝒲_{j+1}`, `Loc S`, `k^{(2)}`, `J`
  are unchanged;
* the constant goes entirely into `u^{obs}_{j+1}(B)` (`upO_addc`), hence `V_{j+1}` is unchanged
  (`VpO_addc`);
* with `K = 0` the factors `e^{−κ(B)}` of `I_j(B)` and of `I_{j+1}(B)` appear exactly once per
  block of every polymer and cancel against the normalisation `e^{u^{obs}(U)}`
  (`Knext2O_addc`), so `K_{j+1}` is unchanged (`KplusO_addc`).

So the whole step is exact in the constant: only the accumulated observable constant moves
(`uObsTot_addc`). (`σ_a² = 0` is not used: the constants are central and the exponential is
additive on commuting elements, `oexp_add_right_obs`.)
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD LocObs

/-! ### Constants -/

section Pure

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- An observable constant: `ε G = G` and `G_∅ = 0`. -/
structure IsCstObs (G : OE c Λ) : Prop where
  he : epsO G = G
  hb : bulk G = 0

theorem thetaO_cst {G : OE c Λ} (he : epsO G = G) : thetaO G = inclO G := by
  rw [← he]
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [AlgHom.commutes]

theorem EthO_cst_mul (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) (X : OE c Λ) :
    EthO C (G * X) = G * EthO C X := by
  rw [EthO, map_mul, thetaO_cst he, ECCO_inclO_mul]; rfl

theorem EthO_one' (C : Matrix Λ Λ ℂ) : EthO C (1 : OE c Λ) = 1 := by
  rw [EthO, map_one, ECCO_one]

theorem EthO_cst (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) : EthO C G = G := by
  have h := EthO_cst_mul C he 1
  rwa [mul_one, EthO_one', mul_one] at h

theorem expO_cst_mul (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) (X : OE c Λ) :
    expO C (G * X) = G * expO C X := by
  rw [← EthO_eq_expO, ← EthO_eq_expO, EthO_cst_mul C he]

/-- **`F_C(G, B) = 0` for a constant `G`.** -/
theorem FCO_cst_left (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) (B : OE c Λ) :
    FCO C G B = 0 := by
  have h1 : expO (-C) G = G := by rw [← EthO_eq_expO, EthO_cst _ he]
  have h2 : expO C (expO (-C) B) = B := by
    have := expO_neg_expO (-C) B
    rwa [neg_neg] at this
  rw [FCO, h1, expO_cst_mul C he, h2, sub_self]

theorem FCO_cst_right (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) (A : OE c Λ) :
    FCO C A G = 0 := by
  rw [FCO_comm, FCO_cst_left C he]

theorem FCO_add_cst_left (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) (A B : OE c Λ) :
    FCO C (A + G) B = FCO C A B := by
  rw [FCO_add_left, FCO_cst_left C he, add_zero]

theorem FCO_add_cst_right (C : Matrix Λ Λ ℂ) {G : OE c Λ} (he : epsO G = G) (A B : OE c Λ) :
    FCO C A (B + G) = FCO C A B := by
  rw [FCO_add_right, FCO_cst_right C he, add_zero]

theorem πobs_obs {G : OE c Λ} (hb : bulk G = 0) : πobs G = G := by
  have h := eq_emb_add_πobs G
  rw [hb, map_zero, zero_add] at h
  exact h.symm

/-- `e^{F + G} = e^F e^G` for any `F` and an observable `G` (both sides vanish if `F` is not
nilpotent). -/
theorem oexp_add_right_obs (F : OE c Λ) {G : OE c Λ} (hb : bulk G = 0) :
    oexp (F + G) = oexp F * oexp G := by
  by_cases hF : IsNilpotent F
  · exact oexp_add hF (isNilpotent_of_obs hb)
  · have hFG : ¬ IsNilpotent (F + G) := by
      intro h
      apply hF
      have := (Commute.all (F + G) (-G)).isNilpotent_add h (isNilpotent_of_obs
        (by rw [map_neg, hb, neg_zero]))
      rwa [add_neg_cancel_right] at this
    show IsNilpotent.exp (F + G) = IsNilpotent.exp F * oexp G
    rw [nilExp_of_not hF, nilExp_of_not hFG, zero_mul]

theorem prod_oexp_obs {ι : Type*} (s : Finset ι) (F : ι → OE c Λ)
    (hF : ∀ i ∈ s, bulk (F i) = 0) : ∏ i ∈ s, oexp (F i) = oexp (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, sum_empty, oexp_zero]
  | insert i s hi ih =>
    have hs : bulk (∑ k ∈ s, F k) = 0 := by
      rw [map_sum]; exact sum_eq_zero fun k hk => hF k (mem_insert_of_mem hk)
    rw [prod_insert hi, sum_insert hi, ih (fun k hk => hF k (mem_insert_of_mem hk)),
      add_comm (F i), oexp_add_right_obs _ (hF i (mem_insert_self i s)), mul_comm]

theorem epsO_oexp_obs {G : OE c Λ} (he : epsO G = G) (hb : bulk G = 0) :
    epsO (oexp G) = oexp G := by
  rw [oexp_of_obs hb, map_add, map_add, map_one, map_smul, map_pow, he]

theorem IsCstObs.neg {G : OE c Λ} (h : IsCstObs G) : IsCstObs (-G) :=
  ⟨by rw [map_neg, h.he], by rw [map_neg, h.hb, neg_zero]⟩

theorem IsCstObs.sum {ι : Type*} (s : Finset ι) {G : ι → OE c Λ} (h : ∀ i, IsCstObs (G i)) :
    IsCstObs (∑ i ∈ s, G i) :=
  ⟨by rw [map_sum]; exact sum_congr rfl fun i _ => (h i).he,
   by rw [map_sum]; exact sum_eq_zero fun i _ => (h i).hb⟩

theorem IsCstObs.sub {G G' : OE c Λ} (h : IsCstObs G) (h' : IsCstObs G') : IsCstObs (G - G') :=
  ⟨by rw [map_sub, h.he, h'.he], by rw [map_sub, h.hb, h'.hb, sub_zero]⟩

theorem IsCstObs.zero : IsCstObs (0 : OE c Λ) := ⟨map_zero _, map_zero _⟩

theorem IsCstObs.a_eq {G : OE c Λ} (h : IsCstObs G) :
    (G : SA c Λ).a = algebraMap ℂ (N Λ) (ε (G : SA c Λ).a) :=
  (congrArg (fun F : OE c Λ => (F : SA c Λ).a) h.he).symm

theorem IsCstObs.e_eq {G : OE c Λ} (h : IsCstObs G) : (G : SA c Λ).e = 0 := by
  rw [← coe_bulk, h.hb]; rfl

end Pure

theorem IsCstObs.mass2_a {d L N : ℕ} [NeZero L] {c : Obs.Case} {G : OE c (Lam d L N)}
    (h : IsCstObs G) : mass2 (G : SA c (Lam d L N)).a = 0 := by
  rw [h.a_eq, mass2_algebraMap]

/-! ### The map -/

section Map

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}
variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W κ : OFam c d L N) (K : OAct c d L N)

variable {κ}

theorem VprO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    VprO C (V + κ) b = VprO C V b + κ b := by
  rw [VprO, VprO, Pi.add_apply, EthO_add, EthO_cst C (hκ b).he]

theorem VprLO_addc (hκ : ∀ b, IsCstObs (κ b)) :
    VprLO j C (V + κ) = VprLO j C V + ∑ b ∈ blockIdx (L := L) (N := N) j, κ b := by
  rw [VprLO, VprLO, ← sum_add_distrib]
  exact sum_congr rfl fun b _ => VprO_addc C V hκ b

theorem SCorO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    SCorO j C (V + κ) b = SCorO j C V b := by
  have hS := IsCstObs.sum (blockIdx (L := L) (N := N) j) hκ
  rw [SCorO, SCorO, VprO_addc C V hκ, VprLO_addc j C V hκ, map_add, map_add,
    πobs_obs (hκ b).hb, πobs_obs hS.hb, FCO_add_cst_left C (hκ b).he,
    FCO_add_cst_right C hS.he, FCO_add_cst_left C (hκ b).he, FCO_add_cst_right C hS.he]

theorem GO_addc (hκ : ∀ b, IsCstObs (κ b)) (b b' : Fin d → ℕ) :
    GO C (V + κ) b b' = GO C V b b' := by
  rw [GO, GO, VprO_addc C V hκ, VprO_addc C V hκ, map_add, map_add, πobs_obs (hκ b).hb,
    πobs_obs (hκ b').hb, FCO_add_cst_left C (hκ b).he, FCO_add_cst_right C (hκ b').he,
    FCO_add_cst_left C (hκ b).he, FCO_add_cst_right C (hκ b').he]

theorem SFO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    SFO j C (V + κ) b = SFO j C V b := by
  have hS := IsCstObs.sum (blockIdx (L := L) (N := N) j) hκ
  rw [SFO, SFO, SCorO_addc j C V hκ, VprO_addc C V hκ, VprLO_addc j C V hκ,
    FCO_add_cst_left C (hκ b).he, FCO_add_cst_right C hS.he]

theorem SbO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    SbO j C (V + κ) W b = SbO j C V W b := by
  rw [SbO, SbO, SFO_addc j C V hκ]

theorem SXO_addc (hκ : ∀ b, IsCstObs (κ b)) (X : Finset (Lam d L N)) :
    SXO j C (V + κ) W X = SXO j C V W X := by
  rw [SXO, SXO]; exact sum_congr rfl fun b _ => SbO_addc j C V W hκ b

theorem LSO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    LSO P j C (V + κ) W b = LSO P j C V W b := by
  rw [LSO, LSO, SXO_addc j C V W hκ]

theorem WpO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    WpO P j C (V + κ) W b = WpO P j C V W b := by
  rw [WpO, WpO, SbO_addc j C V W hκ, LSO_addc P j C V W hκ]

theorem Wnext2O_addc (hκ : ∀ b, IsCstObs (κ b)) (c' : Fin d → ℕ) :
    Wnext2O P j C (V + κ) W c' = Wnext2O P j C V W c' := by
  rw [Wnext2O, Wnext2O]
  congr 1
  exact prod_congr rfl fun b _ => by rw [WpO_addc P j C V W hκ]

theorem uVpO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    uVpO P j C (V + κ) W K b = uVpO P j C V W K b + κ b := by
  rw [uVpO, uVpO, VprO_addc C V hκ, LSO_addc P j C V W hκ]; abel

theorem upB_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    upB P j C (V + κ) W K b = upB P j C V W K b := by
  rw [upB, upB, uVpO_addc P j C V W K hκ, map_add, (hκ b).hb, add_zero]

theorem upO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    upO P j C (V + κ) W K b = upO P j C V W K b + κ b := by
  rw [upO, upO, uVpO_addc P j C V W K hκ, map_add, map_add, (hκ b).he, πobs_obs (hκ b).hb]

/-- **`V_{j+1}(B)` does not see the constants.** -/
theorem VpO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    VpO P j C (V + κ) W K b = VpO P j C V W K b := by
  rw [VpO, VpO, uVpO_addc P j C V W K hκ, upB_addc P j C V W K hκ, upO_addc P j C V W K hκ]
  abel

theorem Vnext2O_addc (hκ : ∀ b, IsCstObs (κ b)) (c' : Fin d → ℕ) :
    Vnext2O P j C (V + κ) W K c' = Vnext2O P j C V W K c' := by
  rw [Vnext2O, Vnext2O]; exact sum_congr rfl fun b _ => VpO_addc P j C V W K hκ b

theorem GpO_addc (hκ : ∀ b, IsCstObs (κ b)) :
    GpO P j C (V + κ) W K = GpO P j C V W K := by
  funext b; rw [GpO, GpO, VpO_addc P j C V W K hκ, WpO_addc P j C V W hκ]

theorem ItO_addc (hκ : ∀ b, IsCstObs (κ b)) :
    ItO P j C (V + κ) W K = ItO P j C V W K := by
  funext c'; rw [ItO, ItO, GpO_addc P j C V W K hκ]

theorem k2O_addc (hκ : ∀ b, IsCstObs (κ b)) (X : Finset (Lam d L N)) :
    k2O j C (V + κ) X = k2O j C V X := by
  have hS := IsCstObs.sum (blockIdx (L := L) (N := N) j) hκ
  have h1 : ∀ b, FCO C (VprO C (V + κ) b) (VprLO j C (V + κ) - VprO C (V + κ) b) =
      FCO C (VprO C V b) (VprLO j C V - VprO C V b) := by
    intro b
    rw [VprO_addc C V hκ, VprLO_addc j C V hκ, add_sub_add_comm, FCO_add_cst_left C (hκ b).he,
      FCO_add_cst_right C (hS.sub (hκ b)).he]
  have h2 : ∀ b b', FCO C (VprO C (V + κ) b) (VprO C (V + κ) b') =
      FCO C (VprO C V b) (VprO C V b') := by
    intro b b'
    rw [VprO_addc C V hκ, VprO_addc C V hκ, FCO_add_cst_left C (hκ b).he,
      FCO_add_cst_right C (hκ b').he]
  unfold k2O
  simp only [h1, h2, SCorO_addc j C V hκ]

theorem K2O_addc (hκ : ∀ b, IsCstObs (κ b)) (U : Finset (Lam d L N)) :
    K2O j C (V + κ) U = K2O j C V U := by
  unfold K2O; simp only [k2O_addc j C V hκ]

theorem kapO_addc (hκ : ∀ b, IsCstObs (κ b)) (X : Finset (Lam d L N)) (c' : Fin d → ℕ) :
    kapO j C (V + κ) X c' = kapO j C V X c' := by
  have hS := IsCstObs.sum (blockIdx (L := L) (N := N) j) hκ
  have h1 : ∀ b, FCO C (VprO C (V + κ) b) (VprLO j C (V + κ) - VprO C (V + κ) b) =
      FCO C (VprO C V b) (VprLO j C V - VprO C V b) := by
    intro b
    rw [VprO_addc C V hκ, VprLO_addc j C V hκ, add_sub_add_comm, FCO_add_cst_left C (hκ b).he,
      FCO_add_cst_right C (hS.sub (hκ b)).he]
  have h2 : ∀ b b', FCO C (VprO C (V + κ) b) (VprO C (V + κ) b') =
      FCO C (VprO C V b) (VprO C V b') := by
    intro b b'
    rw [VprO_addc C V hκ, VprO_addc C V hκ, FCO_add_cst_left C (hκ b).he,
      FCO_add_cst_right C (hκ b').he]
  unfold kapO
  simp only [h1, h2, SCorO_addc j C V hκ, GO_addc C V hκ]

theorem JhO_addc (hκ : ∀ b, IsCstObs (κ b)) :
    JhO j C (V + κ) = JhO j C V := by
  funext c' U; unfold JhO; simp only [kapO_addc j C V hκ]

theorem IbO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    IbO (V + κ) W b = oexp (-κ b) * IbO V W b := by
  rw [IbO, IbO, Pi.add_apply, neg_add, oexp_add_right_obs _ (hκ b).neg.hb]; ring

theorem IpO_addc (hκ : ∀ b, IsCstObs (κ b)) (b : Fin d → ℕ) :
    IpO P j C (V + κ) W K b = oexp (-κ b) * IpO P j C V W K b := by
  rw [IpO, IpO, upB_addc P j C V W K hκ, upO_addc P j C V W K hκ, GpO_addc P j C V W K hκ,
    expU, expU, neg_add, oexp_add_right_obs _ (hκ b).neg.hb, Algebra.smul_def, Algebra.smul_def]
  ring

theorem gdIO_scale {ζ : OFam c d L N} (hζ : ∀ b, epsO (ζ b) = ζ b) (Ib Ip : OFam c d L N)
    (b : Fin d → ℕ) :
    gdIO (fun b => ζ b * Ib b) (fun b => ζ b * Ip b) b = inclO (ζ b) * gdIO Ib Ip b := by
  rw [gdIO, gdIO, map_mul, map_mul, thetaO_cst (hζ b), mul_sub]

end Map

section Knext

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}
variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam c d L N) {κ : OFam c d L N}

/-- **With `K = 0`, `K_{j+1}` does not see the constants**: the factors `e^{−κ(B)}` cancel
against the normalisation. -/
theorem Knext2O_addc (hκ : ∀ b, IsCstObs (κ b)) (U : Finset (Lam d L N)) :
    Knext2O P j C (V + κ) W 0 U = Knext2O P j C V W 0 U := by
  classical
  set ζ : OFam c d L N := fun b => oexp (-κ b) with hζd
  have hζ : ∀ b, epsO (ζ b) = ζ b := fun b => epsO_oexp_obs (hκ b).neg.he (hκ b).neg.hb
  have hIb : IbO (V + κ) W = fun b => ζ b * IbO V W b := funext fun b => IbO_addc V W hκ b
  have hIp : IpO P j C (V + κ) W 0 = fun b => ζ b * IpO P j C V W 0 b :=
    funext fun b => IpO_addc P j C V W 0 hκ b
  have hg : gKnextO j C (IbO (V + κ) W) (IpO P j C (V + κ) W 0) 0 (J2O P j 0) U =
      (∏ b ∈ blocks j U, ζ b) *
        gKnextO j C (IbO V W) (IpO P j C V W 0) 0 (J2O P j 0) U := by
    rw [gKnextO_zero P j _ _ C U, gKnextO_zero P j _ _ C U, mul_sum, hIb, hIp]
    refine sum_congr rfl fun X hX => ?_
    obtain ⟨hXP, hcl⟩ := mem_filter.1 hX
    have hXp : IsPolymer j X := (mem_Pj.1 hXP).2
    have hUp : IsPolymer j U := by rw [← hcl]; exact IsPolymer.of_succ (isPolymer_clo j X)
    have hXU : X ⊆ U := by rw [← hcl]; exact subset_clo j X
    have hpow : gdIPowO j (fun b => ζ b * IbO V W b) (fun b => ζ b * IpO P j C V W 0 b) X =
        inclO (∏ b ∈ blocks j X, ζ b) * gdIPowO j (IbO V W) (IpO P j C V W 0) X := by
      rw [gdIPowO, gdIPowO, map_prod, ← prod_mul_distrib]
      exact prod_congr rfl fun b _ => gdIO_scale hζ _ _ b
    have hbp : bpowO j (fun b => ζ b * IpO P j C V W 0 b) (U \ X) =
        (∏ b ∈ blocks j (U \ X), ζ b) * bpowO j (IpO P j C V W 0) (U \ X) := by
      rw [bpowO, bpowO, prod_mul_distrib]
    have hsplit : ∏ b ∈ blocks j U, ζ b =
        (∏ b ∈ blocks j (U \ X), ζ b) * ∏ b ∈ blocks j X, ζ b := by
      conv_lhs => rw [← sdiff_union_of_subset hXU]
      exact prod_blocks_union ζ (IsPolymer.sdiff hUp hXp) hXp sdiff_disjoint
    rw [hpow, hbp, ECCO_inclO_mul, hsplit]
    ring
  have hu : uXO P j C (V + κ) W 0 U = uXO P j C V W 0 U + ∑ b ∈ blocks j U, κ b := by
    rw [uXO, uXO, ← sum_add_distrib]
    exact sum_congr rfl fun b _ => upO_addc P j C V W 0 hκ b
  have huB : uXB P j C (V + κ) W 0 U = uXB P j C V W 0 U := by
    rw [uXB, uXB]; exact sum_congr rfl fun b _ => upB_addc P j C V W 0 hκ b
  have hS := IsCstObs.sum (blocks j U) hκ
  have hprod : ∏ b ∈ blocks j U, ζ b = oexp (-∑ b ∈ blocks j U, κ b) := by
    rw [prod_oexp_obs _ _ fun b _ => (hκ b).neg.hb, sum_neg_distrib]
  have hcancel : oexp (∑ b ∈ blocks j U, κ b) * oexp (-∑ b ∈ blocks j U, κ b) = 1 := by
    rw [← oexp_add_right_obs _ hS.neg.hb, add_neg_cancel, oexp_zero]
  rw [Knext2O, Knext2O, hg, hu, huB, expU, expU, oexp_add_right_obs _ hS.hb, hprod]
  calc Complex.exp (uXB P j C V W 0 U) • (oexp (uXO P j C V W 0 U) *
          oexp (∑ b ∈ blocks j U, κ b)) *
        (oexp (-∑ b ∈ blocks j U, κ b) * gKnextO j C (IbO V W) (IpO P j C V W 0) 0 (J2O P j 0) U)
      = Complex.exp (uXB P j C V W 0 U) • oexp (uXO P j C V W 0 U) *
          (oexp (∑ b ∈ blocks j U, κ b) * oexp (-∑ b ∈ blocks j U, κ b)) *
          gKnextO j C (IbO V W) (IpO P j C V W 0) 0 (J2O P j 0) U := by
        rw [Algebra.smul_def, Algebra.smul_def]; ring
    _ = _ := by rw [hcancel, mul_one]

theorem KnewO_addc (hκ : ∀ b, IsCstObs (κ b)) (U : Finset (Lam d L N)) :
    KnewO P j C (V + κ) W 0 U = KnewO P j C V W 0 U := by
  rw [KnewO, KnewO, Knext2O_addc P j C V W hκ, GpO_addc P j C V W 0 hκ, K2O_addc j C V hκ]

/-- **With `K = 0`, `K_{j+1}` does not see the constants.** -/
theorem KplusO_addc (hκ : ∀ b, IsCstObs (κ b)) :
    KplusO P j C (V + κ) W 0 = KplusO P j C V W 0 := by
  have h : KnewO P j C (V + κ) W 0 = KnewO P j C V W 0 :=
    funext fun U => KnewO_addc P j C V W hκ U
  rw [KplusO, KplusO, ItO_addc P j C V W 0 hκ, h, JhO_addc j C V hκ]

theorem wProdX_addc (hκ : ∀ b, IsCstObs (κ b)) (m : Alg d L N →ₗ[ℂ] ℂ)
    (X : Finset (Lam d L N)) (Γ : Matrix (Lam d L N) (Lam d L N) ℂ) :
    wProdX P j C (V + κ) W m X Γ = wProdX P j C V W m X Γ := by
  unfold wProdX
  simp only [Wnext2O_addc P j C V W hκ, WpO_addc P j C V W hκ]

end Knext

end

end Obs2
