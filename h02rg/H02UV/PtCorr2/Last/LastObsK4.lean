import PtCorr2.Last.LastObsK3

/-!
# The `σ_a` jets of `F_N` through the reference activity (model level)

**`finG_jet_le`** (last scale `j + 1 = N`, any inputs): with the weighted norm `‖·‖_{α,β}` of
`PtCorr2.Last.LastObsK3` and the jet bounds `∑_B‖JT S(B)‖ ≤ ρ`, `∑_Bα|c2Y(B)_∅| ≤ ρ`,
`∑_Bαβ|c2Y(B)_a| ≤ B`, `‖JT K'(Λ)‖ ≤ κ`, `|∑_Bε(Loc_{Λ,B}S(Λ))_∅| ≤ ρ`, `ρ, κ ≤ 1`:

  `αβ|c2(F_N)_a + ∑_B c2V_N(B)_a| ≤ 60(1 + B)(ρ + κ)`,  `β|ε(F_N)_a| ≤ 60(1 + B)(ρ + κ)`.

(`c2(F_N)_a + ∑_Bc2V_N(B)_a = c2(F_N)_a - ∑_Bm₂V_N(B)_a = c2K_N(Λ)_a` under translation
invariance, `PtCorr2.finO_last_TI`.) The localisation `Loc_{Λ,B}` enters only through
`∑_Bε(Loc_{Λ,B}S(Λ))` and the exact totals `∑_Bε(·)_a`, `∑_Bc2(·)_a` of its `σ_a` part.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Obs.Gen TrivSqZeroExt

variable {L N : ℕ} [NeZero L]

theorem D2_smul_eq (c : ℂ) (z : D2) : c • z = (inl (inl c) : D2) * z := by
  refine TrivSqZeroExt.ext (TrivSqZeroExt.ext ?_ ?_) (TrivSqZeroExt.ext ?_ ?_) <;>
    simp [fst_mul, snd_mul]

section Model

variable (P : ObsPts 2 L N) (j : ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ)
  (V W : OFam .two 2 L N) (K : OAct .two 2 L N)

theorem c2_YpN_a (b : Fin 2 → ℕ) :
    Suscept.c2 ((YpN C V b : SA .two (Lam 2 L N)).a) =
      Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a) := by
  have halg : ((algebraMap ℂ (OE .two (Lam 2 L N)) (upBN C V b) : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
  have hu : (upON C V b : SA .two (Lam 2 L N)).a =
      algebraMap ℂ (Alg 2 L N) (ε (VprO C V b : SA .two (Lam 2 L N)).a) := by
    show cmp true (πobs (epsO (VprO C V b)) : SA .two (Lam 2 L N)) = _
    rw [cmp_πobs]; rfl
  have h1 : (YpN C V b : SA .two (Lam 2 L N)).a =
      (VprO C V b : SA .two (Lam 2 L N)).a -
        ((algebraMap ℂ (OE .two (Lam 2 L N)) (upBN C V b) : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).a - (upON C V b : SA .two (Lam 2 L N)).a := rfl
  rw [h1, halg, hu, sub_zero, PtCorr.c2_sub, Suscept.c2_algebraMap, sub_zero]

theorem c2_VpO_a_last (hj : j + 1 = N) (b : Fin 2 → ℕ) :
    Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a) =
      Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a) -
        Suscept.c2 ((LSO P j C V W b : SA .two (Lam 2 L N)).a) := by
  have halg : ((algebraMap ℂ (OE .two (Lam 2 L N)) (upB P j C V W K b) : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_a _
  have h1 : (VpO P j C V W K b : SA .two (Lam 2 L N)).a =
      (uVpO P j C V W K b : SA .two (Lam 2 L N)).a -
        ((algebraMap ℂ (OE .two (Lam 2 L N)) (upB P j C V W K b) : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).a - (upO P j C V W K b : SA .two (Lam 2 L N)).a := rfl
  have h2 : (uVpO P j C V W K b : SA .two (Lam 2 L N)).a =
      (VprO C V b : SA .two (Lam 2 L N)).a - (EthO C (Q2O P j K b) : SA .two (Lam 2 L N)).a -
        (LSO P j C V W b : SA .two (Lam 2 L N)).a := rfl
  have hQ : (EthO C (Q2O P j K b) : SA .two (Lam 2 L N)).a = 0 := by
    rw [Q2O_last P hj K b]
    show ((EthO C 0 : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = 0
    rw [show EthO C (0 : OE .two (Lam 2 L N)) = 0 from (EthOL C).map_zero]; rfl
  rw [h1, halg, upO_a, h2, hQ, sub_zero, sub_zero, PtCorr.c2_sub, Suscept.c2_algebraMap, sub_zero,
    PtCorr.c2_sub]

set_option maxHeartbeats 4000000 in
/-- **The `σ_a` jets of `F_N` at the last scale.** -/
theorem finG_jet_le (hj : j + 1 = N) {α β ρ κ B : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hS : ∑ b ∈ blockIdx (L := L) (N := N) j, nw α β (JT (SbO j C V W b)) ≤ ρ)
    (hy : ∑ b ∈ blockIdx (L := L) (N := N) j,
      α * ‖Suscept.c2 ((YpN C V b : SA .two (Lam 2 L N)).e)‖ ≤ ρ)
    (hB : ∑ b ∈ blockIdx (L := L) (N := N) j,
      α * β * ‖Suscept.c2 ((VprO C V b : SA .two (Lam 2 L N)).a)‖ ≤ B)
    (hk : nw α β (JT (KNO j C V W K univ)) ≤ κ)
    (hx : ‖∑ b ∈ blockIdx (L := L) (N := N) j, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).e)‖ ≤ ρ)
    (hρ1 : ρ ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    α * β * ‖Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a)‖ ≤
      60 * (1 + B) * (ρ + κ) ∧
    β * ‖ε ((finG P j C V W K : SA .two (Lam 2 L N)).a)‖ ≤ 60 * (1 + B) * (ρ + κ) := by
  classical
  set s := blockIdx (L := L) (N := N) j
  set Y : (Fin 2 → ℕ) → D2 := fun b => JT (YpN C V b)
  set S : (Fin 2 → ℕ) → D2 := fun b => JT (SbO j C V W b)
  set k := JT (KNO j C V W K univ)
  set x : ℂ := -∑ b ∈ s, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).e)
  -- the jet of `F_N`
  have hLa : ∑ b ∈ s, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).a) = ∑ b ∈ s, (S b).snd.fst := by
    have e : ∀ b, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).a) =
        ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).a) := fun b => rfl
    rw [sum_congr rfl fun b _ => e b, eps_total_LS P j C V W]
    exact sum_congr rfl fun b _ => (JT_eps_a _).symm
  have hJ : JT (finG P j C V W K) = (inl (inl (Complex.exp x)) : D2) *
      (1 + inr (inl (-∑ b ∈ s, (S b).snd.fst))) * ((∏ b ∈ s, ((1 - Y b) * (1 + S b))) + k) := by
    rw [finG_eq P j C V W K hj, JT_mul, JT_expU_diff P j C V W K hj, D2_smul_eq, JT_add]
    have hb : bpowO j (GpN j C V W) univ = ∏ b ∈ s, GpN j C V W b := rfl
    rw [hb, JT_prod]
    rw [show ∑ b ∈ blocks (L := L) (N := N) j univ, ε ((LSO P j C V W b : SA .two (Lam 2 L N)).a) =
      ∑ b ∈ s, (S b).snd.fst from hLa]
    congr 2
    exact prod_congr rfl fun b _ => JT_GpN j C V W b
  have hY1 : ∀ b, (Y b).fst.fst = 0 := fun b => JT_fst_fst_of_eps (eps_YpN C V b)
  have hY2 : ∀ b, (Y b).snd.fst = 0 := fun b => JT_snd_fst_of_eps (eps_YpN_a C V b)
  have hy' : ∑ b ∈ s, α * ‖(Y b).fst.snd‖ ≤ ρ := by
    refine le_trans (le_of_eq (sum_congr rfl fun b _ => ?_)) hy
    rw [JT_c2_e]
  have hB' : ∑ b ∈ s, α * β * ‖(Y b).snd.snd‖ ≤ B := by
    refine le_trans (le_of_eq (sum_congr rfl fun b _ => ?_)) hB
    rw [JT_c2_a, c2_YpN_a]
  have hx' : ‖x‖ ≤ ρ := by rw [norm_neg]; exact hx
  have key := jet_main hα hβ s Y S k x hY1 hY2 hS hy' hB' hk hx' hρ1 hκ0 hκ1
  rw [← hJ] at key
  set Z := JT (finG P j C V W K) -
    (1 - ∑ i ∈ s, Y i + ∑ i ∈ s, S i + inr (inl (-∑ i ∈ s, (S i).snd.fst)))
  have hZ11 : Z.snd.snd = Suscept.c2 ((finG P j C V W K : SA .two (Lam 2 L N)).a) +
      ∑ b ∈ s, Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a) := by
    have hLS : ∑ b ∈ s, Suscept.c2 ((LSO P j C V W b : SA .two (Lam 2 L N)).a) =
        ∑ b ∈ s, Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a) := by
      have h := total_W_mass P j C V W mass2L (locMass_two P.a)
      have e : ∀ b, mass2L ((WpO P j C V W b : SA .two (Lam 2 L N)).a) =
          -(Suscept.c2 ((SbO j C V W b : SA .two (Lam 2 L N)).a) -
            Suscept.c2 ((LSO P j C V W b : SA .two (Lam 2 L N)).a)) := fun b => by
        show mass2 _ = _
        rw [mass2_eq_neg_c2]
        congr 1
        exact PtCorr.c2_sub _ _
      rw [sum_congr rfl fun b _ => e b, sum_neg_distrib, neg_eq_zero, sum_sub_distrib,
        sub_eq_zero] at h
      exact h.symm
    have h1 : ∑ b ∈ s, Suscept.c2 ((VpO P j C V W K b : SA .two (Lam 2 L N)).a) =
        ∑ b ∈ s, (Y b).snd.snd - ∑ b ∈ s, (S b).snd.snd := by
      rw [sum_congr rfl fun b _ => c2_VpO_a_last P j C V W K hj b, sum_sub_distrib, hLS]
      congr 1
      · exact sum_congr rfl fun b _ => by rw [JT_c2_a, c2_YpN_a]
      · exact sum_congr rfl fun b _ => by rw [JT_c2_a]
    rw [h1]
    simp only [Z, snd_sub, snd_add, snd_one, snd_inr, snd_sum, sub_zero, zero_sub]
    rw [JT_c2_a]
    simp only [snd_sub, snd_add, snd_neg, snd_sum, snd_zero, snd_inl]
    ring
  have hZ10 : Z.snd.fst = ε ((finG P j C V W K : SA .two (Lam 2 L N)).a) := by
    simp only [Z, snd_sub, snd_add, snd_one, snd_inr, snd_sum, fst_sub, fst_add, fst_neg,
      fst_sum, fst_zero, fst_inl, hY2, JT_eps_a]
    simp
  have hn11 : α * β * ‖Z.snd.snd‖ ≤ nw α β Z := by
    unfold nw
    have := norm_nonneg Z.fst.fst
    have := mul_nonneg hα (norm_nonneg Z.fst.snd)
    have := mul_nonneg hβ (norm_nonneg Z.snd.fst)
    linarith
  have hn10 : β * ‖Z.snd.fst‖ ≤ nw α β Z := by
    unfold nw
    have := norm_nonneg Z.fst.fst
    have := mul_nonneg hα (norm_nonneg Z.fst.snd)
    have := mul_nonneg (mul_nonneg hα hβ) (norm_nonneg Z.snd.snd)
    linarith
  exact ⟨hZ11 ▸ hn11.trans key, hZ10 ▸ hn10.trans key⟩

end Model

end

end PtCorr2
