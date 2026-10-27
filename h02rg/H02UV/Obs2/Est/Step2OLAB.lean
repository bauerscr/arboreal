import Obs2.Est.Step2OL
import Obs2.Est.Step2OAB
import Obs2.Est.BlockOAB6

/-!
# The second-order step on the `σ_aσ_b` sector, output regulator `λA` (`ab` copy of `Obs2.Est.Step2OL`)

**`step2O_tsLAB`**: `step2O_tsAB` with output regulator `λA`, from `Llin2O_ab_boundL` and
`Knext2O_crudeLAB`. Input of the reblocking estimate `stepKO_tsAB`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

set_option maxHeartbeats 1000000 in
/-- **Theorem `step2` with sources**, output regulator `λA`. -/
theorem step2O_tsLAB (d : ℕ) (hd : 2 ≤ d) : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∀ lam : ℝ, 1 ≤ lam → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (N j : ℕ), j + 1 < N → ∀ ℓ ℓ' ℓC : ℝ, 0 < ℓ → 0 < ℓ' → 0 < ℓC → ℓ' + ℓC ≤ 2 * ℓ →
    ∀ C : Matrix (Lam d L N) (Lam d L N) ℂ, GoodCov2 j ℓC C →
    ∀ (c : Obs.Case) (P : ObsPts d L N) (w : Wt), w.Sub → w.a ≠ ⊤ → w.b ≠ ⊤ → w.ab ≠ ⊤ →
    ∀ (V W : OFam c d L N) (K : OAct c d L N),
      (∀ b, V b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ b, W b ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) →
      (∀ X, IsConn j X → K X ∈ (anc P X : Subalgebra ℂ (OE c (Lam d L N)))) →
      InF j (bulkF V) → InF j (bulkF W) →
      (∀ b, ε ((bulkF V b : EvR (Lam d L N)) : Alg d L N) = 0) → InK2 j (bulkF K) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (V b : SA c (Lam d L N))) →
      (∀ b, CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
        (W b : SA c (Lam d L N))) →
      (∀ X, IsConn j X → CmpInA (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))) →
      (∀ X, IsConn j X → IsSymS (K X : SA c (Lam d L N))) →
      ∀ g : ℝ, 0 ≤ g → g ≤ ε₀ →
      Fnorm j ℓ (bulkF V) ≤ ENNReal.ofReal g → Fnorm j ℓ (bulkF W) ≤ ENNReal.ofReal (g ^ 2) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal g) →
      (∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal (g ^ 2)) →
      ∀ k : ℝ, 0 ≤ k → k ≤ ε₀ →
      Knorm j ℓ A (bulkF K) ≤ ENNReal.ofReal k →
      (∀ X, IsConn j X →
        ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (K X) ≤ ENNReal.ofReal k) →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        ENNReal.ofReal ((lam * A) ^ (nb (j + 1) U - 2 ^ d)) *
          oTj d L w (j + 1) ℓ' ((Knext2O P j C V W K U - K2O j C V U : OE c (Lam d L N)) :
            SA c (Lam d L N)) ≤
          ENNReal.ofReal (C₀ * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-η)) * k) +
          ENNReal.ofReal (C₁ * (g ^ 3 + g * k + k ^ 2)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cb, ηb, Lb, hCb, hηb, hLb⟩ := Llin2_boundL d hd
  obtain ⟨Co, ηo, Lo, hCo, hηo, hLo⟩ := Llin2O_ab_boundL d hd
  obtain ⟨Lc, hLc⟩ := Knext2O_crudeLAB d hd1
  refine ⟨Cb + Co, min ηb ηo, max (max Lb Lo) (max Lc 1), by positivity, lt_min hηb hηo, ?_⟩
  intro L _ hL lam hlam
  have hLb' : Lb ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLo' : Lo ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLc' : Lc ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  obtain ⟨A₁, hA₁, hA₁'⟩ := hLb L hLb' lam hlam
  obtain ⟨A₂, hA₂, hA₂'⟩ := hLo L hLo' lam hlam
  obtain ⟨A₃, hA₃, hA₃'⟩ := hLc L hLc' lam hlam
  refine ⟨max A₁ (max A₂ A₃), le_trans hA₁ (le_max_left _ _), ?_⟩
  intro A hA
  have hAA₁ : A₁ ≤ A := le_trans (le_max_left _ _) hA
  have hAA₂ : A₂ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hAA₃ : A₃ ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hA1 : 1 ≤ A := le_trans hA₁ hAA₁
  have hA0 : 0 < A := by linarith
  obtain ⟨r₀, hr₀, hcr⟩ := hA₃' A hAA₃
  set ρ := min r₀ 1 with hρdef
  have hρ0 : 0 < ρ := lt_min hr₀ one_pos
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hρr : ρ ≤ r₀ := min_le_left _ _
  refine ⟨ρ, 4 * (4 / ρ ^ 3), hρ0, by positivity, ?_⟩
  intro N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw hwa hwb hwab V W K hVab hWab hKab hKanc hV hW hV0 hK
    hlocV hlocW hlocK hsym g hg0 hgρ hVg hWg hVo hWo k hk0 hkρ hKk hKo U hU
  have hUne : U.Nonempty := hU.2.1
  have hV0' : ∀ b, ε ((V b : SA c (Lam d L N)).e) = 0 := hV0
  -- the two-parameter family
  set F : ℂ → ℂ → OE c (Lam d L N) := fun t s => Knext2O P j C (VtO V t) (WtO W t) (s • K) U
    with hF
  have hVt0 : ∀ t b, ε ((VtO V t b : SA c (Lam d L N)).e) = 0 := fun t b => by
    rw [VtO, eps_e_smul, hV0', mul_zero]
  have hF1 : ∀ s, HolW (fun t => F t s) := fun s =>
    Knext2O_holW (E := ℂ) P j C (Vf := fun t => VtO V t) (Wf := fun t => WtO W t)
      (Kf := fun _ => s • K)
      (fun b => HolW.smul differentiable_id (HolW.const _))
      (fun b => HolW.smul (differentiable_id.pow 2) (HolW.const _))
      (fun X => HolW.const _) hVt0 U
  have hF2 : ∀ t, HolW (fun s => F t s) := fun t =>
    Knext2O_holW (E := ℂ) P j C (Vf := fun _ => VtO V t) (Wf := fun _ => WtO W t)
      (Kf := fun s => s • K) (fun b => HolW.const _) (fun b => HolW.const _)
      (fun X => HolW.smul differentiable_id (HolW.const _)) (fun _ b => hVt0 t b) U
  -- the crude bound on the polydisc
  set wt : ℝ := (lam * A) ^ (nb (j + 1) U - 2 ^ d) with hwt
  have hwt0 : 0 ≤ wt := pow_nonneg (by positivity) _
  have hball : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
      ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ →
        ENNReal.ofReal wt * oTj d L w (j + 1) ℓ' (F t s : SA c (Lam d L N)) ≤ ENNReal.ofReal 1 := by
    intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
    have hR₁0 : 0 ≤ R₁ := by linarith
    have hRg : (R₁ * g) ^ 2 ≤ ρ := by
      have : 0 ≤ R₁ * g := by positivity
      nlinarith
    have ht2 : ENNReal.ofReal ‖t‖ * ENNReal.ofReal g ≤ ENNReal.ofReal r₀ := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hR₁g.trans hρr))
      exact mul_le_mul_of_nonneg_right ht hg0
    have htt : ENNReal.ofReal (‖t‖ ^ 2) * ENNReal.ofReal (g ^ 2) ≤ ENNReal.ofReal r₀ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hRg.trans hρr))
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right ht hg0) 2
    have hss : ENNReal.ofReal ‖s‖ * ENNReal.ofReal k ≤ ENNReal.ofReal r₀ := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hR₂k.trans hρr))
      exact mul_le_mul_of_nonneg_right hs hk0
    refine hcr N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w hw (VtO V t) (WtO W t) (s • K)
      (fun b => Subalgebra.smul_mem _ (hVab b) t) (fun b => Subalgebra.smul_mem _ (hWab b) (t ^ 2))
      (fun X hX => Subalgebra.smul_mem _ (hKab X hX) s)
      (by rw [bulkF_VtO]; exact hV.smul t) (by rw [bulkF_WtO]; exact hW.smul (t ^ 2))
      (by
        rw [bulkF_VtO]; intro b
        rw [Subalgebra.coe_smul, map_smul, hV0, smul_zero])
      (by rw [bulkF_smulK]; exact hK.smul s)
      (by
        rw [bulkF_VtO, Fnorm_smul]
        exact (mul_le_mul_left' hVg _).trans ht2)
      (by
        rw [bulkF_WtO, Fnorm_smul, norm_pow]
        exact (mul_le_mul_left' hWg _).trans htt)
      (by
        rw [bulkF_smulK, Knorm_smul]
        exact (mul_le_mul_left' hKk _).trans hss)
      (fun b => (hlocV b).smul t) (fun b => (hlocW b).smul (t ^ 2))
      (fun X hX => (hlocK X hX).smul s)
      (fun b hb => by
        show oTo w j ℓ (t • V b) ≤ _
        rw [oTo_smul]; exact (mul_le_mul_left' (hVo b hb) _).trans ht2)
      (fun b hb => by
        show oTo w j ℓ (t ^ 2 • W b) ≤ _
        rw [oTo_smul, norm_pow]; exact (mul_le_mul_left' (hWo b hb) _).trans htt)
      (fun X hX => by
        show ENNReal.ofReal (A ^ (nb j X - 2 ^ d)) * oTo w j ℓ (s • K X) ≤ _
        rw [oTo_smul, mul_left_comm]
        exact (mul_le_mul_left' (hKo X hX) _).trans hss)
      U hU
  -- the expansions
  have hexp : ExpW2 (fun t => F t 0) 0 0 (K2O j C V U) := by
    refine (Knext2O_expansion P j C W hV0' hUne).congr fun t => ?_
    simp only [hF, zero_smul]
  have hlin : ExpW1 (fun s => F 0 s) 0 (Llin2O P j C K U) := by
    refine (Knext2O_lin P j C K hUne).congr fun s => ?_
    simp only [hF, VtO_zero, WtO_zero]
  have hF00 : F 0 0 = 0 := by
    obtain ⟨q, -, e⟩ := hlin
    have := e 0
    simpa using this
  have e11 : F 1 1 = Knext2O P j C V W K U := by simp only [hF, VtO_one, WtO_one, one_smul]
  -- the remainder `R = K_{j+1} - K^{(2)} - 𝓛(K)`, componentwise
  set B : ℝ := 4 / ρ ^ 3 * (g ^ 3 + g * k + k ^ 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set R := Knext2O P j C V W K U - K2O j C V U - Llin2O P j C K U with hR
  have hcomp : ∀ (π : SA c (Lam d L N) →ₗ[ℂ] Alg d L N) (m : ℝ≥0∞), m ≠ ⊤ →
      (∀ G : OE c (Lam d L N), m * Tj d (L : ℝ) (j + 1) ℓ' (π (G : SA c (Lam d L N))) ≤
        ENNReal.ofReal wt * oTj d L w (j + 1) ℓ' (G : SA c (Lam d L N))) →
      m * Tj d (L : ℝ) (j + 1) ℓ' (π (R : SA c (Lam d L N))) ≤ ENNReal.ofReal B := by
    intro π m hm hπ
    refine wT_le_of_pair hm hB0 fun g' hg' => ?_
    set Λw := cpairL π m.toReal g' with hΛw
    have hpb : ∀ R₁ : ℝ, 1 ≤ R₁ → R₁ * g ≤ ρ → ∀ R₂ : ℝ, 1 ≤ R₂ → R₂ * k ≤ ρ →
        ∀ t s : ℂ, ‖t‖ ≤ R₁ → ‖s‖ ≤ R₂ → ‖Λw (F t s)‖ ≤ 1 := by
      intro R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs
      rw [hΛw, norm_cpairL π ENNReal.toReal_nonneg]
      exact pair_le_of_wT hm zero_le_one
        ((hπ (F t s)).trans (hball R₁ hR₁ hR₁g R₂ hR₂ hR₂k t s ht hs)) hg'
    have h := cauchy_assemble hF1 hF2 hexp hlin hF00 Λw hρ0 hρ1 hg0 hgρ hk0 hkρ hpb
    rw [e11, ← map_sub, ← map_sub, hΛw, norm_cpairL π ENNReal.toReal_nonneg] at h
    exact h
  have hRe := hcomp eL (ENNReal.ofReal wt) ENNReal.ofReal_ne_top fun G => by
    rw [oTj_eq4]
    exact mul_le_mul_left' (le_add_right (le_add_right (le_add_right le_rfl))) _
  have hRa := hcomp aL (ENNReal.ofReal wt * w.a) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwa)
    fun G => by
      rw [oTj_eq4, mul_assoc]
      exact mul_le_mul_left' (le_add_right (le_add_right le_add_self)) _
  have hRb := hcomp bL (ENNReal.ofReal wt * w.b) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwb)
    fun G => by
      rw [oTj_eq4, mul_assoc]
      exact mul_le_mul_left' (le_add_right le_add_self) _
  have hRab := hcomp abL (ENNReal.ofReal wt * w.ab)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwab) fun G => by
      rw [oTj_eq4, mul_assoc]
      exact mul_le_mul_left' le_add_self _
  have hRtot : ENNReal.ofReal wt * oTj d L w (j + 1) ℓ' (R : SA c (Lam d L N)) ≤
      ENNReal.ofReal (4 * (4 / ρ ^ 3) * (g ^ 3 + g * k + k ^ 2)) := by
    rw [oTj_eq4, mul_add, mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    refine (add_le_add (add_le_add (add_le_add hRe hRa) hRb) hRab).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add hB0 hB0, ← ENNReal.ofReal_add (by positivity) hB0,
      ← ENNReal.ofReal_add (by positivity) hB0, hBdef]
    congr 1; ring
  -- the linear part
  have hLe : ENNReal.ofReal wt * Tj d (L : ℝ) (j + 1) ℓ'
      (Llin2O P j C K U : SA c (Lam d L N)).e ≤
        ENNReal.ofReal (Cb * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-ηb))) * ENNReal.ofReal k := by
    have h := hA₁' A hAA₁ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC (bulkF K) hK U hU
    rw [← bulk_Llin2O P hjN C K U] at h
    exact h.trans (mul_le_mul_left' hKk _)
  have hLo0 := hA₂' A hAA₂ N j hjN ℓ ℓ' ℓC hℓ hℓ' hℓC hsum C hC c P w (KconnO j K)
    (KconnO_mem_ab hKab) (fun X hX => by rw [KconnO_of_conn hX]; exact hKanc X hX)
    (fun X hX => by rw [KconnO_of_conn hX]; exact (hlocK X hX).ab)
    (fun X hX => by rw [KconnO_of_conn hX]; exact hsym X hX) (ENNReal.ofReal k)
    (fun X hX => by rw [KconnO_of_conn hX]; exact hKo X hX) U hU
  have hLo : ENNReal.ofReal wt * oTo w (j + 1) ℓ' (Llin2O P j C K U) ≤
      ENNReal.ofReal (Co * ((L : ℝ)⁻¹ + A ^ (-ηo))) * ENNReal.ofReal k := by
    rw [Llin2O_KconnO P hjN C K U]; exact hLo0
  have hLtot : ENNReal.ofReal wt * oTj d L w (j + 1) ℓ' (Llin2O P j C K U : SA c (Lam d L N)) ≤
      ENNReal.ofReal ((Cb + Co) * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-min ηb ηo)) * k) := by
    rw [oTj_eq_bulk_add, mul_add]
    refine (add_le_add hLe hLo).trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hk0)
    have hL1 : (1 : ℝ) ≤ L := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    have hL0 : (0 : ℝ) < L := by linarith
    have hx : (L : ℝ)⁻¹ ≤ (L : ℝ) ^ d / (L : ℝ) ^ 3 := by
      have h2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
      calc (L : ℝ)⁻¹ = (L : ℝ) ^ 2 / (L : ℝ) ^ 3 := by field_simp
        _ ≤ (L : ℝ) ^ d / (L : ℝ) ^ 3 := div_le_div_of_nonneg_right h2 (by positivity)
    have hb : A ^ (-ηb) ≤ A ^ (-min ηb ηo) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_left _ _))
    have ho : A ^ (-ηo) ≤ A ^ (-min ηb ηo) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_right _ _))
    calc Cb * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-ηb)) + Co * ((L : ℝ)⁻¹ + A ^ (-ηo))
        = Cb * ((L : ℝ) ^ d / (L : ℝ) ^ 3) + Cb * A ^ (-ηb) + (Co * (L : ℝ)⁻¹ + Co * A ^ (-ηo)) := by
          ring
      _ ≤ Cb * ((L : ℝ) ^ d / (L : ℝ) ^ 3) + Cb * A ^ (-min ηb ηo) +
          (Co * ((L : ℝ) ^ d / (L : ℝ) ^ 3) + Co * A ^ (-min ηb ηo)) := by
          gcongr
      _ = (Cb + Co) * ((L : ℝ) ^ d / (L : ℝ) ^ 3 + A ^ (-min ηb ηo)) := by ring
  -- assemble
  have hdec : Knext2O P j C V W K U - K2O j C V U = Llin2O P j C K U + R := by rw [hR]; abel
  rw [hdec]
  refine (mul_le_mul_left' (oT_add_le _ _) _).trans ?_
  rw [mul_add]
  exact add_le_add hLtot hRtot

end

end Obs2
