import Ward.Conn4pt
import FRD.LatticeSum

/-!
# Lemma `cor:aNlimit`: `λθ = 1`

For real `b ∈ (0, b̄]`: `λ θ = 1` with `λ = lamInf`, `θ = 1 - c₀² γ` (`cor_aNlimit_of`).

Proof (as in `h02rg.tex`): with `w_N = c₀²/(|Λ_N| ã_{N,N})`,
* `θ = λ w_N (1 + E_N)`, `E_N = O(b L^{-κ₁N})` (`cor:anm0`);
* `𝔼|T_0|/|Λ_N| = w_N (1 + O(b L^{-κN})) + O(b L^{-(d-2)N})` (`cor:macro`);
* `𝔼|T_0|/|Λ_N| = |Λ_N|^{-1} ∑_x P[0 ↔ x] → θ²` (summing `cor:conn4pt`, with the lattice sums
  `|Λ_N|^{-1} ∑_{x ≠ 0} |x|^{-s} = O(L^{-sN})`, `0 < s < d`, `FRD.latticeSum_le`).
Hence `w_N → θ²` and `θ = λ θ²`, and `θ ≠ 0`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

theorem tendsto_card_inv (hd1 : 1 ≤ d) (hL2 : 2 ≤ L) :
    Tendsto (fun N : ℕ => (Fintype.card (Lam d L N) : ℝ)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_mul (L := L) hL2 (s := (d : ℝ)) (by exact_mod_cast hd1)
  refine h.congr fun N => ?_
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  rw [Suscept.card_lam, Nat.cast_pow, ← pow_mul, Real.rpow_neg hL0.le, ← Real.rpow_natCast]
  congr 2; push_cast; ring

set_option maxHeartbeats 16000000 in
/-- **`cor:aNlimit`**: `λ θ = 1`. -/
theorem cor_aNlimit_of (hd : 3 ≤ d) (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ∃ bbar : ℝ, 0 < bbar ∧ ∀ b, 0 < b → b ≤ bbar →
      lamInf d L V₀c lbar b * (1 - c2F V₀c b 0 * gamInf d L V₀c lbar b) = 1 := by
  have HF := HW.toFlowData
  have hd1 : 1 ≤ d := by omega
  have hL2 := HF.hL2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hκ := HF.κ_pos
  have hC := HF.C_nonneg
  obtain ⟨bm, Cm, hbm, -, hCm, -, hmac⟩ := cor_macro_of hd HW
  obtain ⟨ba, Ca, hba, -, -, hCa, -, hanm⟩ := cor_anm0_of hd HW hLodd
  obtain ⟨bc, Cc, KΓ, hbc, hbc2, hbc1, hCc, hper, hconn⟩ := cor_conn4pt_of hd HW hLodd
  obtain ⟨C₁, hC₁, hls1⟩ := FRD.latticeSum_le (d := d) (s := (d : ℝ) - 2)
    (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith) (by linarith)
  have hκ₁ : 0 < min κ 1 := lt_min hκ one_pos
  obtain ⟨C₂, hC₂, hls2⟩ := FRD.latticeSum_le (d := d) (s := (d : ℝ) - 2 + min κ 1)
    (by have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith)
    (by have := min_le_right κ 1; linarith)
  obtain ⟨Cg, hCg0, hCg⟩ := FRD.greenZd_bound_supNorm hd
  have hKΓ0 : 0 ≤ KΓ := by
    obtain ⟨x, hx⟩ := exists_ne_zero_lam hd1 hL2 (by norm_num : 1 ≤ 2)
    exact (abs_nonneg _).trans (hconn 2 le_rfl (bc / 2) (by positivity) (by linarith) x hx).1
  set bbar := min (min bm ba) (min bc (min (1 / (4 * KΓ + 4)) (1 / (4 * C + 4)))) with hbbar
  have hb1 : bbar ≤ bm := (min_le_left _ _).trans (min_le_left _ _)
  have hb2 : bbar ≤ ba := (min_le_left _ _).trans (min_le_right _ _)
  have hb3 : bbar ≤ bc := (min_le_right _ _).trans (min_le_left _ _)
  have hb4 : bbar ≤ 1 / (4 * KΓ + 4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb5 : bbar ≤ 1 / (4 * C + 4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbpos : 0 < bbar := lt_min (lt_min hbm hba) (lt_min hbc (lt_min (by positivity)
    (by positivity)))
  refine ⟨bbar, hbpos, fun b hb hbb => ?_⟩
  have hbl : b ≤ lbar := by linarith
  have hb1' : b ≤ 1 := (hbb.trans hb3).trans hbc1
  have h4C : (4 * C + 4) * b ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hbb.trans hb5) (by positivity : (0 : ℝ) ≤ 4 * C + 4)
    rwa [mul_one_div_cancel (by positivity)] at this
  have h4K : (4 * KΓ + 4) * b ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hbb.trans hb4) (by positivity : (0 : ℝ) ≤ 4 * KΓ + 4)
    rwa [mul_one_div_cancel (by positivity)] at this
  -- notation
  set c := c2F V₀c b 0 with hc
  set γ := gamInf d L V₀c lbar b with hγdef
  set lam := lamInf d L V₀c lbar b with hlam
  set θ := 1 - c * γ with hθ
  have hs := abs_s0R_le HF hb.le hbl le_rfl
  have hsb : -(1 / 2) ≤ s0R V₀c b 0 ∧ s0R V₀c b 0 ≤ 1 / 2 := by
    constructor <;> nlinarith [(abs_le.1 hs).1, (abs_le.1 hs).2]
  have hc0 : 0 < c := c2F_pos hb (by linarith [hsb.1])
  have hcb : c ≤ 2 * b := by
    rw [hc]; unfold c2F; rw [div_le_iff₀ (by linarith [hsb.1])]; nlinarith [hsb.1]
  have hγ : |γ| ≤ KΓ := by
    obtain ⟨x, hx⟩ := exists_ne_zero_lam hd1 hL2 (by norm_num : 1 ≤ 2)
    exact (hconn 2 le_rfl b hb (hbb.trans hb3) x hx).1
  have hθ2 : 1 / 2 ≤ θ := by
    have h1 : c * γ ≤ c * |γ| := mul_le_mul_of_nonneg_left (le_abs_self γ) hc0.le
    have h2 : c * |γ| ≤ 2 * b * KΓ :=
      mul_le_mul hcb hγ (abs_nonneg _) (by linarith)
    nlinarith
  -- the sequences
  have hdata : ∀ N : ℕ, ∃ E₁ E₂ E₃ : ℝ, 2 ≤ N →
      0 < atR d L V₀c N b ∧ |E₁| ≤ Cm * b * (L : ℝ) ^ (-(κ * N)) ∧
      |E₂| ≤ Cm * b * (L : ℝ) ^ (2 * N) ∧
      H02.expTree (nnW d L N (betaF V₀c b 0)) (nnW_symm _) 0 = c * (1 + E₁) / atR d L V₀c N b + E₂ ∧
      |E₃| ≤ Ca * b * (L : ℝ) ^ (-(min κ 1 * N)) ∧
      1 = c * (γ + lam / (Fintype.card (Lam d L N) * atR d L V₀c N b) * (1 + E₃)) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨ha, ⟨E₁, E₂, h1, h2, h3⟩, -⟩ := hmac N (by omega) b hb (hbb.trans hb1)
      obtain ⟨-, -, E₃, h4, h5⟩ := hanm N hN b hb (hbb.trans hb2)
      exact ⟨E₁, E₂, E₃, fun _ => ⟨ha, h1, h2, h3, h4, h5⟩⟩
    · exact ⟨0, 0, 0, fun h => absurd h hN⟩
  choose E₁ E₂ E₃ hE using hdata
  set card := fun N : ℕ => (Fintype.card (Lam d L N) : ℝ) with hcard
  set w := fun N : ℕ => c / (card N * atR d L V₀c N b) with hw
  set T := fun N : ℕ => H02.expTree (nnW d L N (betaF V₀c b 0)) (nnW_symm _) 0 with hT
  have hcard0 : ∀ N, 0 < card N := fun N => Suscept.card_lam_pos N
  -- `θ = λ w_N (1 + E₃)`
  have hθw : ∀ N, 2 ≤ N → θ = lam * w N * (1 + E₃ N) := by
    intro N hN
    obtain ⟨ha, -, -, -, -, hid⟩ := hE N hN
    have hM : card N * atR d L V₀c N b ≠ 0 := (mul_pos (hcard0 N) ha).ne'
    rw [hθ, hw]
    simp only
    linear_combination hid
  -- `T_N/|Λ_N| = w_N (1 + E₁) + E₂/|Λ_N|`
  have hTw : ∀ N, 2 ≤ N → T N / card N = w N * (1 + E₁ N) + E₂ N / card N := by
    intro N hN
    obtain ⟨ha, -, -, h3, -, -⟩ := hE N hN
    rw [hT, hw]; simp only; rw [h3]
    field_simp
  -- the limits of the errors
  have tL := fun {s : ℝ} (hs : 0 < s) => tendsto_rpow_neg_mul (L := L) hL2 hs
  have hE₁T : Tendsto E₁ atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tL hκ).const_mul (Cm * b); rw [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ this
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs]; exact (hE N hN).2.1
  have hE₃T : Tendsto E₃ atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tL hκ₁).const_mul (Ca * b); rw [mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ this
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs]; exact (hE N hN).2.2.2.2.1
  have hE₂T : Tendsto (fun N => E₂ N / card N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tL (s := (d : ℝ) - 2) (by
      have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith)).const_mul (Cm * b)
    rw [mul_zero] at h
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hcard0 N), div_le_iff₀ (hcard0 N)]
    have key : (L : ℝ) ^ (2 * N) / card N = (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) := by
      rw [hcard]; simp only; rw [Suscept.card_lam]; push_cast
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hL0]
      congr 1; push_cast; ring
    calc |E₂ N| ≤ Cm * b * (L : ℝ) ^ (2 * N) := (hE N hN).2.2.1
      _ = Cm * b * ((L : ℝ) ^ (2 * N) / card N) * card N := by
          have := (hcard0 N).ne'; field_simp
      _ = Cm * b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) * card N := by rw [key]
  -- `T_N/|Λ_N| → θ²`
  have hTT : Tendsto (fun N => T N / card N) atTop (𝓝 (θ ^ 2)) := by
    set B := fun N : ℕ => |1 - θ ^ 2| * (card N)⁻¹ +
      2 * c * |lam * θ| * Cg * (C₁ * (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) +
      Cc * b ^ 2 * (C₂ * (L : ℝ) ^ (-(((d : ℝ) - 2 + min κ 1) * N))) +
      Cc * (b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) with hB
    have hBT : Tendsto B atTop (𝓝 0) := by
      have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by
        have : (3 : ℝ) ≤ d := (by exact_mod_cast hd); linarith
      have h := (((tendsto_card_inv (L := L) hd1 hL2).const_mul |1 - θ ^ 2|).add
        (((tL hd2).const_mul C₁).const_mul (2 * c * |lam * θ| * Cg))).add
        (((tL (by linarith : (0 : ℝ) < (d : ℝ) - 2 + min κ 1)).const_mul C₂).const_mul
          (Cc * b ^ 2)) |>.add
        ((((tL hd2).const_mul b).add ((tL hκ₁).const_mul (b ^ 2))).const_mul Cc)
      simp only [mul_zero, add_zero] at h
      exact h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hBT
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs]
    have hsplit : T N = 1 + ∑ x ∈ univ.filter (fun x : Lam d L N => x ≠ 0),
        H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _) (fun F => F.Reachable 0 x) := by
      have hP0 : H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
          (fun F => F.Reachable (0 : Lam d L N) 0) = 1 := by
        rw [← H02.arborealProb_true (nnW_symm (d := d) (L := L) (N := N) _) (nnW_nonneg (le_of_lt (betaF_pos hb
          (by linarith [hsb.1]))))]
        simp only [SimpleGraph.Reachable.refl]
      rw [hT]; simp only
      rw [H02.expTree_eq_sum, Finset.filter_ne', ← Finset.add_sum_erase _ _ (mem_univ 0), hP0]
    have hcardS : card N = 1 + ((univ.filter (fun x : Lam d L N => x ≠ 0)).card : ℝ) := by
      rw [hcard]; simp only
      rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ]
      have : 1 ≤ Fintype.card (Lam d L N) := Fintype.card_pos
      push_cast [Nat.cast_sub this]; ring
    have hdiff : T N / card N - θ ^ 2 = ((1 - θ ^ 2) +
        ∑ x ∈ univ.filter (fun x : Lam d L N => x ≠ 0),
          (H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
            (fun F => F.Reachable 0 x) - θ ^ 2)) / card N := by
      rw [sub_eq_iff_eq_add, div_add' _ _ _ (hcard0 N).ne', hsplit, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [hcardS]; ring
    rw [hdiff, abs_div, abs_of_pos (hcard0 N), div_le_iff₀ (hcard0 N)]
    -- pointwise bounds
    have hpt : ∀ x ∈ univ.filter (fun x : Lam d L N => x ≠ 0),
        |H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _) (fun F => F.Reachable 0 x) -
          θ ^ 2| ≤ 2 * c * |lam * θ| * Cg * ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2)) +
          Cc * b ^ 2 * ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) +
          Cc * (b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) := by
      intro x hx
      have hx0 : x ≠ 0 := (mem_filter.1 hx).2
      obtain ⟨-, hP⟩ := hconn N hN b hb (hbb.trans hb3) x hx0
      have hrep : rep x ≠ 0 := fun h => hx0 (by rw [← prj_rep x, h]; exact Loc.prj_zero)
      have hG := hCg (rep x) hrep
      rw [supNormZ_rep_eq_supNorm] at hG
      have hG' : |2 * c * lam * θ * greenZd d (rep x)| ≤
          2 * c * |lam * θ| * Cg * ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2)) := by
        rw [show 2 * c * lam * θ * greenZd d (rep x) = (2 * c) * (lam * θ) * greenZd d (rep x) by
          ring, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * c), mul_assoc]
        rw [show 2 * c * |lam * θ| * Cg * ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2)) =
          2 * c * (|lam * θ| * (Cg * ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2)))) by ring]
        gcongr
      have e : H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _) (fun F => F.Reachable 0 x) -
          θ ^ 2 = (H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
            (fun F => F.Reachable 0 x) - (θ ^ 2 + 2 * c * lam * θ * greenZd d (rep x))) +
            2 * c * lam * θ * greenZd d (rep x) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have hP' : |H02.arborealProb (nnW d L N (betaF V₀c b 0)) (nnW_symm _)
          (fun F => F.Reachable 0 x) - (θ ^ 2 + 2 * c * lam * θ * greenZd d (rep x))| ≤
          Cc * (b ^ 2 * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) +
            b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) := hP
      have hmul : Cc * (b ^ 2 * (supNorm x : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) +
            b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) =
          Cc * b ^ 2 * ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) +
          Cc * (b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) + b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) := by
        ring
      linarith
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add le_rfl ((abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpt))).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    have l1 := hls1 L N
    have l2 := hls2 L N
    have hcN := hcard0 N
    have hcardle : ((univ.filter (fun x : Lam d L N => x ≠ 0)).card : ℝ) ≤ card N := by
      rw [hcardS]; linarith
    have hS1 : ∑ x ∈ univ.filter (fun x : Lam d L N => x ≠ 0),
        ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2)) ≤
        card N * (C₁ * (L : ℝ) ^ (-(((d : ℝ) - 2) * N))) := by
      rw [inv_mul_le_iff₀ hcN] at l1; exact l1
    have hS2 : ∑ x ∈ univ.filter (fun x : Lam d L N => x ≠ 0),
        ((supNorm x : ℕ) : ℝ) ^ (-((d : ℝ) - 2 + min κ 1)) ≤
        card N * (C₂ * (L : ℝ) ^ (-(((d : ℝ) - 2 + min κ 1) * N))) := by
      rw [inv_mul_le_iff₀ hcN] at l2; exact l2
    have hq0 : 0 ≤ 2 * c * |lam * θ| * Cg := by positivity
    have hq1 : 0 ≤ Cc * (b * (L : ℝ) ^ (-(((d : ℝ) - 2) * N)) +
        b ^ 2 * (L : ℝ) ^ (-(min κ 1 * N))) := by positivity
    rw [hB]; simp only
    have e1 : |1 - θ ^ 2| * (card N)⁻¹ * card N = |1 - θ ^ 2| := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hS1 hq0, mul_le_mul_of_nonneg_left hS2
      (by positivity : (0 : ℝ) ≤ Cc * b ^ 2), mul_le_mul_of_nonneg_right hcardle hq1]
  -- `w_N → θ²`
  have hwT : Tendsto w atTop (𝓝 (θ ^ 2)) := by
    have h := (hTT.sub hE₂T).div (tendsto_const_nhds.add hE₁T) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    rw [sub_zero, add_zero, div_one] at h
    refine h.congr' ?_
    have habs : Tendsto (fun N => |E₁ N|) atTop (𝓝 0) := by
      simpa using hE₁T.abs
    filter_upwards [eventually_ge_atTop 2, (tendsto_order.1 habs).2 1 (by norm_num)] with N hN hN'
    have hE₁1 : 1 + E₁ N ≠ 0 := by
      intro h0; have := abs_lt.1 hN'; linarith
    show (T N / card N - E₂ N / card N) / (1 + E₁ N) = w N
    rw [hTw N hN]; field_simp; ring
  -- `θ = λ θ²`
  have hlim : Tendsto (fun N => lam * w N * (1 + E₃ N)) atTop (𝓝 (lam * θ ^ 2 * (1 + 0))) :=
    (tendsto_const_nhds.mul hwT).mul (tendsto_const_nhds.add hE₃T)
  have hθθ : θ = lam * θ ^ 2 := by
    rw [add_zero, mul_one] at hlim
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_ge_atTop 2] with N hN using hθw N hN
  have hθ0 : θ ≠ 0 := by linarith
  have : lam * θ * θ = 1 * θ := by rw [one_mul]; nlinarith [hθθ]
  exact mul_right_cancel₀ hθ0 this

end

end Ward
