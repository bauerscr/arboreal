import Step2.Map.Conj2
import Step2.Map.HolC
import FRD.Continuity

/-!
# Continuity in `m²` (Expected result `thm:step-rest`)

* `frdC_continuousAt`: the symbols `Ĉ_k(p)` of the decomposition of `FRD` are continuous in
  `m² > 0`;
* `Gint_continuousAt`: at fixed `ζ`, `Γ^int_{j+1}(p)` is continuous in `m² > 0` wherever the
  denominators of its construction do not vanish (the same rational structure as for
  holomorphy in `ζ`, `DressedFRD.Data.Hol`);
* `Cdr_continuousOn`: the dressed covariance `C'_{j+1}` is continuous in `m² ∈ (0, L^{-2(N-1)}]`;
* `Kplus_continuous_cov`: `K_{j+1}` is a continuous (indeed holomorphic) function of the
  covariance.

So the step map is continuous in `m² > 0`. At `m² = 0` the zero mode of `C_N` is singular.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Set Filter Topology

section Symbols

variable (P : PtFamily) {d n : ℕ} [NeZero n]

theorem wt_Ioc_continuousOn (hd : 1 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (m : Torus d n) :
    ContinuousOn (fun msq => wt P msq (Ioc a b) m) (Ici 0) := by
  obtain ⟨K, hK0, hK⟩ := eval_le_const P
  refine (continuousOn_inv_two_d (fun x hx => hx) hd).mul ?_
  refine continuousOn_integral P (continuousOn_uhat (fun x hx => hx) hd m)
    (fun x hx => uhat_mem hx m) measurableSet_Ioc
    (fun t ht => lt_of_le_of_lt ha ht.1) (B := fun _ => |b| * K)
    (MeasureTheory.integrableOn_const (by simp)) fun msq hmsq t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
  exact mul_le_mul (ht.2.trans (le_abs_self _)) (hK t ht0 _ (uhat_mem hmsq m))
    (P.nonneg t ht0 _ (uhat_mem hmsq m)) (abs_nonneg _)

theorem wt_Ioi_continuousOn (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (m : Torus d n) :
    ContinuousOn (fun msq => wt P msq (Ioi a) m) (Ioi 0) := by
  refine continuousOn_of_Icc_pos fun δ M hδ hδM => ?_
  refine (continuousOn_inv_two_d (fun x hx => hδ.le.trans hx.1) hd).mul ?_
  have hdpos : (0 : ℝ) < 2 * d + M := by have : (0 : ℝ) ≤ d := d.cast_nonneg; linarith
  refine continuousOn_integral_Ioi P (continuousOn_uhat (fun x hx => hδ.le.trans hx.1) hd m)
    (fun x hx => uhat_mem (hδ.le.trans hx.1) m) (div_pos hδ hdpos) (fun x hx => ?_) ha
  unfold uhat
  have h1 : 0 < 2 * (d : ℝ) + x := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith [hx.1]
  rw [div_le_div_iff₀ hdpos h1]
  nlinarith [hx.1, hx.2, lam_nonneg m]

/-- The symbols `Ĉ_k` are continuous in `m² > 0`. -/
theorem frdC_continuousAt (hd : 1 ≤ d) (L N k : ℕ) (m : Torus d n) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun msq => DressedFRD.frdC P (d := d) (n := n) msq L N k m) x₀ := by
  have hL : (0 : ℝ) ≤ L := L.cast_nonneg
  unfold DressedFRD.frdC
  split_ifs with hk
  · exact ((wt_Ioc_continuousOn P hd (lowEnd_nonneg hL k) m).continuousAt
      (Ici_mem_nhds hx₀))
  · exact ((wt_Ioi_continuousOn P hd (lowEnd_nonneg hL N) m).continuousAt (Ioi_mem_nhds hx₀))

end Symbols

namespace MsqCont

open DressedFRD DressedFRD.Data

variable (P : PtFamily) {d n : ℕ} [NeZero n] (L N : ℕ) (ζ : ℕ → ℂ)

/-- The data at mass `m²`, with fixed `L`, `N`, `ζ`. -/
def Dm (msq : ℝ) : Data d n := ⟨L, N, msq, frdC P msq L N, ζ⟩

/-- Functions continuous at `x₀`. -/
def cSub (x₀ : ℝ) : Subring (ℝ → ℂ) where
  carrier := {F | ContinuousAt F x₀}
  mul_mem' ha hb := ContinuousAt.mul ha hb
  one_mem' := continuousAt_const
  add_mem' ha hb := ContinuousAt.add ha hb
  zero_mem' := continuousAt_const
  neg_mem' ha := ContinuousAt.neg ha

variable {P L N ζ} {x₀ : ℝ}

local notation "H" => cSub x₀

theorem const_mem (c : ℂ) : (fun _ => c) ∈ H := continuousAt_const

theorem fsum_mem {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ} (h : ∀ i ∈ s, g i ∈ H) :
    (fun z => ∑ i ∈ s, g i z) ∈ H := by
  have := Subring.sum_mem (cSub x₀) h; rwa [Finset.sum_fn] at this

theorem fprod_mem {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℂ} (h : ∀ i ∈ s, g i ∈ H) :
    (fun z => ∏ i ∈ s, g i z) ∈ H := by
  have := Subring.prod_mem (cSub x₀) h; rwa [Finset.prod_fn] at this

theorem inv_mem {F : ℝ → ℂ} (hF : F ∈ H) (h0 : F x₀ ≠ 0) : (fun z => (F z)⁻¹) ∈ H :=
  ContinuousAt.inv₀ hF h0

theorem div_mem' {F G : ℝ → ℂ} (hF : F ∈ H) (hG : G ∈ H) (h0 : G x₀ ≠ 0) :
    (fun z => F z / G z) ∈ H := ContinuousAt.div hF hG h0

variable (hd : 1 ≤ d) (hx₀ : 0 < x₀)
include hd hx₀

theorem C_mem (k : ℕ) (m : Torus d n) : (fun msq => ((Dm P L N ζ msq).C k m : ℂ)) ∈ H :=
  Complex.continuous_ofReal.continuousAt.comp (frdC_continuousAt P hd L N k m hx₀)

omit hd hx₀ in
theorem Asym_mem (m : Torus d n) : (fun msq => Asym (d := d) (n := n) msq m) ∈ H := by
  show ContinuousAt (fun msq : ℝ => ((lam m + msq : ℝ) : ℂ)) x₀
  fun_prop

theorem Cle_mem (k : ℕ) (m : Torus d n) : (fun msq => Cle (Dm P L N ζ msq).C k m) ∈ H := by
  simp only [Cle, Finset.sum_apply, ofR]
  exact fsum_mem _ fun i _ => C_mem hd hx₀ i m

theorem Cgt_mem (k : ℕ) (m : Torus d n) :
    (fun msq => Cgt (Dm P L N ζ msq).C N k m) ∈ H := by
  simp only [Cgt, Finset.sum_apply, ofR]
  exact fsum_mem _ fun i _ => C_mem hd hx₀ i m

theorem Ehat_mem (k : ℕ) (m : Torus d n) :
    (fun msq => Ehat msq (Dm P L N ζ msq).C k m) ∈ H := by
  simp only [Ehat, Pi.mul_apply]
  exact Subring.mul_mem _ (Asym_mem m) (Cle_mem hd hx₀ k m)

/-- A family of tails, continuous at `x₀` at each momentum. -/
def CFam (R : ℝ → ℕ → Sym d n) : Prop := ∀ r m, (fun z => R z r m) ∈ cSub x₀

omit hd hx₀ in
theorem Z_eq (msq : ℝ) (k : ℕ) : (Dm P L N ζ msq : Data d n).Z k = ∏ i ∈ range k, (1 + ζ i) := rfl

omit hd hx₀ in
theorem zp_eq (msq : ℝ) (k : ℕ) : (Dm P L N ζ msq : Data d n).zp k = ζ k / (1 + ζ k) := rfl

theorem letV_mem {k : ℕ} {R : ℝ → ℕ → Sym d n} (hR : CFam (x₀ := x₀) R)
    (κ : Fin 3) (ℓ : Option ℕ) (m : Torus d n) :
    (fun z => (Dm P L N ζ z : Data d n).letV k (R z) κ ℓ m) ∈ H := by
  rcases ℓ with _ | r <;> fin_cases κ
  · exact Cle_mem hd hx₀ k m
  · show (fun z => (1 - Ehat z (Dm P L N ζ z : Data d n).C k) m) ∈ H
    simp only [Pi.sub_apply, Pi.one_apply]
    exact Subring.sub_mem _ (Subring.one_mem _) (Ehat_mem hd hx₀ k m)
  · exact Ehat_mem hd hx₀ k m
  · show (fun z => ((-((Dm P L N ζ z : Data d n).Z k • R z r) : Sym d n)) m) ∈ H
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Z_eq]
    exact Subring.neg_mem _ (Subring.mul_mem _ (const_mem _) (hR r m))
  · show (fun z => (((Dm P L N ζ z : Data d n).Z k • (Asym z * R z r) : Sym d n)) m) ∈ H
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Z_eq]
    exact Subring.mul_mem _ (const_mem _) (Subring.mul_mem _ (Asym_mem m) (hR r m))
  · show (fun z => ((-((Dm P L N ζ z : Data d n).Z k • (Asym z * R z r)) : Sym d n)) m) ∈ H
    simp only [Pi.neg_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Z_eq]
    exact Subring.neg_mem _ (Subring.mul_mem _ (const_mem _) (Subring.mul_mem _ (Asym_mem m)
      (hR r m)))

theorem eps_mem {k : ℕ} {R : ℝ → ℕ → Sym d n} (hR : CFam (x₀ := x₀) R) (m : Torus d n) :
    (fun z => (Dm P L N ζ z : Data d n).eps k (R z) m) ∈ H := by
  simp only [eps, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  exact Subring.sub_mem _ (Ehat_mem hd hx₀ k m) (fsum_mem _ fun r _ =>
    Subring.mul_mem _ (const_mem _) (Subring.mul_mem _ (Asym_mem m) (hR r m)))

theorem wLen_mem {k : ℕ} {R : ℝ → ℕ → Sym d n} (hR : CFam (x₀ := x₀) R) (s l : ℕ)
    (m : Torus d n) : (fun z => (Dm P L N ζ z : Data d n).wLen k (R z) s l m) ∈ H := by
  show (fun z => (∑ w ∈ (words k N l).filter (fun w => scale L k N
      (rbar ((Dm P L N ζ z : Data d n).rbV k) w) = s), wordVal ((Dm P L N ζ z : Data d n).letV k (R z)) w) m) ∈ H
  simp only [Finset.sum_apply, wordVal, Finset.prod_apply]
  exact fsum_mem _ fun w _ => fprod_mem _ fun i _ => letV_mem hd hx₀ hR _ _ m

theorem wLow_mem {k : ℕ} {R : ℝ → ℕ → Sym d n} (hR : CFam (x₀ := x₀) R) (s : ℕ)
    (m : Torus d n) : (fun z => (Dm P L N ζ z : Data d n).wLow k (R z) s m) ∈ H := by
  show (fun z => (∑ l ∈ range (L ^ s), (Dm P L N ζ z : Data d n).zp k ^ (l + 1) •
    (Dm P L N ζ z : Data d n).wLen k (R z) s l) m) ∈ H
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zp_eq]
  exact fsum_mem _ fun l _ => Subring.mul_mem _ (const_mem _) (wLen_mem hd hx₀ hR s l m)

theorem wTot_mem {k : ℕ} {R : ℝ → ℕ → Sym d n} (hR : CFam (x₀ := x₀) R) (m : Torus d n)
    (hden : 1 - (Dm P L N ζ x₀ : Data d n).zp k * (Dm P L N ζ x₀ : Data d n).eps k (R x₀) m ≠ 0) :
    (fun z => (Dm P L N ζ z : Data d n).wTot k (R z) m) ∈ H := by
  simp only [wTot]
  have he := eps_mem (P := P) (L := L) (N := N) (ζ := ζ) hd hx₀ (k := k) hR m
  have hA : (fun z => (Asym (d := d) (n := n) z m)⁻¹) ∈ H := by
    refine inv_mem (Asym_mem m) ?_
    simp only [Asym]
    exact_mod_cast (by have := lam_nonneg m; linarith : lam m + x₀ ≠ 0)
  refine div_mem' (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ (const_mem _) hA) he)
    (Subring.sub_mem _ (Subring.one_mem _) he))
    (Subring.sub_mem _ (Subring.one_mem _) (Subring.mul_mem _ (const_mem _) he)) hden

theorem wSc_mem {k : ℕ} {R : ℝ → ℕ → Sym d n} (hR : CFam (x₀ := x₀) R) (s : ℕ) (m : Torus d n)
    (hden : 1 - (Dm P L N ζ x₀ : Data d n).zp k * (Dm P L N ζ x₀ : Data d n).eps k (R x₀) m ≠ 0) :
    (fun z => (Dm P L N ζ z : Data d n).wSc k (R z) s m) ∈ H := by
  by_cases hs : s < N
  · show (fun z => (if s < N then (Dm P L N ζ z : Data d n).wLow k (R z) s
      else (Dm P L N ζ z : Data d n).wTop k (R z)) m) ∈ H
    simp only [hs, if_true]; exact wLow_mem hd hx₀ hR s m
  · show (fun z => (if s < N then (Dm P L N ζ z : Data d n).wLow k (R z) s
      else (Dm P L N ζ z : Data d n).wTop k (R z)) m) ∈ H
    simp only [hs, if_false]
    show (fun z => ((Dm P L N ζ z : Data d n).wTot k (R z) -
      ∑ s ∈ Ico (k + 1) N, (Dm P L N ζ z : Data d n).wLow k (R z) s) m) ∈ H
    simp only [Pi.sub_apply, Finset.sum_apply]
    exact Subring.sub_mem _ (wTot_mem hd hx₀ hR m hden)
      (fsum_mem _ fun s _ => wLow_mem hd hx₀ hR s m)

theorem tails_mem (hZ : ∀ k, (∏ i ∈ range k, (1 + ζ i)) ≠ 0) :
    ∀ k, (∀ k' < k, ∀ m, 1 - (Dm P L N ζ x₀ : Data d n).zp k' *
        (Dm P L N ζ x₀ : Data d n).eps k' ((Dm P L N ζ x₀ : Data d n).tails k') m ≠ 0) →
      CFam (x₀ := x₀) fun z => (Dm P L N ζ z : Data d n).tails k
  | 0, _ => fun r m => const_mem 0
  | k + 1, hden => fun r m => by
    have ih := tails_mem hZ k fun k' hk' => hden k' (by omega)
    show (fun z => (if k + 2 ≤ r ∧ r ≤ N then
      ((Dm P L N ζ z : Data d n).Z (k + 1))⁻¹ • ((Dm P L N ζ z : Data d n).Z k • (Dm P L N ζ z : Data d n).tails k r +
        (Dm P L N ζ z : Data d n).wSc k ((Dm P L N ζ z : Data d n).tails k) r) else 0) m) ∈ H
    split_ifs
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Z_eq]
      exact Subring.mul_mem _ (const_mem _)
        (Subring.add_mem _ (Subring.mul_mem _ (const_mem _) (ih r m))
          (wSc_mem hd hx₀ ih r m (hden k (by omega) m)))
    · exact const_mem 0

theorem Gam_mem (hZ : ∀ k, (∏ i ∈ range k, (1 + ζ i)) ≠ 0) {k : ℕ}
    (hden : ∀ k' < k, ∀ m, 1 - (Dm P L N ζ x₀ : Data d n).zp k' *
      (Dm P L N ζ x₀ : Data d n).eps k' ((Dm P L N ζ x₀ : Data d n).tails k') m ≠ 0)
    (m : Torus d n) : (fun z => (Dm P L N ζ z : Data d n).Gam k m) ∈ H := by
  show (fun z => ((Dm P L N ζ z : Data d n).Z k)⁻¹ * Cgt (Dm P L N ζ z : Data d n).C N k m +
    (∑ r ∈ Ioc k N, (Dm P L N ζ z : Data d n).tails k r) m) ∈ H
  simp only [Finset.sum_apply, Z_eq]
  exact Subring.add_mem _ (Subring.mul_mem _ (const_mem _) (Cgt_mem hd hx₀ k m))
    (fsum_mem _ fun r _ => tails_mem hd hx₀ hZ k hden r m)

/-- **`Γ^int_{j+1}(p)` is continuous in `m²` at `x₀ > 0`**, given the denominators at `x₀`. -/
theorem Gint_mem (hZ : ∀ k, (∏ i ∈ range k, (1 + ζ i)) ≠ 0) {j : ℕ}
    (hden : ∀ k ≤ j, ∀ m, 1 - (Dm P L N ζ x₀ : Data d n).zp k *
      (Dm P L N ζ x₀ : Data d n).eps k ((Dm P L N ζ x₀ : Data d n).tails k) m ≠ 0)
    (hden' : ∀ m, 1 + ζ j * (Dm P L N ζ x₀ : Data d n).Z j * Asym x₀ m *
      (Dm P L N ζ x₀ : Data d n).Gam j m ≠ 0)
    (m : Torus d n) : (fun z => (Dm P L N ζ z : Data d n).Gint j m) ∈ H := by
  have hR := tails_mem hd hx₀ hZ j fun k hk => hden k hk.le
  by_cases hj : j + 1 < N
  · show (fun z => (if j + 1 < N then ((Dm P L N ζ z : Data d n).Z (j + 1))⁻¹ •
      (ofR ((Dm P L N ζ z : Data d n).C (j + 1)) + (Dm P L N ζ z : Data d n).Z j • (Dm P L N ζ z : Data d n).tails j (j + 1) +
        (Dm P L N ζ z : Data d n).wSc j ((Dm P L N ζ z : Data d n).tails j) (j + 1))
      else (Dm P L N ζ z : Data d n).absorbed j) m) ∈ H
    simp only [hj, if_true, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Z_eq, ofR]
    exact Subring.mul_mem _ (const_mem _)
      (Subring.add_mem _ (Subring.add_mem _ (C_mem hd hx₀ _ m)
        (Subring.mul_mem _ (const_mem _) (hR _ m)))
        (wSc_mem hd hx₀ hR _ m (hden j le_rfl m)))
  · show (fun z => (if j + 1 < N then ((Dm P L N ζ z : Data d n).Z (j + 1))⁻¹ •
      (ofR ((Dm P L N ζ z : Data d n).C (j + 1)) + (Dm P L N ζ z : Data d n).Z j • (Dm P L N ζ z : Data d n).tails j (j + 1) +
        (Dm P L N ζ z : Data d n).wSc j ((Dm P L N ζ z : Data d n).tails j) (j + 1))
      else (Dm P L N ζ z : Data d n).absorbed j) m) ∈ H
    simp only [hj, if_false, absorbed]
    have hG := Gam_mem hd hx₀ hZ (k := j) (fun k hk => hden k hk.le) m
    refine div_mem' hG (Subring.add_mem _ (Subring.one_mem _) (Subring.mul_mem _
      (Subring.mul_mem _ (const_mem _) (Asym_mem m)) hG)) (hden' m)

end MsqCont

open MsqCont in
/-- **The dressed covariance is continuous in `m² ∈ (0, L^{-2(N-1)}]`** (fixed `ζ`). -/
theorem Cdr_continuousOn (P : PtFamily) {d L : ℕ} [NeZero L] (hd : 2 ≤ d) (hL7 : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∀ (N : ℕ), 1 ≤ N → ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ ζbar) →
      ∀ j, j + 1 < N → ∀ x y : Lam d L N,
        ContinuousOn (fun msq => Cdr (Dm P L N ζ msq : DressedFRD.Data d (L ^ N)) j x y)
          (Ioc 0 ((L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))) := by
  have hq : 2 ≤ 2 * pPhi d := by simp only [pPhi]; omega
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL7 (q := 2 * pPhi d)
    (M := 2 * pPhi d + d + 1) le_rfl
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := DressedFRD.thm_main_full (d := d) hd hq hL7
    (M := 2 * pPhi d + d + 1) le_rfl hcS
  refine ⟨ζbar, hζ, fun N hN ζ hζi j hj x y => ?_⟩
  have hZ : ∀ k, (∏ i ∈ range k, (1 + ζ i)) ≠ 0 := fun k => prod_ne_zero_iff.2 fun i _ h0 => by
    have h1 : ζ i = -1 := by linear_combination h0
    have := hζi i; rw [h1] at this; norm_num at this; linarith
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt ?_
  have hS' := hS (L ^ N) N x₀ hN rfl hx₀.1
  have hc : ∀ k, k < N → (Dm P L N ζ x₀ : DressedFRD.Data d (L ^ N)).Concl (2 * pPhi d) ζbar K k :=
    fun k hk => hK (L ^ N) (Dm P L N ζ x₀) rfl rfl hS' hx₀.2 hζi k hk
  have hG : ∀ m, ContinuousAt (fun z => (Dm P L N ζ z : DressedFRD.Data d (L ^ N)).Gint j m) x₀ :=
    fun m => Gint_mem (by omega) hx₀.1 hZ (fun k hk m => (hc k (by omega)).den_eps m)
      (fun m => (hc j (by omega)).den m) m
  simp only [Cdr, DressedFRD.kmat, DressedFRD.kern]
  refine continuousAt_const.mul (tendsto_finsetSum _ fun m _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, MsqCont.Z_eq]
  exact (continuousAt_const.mul (hG m)).mul continuousAt_const

/-- **`K_{j+1}` is a continuous function of the covariance** (coefficient-wise). -/
theorem Kplus_continuous_cov {d L N : ℕ} [NeZero L] (j : ℕ) (V W : Fam d L N) (K : Act d L N)
    (hV0 : ∀ b, ε (V b : Alg d L N) = 0) (U : Finset (Lam d L N)) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) :
    Continuous (fun M : Lam d L N → Lam d L N → ℂ =>
      coeff (Kplus j M V W K U : Alg d L N) z) :=
  (Kplus_holC (E := Lam d L N → Lam d L N → ℂ) (Cf := fun M => M) j
    (fun x y => differentiable_pi.1 (differentiable_pi.1 differentiable_id x) y)
    (Vf := fun _ => V) (Wf := fun _ => W) (Kf := fun _ => K) (fun b => HolE.const _)
    (fun b => HolE.const _) (fun X => HolE.const _) (fun _ b => hV0 b) U n z).continuous

end

end Step2
