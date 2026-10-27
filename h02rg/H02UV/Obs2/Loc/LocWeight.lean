import Loc.Loc4Est
import Loc.Loc2Large

/-!
# Weighted pairings and differences of fields (for the two-point localisation in `d = 2`)

* `weighted_bound`: for `F ∈ 𝒩(X^□)`, `X` small, a spin pattern `σ` and one-point weights
  `H_r : ℤ^d → ℝ` (in coordinates relative to the base point of `X`) that vanish at distance
  `≥ 2R`, `R = 2^{d+1} L^j`, and satisfy `|∇^α H_r| ≤ A_r R^{-|α|}`,
  `|∑_x F_{(x,σ)} ∏_r H_r(x_r)| ≤ n! ℓ^{-n} ∏_r A_r ‖F‖_{T_j(ℓ)}`
  (the weighted sum is the pairing of `F` with a test function of `Φ_j(ℓ)`-norm
  `≤ ℓ^{-n} ∏ A_r`);
* `D1_add`, `D1_smul`, `D1_sum`, `D1_sub`: linearity of one-point derivatives;
* `tNorm_ψ_sub_le`: `‖ψ_{(b,s)} - ψ_{(a,s)}‖_{T(h,ℓ)} ≤ ℓ |r(b-a)|_1 / h` (path of unit steps).
-/

namespace Obs2

noncomputable section

open Finset Grassmann FRD Loc

variable {d L N : ℕ} [NeZero L]

/-! ### Linearity of `D1` -/

section D1Lin

variable {E Y : Type*} [Fintype E] [DecidableEq E]

theorem D1_smul (s : (E → ℕ) → Y → Y) (a : E → ℕ) (c : ℝ) (f : Y → ℝ) (y : Y) :
    D1 s a (fun v => c * f v) y = c * D1 s a f y := by
  rw [D1_eq_sum, D1_eq_sum, mul_sum]
  exact sum_congr rfl fun b _ => by ring

theorem D1_sub (s : (E → ℕ) → Y → Y) (a : E → ℕ) (f g : Y → ℝ) (y : Y) :
    D1 s a (fun v => f v - g v) y = D1 s a f y - D1 s a g y := by
  rw [D1_eq_sum, D1_eq_sum, D1_eq_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun b _ => by ring

theorem D1_sum {ι : Type*} (S : Finset ι) (s : (E → ℕ) → Y → Y) (a : E → ℕ) (f : ι → Y → ℝ)
    (y : Y) : D1 s a (fun v => ∑ i ∈ S, f i v) y = ∑ i ∈ S, D1 s a (f i) y := by
  rw [D1_eq_sum]
  simp_rw [D1_eq_sum, mul_sum]
  exact sum_comm

end D1Lin

/-! ### The weighted bound -/

theorem weighted_bound (hL : 2 ^ (d + 3) + 8 * d < L) {j : ℕ} (hj : j < N)
    (X : Finset (Lam d L N)) (F : Alg d L N) {n : ℕ} (σ : Fin n → ℤˣ)
    (H : Fin n → Zd d → ℝ) (A : Fin n → ℝ) (hA : ∀ r, 0 ≤ A r)
    (hfar : ∀ r u, 2 * (rad d L j : ℝ) ≤ supNormZ u → H r u = 0)
    (hD : ∀ r (α : Dir d → ℕ) u, Grassmann.mabs α ≤ pPhi d →
      |D1 (fun b v => b +ᵥ v) α (H r) u| ≤ A r / (rad d L j : ℝ) ^ Grassmann.mabs α)
    {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ‖∑ x : Fin n → Lam d L N, coeff F (fun r => (x r, σ r)) *
        ((∏ r, H r (rep (x r - base X)) : ℝ) : ℂ)‖ ≤
      n.factorial * (ℓ⁻¹ ^ n * ∏ r, A r) * (Tj d (L : ℝ) j ℓ F).toReal := by
  set b := base X
  set s : ℝ := (L : ℝ) ^ j with hs
  set R : ℝ := (rad d L j : ℝ) with hRdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hRs : R = 2 ^ (d + 1) * s := by simp [R, s]
  have hR1 : 1 ≤ R := by rw [hRdef]; exact Nat.one_le_cast.2 (one_le_rad j)
  have hsR : s ≤ R := by
    rw [hRs]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  set Hs : Fin n → Sf (Zd d) → ℝ := fun r => spinF (σ r) (H r)
  set M : ℝ := ℓ⁻¹ ^ n * ∏ r, A r
  have hM0 : 0 ≤ M := mul_nonneg (by positivity) (prod_nonneg fun r _ => hA r)
  let g : TestFn (Lam d L N) := single n (fun z => ((∏ r, Hs r ((ρS b ∘ z) r) : ℝ) : ℂ))
  have hpair : pair F g = (n.factorial : ℂ)⁻¹ * ∑ x : Fin n → Lam d L N,
      coeff F (fun r => (x r, σ r)) * ((∏ r, H r (rep (x r - b)) : ℝ) : ℂ) := by
    rw [pair_single, sum_pattern σ _ (fun z hz => ?_)]
    · congr 1
      refine sum_congr rfl fun x _ => ?_
      congr 2
      refine prod_congr rfl fun r _ => ?_
      simp [Hs, spinF, ρS]
    · have : ∃ r, (z r).2 ≠ σ r := by
        by_contra h; push Not at h; exact hz (funext h)
      obtain ⟨r, hr⟩ := this
      rw [prod_eq_zero (mem_univ r), Complex.ofReal_zero, mul_zero]
      simp [Hs, spinF, ρS, hr]
  have hnorm : phiNorm (Dir d) (pPhi d) s ℓ g ≤ ENNReal.ofReal M := by
    refine phiNorm_single_le hM0 fun z α hα => ?_
    rw [nabla_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rw [nab_comp_ρS b (fun w => ∏ r, Hs r (w r)) (S := 2 * rad d L j) (P := pPhi d)
      (size_cond hL hj) (fun w ⟨k, hk⟩ => by
        refine prod_eq_zero (mem_univ k) ?_
        have : 2 * R ≤ (supNormZ (w k).1 : ℝ) := by
          rw [hRdef]; exact_mod_cast hk.le
        simp only [Hs, spinF]
        split_ifs
        · exact hfar k _ this
        · rfl) α hα z, nabla_prod]
    set u := ρS b ∘ z
    have hb : ∀ r, |D1 sh (α r) (Hs r) (u r)| ≤ A r / R ^ Grassmann.mabs (α r) := by
      intro r
      simp only [Hs]
      rw [D1_spinF]
      split_ifs
      · exact hD r (α r) (u r).1 (hα r)
      · simp only [abs_zero]
        have := hA r
        positivity
    rw [abs_prod]
    have hprod : ∏ r, |D1 sh (α r) (Hs r) (u r)| ≤ (∏ r, A r) / R ^ ord α := by
      calc ∏ r, |D1 sh (α r) (Hs r) (u r)| ≤ ∏ r, (A r / R ^ Grassmann.mabs (α r)) :=
            prod_le_prod (fun _ _ => abs_nonneg _) fun r _ => hb r
        _ = (∏ r, A r) / R ^ ord α := by
            rw [prod_div_distrib, prod_pow_eq_pow_sum, ord]
    have hsR' : s ^ ord α / R ^ ord α ≤ 1 :=
      (div_le_one (by positivity)).2 (pow_le_pow_left₀ (by linarith) hsR _)
    have hA0 : 0 ≤ ∏ r, A r := prod_nonneg fun r _ => hA r
    calc ℓ⁻¹ ^ n * s ^ ord α * ∏ r, |D1 sh (α r) (Hs r) (u r)|
        ≤ ℓ⁻¹ ^ n * s ^ ord α * ((∏ r, A r) / R ^ ord α) := by gcongr
      _ = M * (s ^ ord α / R ^ ord α) := by simp only [M]; ring
      _ ≤ M * 1 := by gcongr
      _ = M := mul_one M
  have h := abs_pair_le (by positivity) hℓ F hM0 hnorm
  rw [hpair, norm_mul, norm_inv, Complex.norm_natCast] at h
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [inv_mul_le_iff₀ hf] at h
  refine h.trans (le_of_eq ?_)
  simp only [Tj, s, M]
  ring

/-! ### Differences of fields -/

theorem dstB_le_norm1 (a b : Lam d L N) (b0 : Lam d L N) (s : ℤˣ) :
    dstB a ((b, s) : Sf (Lam d L N)) ≤ ∑ i, |lift b0 b i - lift b0 a i| := by
  unfold dstB
  have e : (b - a : Lam d L N) = prj (rep (b - b0) - rep (a - b0)) := by
    rw [prj_sub, prj_rep, prj_rep]; abel
  rw [e]
  refine (norm1_rep_prj_le _).trans (le_of_eq ?_)
  unfold norm1 lift
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs, Pi.sub_apply, Int.cast_sub]

/-- `‖ψ_{(b,s)} - ψ_{(a,s)}‖_{T(h,ℓ)} ≤ ℓ · dstB a (b,s) / h`. -/
theorem tNorm_ψ_sub_le {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ)
    (a b : Lam d L N) (s : ℤˣ) :
    tNorm (Dir d) p h ℓ (ψ ((b, s) : Sf (Lam d L N)) - ψ (a, s)) ≤
      ENNReal.ofReal (dstB a ((b, s) : Sf (Lam d L N)) * (ℓ * h⁻¹)) := by
  refine tNorm_le fun g hg => ?_
  set φ : Sf (Lam d L N) → ℂ := fun y => pair (ψ y) g
  have hK : ∀ (y : Sf (Lam d L N)) (e : Dir d),
      ‖φ (sh (Pi.single e 1) y) - φ y‖ ≤ ℓ * h⁻¹ := by
    intro y e
    have := MonoEst.abs_pair_Dψ_le (E := Dir d) (p := p) hh hℓ (a := (Pi.single e 1 : Dir d → ℕ))
      (by rw [mabs_single]; exact hp) y hg
    rw [MonoEst.Dψ_one, MonoEst.pair_sub', mabs_single, pow_one] at this
    exact this
  have := pathH_dstB a φ (ℓ * h⁻¹) hK ((b, s) : Sf (Lam d L N))
  rw [MonoEst.pair_sub']
  exact this

end

end Obs2
