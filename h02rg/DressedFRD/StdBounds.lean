import DressedFRD.Lattice
import DressedFRD.Std

/-!
# `lem:std`(c),(d): consequences of (S4)

`StdFull` adds to `StdHyp` the bounds (S4) and (S5) of `def:std`:
* (S4a) `|∇^β C_k(0,x)| ≤ c_S L^{-(k-1)(d-2+|β|)}` for `|β| ≤ M`;
* (S4b) `∇^α_x ∇^α_y C_k(x,x) = ⨍ |σ_α|^2 Ĉ_k ≤ c_S L^{-(k-1)(d-2+2|α|)}` for `|α| ≤ q`;
* (S5) `Ĉ_N(p) (1 + L^{N-1}|p|_σ)^M ≤ c_S L^d L^{2(N-1)}` for `p ≠ 0`.

(S4b) is the coincident-point form of the two-point bound with `|α|, |β| ≤ q`; this is what
`lem:std`(c) uses.

* `std_c`: `‖C_k‖_{(k-1)} ≤ c_S` (Cauchy–Schwarz).
* `std_d`: `Ĉ_k(p) (1 + L^{k-1}|p|_σ)^M ≤ c_d L^d L^{2(k-1)}`, `c_d = 2^M (1+2M)^d c_S`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann ComplexConjugate

variable {d n : ℕ} [NeZero n]

/-- (S1)–(S5). -/
structure StdFull (L N q M : ℕ) (msq cS : ℝ) (C : ℕ → Torus d n → ℝ) : Prop where
  base : StdHyp L N msq C
  hM : q + d + 1 ≤ M
  hcS : 0 ≤ cS
  S4a : ∀ k, 1 ≤ k → k < N → ∀ β : Dir d → ℕ, Grassmann.mabs β ≤ M → ∀ x,
    ‖dop β (kern (ofR (C k))) x‖ ≤
      cS * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs β)))
  S4b : ∀ k, 1 ≤ k → k < N → ∀ α : Dir d → ℕ, Grassmann.mabs α ≤ q →
    avg (fun m => ‖sigma α m‖ ^ 2 * C k m) ≤
      cS * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + 2 * Grassmann.mabs α)))
  S5 : ∀ m : Torus d n, m ≠ 0 →
    C N m * (1 + (L : ℝ) ^ (N - 1) * pnorm m) ^ M ≤ cS * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (N - 1))

variable {L N q M : ℕ} {msq cS : ℝ} {C : ℕ → Torus d n → ℝ}

/-- `lem:std`(c): `‖C_k‖_{(k-1)} ≤ c_S`. -/
theorem std_c (h : StdFull L N q M msq cS C) (hL : 1 ≤ L) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    snorm L q (k - 1) (ofR (C k)) ≤ cS := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  refine snorm_le_iff.2 fun α hα => ?_
  have hC0 : ∀ m, 0 ≤ C k m := h.base.nonneg k
  -- Cauchy–Schwarz
  have hcs : (∑ m, ‖sigma α m‖ * C k m) ^ 2 ≤
      (∑ m, ‖sigma α m‖ ^ 2 * C k m) * ∑ m, C k m := by
    have := Finset.sum_mul_sq_le_sq_mul_sq univ (fun m => ‖sigma α m‖ * Real.sqrt (C k m))
      (fun m => Real.sqrt (C k m))
    simp only [mul_pow, Real.sq_sqrt (hC0 _)] at this
    convert this using 2
    refine sum_congr rfl fun m _ => ?_
    rw [mul_assoc, Real.mul_self_sqrt (hC0 m)]
  have hb := h.S4b k hk1 hkN α hα
  have hb0 := h.S4b k hk1 hkN 0 (by simp [Grassmann.mabs])
  simp only [sigma_zero, norm_one, one_pow, one_mul, Grassmann.mabs, Pi.zero_apply,
    sum_const_zero, Nat.cast_zero, mul_zero, add_zero] at hb0
  have hmom : mom α (ofR (C k)) = avg fun m => ‖sigma α m‖ * C k m := by
    unfold mom; congr 1; funext m
    rw [ofR, Complex.norm_real, Real.norm_of_nonneg (hC0 m)]
  rw [hmom]
  set A := avg fun m => ‖sigma α m‖ * C k m
  have hA0 : 0 ≤ A := avg_nonneg fun m => mul_nonneg (norm_nonneg _) (hC0 m)
  have hAsq : A ^ 2 ≤ (avg fun m => ‖sigma α m‖ ^ 2 * C k m) * avg fun m => C k m := by
    simp only [A, avg]
    rw [mul_pow, mul_mul_mul_comm, ← sq]
    exact mul_le_mul_of_nonneg_left hcs (by positivity)
  set c := ((k - 1 : ℕ) : ℝ)
  set a := (Grassmann.mabs α : ℝ)
  have hprod : (avg fun m => ‖sigma α m‖ ^ 2 * C k m) * (avg fun m => C k m) ≤
      (cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a)))) ^ 2 := by
    calc (avg fun m => ‖sigma α m‖ ^ 2 * C k m) * (avg fun m => C k m)
        ≤ (cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + 2 * a)))) * (cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2)))) :=
          mul_le_mul hb hb0 (avg_nonneg fun m => hC0 m)
            (mul_nonneg h.hcS (Real.rpow_nonneg hL0.le _))
      _ = cS ^ 2 * ((L : ℝ) ^ (-(c * ((d : ℝ) - 2 + 2 * a))) * (L : ℝ) ^ (-(c * ((d : ℝ) - 2)))) := by
          ring
      _ = cS ^ 2 * ((L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a)))) ^ 2 := by
          rw [← Real.rpow_add hL0, ← Real.rpow_mul_natCast hL0.le]; congr 2; push_cast; ring
      _ = (cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a)))) ^ 2 := by ring
  have hB0 : 0 ≤ cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a))) :=
    mul_nonneg h.hcS (Real.rpow_nonneg hL0.le _)
  have hA : A ≤ cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a))) :=
    (pow_le_pow_iff_left₀ hA0 hB0 (by norm_num : (2 : ℕ) ≠ 0)).1 (hAsq.trans hprod)
  calc wgt d L (k - 1) α * A ≤ wgt d L (k - 1) α * (cS * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a)))) :=
        mul_le_mul_of_nonneg_left hA (wgt_pos hL0 _ _).le
    _ = cS * ((L : ℝ) ^ (c * ((d : ℝ) - 2 + a)) * (L : ℝ) ^ (-(c * ((d : ℝ) - 2 + a)))) := by
        unfold wgt; ring
    _ = cS := by rw [← Real.rpow_add hL0, add_neg_cancel, Real.rpow_zero, mul_one]

/-- The translation symbol `m ↦ e^{ik·v}` has range `|v|_∞`. -/
theorem rng_char_le (v : Torus d n) : rng (fun m : Torus d n => char m v) ≤ supNorm v := by
  refine rng_le_iff.2 fun x hx => ?_
  have hx' : v + x ≠ 0 := by
    intro h
    have : x = -v := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [this, supNorm_neg] at hx; omega
  simp only [kern]
  rw [show (∑ m, char m v * char m x) = ∑ m, char m (v + x) by
    exact sum_congr rfl fun m _ => (char_add_right m v x).symm, sum_char_left, if_neg hx', mul_zero]

theorem rng_char_sub_one_le (v : Torus d n) :
    rng (fun m : Torus d n => char m v - 1) ≤ supNorm v := by
  have : (fun m : Torus d n => char m v - 1) = (fun m => char m v) - fun _ => (1 : ℂ) := rfl
  rw [this]
  refine (rng_sub_le _ _).trans ?_
  rw [rng_const]; exact max_le (rng_char_le v) (Nat.zero_le _)

/-- `rng σ_β ≤ |β|`. -/
theorem rng_sigma_le (β : Dir d → ℕ) : rng (sigma β : Sym d n) ≤ Grassmann.mabs β := by
  have e : (sigma β : Sym d n) = ∏ e, (fun m : Torus d n => char m (dirVec e) - 1) ^ β e := by
    funext m; simp [sigma, Finset.prod_apply, Pi.pow_apply]
  rw [e]
  refine (rng_prod_le _ _).trans ?_
  unfold Grassmann.mabs
  refine sum_le_sum fun e _ => (rng_pow_le _ _).trans ?_
  have := (rng_char_sub_one_le (dirVec e : Torus d n)).trans (supNorm_dirVec_le e)
  calc β e * rng (fun m : Torus d n => char m (dirVec e) - 1) ≤ β e * 1 :=
        Nat.mul_le_mul_left _ this
    _ = β e := mul_one _

/-- `|σ_β Ĉ_k| ≤ ((1+2M) L^k)^d c_S L^{-(k-1)(d-2+|β|)}` for `|β| ≤ M`. -/
theorem sigma_C_le (h : StdFull L N q M msq cS C) (hL : 1 ≤ L) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k < N) {β : Dir d → ℕ} (hβ : Grassmann.mabs β ≤ M) (m : Torus d n) :
    ‖sigma β m‖ * C k m ≤ ((1 + 2 * M : ℝ) * (L : ℝ) ^ k) ^ d *
      (cS * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs β)))) := by
  set v : Sym d n := fun m => sigma β m * ofR (C k) m
  have hv : ‖v m‖ = ‖sigma β m‖ * C k m := by
    simp only [v, ofR, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.base.nonneg k m)]
  have hk : ∀ x, ‖kern v x‖ ≤
      cS * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + Grassmann.mabs β))) := by
    intro x; rw [← dop_kern]; exact h.S4a k hk1 hkN β hβ x
  have hrng : ((2 * rng v + 1 : ℕ) : ℝ) ≤ (1 + 2 * M : ℝ) * (L : ℝ) ^ k := by
    have h1 : rng v ≤ rng (sigma β : Sym d n) + rng (ofR (C k)) := by
      have : v = (sigma β : Sym d n) * ofR (C k) := rfl
      rw [this]; exact rng_mul_le _ _
    have h2 := rng_sigma_le (n := n) β
    have h3 := h.base.range k hk1 hkN
    have h4 : 1 ≤ L ^ k := Nat.one_le_pow _ _ (by omega)
    have : 2 * rng v + 1 ≤ (1 + 2 * M) * L ^ k := by nlinarith
    exact_mod_cast this
  rw [← hv]
  refine (norm_le_sum_kern v m).trans ((sum_kern_le v hk).trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg h.hcS (Real.rpow_nonneg (by positivity) _))
  exact_mod_cast pow_le_pow_left₀ (by positivity) hrng d

theorem pow_exponent_identity {L : ℝ} (hL : 0 < L) {k : ℕ} (hk : 1 ≤ k) (d : ℕ) :
    L ^ (k * d) * L ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2))) = L ^ d * L ^ (2 * (k - 1)) := by
  rw [← Real.rpow_natCast L (k * d), ← Real.rpow_add hL, ← Real.rpow_natCast L d,
    ← Real.rpow_natCast L (2 * (k - 1)), ← Real.rpow_add hL]
  congr 1
  push_cast [Nat.cast_sub hk]; ring

/-- `lem:std`(d): `Ĉ_k(p) (1 + L^{k-1}|p|_σ)^M ≤ c_d L^d L^{2(k-1)}`. -/
theorem std_d (h : StdFull L N q M msq cS C) (hd : 1 ≤ d) (hL : 1 ≤ L) {k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k < N) (m : Torus d n) :
    C k m * (1 + (L : ℝ) ^ (k - 1) * pnorm m) ^ M ≤
      2 ^ M * (1 + 2 * M : ℝ) ^ d * cS * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (k - 1)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hC0 := h.base.nonneg k m
  set B := (1 + 2 * M : ℝ) ^ d * cS * (L : ℝ) ^ d * (L : ℝ) ^ (2 * (k - 1))
  have hB0 : 0 ≤ B := by have := h.hcS; positivity
  set y := (L : ℝ) ^ (k - 1) * pnorm m
  have hy0 : 0 ≤ y := mul_nonneg (by positivity) (pnorm_nonneg m)
  -- `β = 0`
  have h0 : C k m ≤ B := by
    have := sigma_C_le h hL hk1 hkN (β := 0) (by simp [Grassmann.mabs]) m
    simp only [sigma_zero, norm_one, one_mul, Grassmann.mabs, Pi.zero_apply, sum_const_zero,
      Nat.cast_zero, add_zero] at this
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, ← pow_mul]
    have := pow_exponent_identity hL0 hk1 d
    simp only [B]
    calc (1 + 2 * (M : ℝ)) ^ d * (L : ℝ) ^ (k * d) * (cS * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2))))
        = (1 + 2 * (M : ℝ)) ^ d * cS * ((L : ℝ) ^ (k * d) *
            (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2)))) := by ring
      _ = _ := by rw [this]; ring
  -- `β = M e_i` with `|p|_σ = |e^{ip_i} - 1|`
  have hM : C k m * y ^ M ≤ B := by
    obtain ⟨i, hi⟩ := exists_pnorm_eq hd m
    set β : Dir d → ℕ := Pi.single (Sum.inl i) M
    have hβ : Grassmann.mabs β = M := by simp [Grassmann.mabs, β]
    have hs : ‖sigma β m‖ = pnorm m ^ M := by
      unfold sigma
      rw [prod_eq_single (Sum.inl i) (fun e _ he => by simp [β, Pi.single_apply, he]) (by simp),
        norm_pow, hi]
      simp [β, dirVec_inl]
    have := sigma_C_le h hL hk1 hkN (β := β) (by rw [hβ]) m
    rw [hs, hβ] at this
    have hLM : y ^ M = (L : ℝ) ^ ((k - 1) * M) * pnorm m ^ M := by
      simp only [y]; rw [mul_pow, ← pow_mul]
    rw [hLM]
    have e1 : ((L : ℝ) ^ ((k - 1) * M)) * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + M))) =
        (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2))) := by
      rw [← Real.rpow_natCast L ((k - 1) * M), ← Real.rpow_add hL0]
      congr 1; push_cast; ring
    have hpos : 0 ≤ (L : ℝ) ^ ((k - 1) * M) := by positivity
    calc C k m * ((L : ℝ) ^ ((k - 1) * M) * pnorm m ^ M)
        = (L : ℝ) ^ ((k - 1) * M) * (pnorm m ^ M * C k m) := by ring
      _ ≤ (L : ℝ) ^ ((k - 1) * M) * (((1 + 2 * M : ℝ) * (L : ℝ) ^ k) ^ d *
          (cS * (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2 + M))))) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = (1 + 2 * (M : ℝ)) ^ d * cS * ((L : ℝ) ^ (k * d) *
            (L : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) * ((d : ℝ) - 2)))) := by
          rw [← e1, mul_pow, ← pow_mul]; ring
      _ = B := by rw [pow_exponent_identity hL0 hk1 d]; simp only [B]; ring
  -- combine: `(1+y)^M ≤ 2^M max(1, y^M)`
  rcases le_total y 1 with hy1 | hy1
  · have : (1 + y) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
    calc C k m * (1 + y) ^ M ≤ C k m * 2 ^ M := mul_le_mul_of_nonneg_left this hC0
      _ ≤ B * 2 ^ M := mul_le_mul_of_nonneg_right h0 (by positivity)
      _ = _ := by simp only [B]; ring
  · have : (1 + y) ^ M ≤ 2 ^ M * y ^ M := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) M
    calc C k m * (1 + y) ^ M ≤ C k m * (2 ^ M * y ^ M) := mul_le_mul_of_nonneg_left this hC0
      _ = 2 ^ M * (C k m * y ^ M) := by ring
      _ ≤ 2 ^ M * B := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by simp only [B]; ring

end

end DressedFRD
