module

public import ArborealDecay.BCHS.Smooth

/-!
# Nilpotent Taylor shifts are algebra homomorphisms (R1, single direction)

`ArborealDecay.Horo.shiftT v c n K F x = ∑_{m < K} (c(x)^m / m!) (∂_v^m F)(x) n^m` is the value of `F`
at the shifted point `x + c(x) n v`.  For smooth (`SSmooth`) superfunctions and `n` central with
`n^K = 0`:

* `shiftT_mul`: `(FG)(x + c n v) = F(x + c n v) G(x + c n v)`;
* `shiftT_scomp`: `g(S)(x + c n v) = g(S(x + c n v))` for `g` smooth on an open set containing the
  bodies, if moreover `n` is even with body `0`.

Both are proved by the downward induction on powers of `n` used in `Super.scomp_scomp`: the
defect along the path `λ ↦ F(x + λ c n v)` vanishes at `λ = 0`, and its `λ`-derivative is `c n`
times defects of derivatives (`pd_shL`).
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset ArborealDecay.Super ArborealDecay.Horo Grassmann
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {E : Type*} [Fintype E]
variable {O : Type*} [Fintype O] [DecidableEq O]

local notation "X" => E → ℝ

/-! ### Iterated derivatives -/

theorem SSmooth.pdn {F : X → Gr O} (hF : SSmooth F) (v : X) (m : ℕ) :
    SSmooth (ArborealDecay.Horo.pdn v m F) := by
  induction m with
  | zero => exact hF
  | succ m ih => exact ih.deriv v

theorem pdn_succ' (v : X) (m : ℕ) (F : X → Gr O) :
    ArborealDecay.Horo.pdn v (m + 1) F = ArborealDecay.Horo.pdn v m (pd v F) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pdn_succ, ih, pdn_succ]

theorem pdn_add {F G : X → Gr O} (hF : SSmooth F) (hG : SSmooth G) (v : X) (m : ℕ) :
    ArborealDecay.Horo.pdn v m (fun x => F x + G x) =
      fun x => ArborealDecay.Horo.pdn v m F x + ArborealDecay.Horo.pdn v m G x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext x
    rw [pdn_succ, ih, pd_add (hF.pdn v m).sdiff (hG.pdn v m).sdiff]
    rfl

theorem isEven_pd {F : X → Gr O} (hF : SDiff F) (hE : ∀ x, IsEven (F x)) (v x : X) :
    IsEven (pd v F x) := by
  unfold IsEven
  have e : F = fun y => (inv' : Gr O →ₐ[ℝ] Gr O).toLinearMap (F y) := funext fun y => (hE y).symm
  have h := pd_map hF (inv' : Gr O →ₐ[ℝ] Gr O).toLinearMap v x
  rw [← e] at h
  exact h.symm

theorem isEven_pdn {F : X → Gr O} (hF : SSmooth F) (hE : ∀ x, IsEven (F x)) (v : X) (m : ℕ)
    (x : X) : IsEven (ArborealDecay.Horo.pdn v m F x) := by
  induction m generalizing x with
  | zero => exact hE x
  | succ m ih => exact isEven_pd (hF.pdn v m).sdiff ih v x

/-! ### Shifts -/

section Shift

variable (v : E → ℝ) (c : (E → ℝ) → ℝ) (n : Gr O) (K : ℕ)

theorem SSmooth.shiftT {F : X → Gr O} (hc : ContDiff ℝ ∞ c) (hF : SSmooth F) :
    SSmooth (ArborealDecay.Horo.shiftT v c n K F) :=
  SSmooth.sum _ fun m _ => SSmooth.smul ((hc.pow m).div_const _) ((hF.pdn v m).mul (SSmooth.const _))

theorem shiftT_add {F G : X → Gr O} (hF : SSmooth F) (hG : SSmooth G) (x : X) :
    ArborealDecay.Horo.shiftT v c n K (fun y => F y + G y) x =
      ArborealDecay.Horo.shiftT v c n K F x + ArborealDecay.Horo.shiftT v c n K G x := by
  simp only [ArborealDecay.Horo.shiftT, pdn_add hF hG, add_mul, smul_add, sum_add_distrib]

theorem shiftT_smul (r : ℝ) {F : X → Gr O} (hF : SSmooth F) (x : X) :
    ArborealDecay.Horo.shiftT v c n K (fun y => r • F y) x =
      r • ArborealDecay.Horo.shiftT v c n K F x := by
  have : ∀ m, ArborealDecay.Horo.pdn v m (fun y => r • F y) =
      fun y => r • ArborealDecay.Horo.pdn v m F y := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      funext y
      rw [pdn_succ, ih, pdn_succ]
      rw [pd_smul (differentiable_const r) (hF.pdn v m).sdiff]
      simp
  simp only [ArborealDecay.Horo.shiftT, this, smul_mul_assoc, smul_sum, smul_comm r]

/-- `λ ↦ F(x + λ c(x) n v)`. -/
def shL (F : X → Gr O) (x : X) (t : ℝ) : Gr O := ArborealDecay.Horo.shiftT v c (t • n) K F x

theorem shL_eq (F : X → Gr O) (x : X) (t : ℝ) :
    shL v c n K F x t = ∑ m ∈ range K,
      t ^ m • ((c x ^ m / m.factorial) • (ArborealDecay.Horo.pdn v m F x * n ^ m)) := by
  simp only [shL, ArborealDecay.Horo.shiftT, smul_pow, mul_smul_comm, smul_comm (t ^ _)]

theorem sdiff_shL (F : X → Gr O) (x : X) : Super.SDiff (shL v c n K F x) := by
  have e : shL v c n K F x = fun t => ∑ m ∈ range K,
      t ^ m • ((c x ^ m / m.factorial) • (ArborealDecay.Horo.pdn v m F x * n ^ m)) :=
    funext (shL_eq v c n K F x)
  rw [e]
  exact SDiff.sum _ fun m _ => SDiff.smul (differentiable_pow m) (SDiff.const _)

theorem pd_pow_smul (m : ℕ) (a : Gr O) (t : ℝ) :
    pd 1 (fun s : ℝ => s ^ m • a) t = ((m : ℝ) * t ^ (m - 1)) • a := by
  rw [pd_smul_const (differentiable_pow m), fderiv_apply_one_eq_deriv]
  congr 1
  simp

/-- The `λ`-derivative of the shift path: `∂_λ F(x + λ c n v) = c n (∂_v F)(x + λ c n v)`. -/
theorem pd_shL {n : Gr O} {K : ℕ} (hn : n ^ K = 0) (hcomm : ∀ a, n * a = a * n)
    (F : X → Gr O) (x : X) (t : ℝ) :
    pd 1 (shL v c n K F x) t = c x • (n * shL v c n K (pd v F) x t) := by
  have e : shL v c n K F x = fun t => ∑ m ∈ range K,
      t ^ m • ((c x ^ m / m.factorial) • (ArborealDecay.Horo.pdn v m F x * n ^ m)) :=
    funext (shL_eq v c n K F x)
  rw [e, pd_sum _ fun m _ => SDiff.smul (differentiable_pow m) (SDiff.const _)]
  simp only [pd_pow_smul]
  rw [shL_eq, mul_sum, smul_sum]
  cases K with
  | zero => simp
  | succ K =>
    rw [sum_range_succ', sum_range_succ]
    simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
    have hlast : c x • (n * t ^ K • ((c x ^ K / (K.factorial : ℝ)) •
        (ArborealDecay.Horo.pdn v K (pd v F) x * n ^ K))) = 0 := by
      have h0 : n * (ArborealDecay.Horo.pdn v K (pd v F) x * n ^ K) = 0 := by
        rw [← mul_assoc, hcomm, mul_assoc, ← pow_succ', hn, mul_zero]
      simp only [mul_smul_comm, h0, smul_zero]
    rw [hlast, add_zero]
    refine sum_congr rfl fun m _ => ?_
    rw [← pdn_succ']
    have hnm : n * (ArborealDecay.Horo.pdn v (m + 1) F x * n ^ m) =
        ArborealDecay.Horo.pdn v (m + 1) F x * n ^ (m + 1) := by
      rw [← mul_assoc, hcomm, mul_assoc, ← pow_succ']
    rw [mul_smul_comm, mul_smul_comm, hnm, smul_smul, smul_smul, smul_smul]
    congr 1
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

variable {n K}

theorem pos_of_pow_eq_zero (hn : n ^ K = 0) (hO : (1 : Gr O) ≠ 0) : 0 < K := by
  rcases Nat.eq_zero_or_pos K with rfl | h
  · exact absurd (by simpa using hn) hO
  · exact h

theorem shiftT_of_one_le (F : X → Gr O) (n' : Gr O) (x : X) (hK : 0 < K) (hn' : ∀ m, 0 < m →
    (c x ^ m / m.factorial) • (ArborealDecay.Horo.pdn v m F x * n' ^ m) = 0) :
    ArborealDecay.Horo.shiftT v c n' K F x = F x := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [ArborealDecay.Horo.shiftT, sum_range_succ', sum_eq_zero fun m _ => hn' (m + 1) (by omega)]
  simp

theorem shL_zero (F : X → Gr O) (x : X) (hK : 0 < K) : shL v c n K F x 0 = F x :=
  shiftT_of_one_le v c F (0 • n) x hK fun m hm => by
    rw [zero_smul, zero_pow hm.ne', mul_zero, smul_zero]

theorem shL_one (F : X → Gr O) (x : X) :
    shL v c n K F x 1 = ArborealDecay.Horo.shiftT v c n K F x := by
  rw [shL, one_smul]

theorem one_ne_zero_gr : (1 : Gr O) ≠ 0 := by
  intro h
  have := congrArg body h
  simp at this

/-! ### Multiplicativity -/

/-- **Shifts are multiplicative.** -/
theorem shiftT_mul (hn : n ^ K = 0) (hcomm : ∀ a, n * a = a * n) {F G : X → Gr O}
    (hF : SSmooth F) (hG : SSmooth G) (x : X) :
    ArborealDecay.Horo.shiftT v c n K (fun y => F y * G y) x =
      ArborealDecay.Horo.shiftT v c n K F x * ArborealDecay.Horo.shiftT v c n K G x := by
  have hK : 0 < K := pos_of_pow_eq_zero hn one_ne_zero_gr
  have hnY : ∀ (Y : Gr O) (j : ℕ), n * Y * n ^ j = Y * n ^ (j + 1) := fun Y j => by
    rw [hcomm Y, mul_assoc, ← pow_succ']
  let D : (X → Gr O) → (X → Gr O) → ℝ → Gr O := fun F G t =>
    shL v c n K (fun y => F y * G y) x t - shL v c n K F x t * shL v c n K G x t
  have hDd : ∀ F G, Super.SDiff (D F G) := fun F G =>
    (sdiff_shL v c n K _ x).sub ((sdiff_shL v c n K F x).mul (sdiff_shL v c n K G x))
  have hD0 : ∀ F G, D F G 0 = 0 := fun F G => by
    simp only [D, shL_zero v c _ x hK, sub_self]
  have hderiv : ∀ F G, SSmooth F → SSmooth G → ∀ t,
      pd 1 (D F G) t = c x • (n * (D (pd v F) G t + D F (pd v G) t)) := by
    intro F G hF hG t
    rw [show D F G = fun t => shL v c n K (fun y => F y * G y) x t -
      shL v c n K F x t * shL v c n K G x t from rfl,
      pd_sub (sdiff_shL v c n K _ x) ((sdiff_shL v c n K F x).mul (sdiff_shL v c n K G x)),
      pd_mul (sdiff_shL v c n K F x) (sdiff_shL v c n K G x), pd_shL v c hn hcomm,
      pd_shL v c hn hcomm, pd_shL v c hn hcomm]
    have hpd : pd v (fun y => F y * G y) = fun y => pd v F y * G y + F y * pd v G y :=
      funext fun y => pd_mul hF.sdiff hG.sdiff v y
    have hadd : shL v c n K (pd v fun y => F y * G y) x t =
        shL v c n K (fun y => pd v F y * G y) x t + shL v c n K (fun y => F y * pd v G y) x t := by
      rw [hpd]
      exact shiftT_add v c (t • n) K ((hF.deriv v).mul hG) (hF.mul (hG.deriv v)) x
    rw [hadd]
    simp only [D]
    set a := shL v c n K F x t
    set b := shL v c n K G x t
    set a' := shL v c n K (pd v F) x t
    set b' := shL v c n K (pd v G) x t
    have h1 : c x • (n * a') * b = c x • (n * (a' * b)) := by rw [smul_mul_assoc, mul_assoc]
    have h2 : a * (c x • (n * b')) = c x • (n * (a * b')) := by
      rw [mul_smul_comm, ← mul_assoc, ← hcomm a, mul_assoc]
    rw [h1, h2, ← smul_add, ← smul_sub]
    congr 1
    noncomm_ring
  have key : ∀ m, ∀ F G, SSmooth F → SSmooth G → ∀ t, D F G t * n ^ (K - m) = 0 := by
    intro m
    induction m with
    | zero => intro F G _ _ t; rw [Nat.sub_zero, hn, mul_zero]
    | succ m ih =>
      intro F G hF hG t
      by_cases hm : K ≤ m
      · rw [show K - (m + 1) = K - m by omega]; exact ih F G hF hG t
      · have hj : K - m = K - (m + 1) + 1 := by omega
        have hconst := eq_of_pd_eq_zero (F := fun t => D F G t * n ^ (K - (m + 1)))
          ((hDd F G).mul (SDiff.const _)) (fun t => by
            rw [pd_mul (hDd F G) (SDiff.const _), pd_const, mul_zero, add_zero,
              hderiv F G hF hG t, smul_mul_assoc, hnY, ← hj, add_mul,
              ih _ _ (hF.deriv v) hG t, ih _ _ hF (hG.deriv v) t, add_zero, smul_zero]) t 0
        rw [hconst, hD0, zero_mul]
  have hfin := key K F G hF hG 1
  rw [Nat.sub_self, pow_zero, mul_one] at hfin
  simpa only [D, shL_one, sub_eq_zero] using hfin

/-! ### Composition -/

theorem body_shiftT (F : X → Gr O) {n' : Gr O} (hn0 : body n' = 0) (hK : 0 < K) (x : X) :
    body (ArborealDecay.Horo.shiftT v c n' K F x) = body (F x) := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [ArborealDecay.Horo.shiftT, map_sum, sum_range_succ']
  simp [map_mul, map_pow, hn0]

theorem isEven_shiftT {F : X → Gr O} (hF : SSmooth F) (hE : ∀ x, IsEven (F x)) {n' : Gr O}
    (hn : IsEven n') (x : X) : IsEven (ArborealDecay.Horo.shiftT v c n' K F x) :=
  IsEven.sum _ fun m _ => ((isEven_pdn hF hE v m x).mul (hn.pow m)).smul _

/-- **Shifts commute with composition**: `g(S)(x + c n v) = g(S(x + c n v))`. -/
theorem shiftT_scomp (hn : n ^ K = 0) (hcomm : ∀ a, n * a = a * n) (hnE : IsEven n)
    (hn0 : body n = 0) {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {S : X → Gr O} (hS : SSmooth S) (hE : ∀ y, IsEven (S y)) (hb : ∀ y, body (S y) ∈ U)
    (x : X) :
    ArborealDecay.Horo.shiftT v c n K (fun y => scomp g (S y)) x =
      scomp g (ArborealDecay.Horo.shiftT v c n K S x) := by
  have hK : 0 < K := pos_of_pow_eq_zero hn one_ne_zero_gr
  have hnY : ∀ (Y : Gr O) (j : ℕ), n * Y * n ^ j = Y * n ^ (j + 1) := fun Y j => by
    rw [hcomm Y, mul_assoc, ← pow_succ']
  set P := shL v c n K S x
  have hP : Super.SDiff P := sdiff_shL v c n K S x
  have hPE : ∀ t, IsEven (P t) := fun t => isEven_shiftT v c hS hE (hnE.smul t) x
  have hPb : ∀ t, body (P t) = body (S x) := fun t =>
    body_shiftT v c S (by rw [map_smul, hn0, smul_zero]) hK x
  have hPU : ∀ t, body (P t) ∈ U := fun t => by rw [hPb]; exact hb x
  have hnt : ∀ t : ℝ, (t • n) ^ K = 0 := fun t => by rw [smul_pow, hn, smul_zero]
  have hct : ∀ t : ℝ, ∀ a, (t • n) * a = a * (t • n) := fun t a => by
    rw [smul_mul_assoc, hcomm, mul_smul_comm]
  let D : (ℝ → ℝ) → ℝ → Gr O := fun φ t =>
    shL v c n K (fun y => scomp φ (S y)) x t - scomp φ (P t)
  have hDd : ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → Super.SDiff (D φ) := fun φ hφ =>
    (sdiff_shL v c n K _ x).sub (SDiff.scomp hU hφ hP hPE hPU)
  have hD0 : ∀ φ, D φ 0 = 0 := fun φ => by
    simp only [D, P, shL_zero v c _ x hK, sub_self]
  have hderiv : ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → ∀ t,
      pd 1 (D φ) t = c x • (n * (D (deriv φ) t * shL v c n K (pd v S) x t)) := by
    intro φ hφ t
    have hφS : SSmooth fun y => scomp φ (S y) := hS.scomp hU hφ hE hb
    have hφ'S : SSmooth fun y => scomp (deriv φ) (S y) :=
      hS.scomp hU (contDiffOn_deriv hU hφ) hE hb
    have hpd : pd v (fun y => scomp φ (S y)) = fun y => scomp (deriv φ) (S y) * pd v S y :=
      funext fun y => pd_scomp hU hφ hS.sdiff hE hb v y
    have hmul : shL v c n K (pd v fun y => scomp φ (S y)) x t =
        shL v c n K (fun y => scomp (deriv φ) (S y)) x t * shL v c n K (pd v S) x t := by
      rw [hpd]
      exact shiftT_mul v c (hnt t) (hct t) hφ'S (hS.deriv v) x
    rw [show D φ = fun t => shL v c n K (fun y => scomp φ (S y)) x t - scomp φ (P t) from rfl,
      pd_sub (sdiff_shL v c n K _ x) (SDiff.scomp hU hφ hP hPE hPU),
      pd_scomp hU hφ hP hPE hPU, pd_shL v c hn hcomm, show P = shL v c n K S x from rfl,
      pd_shL v c hn hcomm, hmul]
    simp only [D, P]
    set a := shL v c n K (fun y => scomp (deriv φ) (S y)) x t
    set q := shL v c n K (pd v S) x t
    set z := scomp (deriv φ) (shL v c n K S x t)
    rw [mul_smul_comm, ← mul_assoc z n q, ← hcomm z, mul_assoc, ← smul_sub, sub_mul, mul_sub]
  have key : ∀ m, ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → ∀ t, D φ t * n ^ (K - m) = 0 := by
    intro m
    induction m with
    | zero => intro φ _ t; rw [Nat.sub_zero, hn, mul_zero]
    | succ m ih =>
      intro φ hφ t
      by_cases hm : K ≤ m
      · rw [show K - (m + 1) = K - m by omega]; exact ih φ hφ t
      · have hj : K - m = K - (m + 1) + 1 := by omega
        have hconst := eq_of_pd_eq_zero (F := fun t => D φ t * n ^ (K - (m + 1)))
          ((hDd φ hφ).mul (SDiff.const _)) (fun t => by
            rw [pd_mul (hDd φ hφ) (SDiff.const _), pd_const, mul_zero, add_zero,
              hderiv φ hφ t]
            set q := shL v c n K (pd v S) x t
            have hq : q * n ^ (K - (m + 1) + 1) = n ^ (K - (m + 1) + 1) * q :=
              (Commute.pow_left (hcomm q) _).eq.symm
            rw [smul_mul_assoc, hnY, mul_assoc, hq, ← mul_assoc, ← hj,
              ih _ (contDiffOn_deriv hU hφ) t, zero_mul, smul_zero]) t 0
        rw [hconst, hD0, zero_mul]
  have hfin := key K g hg 1
  rw [Nat.sub_self, pow_zero, mul_one] at hfin
  simpa only [D, P, shL_one, sub_eq_zero] using hfin

end Shift

end

end ArborealDecay.BCHS

end
