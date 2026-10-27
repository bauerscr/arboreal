import FRD.Decomp

/-!
# Independence of the torus

`C_j(x, y)`, `j < N`, is a function of `x - y` that does not depend on the torus: for every
torus of side `n > L^j` it is `c_j(r(x - y))`, where `r : Λ → ℤ^d` is the centred representative
and `c_j : ℤ^d → ℝ` is defined on `ℤ^d` (`Cj_eq_Zd`).

The proof lifts `A = (-Δ + m²)/(2d + m²)` to the operator `A_∞` on finitely supported functions
on `ℤ^d` and uses that polynomials of degree `k` in `A_∞` have range `k`.
-/

namespace FRD

noncomputable section

open Finset MeasureTheory Set Grassmann Matrix

variable {d : ℕ}

/-- `ℤ^d`. -/
abbrev Zd (d : ℕ) := Fin d → ℤ

/-- The unit vectors `±e_i` of `ℤ^d`. -/
def dirZ : Dir d → Zd d
  | Sum.inl i => Pi.single i 1
  | Sum.inr i => -Pi.single i 1

/-- Translation of finitely supported functions: `(τ_a f)(z) = f(z - a)`. -/
def transl (a : Zd d) : (Zd d →₀ ℝ) →ₗ[ℝ] (Zd d →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ (· + a)

theorem transl_apply (a : Zd d) (f : Zd d →₀ ℝ) (z : Zd d) : transl a f z = f (z - a) := by
  conv_lhs => rw [show z = (z - a) + a by abel]
  exact Finsupp.mapDomain_apply (add_left_injective a) f _

theorem transl_single (a z : Zd d) (c : ℝ) :
    transl a (Finsupp.single z c) = Finsupp.single (z + a) c := by
  simp [transl, Finsupp.mapDomain_single]

/-- `A_∞ = (-Δ^{ℤ^d} + m²)/(2d + m²)`: `(A_∞ f)(z) = f(z) - (2d+m²)^{-1} ∑_e f(z + e)`. -/
def Ainf (d : ℕ) (msq : ℝ) : Module.End ℝ (Zd d →₀ ℝ) :=
  LinearMap.id - (2 * d + msq)⁻¹ • ∑ e : Dir d, transl (-dirZ e)

theorem Ainf_apply (msq : ℝ) (f : Zd d →₀ ℝ) (z : Zd d) :
    Ainf d msq f z = f z - (2 * d + msq)⁻¹ * ∑ e : Dir d, f (z + dirZ e) := by
  simp only [Ainf, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.coe_sum, Finset.sum_apply, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Finsupp.coe_finsetSum, transl_apply, sub_neg_eq_add]

theorem Ainf_transl (msq : ℝ) (a : Zd d) (f : Zd d →₀ ℝ) :
    Ainf d msq (transl a f) = transl a (Ainf d msq f) := by
  ext z
  simp only [Ainf_apply, transl_apply]
  congr 2
  refine sum_congr rfl fun e _ => ?_
  congr 1; abel

/-- Polynomials of an operator commute with everything the operator commutes with. -/
theorem commute_aeval {M : Type*} [AddCommGroup M] [Module ℝ M] {T S : Module.End ℝ M}
    (h : Commute T S) (p : Polynomial ℝ) : Commute (Polynomial.aeval T p) S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_left k).smul_left a

theorem aeval_Ainf_transl (msq : ℝ) (p : Polynomial ℝ) (a : Zd d) (f : Zd d →₀ ℝ) :
    Polynomial.aeval (Ainf d msq) p (transl a f) = transl a (Polynomial.aeval (Ainf d msq) p f) := by
  have hc : Commute (Ainf d msq) (transl a) := LinearMap.ext fun f => Ainf_transl msq a f
  exact LinearMap.congr_fun (commute_aeval hc p) f

theorem Ainf_single (msq : ℝ) (z : Zd d) (c : ℝ) :
    Ainf d msq (Finsupp.single z c) =
      Finsupp.single z c - (2 * d + msq)⁻¹ • ∑ e : Dir d, Finsupp.single (z - dirZ e) c := by
  simp [Ainf, transl_single, sub_eq_add_neg]

/-! ### Projection to the torus -/

variable {n : ℕ} [NeZero n]

/-- The covering map `ℤ^d → Λ`. -/
def prj (z : Zd d) : Torus d n := (fun i => (z i : ZMod n) : Fin d → ZMod n)

theorem prj_add (z w : Zd d) : (prj (z + w) : Torus d n) = prj z + prj w := by
  show (fun i => ((z i + w i : ℤ) : ZMod n)) = _
  funext i; push_cast; rfl

theorem prj_sub (z w : Zd d) : (prj (z - w) : Torus d n) = prj z - prj w := by
  show (fun i => ((z i - w i : ℤ) : ZMod n)) = _
  funext i; push_cast; rfl

theorem prj_neg (z : Zd d) : (prj (-z) : Torus d n) = -prj z := by
  funext i
  show (((-z) i : ℤ) : ZMod n) = -((z i : ℤ) : ZMod n)
  simp

theorem prj_dirZ (e : Dir d) : (prj (dirZ e) : Torus d n) = dirVec e := by
  rcases e with i | i
  · show (fun j => (((Pi.single i (1 : ℤ) : Fin d → ℤ) j : ℤ) : ZMod n)) =
      (Pi.single i 1 : Fin d → ZMod n)
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  · show (fun j => (((-(Pi.single i (1 : ℤ) : Fin d → ℤ)) j : ℤ) : ZMod n)) =
      -(Pi.single i 1 : Fin d → ZMod n)
    funext j; by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- Pushing finitely supported functions on `ℤ^d` forward to the torus. -/
def push : (Zd d →₀ ℝ) →ₗ[ℝ] (Torus d n → ℝ) :=
  Finsupp.lcoeFun ∘ₗ Finsupp.lmapDomain ℝ ℝ prj

theorem push_single (z : Zd d) (c : ℝ) :
    (push (Finsupp.single z c) : Torus d n → ℝ) = Pi.single (prj z) c := by
  ext x; simp [push, Finsupp.mapDomain_single, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem push_apply (f : Zd d →₀ ℝ) (x : Torus d n) :
    push f x = ∑ z ∈ f.support, if prj z = x then f z else 0 := by
  simp only [push, LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.lcoeFun_apply,
    Finsupp.mapDomain, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]

/-- `A = (-Δ + m²)/(2d + m²)` on the torus. -/
abbrev Amat (d n : ℕ) [NeZero n] (msq : ℝ) : Matrix (Torus d n) (Torus d n) ℝ := fmat (uhat msq)

theorem Amat_apply {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) (x y : Torus d n) :
    Amat d n msq x y = (if x = y then 1 else 0) -
      (2 * d + msq)⁻¹ * ∑ e : Dir d, if y = x + dirVec e then 1 else 0 := by
  rw [Amat, fmat_uhat, Matrix.smul_apply, Matrix.add_apply, negLap, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, smul_eq_mul]
  split_ifs
  · field_simp; ring
  · ring

theorem mulVec_single_apply {M : Matrix (Torus d n) (Torus d n) ℝ} (j x : Torus d n) (c : ℝ) :
    (M *ᵥ Pi.single j c) x = M x j * c := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `push ∘ A_∞ = A ∘ push`. -/
theorem push_Ainf {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) :
    (push : (Zd d →₀ ℝ) →ₗ[ℝ] (Torus d n → ℝ)) ∘ₗ Ainf d msq =
      (Amat d n msq).mulVecLin ∘ₗ push := by
  refine Finsupp.lhom_ext fun z c => ?_
  ext x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Ainf_single, map_sub, map_smul, map_sum,
    push_single, Matrix.mulVecLin_apply, mulVec_single_apply, Amat_apply hmsq]
  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, push_single, smul_eq_mul, prj_sub,
    prj_dirZ, Pi.single_apply]
  rw [sub_mul, mul_assoc, Finset.sum_mul]
  congr 1
  · split_ifs <;> simp
  congr 1
  refine sum_congr rfl fun e _ => ?_
  by_cases h : x = prj z - dirVec e
  · rw [if_pos h, if_pos (by rw [h]; abel), one_mul]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h']; abel)), zero_mul]

theorem push_aeval {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) (p : Polynomial ℝ) (f : Zd d →₀ ℝ) :
    (push (Polynomial.aeval (Ainf d msq) p f) : Torus d n → ℝ) =
      Polynomial.aeval (Amat d n msq) p *ᵥ push f := by
  have hpow : ∀ k : ℕ, ∀ f, (push ((Ainf d msq ^ k) f) : Torus d n → ℝ) =
      (Amat d n msq ^ k) *ᵥ push f := by
    intro k
    induction k with
    | zero => intro f; simp
    | succ k ih =>
      intro f
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]
      congr 1
      exact LinearMap.congr_fun (push_Ainf hmsq) f
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.add_mulVec]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, LinearMap.smul_apply, map_smul, hpow, Matrix.smul_mulVec]

/-! ### Range on `ℤ^d` -/

/-- `|z|_∞` on `ℤ^d`. -/
def supNormZ (z : Zd d) : ℕ := Finset.univ.sup fun i => (z i).natAbs

theorem supNormZ_le_iff (z : Zd d) (k : ℕ) : supNormZ z ≤ k ↔ ∀ i, (z i).natAbs ≤ k := by
  simp [supNormZ, Finset.sup_le_iff]

theorem natAbs_le_supNormZ (z : Zd d) (i : Fin d) : (z i).natAbs ≤ supNormZ z :=
  Finset.le_sup (f := fun i => (z i).natAbs) (mem_univ i)

theorem supNormZ_add_le (z w : Zd d) : supNormZ (z + w) ≤ supNormZ z + supNormZ w := by
  rw [supNormZ_le_iff]
  intro i
  exact (Int.natAbs_add_le _ _).trans (add_le_add (natAbs_le_supNormZ z i) (natAbs_le_supNormZ w i))

theorem supNormZ_dirZ (e : Dir d) : supNormZ (dirZ e) ≤ 1 := by
  rw [supNormZ_le_iff]
  intro j
  rcases e with i | i <;> by_cases h : j = i <;> simp [dirZ, Pi.single_apply, h]

/-- `f` is supported in the box `|z|_∞ ≤ R`. -/
def BoxSupp (R : ℕ) (f : Zd d →₀ ℝ) : Prop := ∀ z, f z ≠ 0 → supNormZ z ≤ R

theorem BoxSupp.mono {R R' : ℕ} {f : Zd d →₀ ℝ} (hf : BoxSupp R f) (h : R ≤ R') : BoxSupp R' f :=
  fun z hz => (hf z hz).trans h

theorem BoxSupp.apply_Ainf {R : ℕ} {f : Zd d →₀ ℝ} (hf : BoxSupp R f) (msq : ℝ) :
    BoxSupp (R + 1) (Ainf d msq f) := by
  intro z hz
  rw [Ainf_apply] at hz
  by_cases h0 : f z = 0
  · rw [h0, zero_sub, neg_ne_zero] at hz
    obtain ⟨e, -, he⟩ : ∃ e ∈ Finset.univ, f (z + dirZ e) ≠ 0 := by
      by_contra hc; push Not at hc
      exact hz (by rw [sum_eq_zero fun e he => hc e he, mul_zero])
    have h1 := hf _ he
    have h2 := supNormZ_add_le (z + dirZ e) (-dirZ e)
    have h3 : supNormZ (-dirZ e) ≤ 1 := by
      have := supNormZ_dirZ e
      rw [supNormZ_le_iff] at this ⊢
      intro i; simpa using this i
    rw [add_neg_cancel_right] at h2
    omega
  · exact (hf z h0).trans (Nat.le_succ R)

theorem BoxSupp.add {R : ℕ} {f g : Zd d →₀ ℝ} (hf : BoxSupp R f) (hg : BoxSupp R g) :
    BoxSupp R (f + g) := by
  intro z hz
  by_cases h : f z = 0
  · exact hg z (by simpa [h] using hz)
  · exact hf z h

theorem BoxSupp.smul {R : ℕ} {f : Zd d →₀ ℝ} (hf : BoxSupp R f) (c : ℝ) : BoxSupp R (c • f) :=
  fun z hz => hf z (by intro h; apply hz; simp [h])

theorem BoxSupp.zero (R : ℕ) : BoxSupp R (0 : Zd d →₀ ℝ) := fun _ hz => by simp at hz

theorem BoxSupp.aeval {R : ℕ} {f : Zd d →₀ ℝ} (hf : BoxSupp R f) (msq : ℝ) (p : Polynomial ℝ) :
    BoxSupp (R + p.natDegree) (Polynomial.aeval (Ainf d msq) p f) := by
  have hpow : ∀ k : ℕ, BoxSupp (R + k) ((Ainf d msq ^ k) f) := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact ih.apply_Ainf msq
  rw [Polynomial.aeval_eq_sum_range, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_induction _ (BoxSupp (R + p.natDegree)) (fun _ _ ha hb => ha.add hb)
    (BoxSupp.zero _) fun i hi => ?_
  rw [LinearMap.smul_apply]
  exact ((hpow i).mono (by simp at hi; omega)).smul _

/-! ### The centred representative -/

/-- The centred representative `r(x) ∈ ℤ^d` of `x ∈ Λ`, with `|r(x)_i| = |x_i|`. -/
def rep (x : Torus d n) : Zd d := fun i =>
  if ((x : Fin d → ZMod n) i).val ≤ n - ((x : Fin d → ZMod n) i).val then
    (((x : Fin d → ZMod n) i).val : ℤ) else (((x : Fin d → ZMod n) i).val : ℤ) - n

theorem prj_rep (x : Torus d n) : (prj (rep x) : Torus d n) = x := by
  show (fun i => ((rep x i : ℤ) : ZMod n)) = (x : Fin d → ZMod n)
  funext i
  unfold rep
  split_ifs <;> simp

theorem natAbs_rep (x : Torus d n) (i : Fin d) :
    (rep x i).natAbs = zabs ((x : Fin d → ZMod n) i) := by
  unfold rep zabs
  have := ZMod.val_lt ((x : Fin d → ZMod n) i)
  split_ifs with h
  · rw [min_eq_left h, Int.natAbs_natCast]
  · rw [min_eq_right (by omega)]; omega

/-- Uniqueness: a lift `z` of `x` with `2|z|_∞ < n` is `r(x)`. -/
theorem eq_rep {z : Zd d} {x : Torus d n} (hz : prj z = x) (hs : 2 * supNormZ z < n) :
    z = rep x := by
  funext i
  have h1 : ((z i : ℤ) : ZMod n) = ((rep x i : ℤ) : ZMod n) := by
    have e1 := congrFun (congrArg (fun y : Torus d n => (y : Fin d → ZMod n)) hz) i
    have e2 := congrFun (congrArg (fun y : Torus d n => (y : Fin d → ZMod n)) (prj_rep x)) i
    exact e1.trans e2.symm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨c, hc⟩ := h1
  have ha := natAbs_le_supNormZ z i
  have hb : (rep x i).natAbs ≤ n / 2 := by
    rw [natAbs_rep]; unfold zabs; omega
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · have : (n : ℤ) * c ≤ -n := by nlinarith
    omega
  · subst hc0; omega
  · have : (n : ℤ) ≤ n * c := by nlinarith
    omega

/-- The main lifting lemma: `p(A)(x, y) = (p(A_∞) δ_0)(r(x - y))` for `2 deg p < n`. -/
theorem aeval_Amat_eq {msq : ℝ} (hmsq : 2 * (d : ℝ) + msq ≠ 0) (p : Polynomial ℝ)
    (hp : 2 * p.natDegree < n) (x y : Torus d n) :
    Polynomial.aeval (Amat d n msq) p x y =
      Polynomial.aeval (Ainf d msq) p (Finsupp.single 0 1) (rep (x - y)) := by
  set h := Polynomial.aeval (Ainf d msq) p (Finsupp.single 0 1)
  have hbox : BoxSupp p.natDegree h := by
    have h0 : BoxSupp 0 (Finsupp.single (0 : Zd d) (1 : ℝ)) := by
      intro z hz
      rw [Finsupp.single_apply] at hz
      split_ifs at hz with h'
      · subst h'; simp [supNormZ]
      · exact absurd rfl hz
    simpa using h0.aeval msq p
  set yt := rep y
  have hlift : (Pi.single y 1 : Torus d n → ℝ) = push (transl yt (Finsupp.single 0 1)) := by
    rw [transl_single, zero_add, push_single, prj_rep]
  have h1 : Polynomial.aeval (Amat d n msq) p x y =
      (Polynomial.aeval (Amat d n msq) p *ᵥ Pi.single y 1) x := by
    rw [mulVec_single_apply, mul_one]
  rw [h1, hlift, ← push_aeval hmsq, aeval_Ainf_transl, push_apply]
  rw [Finset.sum_eq_single (yt + rep (x - y))]
  · rw [if_pos, transl_apply, add_sub_cancel_left]
    rw [prj_add, prj_rep, prj_rep]; abel
  · intro z hz hne
    rw [if_neg]
    intro hzx
    apply hne
    rw [Finsupp.mem_support_iff, transl_apply] at hz
    have hs := hbox _ hz
    have := eq_rep (x := x - y) (z := z - yt) (by rw [prj_sub, hzx, prj_rep]) (by omega)
    rw [← this]; abel
  · intro hnot
    rw [Finsupp.notMem_support_iff] at hnot
    rw [hnot]; split_ifs <;> rfl

/-! ### `C_j` as a function on `ℤ^d` -/

variable (P : PtFamily)

/-- The covariance of the scales `S` on `ℤ^d`:
`c_S(z) = (2d+m²)^{-1} ∫_S t^2 (P_t(A_∞) δ_0)(z) dt/t`. -/
def covZ (d : ℕ) (msq : ℝ) (S : Set ℝ) (z : Zd d) : ℝ :=
  (2 * d + msq)⁻¹ * ∫ t in S, t * Polynomial.aeval (Ainf d msq) (P.P t) (Finsupp.single 0 1) z

/-- Independence of the torus: on every torus of side `n > 2b`, the covariance of the scales
`(a, b]` is `c_{(a,b]}(r(x - y))`, with `c_{(a,b]}` defined on `ℤ^d` independently of `n`. -/
theorem cov_eq_covZ {msq : ℝ} (hmsq : 0 ≤ msq) (hd : 1 ≤ d) {a : ℝ} (b : ℝ) (ha : 0 ≤ a)
    (hb : 2 * b < n) (x y : Torus d n) :
    cov P msq (Ioc a b) x y = covZ P d msq (Ioc a b) (rep (x - y)) := by
  have hne : 2 * (d : ℝ) + msq ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [cov_apply_Ioc P hmsq b ha, covZ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
  have hdeg := P.natDegree_le t ht0
  have : 2 * (P.P t).natDegree < n := by
    have : (2 * (P.P t).natDegree : ℝ) < n := by linarith [ht.2]
    exact_mod_cast this
  exact congrArg (t * ·) (aeval_Amat_eq hne _ this x y)

/-- `C_j(x, y) = c_j(r(x - y))` on every torus of side `n > L^j`, where
`c_j = covZ P d m² (L^{j-1}/2, L^j/2]` does not depend on the torus. -/
theorem Cj_eq_Zd {msq : ℝ} (hmsq : 0 ≤ msq) (hd : 1 ≤ d) {L : ℝ} (hL : 0 ≤ L) (j : ℕ)
    (hn : L ^ j < n) (x y : Torus d n) :
    Cj P msq L j x y = covZ P d msq (Ioc (lowEnd L j) (L ^ j / 2)) (rep (x - y)) :=
  cov_eq_covZ P hmsq hd _ (lowEnd_nonneg hL j) (by linarith) x y

end

end FRD
