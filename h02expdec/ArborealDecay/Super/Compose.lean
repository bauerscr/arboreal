module

public import ArborealDecay.Super.Grassmann

/-!
# Composition of smooth functions with even Grassmann elements

For `a ∈ Gr O` write `a = s + n` with `s = body a ∈ ℝ` (the degree-zero part,
`ExteriorAlgebra.algebraMapInv`) and `n = soul a`.  If `a` is even, `n` is nilpotent
(`soul_pow_card_succ`: `n ^ (|O| + 1) = 0`), and for `g : ℝ → ℝ` we define (BHS App. A)
`g(a) := ∑_k g^{(k)}(s) / k! · n^k` (`scomp g a`), a finite sum.

Main algebraic facts:

* `body_scomp`: the body of `g(a)` is `g(body a)`;
* `map_scomp`: algebra homomorphisms preserving the body commute with `g(·)`;
  in particular `pi0 (g(a)) = g(pi0 a)` (see `ArborealDecay.Super.ComposeDiff`);
* `dgen_scomp`: the fermionic chain rule `∂_θ g(a) = g'(a) ∂_θ a`;
* `scomp_mul_fun`: `(g h)(a) = g(a) h(a)`;
* `scomp_exp`: `exp(a) = e^{body a} · IsNilpotent.exp (soul a)`;
* `inverse_eq_scomp_inv`: `Ring.inverse a = (t ↦ t⁻¹)(a)` when `body a ≠ 0`;
* `scomp_of_soul_sq`: `g(a) = g(s) + g'(s) n` when `n² = 0`.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann Finset

set_option linter.unusedSectionVars false

variable {O : Type*}

/-! ### Body and soul -/

/-- The body (degree-zero part) of a Grassmann element. -/
def body : Gr O →ₐ[ℝ] ℝ := ExteriorAlgebra.algebraMapInv

/-- The soul `a - body a`. -/
def soul (a : Gr O) : Gr O := a - algebraMap ℝ (Gr O) (body a)

/-- `a` is even. -/
def IsEven (a : Gr O) : Prop := inv' a = a

@[simp] theorem body_algebraMap (r : ℝ) : body (algebraMap ℝ (Gr O) r) = r := AlgHom.commutes _ r

@[simp] theorem body_one : body (1 : Gr O) = 1 := map_one _

theorem body_ι (v : O → ℝ) : body (ExteriorAlgebra.ι ℝ v) = 0 := algebraMapInv_ι v

@[simp] theorem body_gen [DecidableEq O] (o : O) : body (gen o : Gr O) = 0 := body_ι _

theorem body_inv' (a : Gr O) : body (inv' a) = body a := algebraMapInv_inv' a

theorem soul_add_body (a : Gr O) : soul a + algebraMap ℝ (Gr O) (body a) = a := sub_add_cancel _ _

theorem eq_body_add_soul (a : Gr O) : a = algebraMap ℝ (Gr O) (body a) + soul a := by
  rw [soul]; abel

@[simp] theorem body_soul (a : Gr O) : body (soul a) = 0 := by simp [soul]

theorem soul_add (a b : Gr O) : soul (a + b) = soul a + soul b := by
  simp only [soul, map_add]; abel

theorem soul_neg (a : Gr O) : soul (-a) = -soul a := by
  simp only [soul, map_neg]; abel

theorem soul_algebraMap_add (r : ℝ) (a : Gr O) :
    soul (algebraMap ℝ (Gr O) r + a) = soul a := by
  simp only [soul, map_add, body_algebraMap]; abel

theorem soul_of_body_eq_zero {a : Gr O} (h : body a = 0) : soul a = a := by simp [soul, h]

theorem IsEven.algebraMap (r : ℝ) : IsEven (algebraMap ℝ (Gr O) r) := AlgHom.commutes _ r

theorem IsEven.one : IsEven (1 : Gr O) := map_one _

theorem IsEven.zero : IsEven (0 : Gr O) := map_zero _

theorem IsEven.add {a b : Gr O} (ha : IsEven a) (hb : IsEven b) : IsEven (a + b) := by
  unfold IsEven at *; rw [map_add, ha, hb]

theorem IsEven.sub {a b : Gr O} (ha : IsEven a) (hb : IsEven b) : IsEven (a - b) := by
  unfold IsEven at *; rw [map_sub, ha, hb]

theorem IsEven.neg {a : Gr O} (ha : IsEven a) : IsEven (-a) := by
  unfold IsEven at *; rw [map_neg, ha]

theorem IsEven.mul {a b : Gr O} (ha : IsEven a) (hb : IsEven b) : IsEven (a * b) := by
  unfold IsEven at *; rw [map_mul, ha, hb]

theorem IsEven.smul {a : Gr O} (ha : IsEven a) (c : ℝ) : IsEven (c • a) := by
  unfold IsEven at *; rw [map_smul, ha]

theorem IsEven.pow {a : Gr O} (ha : IsEven a) (k : ℕ) : IsEven (a ^ k) := by
  unfold IsEven at *; rw [map_pow, ha]

theorem IsEven.sum {ι : Type*} (s : Finset ι) {f : ι → Gr O} (hf : ∀ i ∈ s, IsEven (f i)) :
    IsEven (∑ i ∈ s, f i) := by
  unfold IsEven at *; rw [map_sum]; exact Finset.sum_congr rfl hf

theorem IsEven.soul {a : Gr O} (ha : IsEven a) : IsEven (soul a) :=
  ha.sub (IsEven.algebraMap _)

theorem IsEven.comm {a : Gr O} (ha : IsEven a) (b : Gr O) : a * b = b * a :=
  mul_comm_of_even' ha b

theorem IsEven.commute {a : Gr O} (ha : IsEven a) (b : Gr O) : Commute a b := ha.comm b

/-! ### Nilpotency of souls of even elements -/

theorem body_killA (S : Set O) (x : Gr O) : body (killA S x) = body x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp only [killA, ExteriorAlgebra.map_apply_ι]; rw [body_ι, body_ι]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem killA_univ (x : Gr O) : killA Set.univ x = algebraMap ℝ (Gr O) (body x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    have : killV (Set.univ : Set O) v = 0 := by
      ext o; simp [killV_apply]
    simp only [killA, ExteriorAlgebra.map_apply_ι, this, map_zero]
    rw [body_ι, map_zero]
  | mul a b ha hb => rw [map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]

section Expand

variable [DecidableEq O]

theorem expand_mul_aux {θ A0 a1 B0 b1 : Gr O} (hθ : θ * θ = 0) (hA : A0 * θ = θ * inv' A0)
    (hiθ : inv' θ = -θ) :
    (A0 + θ * a1) * (B0 + θ * b1) =
      A0 * B0 + θ * (a1 * (B0 + θ * b1) + inv' (A0 + θ * a1) * b1) := by
  rw [map_add, map_mul, hiθ]
  have h1 : A0 * (θ * b1) = θ * (inv' A0 * b1) := by rw [← mul_assoc, hA, mul_assoc]
  have h2 : θ * (-θ * inv' a1 * b1) = 0 := by
    simp only [neg_mul, mul_neg, ← mul_assoc, hθ, zero_mul, neg_zero]
  simp only [add_mul, mul_add]
  rw [h1, h2, add_zero, ← mul_assoc θ a1 B0, ← mul_assoc θ a1 (θ * b1)]
  abel

/-- `x = π_o x + θ_o ∂_{θ_o} x`. -/
theorem expand (o : O) (x : Gr O) : x = killA {o} x + gen o * dgen o x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
    have hv : v = killV {o} v + v o • Pi.single o 1 := by
      ext o'
      by_cases h : o' = o
      · subst h; simp [killV_apply]
      · simp [killV_apply, h]
    have hd : dgen o (CliffordAlgebra.ι 0 v) = algebraMap ℝ (Gr O) (v o) := by
      simp [dgen, contractLeft_ι]
    rw [hd, ← Algebra.commutes, ← Algebra.smul_def]
    simp only [killA, gen]
    change ExteriorAlgebra.ι ℝ v = ExteriorAlgebra.map (killV {o}) (ExteriorAlgebra.ι ℝ v) + _
    rw [ExteriorAlgebra.map_apply_ι, ← map_smul, ← map_add, ← hv]
  | mul a b ha hb =>
    have hθ : gen o * gen o = (0 : Gr O) := gen_mul_gen_self o
    have hA : killA {o} a * gen o = gen o * inv' (killA {o} a) := by
      rw [gen_mul_eq, inv'_inv']
    rw [map_mul, dgen_mul]
    conv_lhs => rw [ha, hb]
    rw [expand_mul_aux hθ hA (inv'_gen o), ← hb, ← ha]
  | add a b ha hb =>
    rw [map_add, map_add, mul_add]
    conv_lhs => rw [ha, hb]
    abel

theorem add_pow_of_sq_zero {y u : Gr O} (hc : y * u = u * y) (hu : u * u = 0) (m : ℕ) :
    (y + u) ^ (m + 1) = y ^ (m + 1) + ((m + 1 : ℕ) : ℝ) • (y ^ m * u) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : y ^ m * u * y = y ^ (m + 1) * u := by
      rw [mul_assoc, ← hc, ← mul_assoc, ← pow_succ]
    have e2 : y ^ m * u * u = 0 := by rw [mul_assoc, hu, mul_zero]
    rw [pow_succ _ (m + 1), ih, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, e1, e2,
      ← pow_succ, smul_zero, add_zero]
    push_cast
    module

theorem pow_eq_zero_of_killA (T : Finset O) :
    ∀ x : Gr O, IsEven x → body x = 0 → killA (↑T)ᶜ x = x → x ^ (T.card + 1) = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro x _ h0 hk
    rw [Finset.coe_empty, Set.compl_empty, killA_univ, h0, map_zero] at hk
    rw [← hk]; simp
  | insert o T hoT ih =>
    intro x hx h0 hk
    set y := killA {o} x
    set u := gen o * dgen o x
    have hxu : x = y + u := expand o x
    have hy : IsEven y := by unfold IsEven at *; rw [inv'_killA, hx]
    have hy0 : body y = 0 := by rw [body_killA, h0]
    have hyk : killA (↑T)ᶜ y = y := by
      have hs : ((↑T)ᶜ ∪ {o} ∪ (↑(insert o T))ᶜ : Set O) = {o} ∪ (↑(insert o T))ᶜ := by
        ext a; by_cases ha : a = o <;> simp [ha]
      show killA (↑T)ᶜ (killA {o} x) = killA {o} x
      calc killA (↑T)ᶜ (killA {o} x) = killA (↑T)ᶜ (killA {o} (killA (↑(insert o T))ᶜ x)) := by
            rw [hk]
        _ = killA ({o} ∪ (↑(insert o T))ᶜ) x := by rw [killA_killA, killA_killA, hs]
        _ = killA {o} x := by rw [← killA_killA, hk]
    have hIH := ih y hy hy0 hyk
    have hw : inv' (dgen o x) = -dgen o x := by
      have := dgen_inv' o x
      rw [hx] at this
      conv_rhs => rw [this]
      rw [neg_neg]
    have hu : u * u = 0 := by
      simp only [u]
      have e1 : dgen o x * gen o = gen o * inv' (dgen o x) := by rw [gen_mul_eq, inv'_inv']
      rw [mul_assoc, ← mul_assoc (dgen o x), e1, hw]
      simp only [← mul_assoc, gen_mul_gen_self, zero_mul]
    have hc : y * u = u * y := hy.comm u
    rw [Finset.card_insert_of_notMem hoT, hxu, add_pow_of_sq_zero hc hu, pow_succ, hIH,
      zero_mul, zero_mul, smul_zero, add_zero]

variable [Fintype O]

/-- The soul of an even element is nilpotent: `n ^ (|O| + 1) = 0`. -/
theorem pow_card_succ_eq_zero {x : Gr O} (hx : IsEven x) (h0 : body x = 0) :
    x ^ (Fintype.card O + 1) = 0 := by
  have := pow_eq_zero_of_killA (Finset.univ : Finset O) x hx h0 (by simp)
  rwa [Finset.card_univ] at this

theorem soul_pow_card_succ {a : Gr O} (ha : IsEven a) : soul a ^ (Fintype.card O + 1) = 0 :=
  pow_card_succ_eq_zero ha.soul (body_soul a)

theorem isNilpotent_soul {a : Gr O} (ha : IsEven a) : IsNilpotent (soul a) :=
  ⟨_, soul_pow_card_succ ha⟩

end Expand

/-! ### Taylor jets and composition -/

/-- The truncated Taylor sum `∑_{k < K} g^{(k)}(s) / k! · n^k`. -/
def jet (g : ℝ → ℝ) (s : ℝ) (n : Gr O) (K : ℕ) : Gr O :=
  ∑ k ∈ range K, (iteratedDeriv k g s / k.factorial) • n ^ k

/-- The composition `g(a) = ∑_k g^{(k)}(body a) / k! · (soul a)^k` of a function `g : ℝ → ℝ` with
`a ∈ Gr O` (BHS App. A).  The sum runs up to the nilpotency class of `soul a`; for even `a` this
is a finite Taylor sum (`scomp_eq_jet`). -/
def scomp (g : ℝ → ℝ) (a : Gr O) : Gr O := jet g (body a) (soul a) (nilpotencyClass (soul a))

theorem sum_range_pow_eq_of_le (f : ℕ → ℝ) {n : Gr O} {K L : ℕ} (hn : n ^ K = 0) (h : K ≤ L) :
    ∑ k ∈ range L, f k • n ^ k = ∑ k ∈ range K, f k • n ^ k := by
  induction L, h using Nat.le_induction with
  | base => rfl
  | succ L hKL ih => rw [sum_range_succ, ih, pow_eq_zero_of_le hKL hn, smul_zero, add_zero]

theorem jet_eq_of_le (g : ℝ → ℝ) (s : ℝ) {n : Gr O} {K L : ℕ} (hn : n ^ K = 0) (h : K ≤ L) :
    jet g s n L = jet g s n K :=
  sum_range_pow_eq_of_le _ hn h

theorem scomp_eq_jet (g : ℝ → ℝ) {a : Gr O} {K : ℕ} (hK : soul a ^ K = 0) :
    scomp g a = jet g (body a) (soul a) K :=
  (jet_eq_of_le g _ (pow_nilpotencyClass ⟨K, hK⟩) (csInf_le' hK)).symm

theorem scomp_eq_jet_card [DecidableEq O] [Fintype O] (g : ℝ → ℝ) {a : Gr O} (ha : IsEven a)
    {K : ℕ} (hK : Fintype.card O + 1 ≤ K) : scomp g a = jet g (body a) (soul a) K :=
  scomp_eq_jet g (pow_eq_zero_of_le hK (soul_pow_card_succ ha))

theorem jet_zero_left (s : ℝ) (n : Gr O) (K : ℕ) : jet (fun _ => (0 : ℝ)) s n K = 0 := by
  simp [jet]

theorem body_jet (g : ℝ → ℝ) (s : ℝ) {n : Gr O} (hn : body n = 0) (K : ℕ) :
    body (jet g s n (K + 1)) = g s := by
  rw [jet, sum_range_succ', map_add, map_sum]
  simp [hn]

theorem body_scomp (g : ℝ → ℝ) {a : Gr O} (hN : IsNilpotent (soul a)) :
    body (scomp g a) = g (body a) := by
  obtain ⟨K, hK⟩ := hN
  rw [scomp_eq_jet g (K := K + 1) (by rw [pow_succ, hK, zero_mul]), body_jet _ _ (body_soul a)]

theorem IsEven.jet (g : ℝ → ℝ) (s : ℝ) {n : Gr O} (hn : IsEven n) (K : ℕ) :
    IsEven (Super.jet g s n K) :=
  IsEven.sum _ fun k _ => (hn.pow k).smul _

theorem IsEven.scomp (g : ℝ → ℝ) {a : Gr O} (ha : IsEven a) : IsEven (scomp g a) :=
  ha.soul.jet _ _ _

theorem map_jet {O' : Type*} (φ : Gr O →ₐ[ℝ] Gr O') (g : ℝ → ℝ) (s : ℝ) (n : Gr O) (K : ℕ) :
    φ (jet g s n K) = jet g s (φ n) K := by
  simp [jet, map_sum, map_smul, map_pow]

theorem soul_map {O' : Type*} (φ : Gr O →ₐ[ℝ] Gr O') (hφ : ∀ x, body (φ x) = body x) (a : Gr O) :
    soul (φ a) = φ (soul a) := by
  rw [soul, soul, map_sub, AlgHom.commutes, hφ]

/-- Algebra homomorphisms preserving the body commute with composition. -/
theorem map_scomp {O' : Type*} (φ : Gr O →ₐ[ℝ] Gr O') (hφ : ∀ x, body (φ x) = body x)
    (g : ℝ → ℝ) {a : Gr O} (hN : IsNilpotent (soul a)) : φ (scomp g a) = scomp g (φ a) := by
  obtain ⟨K, hK⟩ := hN
  have hK' : soul (φ a) ^ K = 0 := by rw [soul_map φ hφ, ← map_pow, hK, map_zero]
  rw [scomp_eq_jet g hK, scomp_eq_jet g hK', map_jet, soul_map φ hφ, hφ]

theorem scomp_algebraMap (g : ℝ → ℝ) (r : ℝ) :
    scomp g (algebraMap ℝ (Gr O) r) = algebraMap ℝ (Gr O) (g r) := by
  have h0 : soul (algebraMap ℝ (Gr O) r) = 0 := by simp [soul]
  rw [scomp_eq_jet g (K := 1) (by rw [h0, pow_one]), jet]
  simp [Algebra.algebraMap_eq_smul_one]

/-- If `(soul a)² = 0` then `g(a) = g(s) + g'(s) n`. -/
theorem scomp_of_soul_sq (g : ℝ → ℝ) {a : Gr O} (h : soul a * soul a = 0) :
    scomp g a = algebraMap ℝ (Gr O) (g (body a)) + deriv g (body a) • soul a := by
  rw [scomp_eq_jet g (K := 2) (by rw [pow_two, h]), jet]
  simp [sum_range_succ, Algebra.algebraMap_eq_smul_one, iteratedDeriv_one]

/-! ### The fermionic chain rule -/

/-- The common computation behind the chain rules: if `D (n^{k+1}) = (k+1) n^k d` and `D 1 = 0`,
then `∑_{k ≤ K} g^{(k)}(s)/k! D(n^k) = g'(n) d` (truncated at `K`). -/
theorem sum_jet_deriv (g : ℝ → ℝ) (s : ℝ) (n d : Gr O) (D : ℕ → Gr O) (hD0 : D 0 = 0)
    (hD : ∀ k, D (k + 1) = ((k + 1 : ℕ) : ℝ) • (n ^ k * d)) (K : ℕ) :
    ∑ k ∈ range (K + 1), (iteratedDeriv k g s / k.factorial) • D k = jet (deriv g) s n K * d := by
  rw [sum_range_succ', hD0, smul_zero, add_zero, jet, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [hD, smul_smul, smul_mul_assoc, ← iteratedDeriv_succ']
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem dgen_pow (o : O) {n : Gr O} (hn : IsEven n) (k : ℕ) :
    dgen o (n ^ (k + 1)) = ((k + 1 : ℕ) : ℝ) • (n ^ k * dgen o n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : dgen o n * n ^ (k + 1) = n ^ (k + 1) * dgen o n := ((hn.pow (k + 1)).comm _).symm
    rw [pow_succ', dgen_mul, ih, show inv' n = n from hn, hc, mul_smul_comm, ← mul_assoc,
      ← pow_succ']
    push_cast
    module

theorem dgen_soul (o : O) (a : Gr O) : dgen o (soul a) = dgen o a := by
  simp [soul]

/-- **Fermionic chain rule**: `∂_θ g(a) = g'(a) ∂_θ a` for even `a`. -/
theorem dgen_scomp [DecidableEq O] [Fintype O] (o : O) (g : ℝ → ℝ) {a : Gr O} (ha : IsEven a) :
    dgen o (scomp g a) = scomp (deriv g) a * dgen o a := by
  rw [scomp_eq_jet_card g ha (K := Fintype.card O + 1 + 1) (by omega),
    scomp_eq_jet_card (deriv g) ha le_rfl, jet, map_sum]
  simp only [map_smul]
  rw [← dgen_soul o a]
  exact sum_jet_deriv g _ _ _ (fun k => dgen o (soul a ^ k)) (by simp)
    (fun k => dgen_pow o ha.soul k) _

/-! ### Products -/

/-- The Taylor polynomial `∑_{k<K} g^{(k)}(s)/k! X^k`. -/
def jpoly (g : ℝ → ℝ) (s : ℝ) (K : ℕ) : Polynomial ℝ :=
  ∑ k ∈ range K, Polynomial.monomial k (iteratedDeriv k g s / k.factorial)

theorem aeval_jpoly (g : ℝ → ℝ) (s : ℝ) (n : Gr O) (K : ℕ) :
    Polynomial.aeval n (jpoly g s K) = jet g s n K := by
  simp [jpoly, jet, map_sum, Polynomial.aeval_monomial, Algebra.smul_def]

theorem coeff_jpoly (g : ℝ → ℝ) (s : ℝ) (K k : ℕ) :
    (jpoly g s K).coeff k = if k < K then iteratedDeriv k g s / k.factorial else 0 := by
  simp [jpoly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

theorem aeval_eq_sum_of_pow (P : Polynomial ℝ) {n : Gr O} {K : ℕ} (hn : n ^ K = 0) :
    Polynomial.aeval n P = ∑ k ∈ range K, P.coeff k • n ^ k := by
  rw [Polynomial.aeval_eq_sum_range' (n := max K (P.natDegree + 1)) (by omega)]
  exact sum_range_pow_eq_of_le _ hn (le_max_left _ _)

/-- **Product rule** `(g h)(a) = g(a) h(a)`, for `g, h` smooth near `body a`. -/
theorem scomp_mul_fun {g h : ℝ → ℝ} {a : Gr O} (hN : IsNilpotent (soul a))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (body a)) (hh : ContDiffAt ℝ (⊤ : ℕ∞) h (body a)) :
    scomp (fun t => g t * h t) a = scomp g a * scomp h a := by
  obtain ⟨K, hK⟩ := hN
  rw [scomp_eq_jet _ hK, scomp_eq_jet _ hK, scomp_eq_jet _ hK, ← aeval_jpoly g, ← aeval_jpoly h,
    ← map_mul, aeval_eq_sum_of_pow _ hK, jet]
  refine sum_congr rfl fun k hk => ?_
  have hkK : k < K := mem_range.1 hk
  congr 1
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hgk : ContDiffAt ℝ k g (body a) := hg.of_le (by exact_mod_cast le_top)
  have hhk : ContDiffAt ℝ k h (body a) := hh.of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_fun_mul hgk hhk, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
  simp only [coeff_jpoly, hik.trans_lt hkK, (Nat.sub_le k i).trans_lt hkK, ↓reduceIte]
  have h1 := Nat.choose_mul_factorial_mul_factorial hik
  have h2 : (k.choose i : ℝ) * i.factorial * (k - i).factorial = k.factorial := by exact_mod_cast h1
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  have : ((k - i).factorial : ℝ) ≠ 0 := by positivity
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : (k.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hik).ne'
  rw [← h2]
  field_simp

/-! ### The exponential -/

theorem iteratedDeriv_exp (k : ℕ) : iteratedDeriv k Real.exp = Real.exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

theorem jet_exp (s : ℝ) (n : Gr O) (K : ℕ) :
    jet Real.exp s n K = Real.exp s • ∑ k ∈ range K, (k.factorial : ℚ)⁻¹ • n ^ k := by
  rw [jet, smul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [iteratedDeriv_exp, ← Rat.cast_smul_eq_qsmul ℝ, smul_smul]
  congr 1
  push_cast
  ring

/-- `exp(a) = e^{body a} · exp(soul a)`, with `IsNilpotent.exp` the terminating exponential
series. -/
theorem scomp_exp {a : Gr O} (hN : IsNilpotent (soul a)) :
    scomp Real.exp a = Real.exp (body a) • IsNilpotent.exp (soul a) := by
  obtain ⟨K, hK⟩ := hN
  rw [scomp_eq_jet _ hK, jet_exp, IsNilpotent.exp_eq_sum hK]

theorem scomp_exp_of_body_eq_zero {a : Gr O} (hN : IsNilpotent a) (h0 : body a = 0) :
    scomp Real.exp a = IsNilpotent.exp a := by
  rw [scomp_exp (by rwa [soul_of_body_eq_zero h0]), h0, Real.exp_zero, one_smul,
    soul_of_body_eq_zero h0]

theorem scomp_exp_add [DecidableEq O] [Fintype O] {a b : Gr O} (ha : IsEven a) (hb : IsEven b) :
    scomp Real.exp (a + b) = scomp Real.exp a * scomp Real.exp b := by
  rw [scomp_exp (isNilpotent_soul (ha.add hb)), scomp_exp (isNilpotent_soul ha),
    scomp_exp (isNilpotent_soul hb), map_add, soul_add,
    IsNilpotent.exp_add_of_commute (ha.soul.commute _) (isNilpotent_soul ha)
      (isNilpotent_soul hb), Real.exp_add, smul_mul_smul_comm]

/-! ### The inverse -/

theorem iteratedDeriv_inv (k : ℕ) (s : ℝ) :
    iteratedDeriv k (fun t : ℝ => t⁻¹) s = (-1) ^ k * k.factorial * (s ^ (k + 1))⁻¹ := by
  rw [iteratedDeriv_eq_iterate]
  have h := iter_deriv_inv (𝕜 := ℝ) k s
  have e : (fun t : ℝ => t⁻¹) = Inv.inv := rfl
  rw [e, h]
  congr 1
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

theorem jet_inv_mul {s : ℝ} (hs : s ≠ 0) {n : Gr O} {K : ℕ} (hn : n ^ K = 0) :
    (algebraMap ℝ (Gr O) s + n) * jet (fun t : ℝ => t⁻¹) s n K = 1 := by
  set t : ℕ → Gr O := fun k => ((-1) ^ k * (s ^ k)⁻¹) • n ^ k
  have hterm : ∀ k, (algebraMap ℝ (Gr O) s + n) *
      ((iteratedDeriv k (fun t : ℝ => t⁻¹) s / k.factorial) • n ^ k) = t k - t (k + 1) := by
    intro k
    rw [iteratedDeriv_inv, add_mul, ← Algebra.smul_def, mul_smul_comm, smul_smul, ← pow_succ']
    simp only [t]
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [sub_eq_add_neg, ← neg_smul]
    congr 1
    · congr 1; field_simp; ring
    · congr 1; field_simp; ring
  rw [jet, mul_sum]
  simp_rw [hterm]
  rw [sum_range_sub']
  simp [t, hn]

theorem jet_inv_comm (s : ℝ) (n : Gr O) (K : ℕ) :
    (algebraMap ℝ (Gr O) s + n) * jet (fun t : ℝ => t⁻¹) s n K =
      jet (fun t : ℝ => t⁻¹) s n K * (algebraMap ℝ (Gr O) s + n) := by
  have hc : Commute n (jet (fun t : ℝ => t⁻¹) s n K) :=
    Commute.sum_right _ _ _ fun k _ => ((Commute.refl n).pow_right k).smul_right _
  exact (Commute.add_left (Algebra.commutes s _) hc).eq

/-- `Ring.inverse a = (t ↦ t⁻¹)(a)` when `body a ≠ 0`. -/
theorem inverse_eq_scomp_inv {a : Gr O} (hN : IsNilpotent (soul a)) (h0 : body a ≠ 0) :
    Ring.inverse a = scomp (fun t : ℝ => t⁻¹) a := by
  obtain ⟨K, hK⟩ := hN
  rw [scomp_eq_jet _ hK]
  have h1 := jet_inv_mul h0 hK
  have h2 : jet (fun t : ℝ => t⁻¹) (body a) (soul a) K *
      (algebraMap ℝ (Gr O) (body a) + soul a) = 1 := by
    rw [← jet_inv_comm]; exact h1
  let u : (Gr O)ˣ := ⟨_, _, h1, h2⟩
  have e : ((u : (Gr O)ˣ) : Gr O) = a := (eq_body_add_soul a).symm
  exact (congrArg Ring.inverse e.symm).trans (Ring.inverse_unit u)

theorem mul_scomp_inv {a : Gr O} (hN : IsNilpotent (soul a)) (h0 : body a ≠ 0) :
    a * scomp (fun t : ℝ => t⁻¹) a = 1 := by
  obtain ⟨K, hK⟩ := hN
  rw [scomp_eq_jet _ hK]
  calc a * jet (fun t : ℝ => t⁻¹) (body a) (soul a) K =
      (algebraMap ℝ (Gr O) (body a) + soul a) * jet (fun t : ℝ => t⁻¹) (body a) (soul a) K := by
        rw [← eq_body_add_soul a]
    _ = 1 := jet_inv_mul h0 hK

end

end ArborealDecay.Super

end
