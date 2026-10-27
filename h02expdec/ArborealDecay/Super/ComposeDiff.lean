module

public import ArborealDecay.Super.Compose
public import ArborealDecay.Super.Q

/-!
# Chain rules for composition with even superfunctions

Let `S : X → Gr O` be a differentiable family of even Grassmann elements and `g : ℝ → ℝ` smooth on
an open set `U` containing every `body (S p)`.  Then `p ↦ g(S p)` (`scomp`) is differentiable
(`SDiff.scomp`) and

* `pd_scomp`: `∂_v g(S) = g'(S) ∂_v S` (bosonic chain rule);
* `Q_scomp`: `Q g(S) = g'(S) Q S` (BCHS's `Q`, for `X = ℝ^{2N}` and `Gr O = SG N P`);
* `pi0_scomp`: `π_0 g(a) = g(π_0 a)`.

We also record linearity properties of `Q` (`Q_add`, `Q_smul`, `Q_sum`, ...).
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open CliffordAlgebra Grassmann Finset
open scoped ContDiff

set_option linter.unusedSectionVars false

/-! ### Smoothness on open sets -/

section Smooth

variable {g : ℝ → ℝ} {U : Set ℝ}

theorem contDiffOn_iteratedDeriv (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv k g) U := by
  induction k generalizing g with
  | zero => simpa using hg
  | succ k ih =>
    rw [iteratedDeriv_succ']
    exact ih (hg.deriv_of_isOpen hU le_rfl)

theorem contDiffOn_deriv (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (deriv g) U := by
  simpa [iteratedDeriv_one] using contDiffOn_iteratedDeriv hU hg 1

theorem differentiableAt_iteratedDeriv (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (k : ℕ) {t : ℝ}
    (ht : t ∈ U) : DifferentiableAt ℝ (iteratedDeriv k g) t :=
  ((contDiffOn_iteratedDeriv hU hg k).differentiableOn (by simp)).differentiableAt
    (hU.mem_nhds ht)

theorem hasDerivAt_iteratedDeriv (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (k : ℕ) {t : ℝ}
    (ht : t ∈ U) : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g t) t := by
  rw [iteratedDeriv_succ]
  exact (differentiableAt_iteratedDeriv hU hg k ht).hasDerivAt

end Smooth

/-! ### The bosonic chain rule -/

section Bosonic

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {O : Type*} [Fintype O] [DecidableEq O]

theorem SDiff.pow {n : X → Gr O} (hn : SDiff n) (k : ℕ) : SDiff fun p => n p ^ k := by
  induction k with
  | zero => simpa using SDiff.const (1 : Gr O)
  | succ k ih =>
    have e : (fun p => n p ^ (k + 1)) = fun p => n p * n p ^ k := by funext p; rw [pow_succ']
    rw [e]; exact hn.mul ih

theorem pd_pow {n : X → Gr O} (hn : SDiff n) (hE : ∀ p, IsEven (n p)) (v p : X) (k : ℕ) :
    pd v (fun q => n q ^ (k + 1)) p = ((k + 1 : ℕ) : ℝ) • (n p ^ k * pd v n p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (fun q => n q ^ (k + 1 + 1)) = fun q => n q * n q ^ (k + 1) := by
      funext q; rw [pow_succ']
    rw [e, pd_mul hn (hn.pow _), ih, ← ((hE p).pow (k + 1)).comm, mul_smul_comm, ← mul_assoc,
      ← pow_succ']
    push_cast
    module

/-- The body of `S`, as a real function. -/
def bodyF (S : X → Gr O) (p : X) : ℝ := body (S p)

/-- The soul of `S`, written as `S - body S • 1`. -/
def soulF (S : X → Gr O) (p : X) : Gr O := S p - bodyF S p • (1 : Gr O)

theorem soulF_eq (S : X → Gr O) (p : X) : soulF S p = soul (S p) := by
  rw [soulF, soul, Algebra.algebraMap_eq_smul_one, bodyF]

theorem differentiable_bodyF {S : X → Gr O} (hS : SDiff S) : Differentiable ℝ (bodyF S) :=
  hS body.toLinearMap

theorem fderiv_bodyF {S : X → Gr O} (hS : SDiff S) (v p : X) :
    fderiv ℝ (bodyF S) p v = body (pd v S p) :=
  (dual_pd hS body.toLinearMap v p).symm

theorem SDiff.soulF {S : X → Gr O} (hS : SDiff S) : SDiff (soulF S) :=
  hS.sub (SDiff.smul (differentiable_bodyF hS) (SDiff.const _))

theorem pd_soulF {S : X → Gr O} (hS : SDiff S) (v p : X) :
    pd v (soulF S) p = pd v S p - body (pd v S p) • (1 : Gr O) := by
  rw [show soulF S = fun q => S q - bodyF S q • (1 : Gr O) from rfl,
    pd_sub hS (SDiff.smul (differentiable_bodyF hS) (SDiff.const _)),
    pd_smul_const (differentiable_bodyF hS), fderiv_bodyF hS]

variable {g : ℝ → ℝ} {U : Set ℝ}

/-- The Taylor-sum form of `p ↦ g(S p)`. -/
theorem scomp_fun_eq {S : X → Gr O} (hE : ∀ p, IsEven (S p)) {K : ℕ}
    (hK : Fintype.card O + 1 ≤ K) :
    (fun p => scomp g (S p)) = fun p =>
      ∑ k ∈ range K, (iteratedDeriv k g (bodyF S p) / k.factorial) • soulF S p ^ k := by
  funext p
  rw [scomp_eq_jet_card g (hE p) hK, jet, soulF_eq]; rfl

theorem differentiable_coeff (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {S : X → Gr O}
    (hS : SDiff S) (hb : ∀ p, body (S p) ∈ U) (k : ℕ) :
    Differentiable ℝ fun p => iteratedDeriv k g (bodyF S p) / k.factorial := fun p => by
  have h := (differentiableAt_iteratedDeriv hU hg k (hb p)).comp p (differentiable_bodyF hS p)
  have h2 := h.mul_const ((k.factorial : ℝ)⁻¹)
  simp only [Function.comp_def, ← div_eq_mul_inv] at h2
  exact h2

theorem SDiff.scomp (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {S : X → Gr O} (hS : SDiff S)
    (hE : ∀ p, IsEven (S p)) (hb : ∀ p, body (S p) ∈ U) : SDiff fun p => scomp g (S p) := by
  rw [scomp_fun_eq hE le_rfl]
  exact SDiff.sum _ fun k _ => SDiff.smul (differentiable_coeff hU hg hS hb k) (hS.soulF.pow k)

/-- **Bosonic chain rule**: `∂_v g(S) = g'(S) ∂_v S`. -/
theorem pd_scomp (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {S : X → Gr O} (hS : SDiff S)
    (hE : ∀ p, IsEven (S p)) (hb : ∀ p, body (S p) ∈ U) (v p : X) :
    pd v (fun q => scomp g (S q)) p = scomp (deriv g) (S p) * pd v S p := by
  set K := Fintype.card O + 1
  have hn : soulF S p ^ K = 0 := by rw [soulF_eq]; exact soul_pow_card_succ (hE p)
  rw [scomp_fun_eq hE (K := K + 1) (by omega), pd_sum _ fun k _ => SDiff.smul
    (differentiable_coeff hU hg hS hb k) (hS.soulF.pow k)]
  have hterm : ∀ k ∈ range (K + 1),
      pd v (fun q => (iteratedDeriv k g (bodyF S q) / k.factorial) • soulF S q ^ k) p =
        (iteratedDeriv (k + 1) g (bodyF S p) / k.factorial * body (pd v S p)) • soulF S p ^ k +
          (iteratedDeriv k g (bodyF S p) / k.factorial) •
            pd v (fun q => soulF S q ^ k) p := by
    intro k _
    rw [pd_smul (differentiable_coeff hU hg hS hb k) (hS.soulF.pow k)]
    congr 2
    have h1 : HasDerivAt (fun t => iteratedDeriv k g t / k.factorial)
        (iteratedDeriv (k + 1) g (bodyF S p) / k.factorial) (bodyF S p) :=
      (hasDerivAt_iteratedDeriv hU hg k (hb p)).div_const _
    have h2 := h1.comp_hasFDerivAt p (differentiable_bodyF hS p).hasFDerivAt
    rw [show (fun q => iteratedDeriv k g (bodyF S q) / k.factorial) =
      (fun t => iteratedDeriv k g t / k.factorial) ∘ bodyF S from rfl, h2.fderiv,
      FunLike.coe_smul, Pi.smul_apply, fderiv_bodyF hS, smul_eq_mul]
  rw [sum_congr rfl hterm, sum_add_distrib,
    sum_jet_deriv g _ (soulF S p) (pd v (soulF S) p) (fun k => pd v (fun q => soulF S q ^ k) p)
      (by simp) (fun k => pd_pow hS.soulF (fun q => by rw [soulF_eq]; exact (hE q).soul) v p k)]
  rw [scomp_eq_jet_card (deriv g) (hE p) (le_refl K), ← soulF_eq]
  have e1 : ∑ k ∈ range (K + 1),
      (iteratedDeriv (k + 1) g (bodyF S p) / k.factorial * body (pd v S p)) • soulF S p ^ k =
      body (pd v S p) • jet (deriv g) (bodyF S p) (soulF S p) K := by
    rw [← jet_eq_of_le (deriv g) _ hn (Nat.le_succ K), jet, smul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_smul, iteratedDeriv_succ']; ring_nf
  rw [e1, pd_soulF hS]
  change _ = jet (deriv g) (bodyF S p) (soulF S p) K * pd v S p
  rw [mul_sub, mul_smul_comm, mul_one]
  abel

end Bosonic

/-! ### `Q` and composition -/

section QComp

variable {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]
variable {g : ℝ → ℝ} {U : Set ℝ}

/-- **Chain rule for `Q`**: `Q g(S) = g'(S) Q S`. -/
theorem Q_scomp (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {S : Pt N → SG N P} (hS : SDiff S)
    (hE : ∀ p, IsEven (S p)) (hb : ∀ p, body (S p) ∈ U) (p : Pt N) :
    Q (fun q => scomp g (S q)) p = scomp (deriv g) (S p) * Q S p := by
  set D := scomp (deriv g) (S p)
  have hD : IsEven D := (hE p).scomp _
  rw [Q, Q, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pd_scomp hU hg hS hE hb, pd_scomp hU hg hS hE hb]
  have h1 : dξ i (scomp g (S p)) = D * dξ i (S p) := dgen_scomp _ g (hE p)
  have h2 : dη i (scomp g (S p)) = D * dη i (S p) := dgen_scomp _ g (hE p)
  have c1 : ∀ Y : SG N P, ξ i * (D * Y) = D * (ξ i * Y) := fun Y => by
    rw [← mul_assoc, ← hD.comm, mul_assoc]
  have c2 : ∀ Y : SG N P, η i * (D * Y) = D * (η i * Y) := fun Y => by
    rw [← mul_assoc, ← hD.comm, mul_assoc]
  rw [h1, h2, c1, c2, mul_add, mul_sub, mul_add, mul_smul_comm, mul_smul_comm]

/-- `π_0 g(a) = g(π_0 a)`. -/
theorem pi0_scomp (g : ℝ → ℝ) {a : SG N P} (ha : IsEven a) : pi0 (scomp g a) = scomp g (pi0 a) :=
  map_scomp pi0 (body_killA _) g (isNilpotent_soul ha)

theorem IsEven.pi0 {a : SG N P} (ha : IsEven a) : IsEven (pi0 a) := by
  unfold IsEven at *; rw [Super.pi0, inv'_killA, ha]

/-! ### Linearity of `Q` -/

theorem Q_add {F G : Pt N → SG N P} (hF : SDiff F) (hG : SDiff G) (p : Pt N) :
    Q (fun q => F q + G q) p = Q F p + Q G p := by
  rw [Q, Q, Q, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [pd_add hF hG, pd_add hF hG, map_add, map_add]
  simp only [mul_add, smul_add]
  abel

theorem Q_smul (c : ℝ) {F : Pt N → SG N P} (hF : SDiff F) (p : Pt N) :
    Q (fun q => c • F q) p = c • Q F p := by
  rw [Q, Q, smul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pd_smul (differentiable_const c) hF, pd_smul (differentiable_const c) hF]
  simp [smul_add, smul_sub, smul_comm c]

theorem Q_neg {F : Pt N → SG N P} (hF : SDiff F) (p : Pt N) : Q (fun q => -F q) p = -Q F p := by
  have := Q_smul (-1) hF p
  simpa using this

theorem Q_sub {F G : Pt N → SG N P} (hF : SDiff F) (hG : SDiff G) (p : Pt N) :
    Q (fun q => F q - G q) p = Q F p - Q G p := by
  simp only [sub_eq_add_neg]
  rw [Q_add hF hG.neg, Q_neg hG]

theorem Q_sum {ι : Type*} (s : Finset ι) {F : ι → Pt N → SG N P} (hF : ∀ i ∈ s, SDiff (F i))
    (p : Pt N) : Q (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, Q (F i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Q, pd_const]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [Q_add (hF a (mem_insert_self a s)) (SDiff.sum s fun i hi => hF i (mem_insert_of_mem hi)),
      ih fun i hi => hF i (mem_insert_of_mem hi)]

/-- `Q` of a constant not involving the integrated generators vanishes. -/
theorem Q_const {c : SG N P} (hc : ∀ i, dξ i c = 0 ∧ dη i c = 0) (p : Pt N) :
    Q (fun _ => c) p = 0 := by
  refine sum_eq_zero fun i _ => ?_
  simp [(hc i).1, (hc i).2]

theorem Q_algebraMap (r : ℝ) (p : Pt N) : Q (fun _ => algebraMap ℝ (SG N P) r) p = 0 :=
  Q_const (fun i => ⟨by simp [dξ], by simp [dη]⟩) p

end QComp

end

end ArborealDecay.Super

end
