module

public import ArborealDecay.Horo.Schwartz

/-!
# Simultaneous nilpotent changes of generators

Let `ι` index directions `v k`, scalar functions `g k` and nilpotent central elements `n k`
(`n k ^ K = 0`).  The iterated Taylor shift `shiftL l F` is `F(x + ∑_{k ∈ l} g_k(x) n_k v_k)`
(computed one direction at a time), and its Berezinian is
`berL l x = ∏_{k ∈ l} (1 + ∂_{v_k} g_k(x) · n_k)`.

**Main result** (`integral_shiftL_mul`): if `F` is Schwartz, `g_k` and `∂_{v_k} g_k` have
temperate growth, and `∂_{v_j} g_j` is invariant under translation along `v_k` for `j ≠ k`, then
`∫ ℓ (shiftL l F x · berL l x) dx = ∫ ℓ (F x) dx` for every nodup list `l`.

In the horospherical step, `k` ranges over the vertices, `v_k = e_{x_k}`,
`g_k(x, y) = −1/(x_k + z_k)` depends only on `(x_k, y_k)`, and `n_k = ∑_γ η^γ_k ξ^γ_k`.
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open MeasureTheory Finset ArborealDecay.Super

set_option linter.unusedSectionVars false

variable {E : Type*} [Fintype E]
variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

local notation "X" => E → ℝ

/-! ### Functions invariant along a direction -/

theorem fderiv_eq_zero_of_invariant {f : X → ℝ} {x v : X} (hf : DifferentiableAt ℝ f x)
    (hinv : ∀ c : ℝ, f (x + c • v) = f x) : fderiv ℝ f x v = 0 := by
  have hline : HasDerivAt (fun c : ℝ => x + c • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun c : ℝ => f (x + c • v)) (fderiv ℝ f x v) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (fun c : ℝ => f (x + c • v)) 0 0 := by
    simp_rw [hinv]; exact hasDerivAt_const _ _
  exact h1.unique h2

theorem pd_eq_zero_of_invariant {B : X → A} (hB : SDiff B) {v : X}
    (hinv : ∀ x (c : ℝ), B (x + c • v) = B x) (x : X) : pd v B x = 0 := by
  refine ext_dual fun ℓ => ?_
  rw [dual_pd hB, map_zero]
  exact fderiv_eq_zero_of_invariant (hB ℓ x) fun c => by rw [hinv]

/-- Derivatives along `v` do not see a factor that is invariant along `v`. -/
theorem pdn_mul_invariant {v : X} {G B : X → A} (hG : ∀ m, SDiff (pdn v m G)) (hB : SDiff B)
    (hinv : ∀ x (c : ℝ), B (x + c • v) = B x) (m : ℕ) :
    pdn v m (fun x => G x * B x) = fun x => pdn v m G x * B x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext x
    rw [pdn_succ, ih, pd_mul (hG m) hB, pd_eq_zero_of_invariant hB hinv, mul_zero, add_zero,
      pdn_succ]

theorem shiftT_mul_invariant {v : X} {G B : X → A} (hG : ∀ m, SDiff (pdn v m G))
    (hB : SDiff B) (hinv : ∀ x (c : ℝ), B (x + c • v) = B x) (g : X → ℝ) {n : A} (hn : ∀ a : A, n * a = a * n)
    (K : ℕ) (x : X) :
    shiftT v g n K (fun y => G y * B y) x = shiftT v g n K G x * B x := by
  rw [shiftT, shiftT, Finset.sum_mul]
  simp_rw [pdn_mul_invariant hG hB hinv]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : Commute (n ^ m) (B x) := (Commute.pow_left (hn (B x)) m)
  rw [smul_mul_assoc, mul_assoc, mul_assoc, hc.eq]

/-! ### Iterated shifts -/

variable {ι : Type*}

/-- `F(x + ∑_{k ∈ l} g_k(x) n_k v_k)` as an iterated Taylor sum. -/
def shiftL (v : ι → X) (g : ι → X → ℝ) (n : ι → A) (K : ℕ) : List ι → (X → A) → X → A
  | [], F => F
  | k :: l, F => shiftT (v k) (g k) (n k) K (shiftL v g n K l F)

/-- `∂_{v_k} g_k`. -/
def gdir (v : ι → X) (g : ι → X → ℝ) (k : ι) (x : X) : ℝ := fderiv ℝ (g k) x (v k)

/-- The Berezinian `∏_{k ∈ l} (1 + ∂_{v_k} g_k · n_k)` (product taken right to left). -/
def berL (v : ι → X) (g : ι → X → ℝ) (n : ι → A) : List ι → X → A
  | [], _ => 1
  | k :: l, x => berL v g n l x * (1 + gdir v g k x • n k)

variable {v : ι → E → ℝ} {g : ι → (E → ℝ) → ℝ} {n : ι → A} {K : ℕ}

theorem SSchwartz.shiftL {F : X → A} (hF : SSchwartz F)
    (hg : ∀ k, (g k).HasTemperateGrowth) (l : List ι) : SSchwartz (shiftL v g n K l F) := by
  induction l with
  | nil => exact hF
  | cons k l ih => exact ih.shiftT (v k) (hg k) (n k) K

theorem SSchwartz.mul_berL {G : X → A} (hG : SSchwartz G)
    (hgd : ∀ k, (gdir v g k).HasTemperateGrowth) (l : List ι) :
    SSchwartz fun x => G x * berL v g n l x := by
  induction l generalizing G with
  | nil => simpa [berL] using hG
  | cons k l ih =>
    have h := ih (G := G) hG
    have e : (fun x => G x * berL v g n (k :: l) x) =
        fun x => G x * berL v g n l x + gdir v g k x • (G x * berL v g n l x * n k) := by
      funext x
      simp only [berL, mul_add, mul_one, mul_smul_comm, ← mul_assoc]
    rw [e]
    exact h.add ((h.mul_const (n k)).smul (hgd k))

theorem sdiff_berL (hgd : ∀ k, (gdir v g k).HasTemperateGrowth) (l : List ι) :
    SDiff (berL v g n l) := by
  induction l with
  | nil => exact SDiff.const (1 : A)
  | cons k l ih =>
    exact ih.mul ((SDiff.const (1 : A)).add
      ((SDiff.const (n k)).smul ((hgd k).1.differentiable (by simp))))

theorem berL_invariant {k : ι}
    (hinv : ∀ j, j ≠ k → ∀ x (c : ℝ), gdir v g j (x + c • v k) = gdir v g j x)
    {l : List ι} (hk : k ∉ l) (x : X) (c : ℝ) :
    berL v g n l (x + c • v k) = berL v g n l x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at hk
    simp only [berL]
    rw [ih hk.2, hinv j (Ne.symm hk.1)]

/-- **Simultaneous nilpotent change of generators.** -/
theorem integral_shiftL_mul [DecidableEq ι] {F : X → A} (hF : SSchwartz F)
    (hg : ∀ k, (g k).HasTemperateGrowth) (hgd : ∀ k, (gdir v g k).HasTemperateGrowth)
    (hn : ∀ k, n k ^ K = 0) (hc : ∀ k (a : A), n k * a = a * n k)
    (hinv : ∀ j k, j ≠ k → ∀ x (c : ℝ), gdir v g j (x + c • v k) = gdir v g j x)
    {l : List ι} (hl : l.Nodup) (ℓ : Module.Dual ℝ A) :
    ∫ x, ℓ (shiftL v g n K l F x * berL v g n l x) = ∫ x, ℓ (F x) := by
  induction l with
  | nil => simp [shiftL, berL]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    have hS := hF.shiftL (v := v) (n := n) (K := K) hg l
    have e : ∀ x, shiftL v g n K (k :: l) F x * berL v g n (k :: l) x =
        shiftT (v k) (g k) (n k) K (fun y => shiftL v g n K l F y * berL v g n l y) x *
          (1 + fderiv ℝ (g k) x (v k) • n k) := by
      intro x
      rw [shiftT_mul_invariant (fun m => (hS.pdn (v k) m).sdiff) (sdiff_berL hgd l)
        (fun y c => berL_invariant (hinv · k) hl.1 y c) (g k) (hc k) K x]
      simp only [shiftL, berL, gdir, mul_assoc]
    simp_rw [e]
    rw [integral_dual_shiftT_mul_of_schwartz (v k) (hg k) (hn k) (hS.mul_berL hgd l) ℓ]
    exact ih hl.2

end

end ArborealDecay.Horo

end
