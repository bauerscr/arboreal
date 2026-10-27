module

public import Mathlib
public import ArborealDecay.MatrixForest

/-!
# The pinned `t`-law (supplement `def:tlaw`)

Let `V` be finite, `w : V → V → ℝ` a weighted graph (symmetric, nonnegative, `w i i = 0`), and
`ρ : V` the root. Coordinates are `τ : {i // i ≠ ρ} → ℝ`, extended by `0` at `ρ` (`ext ρ τ`).

* `Phi w t = ½ ∑_{i,k ∈ V} w i k (cosh (t i - t k) - 1)` (ordered double sum, factor `½`, so
  that it equals the sum over unordered edges);
* `Hmat w ρ t` with `H i k = - w i k` (`i ≠ k`), `H i i = ∑_{k ∈ V} w i k e^{t k - t i}`;
* `Lmat w ρ t`, the grounded Laplacian with conductances `w i k e^{t i + t k}`;
* `D w ρ t = det (Hmat w ρ t)`;
* `density w ρ a τ = e^{-Phi(τ̂)} D(τ̂)^a (2π)^{-|V∖ρ|/2}`, `Z w ρ a = ∫⁻ density ∈ [0,∞]`;
* `expect w ρ a f = Z⁻¹ ∫ f · density` (real Bochner integral).

The support graph is `supportGraph w` (edges `{i,k}` with `0 < w i k`), and
`edgeSum w g = ½ ∑_{i,k} [0 < w i k] g i k`, which is `∑_{e ∈ E(w)} g_e` for symmetric `g`
(`edgeSum_eq_sum_edgeFinset`).
-/

open Finset Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.TLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A weighted graph in the sense of supplement `def:carrier`: symmetric, nonnegative weights
with zero diagonal. -/
structure IsWGraph (w : V → V → ℝ) : Prop where
  symm : ∀ i k, w i k = w k i
  nonneg : ∀ i k, 0 ≤ w i k
  diag : ∀ i, w i i = 0

/-- The support graph `(V, E(w))`, `E(w) = {{i,k} : w i k > 0}`. -/
def supportGraph (w : V → V → ℝ) : SimpleGraph V := SimpleGraph.fromRel fun i k => 0 < w i k

/-- Extension of `τ : V ∖ ρ → ℝ` by `0` at the root. -/
def ext (ρ : V) (τ : {i // i ≠ ρ} → ℝ) : V → ℝ := fun i => if h : i = ρ then 0 else τ ⟨i, h⟩

/-- `Φ_w(t) = ½ ∑_{i,k} w_{ik} (cosh (t_i - t_k) - 1)`. -/
noncomputable def Phi (w : V → V → ℝ) (t : V → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ k, w i k * (cosh (t i - t k) - 1)

/-- `H^ρ_w(t)`: `H_{ik} = -w_{ik}` for `i ≠ k`, `H_{ii} = ∑_{k ∈ V} w_{ik} e^{t_k - t_i}`. -/
noncomputable def Hmat (w : V → V → ℝ) (ρ : V) (t : V → ℝ) :
    Matrix {i // i ≠ ρ} {i // i ≠ ρ} ℝ :=
  Matrix.of fun i k => if i = k then ∑ m, w i m * exp (t m - t i) else -w i k

/-- The grounded Laplacian `𝓛^{(ρ)}_w(t)` with conductances `w_{ik} e^{t_i + t_k}`. -/
noncomputable def Lmat (w : V → V → ℝ) (ρ : V) (t : V → ℝ) :
    Matrix {i // i ≠ ρ} {i // i ≠ ρ} ℝ :=
  Matrix.of fun i k =>
    if i = k then ∑ m, w i m * exp (t i + t m) else -(w i k * exp (t i + t k))

/-- `D^ρ_w(t) = det H^ρ_w(t)`. -/
noncomputable def D (w : V → V → ℝ) (ρ : V) (t : V → ℝ) : ℝ := (Hmat w ρ t).det

/-- The (unnormalized) density of the pinned `t`-law with respect to Lebesgue measure on
`ℝ^{V∖ρ}`: `e^{-Φ_w(τ̂)} D^ρ_w(τ̂)^a (2π)^{-|V∖ρ|/2}`. -/
noncomputable def density (w : V → V → ℝ) (ρ : V) (a : ℝ) (τ : {i // i ≠ ρ} → ℝ) : ℝ :=
  exp (-Phi w (ext ρ τ)) * D w ρ (ext ρ τ) ^ a *
    (2 * π) ^ (-(Fintype.card {i // i ≠ ρ} : ℝ) / 2)

/-- `Z^ρ_{w,a} = ∫ e^{-Φ} D^a dμ_ρ ∈ [0, ∞]`. -/
noncomputable def Z (w : V → V → ℝ) (ρ : V) (a : ℝ) : ENNReal :=
  ∫⁻ τ, ENNReal.ofReal (density w ρ a τ)

/-- The expectation `E_{w,a}[f] = Z⁻¹ ∫ f · density` under the pinned `t`-law. -/
noncomputable def expect (w : V → V → ℝ) (ρ : V) (a : ℝ)
    (f : ({i // i ≠ ρ} → ℝ) → ℝ) : ℝ :=
  (Z w ρ a).toReal⁻¹ * ∫ τ, f τ * density w ρ a τ

/-- `edgeSum w g = ½ ∑_{i,k} [0 < w_{ik}] g_{ik}`; for symmetric `g` this is
`∑_{e ∈ E(w)} g_e` over unordered support edges. -/
noncomputable def edgeSum (w : V → V → ℝ) (g : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ k, if 0 < w i k then g i k else 0

/-! ### Basic facts -/

@[simp] theorem ext_root (ρ : V) (τ : {i // i ≠ ρ} → ℝ) : ext ρ τ ρ = 0 := by simp [ext]

@[simp] theorem ext_val (ρ : V) (τ : {i // i ≠ ρ} → ℝ) (i : {i // i ≠ ρ}) :
    ext ρ τ i = τ i := by simp [ext, i.2]

theorem ext_add_smul (ρ : V) (τ : {i // i ≠ ρ} → ℝ) (v : V → ℝ) (hv : v ρ = 0) (c : ℝ) :
    ext ρ (τ + c • fun i : {i // i ≠ ρ} => v i) = ext ρ τ + c • v := by
  funext i
  by_cases h : i = ρ
  · subst h; simp [hv]
  · simp [ext, h]

theorem continuous_ext (ρ : V) : Continuous (ext ρ) := by
  refine continuous_pi fun i => ?_
  by_cases h : i = ρ
  · simp only [ext, h, dite_true]; exact continuous_const
  · simp only [ext, h, dite_false]; exact continuous_apply _

theorem supportGraph_adj {w : V → V → ℝ} (hw : ∀ i k, w i k = w k i) {i k : V} :
    (supportGraph w).Adj i k ↔ i ≠ k ∧ 0 < w i k := by
  simp only [supportGraph, SimpleGraph.fromRel_adj, hw k i, or_self]

/-- `H^ρ_w(t) = E_t⁻¹ 𝓛^{(ρ)}_w(t) E_t⁻¹` with `E_t = diag (e^{t_i})`. -/
theorem Hmat_eq (w : V → V → ℝ) (ρ : V) (t : V → ℝ) :
    Hmat w ρ t = diagonal (fun i : {i // i ≠ ρ} => exp (-t i)) * Lmat w ρ t *
      diagonal (fun i : {i // i ≠ ρ} => exp (-t i)) := by
  ext i k
  rw [mul_diagonal, diagonal_mul]
  simp only [Hmat, Lmat, of_apply]
  split_ifs with h
  · subst h
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : exp (t m - t i) = exp (-t i) * exp (t i + t m) * exp (-t i) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [this]; ring
  · have : exp (-t i) * exp (t i + t k) * exp (-t k) = 1 := by
      rw [← exp_add, ← exp_add]; ring_nf; exact exp_zero
    linear_combination (w i k) * this

/-- `(eq:H-L)`: `D^ρ_w(t) = det 𝓛^{(ρ)}_w(t) e^{-2 ∑_{i ≠ ρ} t_i}`. -/
theorem D_eq_det_Lmat (w : V → V → ℝ) (ρ : V) (t : V → ℝ) :
    D w ρ t = (Lmat w ρ t).det * exp (-2 * ∑ i : {i // i ≠ ρ}, t i) := by
  rw [D, Hmat_eq, det_mul, det_mul, det_diagonal, ← exp_sum]
  have : -2 * ∑ i : {i // i ≠ ρ}, t i = ∑ i : {i // i ≠ ρ}, -t i + ∑ i : {i // i ≠ ρ}, -t i := by
    rw [Finset.sum_neg_distrib]; ring
  rw [this, exp_add]; ring

/-- For zero diagonal, `𝓛^{(ρ)}_w(t)` is the principal minor of `MatrixForest.lap` with
conductances `w_{ik} e^{t_i + t_k}`. -/
theorem Lmat_eq_lap (w : V → V → ℝ) (hd : ∀ i, w i i = 0) (ρ : V) (t : V → ℝ) :
    Lmat w ρ t = (MatrixForest.lap fun i k => w i k * exp (t i + t k)).submatrix
      (fun i : {i // i ≠ ρ} => (i : V)) (fun i : {i // i ≠ ρ} => (i : V)) := by
  ext i k
  simp only [Lmat, of_apply, submatrix_apply]
  by_cases h : i = k
  · subst h
    simp only [↓reduceIte]
    rw [MatrixForest.lap_apply_self, ← Finset.add_sum_erase _ _ (Finset.mem_univ _),
      hd, zero_mul, zero_add]
  · simp only [h, ↓reduceIte]
    rw [MatrixForest.lap_apply_of_ne _ (fun h' => h (Subtype.ext h'))]

/-- The tree exponent `∑_{ {i,k} ∈ T} (t_i + t_k) - 2 ∑_{i ≠ ρ} t_i`. -/
noncomputable def treeExp (ρ : V) (T : SimpleGraph V) [Fintype T.edgeSet] (t : V → ℝ) : ℝ :=
  ∑ e ∈ T.edgeFinset, Sym2.lift ⟨fun i k => t i + t k, fun _ _ => add_comm _ _⟩ e -
    2 * ∑ i : {i // i ≠ ρ}, t i

theorem lift_mul_exp (w : V → V → ℝ) (hw : ∀ i k, w i k = w k i) (t : V → ℝ) (e : Sym2 V) :
    Sym2.lift ⟨fun i k => w i k * exp (t i + t k), fun i k => by
      beta_reduce; rw [hw i k, add_comm]⟩ e =
      Sym2.lift ⟨w, hw⟩ e *
        exp (Sym2.lift ⟨fun i k => t i + t k, fun _ _ => add_comm _ _⟩ e) := by
  induction e using Sym2.ind with
  | h i k => simp

open Classical in
/-- **Tree expansion of `D`** (supplement `cor:D-tree`(i)):
`D^ρ_w(t) = ∑_{T spanning tree} w(T) e^{∑_{ik ∈ T}(t_i + t_k) - 2 ∑_{i ≠ ρ} t_i}`.
Equivalently `∑_T w(T) ∏_{i ≠ ρ} e^{t_{p_T(i)} - t_i}`, orienting `T` toward `ρ`. -/
theorem D_eq_treeSum (w : V → V → ℝ) (hw : ∀ i k, w i k = w k i) (hd : ∀ i, w i i = 0)
    (ρ : V) (t : V → ℝ) :
    D w ρ t = ∑ T : SimpleGraph V with T.IsTree,
      (∏ e ∈ T.edgeFinset, Sym2.lift ⟨w, hw⟩ e) * exp (treeExp ρ T t) := by
  have hc : ∀ i k, w i k * exp (t i + t k) = w k i * exp (t k + t i) := fun i k => by
    rw [hw, add_comm]
  rw [D_eq_det_Lmat, Lmat_eq_lap w hd, MatrixForest.det_lap_submatrix_ne _ hc, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp_rw [lift_mul_exp w hw t, Finset.prod_mul_distrib, ← exp_sum, treeExp, sub_eq_add_neg,
    exp_add]
  ring_nf

theorem treeExp_add_smul (ρ : V) (T : SimpleGraph V) [Fintype T.edgeSet] (t v : V → ℝ)
    (c : ℝ) : treeExp ρ T (t + c • v) = treeExp ρ T t + c * treeExp ρ T v := by
  have : ∀ e : Sym2 V, Sym2.lift ⟨fun i k => (t + c • v) i + (t + c • v) k,
      fun _ _ => add_comm _ _⟩ e = Sym2.lift ⟨fun i k => t i + t k, fun _ _ => add_comm _ _⟩ e +
        c * Sym2.lift ⟨fun i k => v i + v k, fun _ _ => add_comm _ _⟩ e := fun e => by
    induction e using Sym2.ind with
    | h i k => simp; ring
  simp only [treeExp, this]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem D_nonneg {w : V → V → ℝ} (hW : IsWGraph w) (ρ : V) (t : V → ℝ) : 0 ≤ D w ρ t := by
  classical
  rw [D_eq_treeSum w hW.symm hW.diag]
  refine Finset.sum_nonneg fun T _ => mul_nonneg (Finset.prod_nonneg fun e _ => ?_)
    (exp_pos _).le
  induction e using Sym2.ind with
  | h i k => exact hW.nonneg i k

/-- `D > 0` for a connected weighted graph (supplement `cor:D-tree`(i)). -/
theorem D_pos {w : V → V → ℝ} (hW : IsWGraph w) (hconn : (supportGraph w).Connected) (ρ : V)
    (t : V → ℝ) : 0 < D w ρ t := by
  classical
  rw [D_eq_treeSum w hW.symm hW.diag]
  obtain ⟨T, hTle, hT⟩ := hconn.exists_isTree_le
  refine Finset.sum_pos' (fun T _ => mul_nonneg (Finset.prod_nonneg fun e _ => ?_)
    (exp_pos _).le) ⟨T, by simpa using hT, mul_pos (Finset.prod_pos fun e he => ?_) (exp_pos _)⟩
  · induction e using Sym2.ind with
    | h i k => exact hW.nonneg i k
  · induction e using Sym2.ind with
    | h i k =>
      have hadj : T.Adj i k := by simpa using he
      exact ((supportGraph_adj hW.symm).1 (hTle hadj)).2

end ArborealDecay.TLaw
