module

public import ArborealDecay.BCHS.Action

/-!
# The rooted horospherical action and its fermionic Gaussian (R3, R4)

Setting of supplement `inp:A-BCHS`/`inp:C-BCHS`: `V` finite, `w` a weighted graph, root `ρ`,
`Λ = V ∖ ρ`, `β = w|_Λ`, `h_i = w_{ρ i}`; a point `p ∈ ℝ^{Λ ⊕ Λ}` is `(τ, s)`.

* `horoF_actionH_eq`: `horoF H = (Φ_w(τ̂) + ½ sᵀ𝓛 s) · 1 + ∑_γ ∑_{a,b} 𝓛_{ab} ψ̄^γ_a ψ^γ_b`
  with `𝓛 = TLaw.Lmat w ρ τ̂` (BCHS (2.59), corrected as in `TSide.lean`);
* `horoF_exp_neg_actionH`: `horoF e^{−H} = e^{−Φ − ½ sᵀ𝓛s} · exp(−Q)`;
* `body_berezin_exp_neg_Qf`: `∫ dψ dψ̄ exp(−Q) = det 𝓛²` (two fermionic Gaussians, BCHS (2.74)).
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset Real Matrix ArborealDecay.Super ArborealDecay.Super.H24 ArborealDecay.Horo Grassmann
open ArborealDecay.TLaw (Lmat Phi ext IsWGraph ext_root ext_val)
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_V_split (ρ : V) (f : V → ℝ) : ∑ i, f i = f ρ + ∑ i : {i // i ≠ ρ}, f i := by
  rw [← Finset.add_sum_erase _ _ (mem_univ ρ)]
  congr 1
  exact Finset.sum_subtype _ (fun i => by simp) f

variable {w : V → V → ℝ} {ρ : V}

/-- `τ = (p (inl i))_i`. -/
def tauP (p : Pt {i // i ≠ ρ}) : {i // i ≠ ρ} → ℝ := fun i => p (.inl i)
/-- `s = (p (inr i))_i`. -/
def sP (p : Pt {i // i ≠ ρ}) : {i // i ≠ ρ} → ℝ := fun i => p (.inr i)

/-- The bosonic horospherical action `Φ_w(τ̂) + ½ sᵀ𝓛 s`. -/
def Hb (w : V → V → ℝ) (ρ : V) (p : Pt {i // i ≠ ρ}) : ℝ :=
  Phi w (ext ρ (tauP p)) + (1 / 2) * (sP p ⬝ᵥ (Lmat w ρ (ext ρ (tauP p))) *ᵥ sP p)

/-- The fermionic quadratic form `∑_γ ∑_{a,b} 𝓛_{ab} ψ̄^γ_a ψ^γ_b`. -/
def Qf (w : V → V → ℝ) (ρ : V) (p : Pt {i // i ≠ ρ}) : B {i // i ≠ ρ} :=
  ∑ γ, ∑ a, ∑ b, Lmat w ρ (ext ρ (tauP p)) a b • qq γ a b

theorem Lmat_ext_apply (hW : IsWGraph w) (τ : {i // i ≠ ρ} → ℝ) (a b : {i // i ≠ ρ}) :
    Lmat w ρ (ext ρ τ) a b = (if a = b then ∑ j : {i // i ≠ ρ}, w a j * exp (τ a + τ j) +
      w ρ a * exp (τ a) else 0) - w a b * exp (τ a + τ b) := by
  simp only [Lmat, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, hW.diag, zero_mul, sub_zero]
    rw [sum_V_split ρ, ext_root, add_zero, hW.symm]
    simp only [ext_val]
    ring
  · simp [hab]

theorem body_action_eq (hW : IsWGraph w) (p : Pt {i // i ≠ ρ}) :
    (1 / 2) * ∑ i : {i // i ≠ ρ}, ∑ j : {i // i ≠ ρ}, w i j * (acoef p i j - 1) +
        ∑ i : {i // i ≠ ρ}, w ρ i * (hz (p (.inl i)) (p (.inr i)) - 1) = Hb w ρ p := by
  rw [Hb, ← horo_action_eq w hW ρ (tauP p) (sP p)]
  simp only [neg_mdot_hxyz]
  set g : V → V → ℝ := fun i k => w i k * (cosh (ext ρ (tauP p) i - ext ρ (tauP p) k) +
    exp (ext ρ (tauP p) i + ext ρ (tauP p) k) * (ext ρ (sP p) i - ext ρ (sP p) k) ^ 2 / 2 - 1)
  have hg : ∀ i k, w i k * (cosh (ext ρ (tauP p) i - ext ρ (tauP p) k) +
      exp (ext ρ (tauP p) i + ext ρ (tauP p) k) * (ext ρ (sP p) i - ext ρ (sP p) k) ^ 2 / 2 - 1)
      = g i k := fun _ _ => rfl
  simp only [hg]
  rw [sum_V_split ρ, sum_V_split ρ (g ρ)]
  simp only [sum_V_split ρ (g _)]
  have hρρ : g ρ ρ = 0 := by simp [g, hW.diag]
  have hρk : ∀ k : {i // i ≠ ρ}, g ρ k = w ρ k * (hz (p (.inl k)) (p (.inr k)) - 1) := by
    intro k; simp only [g, ext_root, ext_val, tauP, sP, hz, zero_sub, cosh_neg, zero_add]
    ring
  have hkρ : ∀ k : {i // i ≠ ρ}, g k ρ = w ρ k * (hz (p (.inl k)) (p (.inr k)) - 1) := by
    intro k; simp only [g, ext_root, ext_val, tauP, sP, hz, sub_zero, add_zero, hW.symm k ρ]
  have hkk : ∀ i j : {i // i ≠ ρ}, g i j = w i j * (acoef p i j - 1) := by
    intro i j; simp only [g, ext_val, tauP, sP, acoef]
  simp only [hρρ, hρk, hkρ, hkk, sum_add_distrib]
  ring

theorem horoF_actionH_eq (hW : IsWGraph w) (p : Pt {i // i ≠ ρ}) :
    horoF (vt _) (fun q => T (actionH (fun a b : {i // i ≠ ρ} => w a b) (fun a => w ρ a) q)) p =
      Hb w ρ p • (1 : B {i // i ≠ ρ}) + Qf w ρ p := by
  rw [horoF_actionH]
  refine (action_split (fun a b : {i // i ≠ ρ} => w a b) (fun i j => hW.symm i j)
    (fun a => w ρ a) p).trans ?_
  rw [body_action_eq hW, Qf]
  congr 1
  refine sum_congr rfl fun γ _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [Lmat_ext_apply hW]
  rfl

/-! ### Parity and body of the fermionic form -/

theorem isEven_qq {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (γ : Bool) (a b : Λ) :
    IsEven (qq γ a b) := by
  unfold IsEven qq; rw [map_mul, η, ξ, inv'_gen, inv'_gen, neg_mul_neg]

theorem body_qq {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (γ : Bool) (a b : Λ) :
    body (qq γ a b) = 0 := by
  rw [qq, map_mul, η, body_gen, zero_mul]

theorem isEven_Qf (p : Pt {i // i ≠ ρ}) : IsEven (Qf w ρ p) :=
  IsEven.sum _ fun γ _ => IsEven.sum _ fun a _ => IsEven.sum _ fun b _ => (isEven_qq γ a b).smul _

theorem body_Qf (p : Pt {i // i ≠ ρ}) : body (Qf w ρ p) = 0 := by
  simp [Qf, map_sum, body_qq]

theorem scomp_exp_neg (r : ℝ) {Q : B {i // i ≠ ρ}} (hQ : IsEven Q) (h0 : body Q = 0) :
    scomp Real.exp (-(r • (1 : B {i // i ≠ ρ}) + Q)) = Real.exp (-r) • IsNilpotent.exp (-Q) := by
  have e : -(r • (1 : B {i // i ≠ ρ}) + Q) = algebraMap ℝ _ (-r) + -Q := by
    rw [neg_add, map_neg, Algebra.algebraMap_eq_smul_one]
  have hs : soul (-(r • (1 : B {i // i ≠ ρ}) + Q)) = -Q := by
    rw [e, soul_algebraMap_add, soul_of_body_eq_zero (by rw [map_neg, h0, neg_zero])]
  have hb : body (-(r • (1 : B {i // i ≠ ρ}) + Q)) = -r := by
    rw [e, map_add, AlgHom.commutes, map_neg, map_neg, h0]; simp
  rw [scomp_exp (by rw [hs]; exact ⟨_, pow_card_succ_eq_zero hQ.neg (by rw [map_neg, h0, neg_zero])⟩),
    hs, hb]

/-! ### The fermionic Gaussian -/

/-- The block matrix `𝓛ᵀ ⊕ 𝓛ᵀ` (one block per flavour). -/
def Mb (w : V → V → ℝ) (ρ : V) (p : Pt {i // i ≠ ρ}) :
    Matrix ({i // i ≠ ρ} ⊕ {i // i ≠ ρ}) ({i // i ≠ ρ} ⊕ {i // i ≠ ρ}) ℝ :=
  Matrix.fromBlocks (Lmat w ρ (ext ρ (tauP p)))ᵀ 0 0 (Lmat w ρ (ext ρ (tauP p)))ᵀ

theorem neg_Qf_eq (p : Pt {i // i ≠ ρ}) :
    -Qf w ρ p = ∑ m, ∑ m', Mb w ρ p m m' • (ξ m * η m' : B {i // i ≠ ρ}) := by
  have hq : ∀ (L : Matrix {i // i ≠ ρ} {i // i ≠ ρ} ℝ) γ (a b : {i // i ≠ ρ}),
      -(L a b • qq γ a b) = L a b • (ξ (mf γ b) * η (mf γ a)) :=
    fun L γ a b => by rw [qq, η, ξ, gen_anticomm, smul_neg, neg_neg]
  rw [Qf, ← sum_neg_distrib]
  simp only [← sum_neg_distrib, hq, Fintype.sum_bool, Fintype.sum_sum_type, Mb,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, sum_const_zero, add_zero, zero_add,
    Matrix.transpose_apply, mf]
  congr 1 <;> exact Finset.sum_comm

theorem body_berezin_exp_neg_Qf (p : Pt {i // i ≠ ρ}) :
    body (berezin (IsNilpotent.exp (-Qf w ρ p))) = (Lmat w ρ (ext ρ (tauP p))).det ^ 2 := by
  rw [neg_Qf_eq, body_berezin_exp_quad, Mb, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose, sq]

end

end ArborealDecay.BCHS

end
