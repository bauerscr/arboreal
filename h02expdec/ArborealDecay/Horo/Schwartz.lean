module

public import ArborealDecay.Horo.Shift

/-!
# Schwartz-class superfunctions

`SSchwartz F`: every coordinate `ℓ ∘ F` of an `A`-valued function on `E → ℝ` is a Schwartz
function.  The class is closed under linear maps, sums, multiplication by scalar functions of
temperate growth, and partial derivatives; it is contained in `SDecay`.  Consequently the
nilpotent change of generators `integral_shiftT_mul` holds for Schwartz `F` and temperate `g`
without further hypotheses (`integral_dual_shiftT_mul_of_schwartz`).
-/

@[expose] public section

namespace ArborealDecay.Horo

noncomputable section

open MeasureTheory Finset ArborealDecay.Super SchwartzMap

set_option linter.unusedSectionVars false

variable {E : Type*} [Fintype E]

local notation "X" => E → ℝ

section Module

variable {A : Type*} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
variable {B : Type*} [AddCommGroup B] [Module ℝ B] [FiniteDimensional ℝ B]

/-- Every coordinate of `F` is a Schwartz function. -/
def SSchwartz (F : X → A) : Prop :=
  ∀ ℓ : Module.Dual ℝ A, ∃ f : 𝓢(X, ℝ), ∀ x, f x = ℓ (F x)

theorem SSchwartz.map {F : X → A} (hF : SSchwartz F) (L : A →ₗ[ℝ] B) :
    SSchwartz fun x => L (F x) := fun ℓ => hF (ℓ ∘ₗ L)

theorem SSchwartz.zero : SSchwartz (fun _ : X => (0 : A)) := fun ℓ => ⟨0, fun x => by simp⟩

theorem SSchwartz.add {F G : X → A} (hF : SSchwartz F) (hG : SSchwartz G) :
    SSchwartz fun x => F x + G x := fun ℓ => by
  obtain ⟨f, hf⟩ := hF ℓ; obtain ⟨g, hg⟩ := hG ℓ
  exact ⟨f + g, fun x => by simp [hf, hg]⟩

theorem SSchwartz.neg {F : X → A} (hF : SSchwartz F) : SSchwartz fun x => -F x := fun ℓ => by
  obtain ⟨f, hf⟩ := hF ℓ
  exact ⟨-f, fun x => by simp [hf]⟩

theorem SSchwartz.sub {F G : X → A} (hF : SSchwartz F) (hG : SSchwartz G) :
    SSchwartz fun x => F x - G x := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem SSchwartz.sum {ι : Type*} (s : Finset ι) {F : ι → X → A}
    (hF : ∀ i ∈ s, SSchwartz (F i)) : SSchwartz fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SSchwartz.zero : SSchwartz fun _ : X => (0 : A))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- Multiplication by a scalar function of temperate growth. -/
theorem SSchwartz.smul {F : X → A} (hF : SSchwartz F) {g : X → ℝ}
    (hg : g.HasTemperateGrowth) : SSchwartz fun x => g x • F x := fun ℓ => by
  obtain ⟨f, hf⟩ := hF ℓ
  exact ⟨smulLeftCLM ℝ g f, fun x => by
    rw [smulLeftCLM_apply_apply hg, hf, map_smul]⟩

theorem SSchwartz.sdiff {F : X → A} (hF : SSchwartz F) : SDiff F := fun ℓ => by
  obtain ⟨f, hf⟩ := hF ℓ
  have : (fun x => ℓ (F x)) = f := funext fun x => (hf x).symm
  rw [this]; exact f.differentiable

theorem SSchwartz.pd {F : X → A} (hF : SSchwartz F) (v : X) : SSchwartz (pd v F) := fun ℓ => by
  obtain ⟨f, hf⟩ := hF ℓ
  have e : (fun x => ℓ (F x)) = f := funext fun x => (hf x).symm
  refine ⟨LineDeriv.lineDerivOp v f, fun x => ?_⟩
  rw [lineDerivOp_apply_eq_fderiv, dual_pd hF.sdiff, e]

theorem SSchwartz.sdecay {F : X → A} (hF : SSchwartz F) : SDecay F := fun ℓ => by
  obtain ⟨f, hf⟩ := hF ℓ
  have e : (fun x => ℓ (F x)) = fun x => f x := funext fun x => (hf x).symm
  rw [e]; exact decay_of_schwartzMap f

theorem SSchwartz.sint {F : X → A} (hF : SSchwartz F) : SInt F volume := hF.sdecay.sint

end Module

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

theorem SSchwartz.pdn {F : X → A} (hF : SSchwartz F) (v : X) (m : ℕ) :
    SSchwartz (ArborealDecay.Horo.pdn v m F) := by
  induction m with
  | zero => exact hF
  | succ m ih => exact ih.pd v

theorem SSchwartz.mul_const {F : X → A} (hF : SSchwartz F) (c : A) :
    SSchwartz fun x => F x * c := hF.map (LinearMap.mulRight ℝ c)

theorem SSchwartz.const_mul {F : X → A} (hF : SSchwartz F) (c : A) :
    SSchwartz fun x => c * F x := hF.map (LinearMap.mulLeft ℝ c)

theorem hasTemperateGrowth_pow_div {g : X → ℝ} (hg : g.HasTemperateGrowth) (m : ℕ) (c : ℝ) :
    (fun x => g x ^ m / c).HasTemperateGrowth := by
  have := (hg.pow m).mul (Function.HasTemperateGrowth.const c⁻¹)
  convert this using 1
  funext x; simp [div_eq_mul_inv]

theorem SSchwartz.shiftT {F : X → A} (hF : SSchwartz F) (v : X) {g : X → ℝ}
    (hg : g.HasTemperateGrowth) (n : A) (K : ℕ) : SSchwartz (shiftT v g n K F) :=
  SSchwartz.sum _ fun m _ => ((hF.pdn v m).mul_const _).smul (hasTemperateGrowth_pow_div hg m _)

theorem SSchwartz.shiftPrim {F : X → A} (hF : SSchwartz F) (v : X) {g : X → ℝ}
    (hg : g.HasTemperateGrowth) (n : A) (m : ℕ) : SSchwartz (shiftPrim v g n F m) :=
  ((hF.pdn v m).mul_const _).smul (hasTemperateGrowth_pow_div hg (m + 1) _)

/-- **Nilpotent change of generators** for Schwartz `F` and temperate `g`:
`∫ ℓ (F(x + g(x) n) · (1 + ∂_v g · n)) dx = ∫ ℓ (F x) dx`. -/
theorem integral_dual_shiftT_mul_of_schwartz (v : X) {g : X → ℝ}
    (hg : g.HasTemperateGrowth) {n : A} {K : ℕ} (hn : n ^ K = 0) {F : X → A}
    (hF : SSchwartz F) (ℓ : Module.Dual ℝ A) :
    ∫ x, ℓ (ArborealDecay.Horo.shiftT v g n K F x * (1 + fderiv ℝ g x v • n)) =
      ∫ x, ℓ (F x) :=
  integral_dual_shiftT_mul v (hg.1.differentiable (by simp)) hn (fun m _ => (hF.pdn v m).sdiff)
    hF.sint (fun m _ => (hF.shiftPrim v hg n m).sdecay) ℓ

end Algebra

end

end ArborealDecay.Horo

end
