import Loc.EstTransfer
import Loc.EstCutoff
import Loc.EstLeibniz
import Step2.Lip.FlowLipCov
import Obs2.Map.GramDiff
import Step2.Coup.CoupFlow

/-!
# Localised Gram representations of `C − C(x₀,x₀) J`

For a covariance `C` with a Gram representation at scale `h₁` (constant `γ₁`) and a box of
radius `R ≤ h₁` around `x₀`, the matrix `C − C(x₀, x₀)` agrees on the box with a covariance
which has a Gram representation at every scale `h ≤ R` with the *small* constant
`K(μ⁻¹ δ + μ γ₁)`, `δ = 4dRγ₁/h₁` (`gram_loc`). The construction uses a smooth cut-off
`χ = cutP 0 R (r(· − x₀))` on the torus (`chiT`, `abs_D1_chiT_le`), a Leibniz bound for
vector-valued functions (`norm_gvec_smul_le`) and the Lipschitz bound of the Gram vectors
(`norm_gram_sub_le`). Sums of Gram representations: `gram_pi`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Obs2

noncomputable section

open Finset Grassmann Loc FRD Step2

variable {d L N : ℕ} [NeZero L]

/-! ### `gvec` of a profile -/

section Gvec

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gvec_single' (Fv : Λ → H) (x : Λ) : gvec Fv (Pi.single x 1) = Fv x := by
  rw [gvec, sum_eq_single x (fun y _ hy => by simp [hy]) (by simp)]
  simp

theorem gvec_add' (Fv : Λ → H) (f g : Λ → ℝ) : gvec Fv (f + g) = gvec Fv f + gvec Fv g := by
  simp only [gvec, Pi.add_apply, Complex.ofReal_add, add_smul, sum_add_distrib]

theorem gvec_rsmul (Fv : Λ → H) (c : ℝ) (f : Λ → ℝ) : gvec Fv (c • f) = (c : ℂ) • gvec Fv f := by
  simp only [gvec, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul, smul_sum]

theorem gvec_fsum (Fv : Λ → H) {ι : Type*} (s : Finset ι) (f : ι → Λ → ℝ) :
    gvec Fv (∑ i ∈ s, f i) = ∑ i ∈ s, gvec Fv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gvec]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, gvec_add', ih]

/-- `∑_y (∇^a δ_x)(y) F_y = ∑_{b ≤ a} c_{a,b} F_{x+b}`. -/
theorem gvec_dprof_eq (Fv : Λ → H) (a : E → ℕ) (x : Λ) :
    gvec Fv (dprof a x) = ∑ b ∈ Iic a, (cf a b : ℂ) • Fv (b +ᵥ x) := by
  rw [dprof, gvec_fsum]
  refine sum_congr rfl fun b _ => ?_
  rw [gvec_rsmul, gvec_single']

theorem gvec_fun_smul (c : ℂ) (F : Λ → H) (f : Λ → ℝ) :
    gvec (fun x => c • F x) f = c • gvec F f := by
  simp only [gvec, smul_sum, smul_comm c]

/-- Derivatives of positive order kill constants. -/
theorem gvec_dprof_sub_const (Fv : Λ → H) (v : H) {a : E → ℕ} (ha : a ≠ 0) (x : Λ) :
    gvec (fun y => Fv y - v) (dprof a x) = gvec Fv (dprof a x) := by
  rw [gvec_dprof_eq, gvec_dprof_eq]
  simp only [smul_sub, sum_sub_distrib, ← sum_smul]
  have : ∑ b ∈ Iic a, (cf a b : ℂ) = 0 := by
    rw [← Complex.ofReal_sum, sum_cf_eq_zero ha, Complex.ofReal_zero]
  rw [this, zero_smul, sub_zero]

theorem gvec_dprof_const_smul (χ : Λ → ℝ) (v : H) (a : E → ℕ) (x : Λ) :
    gvec (fun y => (χ y : ℂ) • v) (dprof a x) =
      ((D1 (fun b y => b +ᵥ y) a χ x : ℝ) : ℂ) • v := by
  rw [gvec_dprof_eq, D1_eq_sum, Complex.ofReal_sum, sum_smul]
  refine sum_congr rfl fun b _ => ?_
  rw [smul_smul, Complex.ofReal_mul]

end Gvec

/-! ### The Leibniz bound for vector-valued functions -/

section Leibniz

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem nabla1_eq {W : Type*} [AddCommGroup W] [Module ℝ W] (s : (E → ℕ) → Λ → Λ) (a : E → ℕ)
    (f : Λ → W) (x : Λ) :
    nabla s (fun _ : Fin 1 => a) (fun z => f (z 0)) (fun _ => x) =
      ∑ b ∈ Iic a, cf a b • f (s b x) := by
  rw [nabla_apply]
  let e : (Fin 1 → E → ℕ) ≃ (E → ℕ) := Equiv.funUnique (Fin 1) (E → ℕ)
  have hS : Fintype.piFinset (fun _ : Fin 1 => Iic a) = (Iic a).map e.symm.toEmbedding := by
    ext β
    simp only [Fintype.mem_piFinset, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h; exact ⟨β 0, h 0, by funext i; fin_cases i; rfl⟩
    · rintro ⟨b, hb, rfl⟩ i; fin_cases i; exact hb
  rw [hS, sum_map]
  refine sum_congr rfl fun b _ => ?_
  simp [e, Equiv.funUnique]

/-- **Leibniz bound**: `‖∇^a(χ V)(x)‖ ≤ 2^{|a|} M` if
`|∇^b χ(x)| ‖∇^{a−b} V(x + b)‖ ≤ M` for all `b ≤ a`. -/
theorem norm_gvec_smul_le (χ : Λ → ℝ) (V : Λ → H) (a : E → ℕ) (x : Λ) {M : ℝ}
    (hM : ∀ b ≤ a, |D1 (fun b y => b +ᵥ y) b χ x| * ‖gvec V (dprof (a - b) (b +ᵥ x))‖ ≤ M) :
    ‖gvec (fun y => (χ y : ℂ) • V y) (dprof a x)‖ ≤ 2 ^ mabs a * M := by
  set w := gvec (fun y => (χ y : ℂ) • V y) (dprof a x) with hw
  have hM0 : 0 ≤ M := (mul_nonneg (abs_nonneg _) (norm_nonneg _)).trans (hM 0 (fun e => Nat.zero_le (a e)))
  rcases eq_or_ne w 0 with h0 | h0
  · rw [h0, norm_zero]; positivity
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 h0
  set s : (E → ℕ) → Λ → Λ := fun b y => b +ᵥ y
  have hs0 : ∀ y, s 0 y = y := fun y => zero_vadd _ y
  have hsa : ∀ b b' y, s (b + b') y = s b (s b' y) := fun b b' y => add_vadd b b' y
  set φ : Λ → ℂ := fun y => inner ℂ w (V y)
  have hinner : inner ℂ w w = nabla s (fun _ : Fin 1 => a)
      (fun z => ((χ (z 0) : ℝ) : ℂ) * φ (z 0)) (fun _ => x) := by
    rw [nabla1_eq s a (fun y => ((χ y : ℝ) : ℂ) * φ y) x]
    have e1 : w = ∑ b ∈ Iic a, (cf a b : ℂ) • ((χ (b +ᵥ x) : ℂ) • V (b +ᵥ x)) :=
      gvec_dprof_eq _ a x
    nth_rewrite 2 [e1]
    rw [inner_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [inner_smul_right, inner_smul_right, Complex.real_smul]
  have key := abs_nabla_mul_le (n := 1) s hs0 hsa (fun _ : Fin 1 => a)
    (fun z => ((χ (z 0) : ℝ) : ℂ)) (fun z => φ (z 0)) (fun _ => x) (M := M * ‖w‖) (by
      intro γ hγ
      have h1 : nabla s γ (fun z => ((χ (z 0) : ℝ) : ℂ)) (fun _ => x) =
          ((D1 s (γ 0) χ x : ℝ) : ℂ) := by
        have : γ = fun _ => γ 0 := by funext i; fin_cases i; rfl
        rw [this]
        refine (nabla1_eq s (γ 0) (fun y => ((χ y : ℝ) : ℂ)) x).trans ?_
        rw [D1_eq_sum, Complex.ofReal_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [Complex.real_smul, Complex.ofReal_mul]
      have h2 : nabla s ((fun _ : Fin 1 => a) - γ) (fun z => φ (z 0)) (fun i => s (γ i) x) =
          inner ℂ w (gvec V (dprof (a - γ 0) (γ 0 +ᵥ x))) := by
        have : ((fun _ : Fin 1 => a) - γ) = fun _ => a - γ 0 := by
          funext i; fin_cases i; rfl
        have hx : (fun i : Fin 1 => s (γ i) x) = fun _ => s (γ 0) x := by
          funext i; fin_cases i; rfl
        rw [this, hx]
        refine (nabla1_eq s (a - γ 0) φ (s (γ 0) x)).trans ?_
        rw [gvec_dprof_eq, inner_sum]
        refine sum_congr rfl fun b _ => ?_
        rw [inner_smul_right, Complex.real_smul]
      rw [h1, h2, Complex.norm_real, Real.norm_eq_abs]
      have hb := hM (γ 0) (hγ 0)
      calc |D1 s (γ 0) χ x| * ‖inner ℂ w (gvec V (dprof (a - γ 0) (γ 0 +ᵥ x)))‖
          ≤ |D1 s (γ 0) χ x| * (‖w‖ * ‖gvec V (dprof (a - γ 0) (γ 0 +ᵥ x))‖) :=
            mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (abs_nonneg _)
        _ = (|D1 s (γ 0) χ x| * ‖gvec V (dprof (a - γ 0) (γ 0 +ᵥ x))‖) * ‖w‖ := by ring
        _ ≤ M * ‖w‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hord : ord (fun _ : Fin 1 => a) = mabs a := by simp [ord]
  rw [← hinner, hord, inner_self_eq_norm_sq_to_K] at key
  have : ‖w‖ ^ 2 ≤ 2 ^ mabs a * (M * ‖w‖) := by simpa using key
  have h3 : ‖w‖ * ‖w‖ ≤ (2 ^ mabs a * M) * ‖w‖ := by nlinarith
  exact le_of_mul_le_mul_right h3 hwpos

end Leibniz


/-! ### The cut-off on the torus -/

section Cut

/-- The cut-off `χ(x) = cutP 0 R (r(x − x₀))` (`= 1` on the box of radius `R` around `x₀`,
`= 0` outside the box of radius `2R`). -/
def chiT (R : ℝ) (x₀ x : Lam d L N) : ℝ := cutP (0 : Fin d → ℕ) R (rep (x - x₀))

theorem chiT_eq_one {R : ℝ} (hR : 0 < R) {x₀ x : Lam d L N}
    (hx : (supNorm (x - x₀) : ℝ) ≤ R) : chiT R x₀ x = 1 := by
  rw [chiT, cutP_eq _ hR (by rwa [supNormZ_rep_eq])]
  simp

theorem chiT_eq_zero {R : ℝ} (hR : 0 < R) {x₀ x : Lam d L N}
    (hx : 2 * R ≤ (supNorm (x - x₀) : ℝ)) : chiT R x₀ x = 0 :=
  cutP_eq_zero _ hR (by rwa [supNormZ_rep_eq])

/-- The constant of the derivative bounds of the cut-off. -/
def cutK (d : ℕ) : ℝ := Classical.choose (exists_D1_cutP_bound d (pPhi d) 0)

theorem cutK_nonneg (d : ℕ) : 0 ≤ cutK d :=
  (Classical.choose_spec (exists_D1_cutP_bound d (pPhi d) 0)).1

theorem abs_D1_cutP_le {R : ℝ} (hR : 1 ≤ R) {a : Dir d → ℕ} (ha : Grassmann.mabs a ≤ pPhi d) (u : Zd d) :
    |D1 (fun b v => b +ᵥ v) a (cutP (0 : Fin d → ℕ) R) u| ≤ cutK d / R ^ Grassmann.mabs a := by
  have := (Classical.choose_spec (exists_D1_cutP_bound d (pPhi d) 0)).2 0 (fun _ => le_rfl) R hR
    a ha u
  simpa [cutK] using this

theorem supNorm_vadd_sub_le (β : Dir d → ℕ) (x x₀ : Lam d L N) :
    supNorm ((β +ᵥ x) - x₀) ≤ supNorm (x - x₀) + Grassmann.mabs β := by
  have e : (β +ᵥ x) - x₀ = (x - x₀) + dirHom β := by
    rw [Grassmann.vadd_def]
    show dirHom β + x - x₀ = x - x₀ + dirHom β
    abel
  have h1 := supNorm_add_le (x - x₀) (dirHom β : Lam d L N)
  have h2 := supNorm_dirHom_le (L := L) (N := N) β
  rw [e]
  omega

/-- **Derivatives of the cut-off**: `|∇^a χ(x)| ≤ K R^{-|a|}`, and `∇^a χ(x) = 0` far from `x₀`. -/
theorem D1_chiT_le {R : ℝ} (hR : 1 ≤ R) {S : ℕ} (hS : 2 * R ≤ S)
    (hSP : 2 * (S + 2 * pPhi d) < L ^ N) {a : Dir d → ℕ} (ha : Grassmann.mabs a ≤ pPhi d)
    (x₀ x : Lam d L N) :
    |D1 (fun b y => b +ᵥ y) a (chiT R x₀) x| ≤ cutK d / R ^ Grassmann.mabs a ∧
      (S + pPhi d < supNorm (x - x₀) → D1 (fun b y => b +ᵥ y) a (chiT R x₀) x = 0) := by
  have hR0 : 0 < R := by linarith
  by_cases hx : supNorm (x - x₀) ≤ S + pPhi d
  · have e : D1 (fun b y => b +ᵥ y) a (chiT R x₀) x =
        D1 (fun b v => b +ᵥ v) a (cutP (0 : Fin d → ℕ) R) (rep (x - x₀)) := by
      rw [D1_eq_sum, D1_eq_sum]
      refine sum_congr rfl fun b hb => ?_
      rw [chiT, rep_vadd_sub x₀ x b hSP ((mabs_le_of_le (mem_Iic.1 hb)).trans ha) hx]
    exact ⟨e ▸ abs_D1_cutP_le hR ha _, fun h => absurd h (not_lt.2 hx)⟩
  · push Not at hx
    have hz : D1 (fun b y => b +ᵥ y) a (chiT R x₀) x = 0 := by
      rw [D1_eq_sum]
      refine sum_eq_zero fun b hb => ?_
      have h1 := lt_supNorm_vadd_sub x₀ x b ((mabs_le_of_le (mem_Iic.1 hb)).trans ha) hx
      have h2 : (S : ℝ) < supNorm ((b +ᵥ x) - x₀) := by exact_mod_cast h1
      rw [chiT_eq_zero hR0 (by linarith), mul_zero]
    rw [hz, abs_zero]
    exact ⟨by have := cutK_nonneg d; positivity, fun _ => rfl⟩

end Cut

/-! ### The Lipschitz bound of Gram vectors -/

section Lip

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_vadd_sub_le (V : Lam d L N → H) {K : ℝ}
    (hK : ∀ e y, ‖V (dirVec e + y) - V y‖ ≤ K) :
    ∀ (m : ℕ) (β : Dir d → ℕ), Grassmann.mabs β = m → ∀ y, ‖V (β +ᵥ y) - V y‖ ≤ m * K := by
  intro m
  induction m with
  | zero =>
    intro β hβ y
    have : β = 0 := by
      funext e
      have := (Finset.sum_eq_zero_iff.1 hβ) e (mem_univ e)
      simpa using this
    subst this
    rw [zero_vadd, sub_self, norm_zero]; simp
  | succ m ih =>
    intro β hβ y
    obtain ⟨e, he⟩ : ∃ e, β e ≠ 0 := by
      by_contra h; push Not at h
      have : Grassmann.mabs β = 0 := Finset.sum_eq_zero fun e _ => h e
      omega
    set β' : Dir d → ℕ := β - Pi.single e 1
    have hβ' : β = Pi.single e 1 + β' := by
      funext e'
      by_cases h : e' = e
      · subst h; simp [β']; omega
      · simp [β', h]
    have hm : Grassmann.mabs β' = m := by
      have : Grassmann.mabs β = Grassmann.mabs (Pi.single e 1 : Dir d → ℕ) + Grassmann.mabs β' := by
        rw [hβ']; simp [Grassmann.mabs, sum_add_distrib]
      have h1 : Grassmann.mabs (Pi.single e 1 : Dir d → ℕ) = 1 := by
        unfold Grassmann.mabs
        rw [sum_eq_single e (fun e' _ he' => by simp [he']) (by simp)]
        simp
      omega
    rw [hβ', add_vadd, single_vadd, add_comm _ (dirVec e)]
    have h1 := hK e (β' +ᵥ y)
    have h2 := ih β' hm y
    calc ‖V (dirVec e + (β' +ᵥ y)) - V y‖
        = ‖(V (dirVec e + (β' +ᵥ y)) - V (β' +ᵥ y)) + (V (β' +ᵥ y) - V y)‖ := by
          congr 1; abel
      _ ≤ K + m * K := norm_add_le_of_le h1 h2
      _ = (↑(m + 1)) * K := by push_cast; ring

theorem dirHomZ_toNat (u : Zd d) :
    dirHomZ (fun e : Dir d => match e with
      | Sum.inl i => (u i).toNat
      | Sum.inr i => (-u i).toNat) = u := by
  show ∑ e, _ • dirZ e = u
  rw [Fintype.sum_sum_type]
  simp only [dirZ]
  funext j
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_neg,
    ← sum_add_distrib]
  rw [sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
  simp only [Pi.single_eq_same, nsmul_eq_mul, mul_one]
  have := Int.toNat_sub_toNat_neg (u j)
  omega

/-- **Lipschitz bound**: `‖V_x − V_{x₀}‖ ≤ d |x − x₀|_∞ K` if every unit step changes `V` by
at most `K`. -/
theorem norm_gram_sub_le (V : Lam d L N → H) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ e y, ‖V (dirVec e + y) - V y‖ ≤ K) (x₀ x : Lam d L N) :
    ‖V x - V x₀‖ ≤ (d * supNorm (x - x₀)) * K := by
  set u := rep (x - x₀)
  set β : Dir d → ℕ := fun e => match e with
    | Sum.inl i => (u i).toNat
    | Sum.inr i => (-u i).toNat
  have hx : β +ᵥ x₀ = x := by
    rw [Grassmann.vadd_def]
    show dirHom β + x₀ = x
    rw [← prj_dirHomZ, dirHomZ_toNat, prj_rep]; abel
  have hm : Grassmann.mabs β ≤ d * supNorm (x - x₀) := by
    have e1 : Grassmann.mabs β = ∑ i, (u i).natAbs := by
      unfold Grassmann.mabs
      rw [Fintype.sum_sum_type, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [β]
      omega
    rw [e1, ← supNormZ_rep_eq]
    calc ∑ i, (u i).natAbs ≤ ∑ _i : Fin d, supNormZ u :=
          sum_le_sum fun i _ => natAbs_le_supNormZ u i
      _ = d * supNormZ u := by simp
  have := norm_vadd_sub_le V hK (Grassmann.mabs β) β rfl x₀
  rw [hx] at this
  refine this.trans (mul_le_mul_of_nonneg_right ?_ hK0)
  exact_mod_cast hm

end Lip


/-! ### The localised Gram representation -/

section GramLoc

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The constant `K = 2^{p_Φ} max(K_χ, 1)` of the localised Gram bound. -/
def locK (d : ℕ) : ℝ := 2 ^ pPhi d * max (cutK d) 1

theorem mabs_single_tau' (e : Dir d) : Grassmann.mabs (Pi.single e 1 : Dir d → ℕ) = 1 := by
  unfold Grassmann.mabs
  rw [sum_eq_single e (fun e' _ he' => by simp [he']) (by simp)]
  simp

theorem one_le_locK (d : ℕ) : 1 ≤ locK d := by
  unfold locK
  have h1 : (1 : ℝ) ≤ 2 ^ pPhi d := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ max (cutK d) 1 := le_max_right _ _
  nlinarith

theorem gvec_sub' {Λ : Type*} [Fintype Λ] {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] (Fv : Λ → H') (f g : Λ → ℝ) :
    gvec Fv (f - g) = gvec Fv f - gvec Fv g := by
  simp only [gvec, Pi.sub_apply, Complex.ofReal_sub, sub_smul, sum_sub_distrib]

theorem inv_pow_le_of_le {R h₁ : ℝ} (hR : 0 < R) (hRh : R ≤ h₁) {n : ℕ} (hn : 1 ≤ n) :
    (h₁ ^ n)⁻¹ ≤ R / h₁ * (R ^ n)⁻¹ := by
  have hh : 0 < h₁ := hR.trans_le hRh
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, pow_succ, div_eq_mul_inv, mul_inv, mul_inv]
  have h1 : (h₁ ^ m)⁻¹ ≤ (R ^ m)⁻¹ :=
    inv_anti₀ (pow_pos hR m) (pow_le_pow_left₀ hR.le hRh m)
  have e : R * h₁⁻¹ * ((R ^ m)⁻¹ * R⁻¹) = (R ^ m)⁻¹ * h₁⁻¹ := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hh.le)

theorem real_comb {μ δ γ K κ₁ κ₂ A B X Y : ℝ} (hμ : 0 < μ) (hA : A ≤ κ₁ * (δ * X))
    (hB : B ≤ κ₂ * γ * X) (h1 : κ₁ ≤ K) (h2 : κ₂ ≤ K) (hXY : X ≤ Y) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hX : 0 ≤ X) (hK : 0 ≤ K) : μ⁻¹ * A + μ * B ≤ K * (μ⁻¹ * δ + μ * γ) * Y := by
  have hμi : 0 < μ⁻¹ := inv_pos.2 hμ
  have e1 : μ⁻¹ * A ≤ μ⁻¹ * (K * (δ * X)) :=
    mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_right h1 (by positivity))) hμi.le
  have e2 : μ * B ≤ μ * (K * γ * X) :=
    mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 hγ) hX)) hμ.le
  have e3 : μ⁻¹ * (K * (δ * X)) + μ * (K * γ * X) = K * (μ⁻¹ * δ + μ * γ) * X := by ring
  have e4 : K * (μ⁻¹ * δ + μ * γ) * X ≤ K * (μ⁻¹ * δ + μ * γ) * Y :=
    mul_le_mul_of_nonneg_left hXY (by positivity)
  linarith

theorem gramBound_pair {F₁ F₂ G₁ G₂ : Lam d L N → H} {c h : ℝ}
    (hb : ∀ a : Dir d → ℕ, Grassmann.mabs a ≤ pPhi d → ∀ x : Lam d L N,
      ‖gvec F₁ (dprof a x)‖ + ‖gvec F₂ (dprof a x)‖ ≤ c * (h ^ Grassmann.mabs a)⁻¹ ∧
      ‖gvec G₁ (dprof a x)‖ + ‖gvec G₂ (dprof a x)‖ ≤ c * (h ^ Grassmann.mabs a)⁻¹) :
    GramBound (Dir d) (pPhi d) h c (fun x => WithLp.toLp 2 (F₁ x, F₂ x))
      (fun x => WithLp.toLp 2 (G₁ x, G₂ x)) := by
  intro a ha x
  refine ⟨(norm_toLp_le _).trans ?_, (norm_toLp_le _).trans ?_⟩
  · rw [gvec_prod]; exact (hb a ha x).1
  · rw [gvec_prod]; exact (hb a ha x).2

/-- **The localised Gram representation of `C − C(x₀,x₀)`**: for a covariance with a Gram
representation at scale `h₁` with constant `γ₁`, and `p_Φ < R ≤ h₁`, there are Gram vectors
`F', G'` with `⟪F'_x, G'_y⟫ = C(x,y) − C(x₀,x₀)` for `|x − x₀|, |y − x₀| ≤ R` and Gram bound
`K(μ⁻¹ δ + μ γ₁)` at every scale `h ≤ R`, `δ = 4dRγ₁/h₁`. -/
theorem gram_loc (hd : 1 ≤ d) {C : Matrix (Lam d L N) (Lam d L N) ℂ} {Fv Gv : Lam d L N → H}
    (hC : IsGram C Fv Gv) {h₁ γ₁ : ℝ} (hγ₁ : 0 ≤ γ₁)
    (hB : GramBound (Dir d) (pPhi d) h₁ γ₁ Fv Gv) {R h : ℝ} (hh : 0 < h) (hhR : h ≤ R)
    (hRh : R ≤ h₁) (hR : 2 * (pPhi d : ℝ) + 1 ≤ R)
    (hN : 2 * (⌈2 * R⌉₊ + 2 * pPhi d) < L ^ N) (x₀ : Lam d L N) {μ : ℝ} (hμ : 0 < μ) :
    ∃ (F' G' : Lam d L N → WithLp 2 (H × H)),
      GramBound (Dir d) (pPhi d) h (locK d * (μ⁻¹ * (4 * d * R * γ₁ / h₁) + μ * γ₁)) F' G' ∧
      ∀ x y, (supNorm (x - x₀) : ℝ) ≤ R → (supNorm (y - x₀) : ℝ) ≤ R →
        inner ℂ (F' x) (G' y) = C x y - C x₀ x₀ := by
  set P := pPhi d with hP
  set χ := chiT (L := L) (N := N) R x₀ with hχ
  set S := ⌈2 * R⌉₊ with hSdef
  have hR1 : 1 ≤ R := by have : (0 : ℝ) ≤ P := Nat.cast_nonneg _; linarith
  have hR0 : 0 < R := by linarith
  have hh₁ : 0 < h₁ := hR0.trans_le hRh
  have hS : 2 * R ≤ S := Nat.le_ceil _
  have hS' : (S : ℝ) < 2 * R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hP1 : 1 ≤ P := by rw [hP]; unfold pPhi; omega
  have hK0 := cutK_nonneg d
  set δ : ℝ := 4 * d * R * γ₁ / h₁ with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  -- unit steps
  have hstep : ∀ (V : Lam d L N → H), (∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N,
      ‖gvec V (dprof a x)‖ ≤ γ₁ * (h₁ ^ Grassmann.mabs a)⁻¹) →
      ∀ e y, ‖V (dirVec e + y) - V y‖ ≤ γ₁ * h₁⁻¹ := by
    intro V hV e y
    have := hV (Pi.single e 1 : Dir d → ℕ) (by rw [mabs_single_tau']; exact hP1) y
    rwa [mabs_single_tau', pow_one, dprof_single, gvec_sub', gvec_single', gvec_single'] at this
  have hBF : ∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N, ‖gvec Fv (dprof a x)‖ ≤ γ₁ * (h₁ ^ Grassmann.mabs a)⁻¹ :=
    fun a ha x => (hB a ha x).1
  have hBG : ∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N, ‖gvec Gv (dprof a x)‖ ≤ γ₁ * (h₁ ^ Grassmann.mabs a)⁻¹ :=
    fun a ha x => (hB a ha x).2
  have hzero : ∀ (V : Lam d L N → H), (∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N,
      ‖gvec V (dprof a x)‖ ≤ γ₁ * (h₁ ^ Grassmann.mabs a)⁻¹) → ‖V x₀‖ ≤ γ₁ := by
    intro V hV
    have := hV 0 (by simp [Grassmann.mabs]) x₀
    rwa [dprof_zero, gvec_single', show Grassmann.mabs (0 : Dir d → ℕ) = 0 by simp [Grassmann.mabs],
      pow_zero, inv_one, mul_one] at this
  -- the first component
  have hcomp1 : ∀ (V : Lam d L N → H), (∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N,
      ‖gvec V (dprof a x)‖ ≤ γ₁ * (h₁ ^ Grassmann.mabs a)⁻¹) →
      ∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N,
      ‖gvec (fun y => (χ y : ℂ) • (V y - V x₀)) (dprof a x)‖ ≤
        2 ^ P * (cutK d * δ * (R ^ Grassmann.mabs a)⁻¹) := by
    intro V hV a ha x
    have hL := norm_gram_sub_le V (by positivity) (hstep V hV) x₀
    refine (norm_gvec_smul_le χ (fun y => V y - V x₀) a x ?_).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ha) (by positivity))
    intro b hb
    have hbP : Grassmann.mabs b ≤ P := (mabs_le_of_le hb).trans ha
    obtain ⟨hD, hD0⟩ := D1_chiT_le (L := L) (N := N) hR1 hS hN hbP x₀ x
    by_cases hba : b = a
    · subst hba
      rw [tsub_self, dprof_zero, gvec_single']
      by_cases hx : S + P < supNorm (x - x₀)
      · rw [hD0 hx, abs_zero, zero_mul]; positivity
      · push Not at hx
        have h1 := supNorm_vadd_sub_le b x x₀
        have h2 : ((supNorm ((b +ᵥ x) - x₀) : ℕ) : ℝ) ≤ S + 2 * P := by
          exact_mod_cast (show supNorm ((b +ᵥ x) - x₀) ≤ S + 2 * P by omega)
        have h3 := hL (b +ᵥ x)
        have h4 : ‖V (b +ᵥ x) - V x₀‖ ≤ δ := by
          refine h3.trans ?_
          rw [hδ]
          have : (d : ℝ) * supNorm ((b +ᵥ x) - x₀) ≤ d * (4 * R) := by
            refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
            linarith
          calc (d : ℝ) * supNorm ((b +ᵥ x) - x₀) * (γ₁ * h₁⁻¹) ≤ d * (4 * R) * (γ₁ * h₁⁻¹) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = 4 * d * R * γ₁ / h₁ := by ring
        calc |D1 (fun b y => b +ᵥ y) b χ x| * ‖V (b +ᵥ x) - V x₀‖
            ≤ cutK d / R ^ Grassmann.mabs b * δ :=
              mul_le_mul hD h4 (norm_nonneg _) (by positivity)
          _ = cutK d * δ * (R ^ Grassmann.mabs b)⁻¹ := by ring
    · have hc : a - b ≠ 0 := by
        intro h0; apply hba
        funext e; have := congrFun h0 e; have := hb e; simp at *; omega
      rw [gvec_dprof_sub_const V (V x₀) hc]
      have hcP : Grassmann.mabs (a - b) ≤ P := (mabs_le_of_le tsub_le_self).trans ha
      have hc1 : 1 ≤ Grassmann.mabs (a - b) := by
        by_contra h0; push Not at h0
        apply hc; funext e
        have := Finset.sum_eq_zero_iff.1 (Nat.lt_one_iff.1 h0) e (mem_univ e)
        simpa using this
      have hsum : Grassmann.mabs a = Grassmann.mabs b + Grassmann.mabs (a - b) := by
        unfold Grassmann.mabs; rw [← sum_add_distrib]
        refine sum_congr rfl fun e _ => ?_
        simp only [Pi.sub_apply]; exact (Nat.add_sub_cancel' (hb e)).symm
      have h1 := hV (a - b) hcP (b +ᵥ x)
      have h2 := inv_pow_le_of_le hR0 hRh hc1
      have h3 : γ₁ * (h₁ ^ Grassmann.mabs (a - b))⁻¹ ≤ δ * (R ^ Grassmann.mabs (a - b))⁻¹ := by
        calc γ₁ * (h₁ ^ Grassmann.mabs (a - b))⁻¹ ≤ γ₁ * (R / h₁ * (R ^ Grassmann.mabs (a - b))⁻¹) :=
              mul_le_mul_of_nonneg_left h2 hγ₁
          _ ≤ δ * (R ^ Grassmann.mabs (a - b))⁻¹ := by
              rw [hδ]
              have : γ₁ * (R / h₁) ≤ 4 * d * R * γ₁ / h₁ := by
                rw [mul_div_assoc', div_le_div_iff_of_pos_right hh₁]
                nlinarith [mul_nonneg hγ₁ hR0.le]
              calc γ₁ * (R / h₁ * (R ^ Grassmann.mabs (a - b))⁻¹)
                  = γ₁ * (R / h₁) * (R ^ Grassmann.mabs (a - b))⁻¹ := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
      calc |D1 (fun b y => b +ᵥ y) b χ x| * ‖gvec V (dprof (a - b) (b +ᵥ x))‖
          ≤ cutK d / R ^ Grassmann.mabs b * (δ * (R ^ Grassmann.mabs (a - b))⁻¹) :=
            mul_le_mul hD (h1.trans h3) (norm_nonneg _) (by positivity)
        _ = cutK d * δ * (R ^ Grassmann.mabs a)⁻¹ := by
            rw [hsum, pow_add]; field_simp
  -- the second component
  have hcomp2 : ∀ (V : Lam d L N → H), (∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N,
      ‖gvec V (dprof a x)‖ ≤ γ₁ * (h₁ ^ Grassmann.mabs a)⁻¹) →
      ∀ a : Dir d → ℕ, Grassmann.mabs a ≤ P → ∀ x : Lam d L N,
      ‖gvec (fun y => (χ y : ℂ) • V x₀) (dprof a x)‖ ≤ cutK d * γ₁ * (R ^ Grassmann.mabs a)⁻¹ := by
    intro V hV a ha x
    rw [gvec_dprof_const_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have := (D1_chiT_le (L := L) (N := N) hR1 hS hN ha x₀ x).1
    calc |D1 (fun b y => b +ᵥ y) a χ x| * ‖V x₀‖ ≤ cutK d / R ^ Grassmann.mabs a * γ₁ :=
          mul_le_mul this (hzero V hV) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- the vectors
  refine ⟨fun x => WithLp.toLp 2 ((μ⁻¹ : ℂ) • ((χ x : ℂ) • (Fv x - Fv x₀)),
      (μ : ℂ) • ((χ x : ℂ) • Fv x₀)),
    fun y => WithLp.toLp 2 ((μ : ℂ) • Gv y, (μ⁻¹ : ℂ) • ((χ y : ℂ) • (Gv y - Gv x₀))), ?_, ?_⟩
  · refine gramBound_pair fun a ha x => ?_
    have hRa : (R ^ Grassmann.mabs a)⁻¹ ≤ (h ^ Grassmann.mabs a)⁻¹ :=
      inv_anti₀ (pow_pos hh _) (pow_le_pow_left₀ hh.le hhR _)
    have hKa : 2 ^ P * cutK d ≤ locK d := by
      unfold locK; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hKb : cutK d ≤ locK d := by
      have : cutK d ≤ 2 ^ P * cutK d := le_mul_of_one_le_left hK0 (one_le_pow₀ (by norm_num))
      linarith
    have hKc : (1 : ℝ) ≤ locK d := one_le_locK d
    have hX : 0 ≤ (R ^ Grassmann.mabs a)⁻¹ := by positivity
    have hn1 : ∀ (c : ℝ) (v : H), ‖((c : ℝ) : ℂ) • v‖ = |c| * ‖v‖ := fun c v => by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hμi : (0 : ℝ) < μ⁻¹ := inv_pos.2 hμ
    have eμ : ((μ⁻¹ : ℂ)) = ((μ⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    refine ⟨?_, ?_⟩
    · rw [gvec_fun_smul, gvec_fun_smul, eμ, hn1, hn1, abs_of_pos hμi, abs_of_pos hμ]
      exact real_comb hμ ((hcomp1 Fv hBF a ha x).trans_eq (by ring)) (hcomp2 Fv hBF a ha x) hKa hKb
        hRa hδ0 hγ₁ hX (by linarith) |>.trans_eq (by rw [hδ])
    · rw [gvec_fun_smul, gvec_fun_smul, eμ, hn1, hn1, abs_of_pos hμi, abs_of_pos hμ, add_comm]
      have h2 : ‖gvec Gv (dprof a x)‖ ≤ 1 * γ₁ * (R ^ Grassmann.mabs a)⁻¹ := by
        rw [one_mul]
        refine (hBG a ha x).trans (mul_le_mul_of_nonneg_left ?_ hγ₁)
        exact inv_anti₀ (pow_pos hR0 _) (pow_le_pow_left₀ hR0.le hRh _)
      exact real_comb hμ ((hcomp1 Gv hBG a ha x).trans_eq (by ring)) h2 hKa hKc hRa hδ0 hγ₁ hX
        (by linarith) |>.trans_eq (by rw [hδ])
  · intro x y hx hy
    have hχx : χ x = 1 := chiT_eq_one hR0 hx
    have hχy : χ y = 1 := chiT_eq_one hR0 hy
    rw [WithLp.prod_inner_apply]
    dsimp only
    rw [hχx, hχy]
    simp only [Complex.ofReal_one, one_smul, inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right]
    rw [← hC, ← hC, ← hC]
    have c1 : (starRingEnd ℂ) ((μ : ℂ)⁻¹) = (μ : ℂ)⁻¹ := by rw [map_inv₀, Complex.conj_ofReal]
    have c2 : (starRingEnd ℂ) (μ : ℂ) = (μ : ℂ) := Complex.conj_ofReal μ
    have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
    rw [c1, c2]
    field_simp
    ring

end GramLoc


/-! ### Sums of Gram representations -/

section GramSum

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ] {p : ℕ}

theorem gvec_zero_fun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : Λ → ℝ) :
    gvec (fun _ : Λ => (0 : H)) f = 0 := by simp [gvec]

/-- **Sums of Gram representations**: the Gram constants add in squares. -/
theorem gram_finsum {ι : Type*} [DecidableEq ι] (s : Finset ι) (M : ι → Matrix Λ Λ ℂ)
    (γ : ι → ℝ) (hγ : ∀ i, 0 ≤ γ i) {h : ℝ} (hh : 0 < h)
    (hrep : ∀ i ∈ s, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (F G : Λ → H), IsGram (M i) F G ∧ GramBound E p h (γ i) F G) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (F G : Λ → H),
      IsGram (∑ i ∈ s, M i) F G ∧ GramBound E p h (Real.sqrt (∑ i ∈ s, γ i ^ 2)) F G := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 0, fun _ => 0, ?_, ?_⟩
    · intro x y; simp
    · intro a ha x; simp [gvec_zero_fun]
  | insert i s hi ih =>
    obtain ⟨H₁, n₁, i₁, F₁, G₁, hG₁, hB₁⟩ := hrep i (mem_insert_self i s)
    obtain ⟨H₂, n₂, i₂, F₂, G₂, hG₂, hB₂⟩ := ih fun k hk => hrep k (mem_insert_of_mem hk)
    refine ⟨WithLp 2 (H₁ × H₂), inferInstance, inferInstance,
      fun x => WithLp.toLp 2 (F₁ x, F₂ x), fun y => WithLp.toLp 2 (G₁ y, G₂ y), ?_, ?_⟩
    · intro x y
      rw [sum_insert hi, Matrix.add_apply, hG₁, hG₂, WithLp.prod_inner_apply]
    · intro a ha x
      have hS : 0 ≤ ∑ k ∈ s, γ k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
      set X := (h ^ Grassmann.mabs a)⁻¹
      have key : ∀ (u : H₁) (v : H₂), ‖u‖ ≤ γ i * X → ‖v‖ ≤ Real.sqrt (∑ k ∈ s, γ k ^ 2) * X →
          ‖WithLp.toLp 2 (u, v)‖ ≤ Real.sqrt (∑ k ∈ insert i s, γ k ^ 2) * X := by
        intro u v hu hv
        have hX : 0 ≤ X := by positivity
        have hn : ‖WithLp.toLp 2 (u, v)‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
          WithLp.prod_norm_sq_eq_of_L2 _
        have hsq : (Real.sqrt (∑ k ∈ insert i s, γ k ^ 2) * X) ^ 2 =
            (γ i * X) ^ 2 + (Real.sqrt (∑ k ∈ s, γ k ^ 2) * X) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (sum_nonneg fun k _ => sq_nonneg _),
            Real.sq_sqrt hS, sum_insert hi]
          ring
        have h1 : ‖u‖ ^ 2 ≤ (γ i * X) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
        have h2 : ‖v‖ ^ 2 ≤ (Real.sqrt (∑ k ∈ s, γ k ^ 2) * X) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hv 2
        have h3 : ‖WithLp.toLp 2 (u, v)‖ ^ 2 ≤ (Real.sqrt (∑ k ∈ insert i s, γ k ^ 2) * X) ^ 2 := by
          rw [hn, hsq]; linarith
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
      constructor
      · have e := gvec_prod F₁ F₂ (dprof a x)
        have : gvec (fun x => WithLp.toLp 2 (F₁ x, F₂ x)) (dprof a x) =
            WithLp.toLp 2 (gvec F₁ (dprof a x), gvec F₂ (dprof a x)) := by
          rw [← e]
        rw [this]
        exact key _ _ (hB₁ a ha x).1 (hB₂ a ha x).1
      · have e := gvec_prod G₁ G₂ (dprof a x)
        have : gvec (fun x => WithLp.toLp 2 (G₁ x, G₂ x)) (dprof a x) =
            WithLp.toLp 2 (gvec G₁ (dprof a x), gvec G₂ (dprof a x)) := by
          rw [← e]
        rw [this]
        exact key _ _ (hB₁ a ha x).2 (hB₂ a ha x).2

end GramSum

end

end Obs2
