import Grassmann.Gram

/-!
# The torus `Λ_N`, the norms `T_j(ℓ)`, and their consequences

* `Torus d n` is the discrete torus `(ℤ/nℤ)^d`; `Λ_N = Torus d (L^N)`.
* `Dir d` indexes `𝓔_d = {e_1, …, e_d, e_{d+1} = -e_1, …, e_{2d} = -e_d}`; a multi-index
  `α ∈ ℕ_0^{𝓔_d}` acts on the torus by `α +ᵥ x = x + ∑_e α(e) e`.
* `Phij`, `Tj` are the norms `Φ_j(ℓ)`, `T_j(ℓ)` of `def:Phi`, `def:Tphi`, with `p_Φ = 2d` and
  spatial scale `L^j`; the same `Tj` on `N (Torus d n ⊕ Torus d n)` is `T_j(ℓ ⊔ ℓ)`.
* `ellj` is `ℓ_j = ℓ_0 L^{-(d-2)j/2}` (`e:ellj`).
* `EC_theta_mul_of_finiteRange` is the factorisation for finite range covariances;
  `covNorm_le_one` is `e:Cleq1` (from the bounds `e:C-bd` and a large `ℓ_0`); and
  `Tj_succ_le`, `Tj_EC_theta_le` are `e:normcontract`.
-/

namespace Grassmann

noncomputable section

open Finset

/-- The discrete torus `(ℤ/nℤ)^d`. -/
def Torus (d n : ℕ) : Type := Fin d → ZMod n

namespace Torus

variable {d n : ℕ}

instance : AddCommGroup (Torus d n) := inferInstanceAs (AddCommGroup (Fin d → ZMod n))
instance : DecidableEq (Torus d n) := inferInstanceAs (DecidableEq (Fin d → ZMod n))
instance [NeZero n] : Fintype (Torus d n) := inferInstanceAs (Fintype (Fin d → ZMod n))

end Torus

/-- The index set of `𝓔_d`: `Sum.inl i ↦ e_i`, `Sum.inr i ↦ -e_i`. -/
abbrev Dir (d : ℕ) := Fin d ⊕ Fin d

variable {d n : ℕ}

/-- The unit vectors `e ∈ 𝓔_d`. -/
def dirVec : Dir d → Torus d n
  | Sum.inl i => (Pi.single i 1 : Fin d → ZMod n)
  | Sum.inr i => -(Pi.single i 1 : Fin d → ZMod n)

/-- `-e` for `e ∈ 𝓔_d` is the unit vector of the swapped direction. -/
theorem dirVec_swap (e : Dir d) : (dirVec e.swap : Torus d n) = -dirVec e := by
  rcases e with i | i
  · rfl
  · exact (neg_neg _).symm

/-- `α ↦ ∑_e α(e) e`. -/
def dirHom : (Dir d → ℕ) →+ Torus d n where
  toFun α := ∑ e, α e • dirVec e
  map_zero' := by simp
  map_add' α β := by simp [add_smul, sum_add_distrib]

/-- Translation by multi-indices: `α +ᵥ x = x + ∑_e α(e) e`. -/
instance : AddAction (Dir d → ℕ) (Torus d n) :=
  AddAction.compHom (Torus d n) (dirHom (d := d) (n := n))

theorem vadd_def (α : Dir d → ℕ) (x : Torus d n) : α +ᵥ x = (∑ e, α e • dirVec e) + x := rfl

theorem single_vadd (e : Dir d) (x : Torus d n) :
    (Pi.single e 1 : Dir d → ℕ) +ᵥ x = x + dirVec e := by
  rw [vadd_def, add_comm]
  congr 1
  rw [sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-! ### The covariance norm in terms of derivatives of `C` -/

section CovGeneral

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) Λ]

theorem psibar_mul_psi_eq (x y : Λ) : psibar x * psi y = psiPow ![(x, -1), (y, 1)] := by
  simp [psiPow, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, psibar,
    psi, ψ, Matrix.vecTail]

theorem covTest_of_ne (C : Matrix Λ Λ ℝ) {m : ℕ} (hm : m ≠ 2) (z : Fin m → Sf Λ) :
    covTest C m z = 0 := by
  simp only [covTest, covForm, coeff_sum, coeff_smul, psibar_mul_psi_eq, psiPow,
    coeff_ιMulti_of_ne _ _ hm, mul_zero, sum_const_zero]

theorem D_psi_one_psibar_mul_psi (x y u : Λ) :
    D (u, 1) (psibar x * psi y) = if u = y then -psibar x else 0 := by
  rw [D_mul, psibar, psi, D_ψ, D_ψ, if_neg (by simp [Prod.ext_iff]), zero_mul, zero_add, inv'_ψ]
  by_cases h : u = y
  · subst h; simp
  · rw [if_neg (by simp [Prod.ext_iff, h]), if_neg h, mul_zero]

theorem covTest_two (C : Matrix Λ Λ ℝ) (u v : Λ) (σ τ : ℤˣ) :
    covTest C 2 ![(u, σ), (v, τ)] =
      (if σ = -1 ∧ τ = 1 then (C u v : ℂ) else 0) -
        (if σ = 1 ∧ τ = -1 then (C v u : ℂ) else 0) := by
  rcases Int.units_eq_one_or σ with rfl | rfl <;> rcases Int.units_eq_one_or τ with rfl | rfl
  · rw [covTest, coeff_two, covForm]
    simp only [map_sum, map_smul, D_psi_one_psibar_mul_psi, apply_ite (D _), map_zero, map_neg,
      smul_ite, smul_zero]
    simp [psibar, D_ψ, Prod.ext_iff]
  · rw [covTest, coeff_two, covForm]
    simp only [map_sum, map_smul, D_psi_one_psibar_mul_psi, apply_ite (D _), map_zero, map_neg,
      smul_ite, smul_zero]
    simp [psibar, D_ψ, Prod.ext_iff, apply_ite ε, Finset.sum_ite_eq, AlgHom.map_smul_of_tower,
      Complex.real_smul]
  · rw [covTest, coeff_covForm]; simp
  · rw [covTest, coeff_two, covForm]
    simp only [map_sum, map_smul, D_psibar_mul_psi, apply_ite (D _), map_zero, smul_ite,
      smul_zero]
    simp [psi, D_ψ, Prod.ext_iff]

/-- `∇^{α_1}_x ∇^{α_2}_y C(x, y)`. -/
def nabC (C : Matrix Λ Λ ℝ) (α₁ α₂ : E → ℕ) (x y : Λ) : ℝ :=
  nabla (fun b x => b +ᵥ x) ![α₁, α₂] (fun z : Fin 2 → Λ => C (z 0) (z 1)) ![x, y]

theorem nab_covTest (C : Matrix Λ Λ ℝ) (α : Fin 2 → E → ℕ) (u v : Λ) (σ τ : ℤˣ) :
    nab α (covTest C 2) ![(u, σ), (v, τ)] =
      (if σ = -1 ∧ τ = 1 then (nabC C (α 0) (α 1) u v : ℂ) else 0) -
        (if σ = 1 ∧ τ = -1 then (nabC C (α 1) (α 0) v u : ℂ) else 0) := by
  let φ : Fin 2 → Λ → Sf Λ := ![fun x => (x, σ), fun x => (x, τ)]
  have hφ : ∀ i (b : E → ℕ) (x : Λ), φ i (b +ᵥ x) = sh b (φ i x) := by
    intro i b x; fin_cases i <;> rfl
  have hz : ![(u, σ), (v, τ)] = fun i => φ i ((![u, v] : Fin 2 → Λ) i) := by
    funext i; fin_cases i <;> rfl
  rw [hz, ← nabla_comp_pi (fun b x => b +ᵥ x) sh φ hφ]
  have hfun : (fun z : Fin 2 → Λ => covTest C 2 fun i => φ i (z i)) =
      fun z => (if σ = -1 ∧ τ = 1 then (C (z 0) (z 1) : ℂ) else 0) -
        (if σ = 1 ∧ τ = -1 then (C (z 1) (z 0) : ℂ) else 0) := by
    funext z
    rw [show (fun i => φ i (z i)) = ![(z 0, σ), (z 1, τ)] by funext i; fin_cases i <;> rfl,
      covTest_two]
  rw [hfun]
  have hswap : nabla (fun b x => b +ᵥ x) α (fun z : Fin 2 → Λ => C (z 1) (z 0)) ![u, v] =
      nabC C (α 1) (α 0) v u := by
    have := nabla_reindex (fun b (x : Λ) => b +ᵥ x) (Equiv.swap (0 : Fin 2) 1)
      ![α 1, α 0] (fun z : Fin 2 → Λ => C (z 0) (z 1)) ![v, u]
    rw [nabC, ← this]
    congr 1
  have hα : α = ![α 0, α 1] := by funext i; fin_cases i <;> rfl
  by_cases h1 : σ = -1 ∧ τ = 1
  · have h2 : ¬(σ = 1 ∧ τ = -1) := fun h2 => absurd (h1.1.symm.trans h2.1) (by decide)
    simp only [if_pos h1, if_neg h2, sub_zero]
    rw [nabla_ofReal, nabC, ← hα]
  · by_cases h2 : σ = 1 ∧ τ = -1
    · simp only [if_neg h1, if_pos h2, zero_sub]
      rw [← hswap, show (fun z : Fin 2 → Λ => -(C (z 1) (z 0) : ℂ)) =
        -(fun z => (C (z 1) (z 0) : ℂ)) from rfl, map_neg, Pi.neg_apply, nabla_ofReal]
    · simp only [if_neg h1, if_neg h2, sub_zero]
      rw [show (fun _ : Fin 2 → Λ => (0 : ℂ)) = 0 from rfl, map_zero, Pi.zero_apply]

variable {p : ℕ} {h ℓ : ℝ}

/-- `‖C‖_{Φ(ℓ)} ≤ M` follows from the bounds
`ℓ^{-2} h^{|α_1| + |α_2|} |∇^{α_1}_x ∇^{α_2}_y C(x,y)| ≤ M` for `|α_i| ≤ p`. -/
theorem covNorm_le (C : Matrix Λ Λ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ α₁ α₂ : E → ℕ, mabs α₁ ≤ p → mabs α₂ ≤ p → ∀ x y,
      ℓ⁻¹ ^ 2 * h ^ (mabs α₁ + mabs α₂) * |nabC C α₁ α₂ x y| ≤ M) :
    covNorm E p h ℓ C ≤ ENNReal.ofReal M := by
  refine phiNorm_le fun m z α hα => ?_
  by_cases hm : m = 2
  · subst hm
    have hz : z = ![((z 0).1, (z 0).2), ((z 1).1, (z 1).2)] := by
      funext i; fin_cases i <;> rfl
    have hord : ord α = mabs (α 0) + mabs (α 1) := by simp [ord, Fin.sum_univ_two]
    unfold phiTerm
    rw [hz, nab_covTest, hord]
    split_ifs with h1 h2 h2
    · exact absurd (h1.1.symm.trans h2.1) (by decide)
    · rw [sub_zero, Complex.norm_real, Real.norm_eq_abs]; exact hb _ _ (hα 0) (hα 1) _ _
    · rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, add_comm]
      exact hb _ _ (hα 1) (hα 0) _ _
    · simpa using hM
  · have : covTest C m = fun _ => 0 := funext (covTest_of_ne C hm)
    unfold phiTerm
    rw [this, show (fun _ : Fin m → Sf Λ => (0 : ℂ)) = 0 from rfl, map_zero]
    simpa using hM

end CovGeneral

/-! ### The norms `Φ_j(ℓ)` and `T_j(ℓ)` -/

/-- `p_Φ = 2d`. -/
abbrev pPhi (d : ℕ) : ℕ := 2 * d

variable [NeZero n]

/-- `‖g‖_{Φ_j(ℓ)}` on `Λ = Torus d n` (`def:Phi`). -/
abbrev Phij (L : ℝ) (j : ℕ) (ℓ : ℝ) (g : TestFn (Torus d n)) : ENNReal :=
  phiNorm (Dir d) (pPhi d) (L ^ j) ℓ g

/-- `‖F‖_{T_j(ℓ)}` (`def:Tphi`), for `X = Λ` and, with `X = Λ ⊕ Λ`, `‖F‖_{T_j(ℓ ⊔ ℓ)}`. -/
abbrev Tj (d : ℕ) {X : Type*} [DecidableEq X] [Fintype X] [AddAction (Dir d → ℕ) X]
    (L : ℝ) (j : ℕ) (ℓ : ℝ) (F : N X) : ENNReal :=
  tNorm (Dir d) (pPhi d) (L ^ j) ℓ F

/-- `‖C‖_{Φ_j(ℓ)}` for a covariance on `Λ`. -/
abbrev covNormj (L : ℝ) (j : ℕ) (ℓ : ℝ) (C : Matrix (Torus d n) (Torus d n) ℝ) : ENNReal :=
  covNorm (Dir d) (pPhi d) (L ^ j) ℓ C

/-- `ℓ_j = ℓ_0 L^{-(d-2) j / 2}` (`e:ellj`). -/
def ellj (d : ℕ) (L ℓ₀ : ℝ) (j : ℕ) : ℝ := ℓ₀ * L ^ (-((d : ℝ) - 2) * j / 2)

theorem ellj_pos {L ℓ₀ : ℝ} (hL : 0 < L) (hℓ₀ : 0 < ℓ₀) (j : ℕ) : 0 < ellj d L ℓ₀ j := by
  unfold ellj; positivity

theorem ellj_succ {L ℓ₀ : ℝ} (hL : 0 < L) (j : ℕ) :
    ellj d L ℓ₀ (j + 1) = ellj d L ℓ₀ j * L ^ (-((d : ℝ) - 2) / 2) := by
  unfold ellj
  rw [mul_assoc, ← Real.rpow_add hL]
  congr 2
  push_cast; ring

/-- For `d ≥ 3` and `L ≥ 4`, `2 ℓ_{j+1} ≤ ℓ_j`. -/
theorem two_ellj_succ_le (hd : 3 ≤ d) {L ℓ₀ : ℝ} (hL : 4 ≤ L) (hℓ₀ : 0 < ℓ₀) (j : ℕ) :
    2 * ellj d L ℓ₀ (j + 1) ≤ ellj d L ℓ₀ j := by
  have hL0 : 0 < L := by linarith
  rw [ellj_succ hL0, mul_comm, mul_assoc]
  refine mul_le_of_le_one_right (ellj_pos hL0 hℓ₀ j).le ?_
  have hd' : (1 : ℝ) / 2 ≤ ((d : ℝ) - 2) / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : L ^ (-((d : ℝ) - 2) / 2) ≤ L ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : L ^ (-(1 : ℝ) / 2) ≤ 1 / 2 := by
    rw [neg_div, Real.rpow_neg hL0.le, ← Real.sqrt_eq_rpow, one_div]
    refine inv_anti₀ (by norm_num) ?_
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hL
  nlinarith [Real.rpow_nonneg hL0.le (-((d : ℝ) - 2) / 2)]

/-- `e:normcontract` (first part): `‖F‖_{T_{j+1}(ℓ_{j+1})} ≤ ‖F‖_{T_{j+1}(2ℓ_{j+1})} ≤
‖F‖_{T_j(ℓ_j)}`. -/
theorem Tj_succ_le (hd : 3 ≤ d) {L ℓ₀ : ℝ} (hL : 4 ≤ L) (hℓ₀ : 0 < ℓ₀) (j : ℕ)
    (F : N (Torus d n)) :
    Tj d L (j + 1) (ellj d L ℓ₀ (j + 1)) F ≤ Tj d L (j + 1) (2 * ellj d L ℓ₀ (j + 1)) F ∧
      Tj d L (j + 1) (2 * ellj d L ℓ₀ (j + 1)) F ≤ Tj d L j (ellj d L ℓ₀ j) F := by
  have hL0 : 0 < L := by linarith
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  constructor
  · exact tNorm_mono (by positivity) le_rfl hℓ (by linarith) F
  · refine tNorm_mono (by positivity) ?_ (by positivity) (two_ellj_succ_le hd hL hℓ₀ j) F
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by linarith)

/-- `e:normcontract` (second part): `‖𝔼_{C_{j+1}} θ F‖_{T_{j+1}(ℓ_{j+1})} ≤ ‖F‖_{T_j(ℓ_j)}`
for a positive semidefinite `C_{j+1}` with `‖C_{j+1}‖_{Φ_{j+1}(ℓ_{j+1})} ≤ 1` (`e:Cleq1`). -/
theorem Tj_EC_theta_le (hd : 3 ≤ d) {L ℓ₀ : ℝ} (hL : 4 ≤ L) (hℓ₀ : 0 < ℓ₀) (j : ℕ)
    {C : Matrix (Torus d n) (Torus d n) ℝ} (hC : C.PosSemidef)
    (hCn : covNormj L (j + 1) (ellj d L ℓ₀ (j + 1)) C ≤ 1) (F : N (Torus d n)) :
    Tj d L (j + 1) (ellj d L ℓ₀ (j + 1)) (EC C (theta F)) ≤ Tj d L j (ellj d L ℓ₀ j) F := by
  have hL0 : 0 < L := by linarith
  exact (tNorm_EC_theta_le (by positivity) (ellj_pos hL0 hℓ₀ _) hC hCn F).trans
    (Tj_succ_le hd hL hℓ₀ j F).2

/-! ### Finite range factorisation -/

/-- `|z|` for `z ∈ ℤ/nℤ`, the distance to `0`. -/
def zabs (z : ZMod n) : ℕ := min z.val (n - z.val)

/-- `|x|_∞` on the torus. -/
def supNorm (x : Torus d n) : ℕ := Finset.univ.sup fun i => zabs ((x : Fin d → ZMod n) i)

theorem zabs_neg (z : ZMod n) : zabs (-z) = zabs z := by
  unfold zabs
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · have := ZMod.val_lt z
    rw [Nat.sub_sub_self this.le, min_comm]

theorem supNorm_neg (x : Torus d n) : supNorm (-x) = supNorm x := by
  unfold supNorm
  congr 1; funext i
  exact zabs_neg _

theorem supNorm_zero : supNorm (0 : Torus d n) = 0 := by
  unfold supNorm
  refine le_antisymm (Finset.sup_le fun i _ => ?_) (Nat.zero_le _)
  show zabs (0 : ZMod n) ≤ 0
  simp [zabs]

/-- The consequence of the finite range property `e:C-range`: if `C(x,y) = 0` whenever
`|x - y|_∞ ≥ R` and `dist_∞(X_1, X_2) > R`, then for `F_i ∈ 𝒩(X_i)`,
`𝔼_C θ (F_1 F_2) = (𝔼_C θ F_1)(𝔼_C θ F_2)`.  (For `C_j`, `R = L^j / 2`.) -/
theorem EC_theta_mul_of_finiteRange (C : Matrix (Torus d n) (Torus d n) ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hC : ∀ x y, R ≤ supNorm (x - y) → C x y = 0) {X₁ X₂ : Set (Torus d n)}
    (hX : ∀ x ∈ X₁, ∀ y ∈ X₂, R < supNorm (x - y)) {F₁ F₂ : N (Torus d n)} (hF₁ : F₁ ∈ NX X₁)
    (hF₂ : F₂ ∈ NX X₂) :
    EC C (theta (F₁ * F₂)) = EC C (theta F₁) * EC C (theta F₂) := by
  refine EC_theta_mul_of_disjoint C ?_ (fun x hx y hy => ⟨hC x y (hX x hx y hy).le, ?_⟩) hF₁ hF₂
  · refine Set.disjoint_left.2 fun x hx₁ hx₂ => ?_
    have := hX x hx₁ x hx₂
    rw [sub_self, supNorm_zero] at this
    push_cast at this
    linarith
  · refine hC y x ?_
    rw [← neg_sub, supNorm_neg]
    exact (hX x hx y hy).le

/-! ### `e:Cleq1` -/

/-- `e:Cleq1`: the scaling estimates `e:C-bd`
`|∇^{α_1}_x ∇^{α_2}_y C_{j+1}(x,y)| ≤ K L^{-(d-2+|α_1|+|α_2|) j}` (`|α_i| ≤ p_Φ`) imply
`‖C_{j+1}‖_{Φ_{j+1}(ℓ_{j+1})} ≤ 1` once `ℓ_0^2 ≥ K L^{d-2+2p_Φ}`. -/
theorem covNormj_le_one {L ℓ₀ K : ℝ} (hL : 1 ≤ L) (hℓ₀ : 0 < ℓ₀) (hK : 0 ≤ K) (j : ℕ)
    {C : Matrix (Torus d n) (Torus d n) ℝ}
    (hbd : ∀ α₁ α₂ : Dir d → ℕ, mabs α₁ ≤ pPhi d → mabs α₂ ≤ pPhi d → ∀ x y,
      |nabC C α₁ α₂ x y| ≤ K * L ^ (-(((d : ℝ) - 2 + mabs α₁ + mabs α₂) * j)))
    (hℓ₀K : K * L ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2) :
    covNormj L (j + 1) (ellj d L ℓ₀ (j + 1)) C ≤ 1 := by
  have hL0 : 0 < L := by linarith
  refine (covNorm_le C zero_le_one fun α₁ α₂ h₁ h₂ x y => ?_).trans_eq ENNReal.ofReal_one
  set D : ℝ := (d : ℝ) - 2
  set A : ℕ := mabs α₁ + mabs α₂
  have e0 : ((L ^ (-D * ((j + 1 : ℕ) : ℝ) / 2))⁻¹) ^ 2 = L ^ (D * (j + 1 : ℕ)) := by
    rw [← Real.rpow_neg hL0.le, ← Real.rpow_mul_natCast hL0.le]
    congr 1; push_cast; ring
  have e1 : (ellj d L ℓ₀ (j + 1))⁻¹ ^ 2 = (ℓ₀ ^ 2)⁻¹ * L ^ (D * (j + 1 : ℕ)) := by
    unfold ellj
    rw [mul_inv, mul_pow, e0, inv_pow]
  have e2 : (L ^ (j + 1)) ^ A = L ^ (((j + 1) * A : ℕ) : ℝ) := by
    rw [← pow_mul, Real.rpow_natCast]
  have hA : (A : ℝ) ≤ 2 * pPhi d := by
    have : A ≤ 2 * pPhi d := by omega
    exact_mod_cast this
  rw [e1, e2]
  calc (ℓ₀ ^ 2)⁻¹ * L ^ (D * (j + 1 : ℕ)) * L ^ (((j + 1) * A : ℕ) : ℝ) * |nabC C α₁ α₂ x y|
      ≤ (ℓ₀ ^ 2)⁻¹ * L ^ (D * (j + 1 : ℕ)) * L ^ (((j + 1) * A : ℕ) : ℝ) *
          (K * L ^ (-((D + A) * j))) := by
        gcongr
        have := hbd α₁ α₂ h₁ h₂ x y
        convert this using 3
        push_cast [A]; ring
    _ = (ℓ₀ ^ 2)⁻¹ * K * (L ^ (D * (j + 1 : ℕ)) * L ^ (((j + 1) * A : ℕ) : ℝ) *
          L ^ (-((D + A) * j))) := by ring
    _ = (ℓ₀ ^ 2)⁻¹ * K * L ^ (D + A) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
        congr 2; push_cast; ring
    _ ≤ (ℓ₀ ^ 2)⁻¹ * K * L ^ (D + 2 * pPhi d) := by
        gcongr
    _ ≤ (ℓ₀ ^ 2)⁻¹ * ℓ₀ ^ 2 := by
        rw [mul_assoc]; gcongr
    _ = 1 := inv_mul_cancel₀ (by positivity)

end

end Grassmann
