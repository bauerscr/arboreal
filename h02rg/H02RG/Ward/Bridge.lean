import Ward.Defs
import H02.Ward
import Grassmann.Berezin
import Psi4.SumParts
import Obs.Corr
import Suscept.Cov
import FRD.Det

/-!
# The bridge between the `ℍ^{0|2}` model and the `ψ`-model (gap B)

Conventions (checked against `H02.action`, `H02.int0`, `Grassmann.EC_eq_berezin`,
`Suscept.Cov`, `Step.VE`, `Psi4.SumParts`):

* `phiC c : Ω^{2Λ} → 𝒩(Λ)` is the `ℝ`-algebra map `ξ_x ↦ c ψ̄_x`, `η_x ↦ c ψ_x`
  (`e:xietapsi` with `c = √((1+s₀)/β)`).  Then `ξ_x η_y ↦ c² ψ̄_x ψ_y = -c² ψ_y ψ̄_x`.
* `c ∂_{ξ_x} ↔ ∂_{ψ̄_x} = D (x,-1)` and `c ∂_{η_x} ↔ ∂_{ψ_x} = D (x,1)` (`phiC_dξ`, `phiC_dη`);
  hence `∏_x ∂_{η_x}∂_{ξ_x}` (`∂_ξ` first) corresponds to `c^{-2|Λ|} ∏_x ∂_{ψ_x}∂_{ψ̄_x}`
  (`∂_ψ̄` first), which is the order of `Grassmann.berezinζ`: no extra sign.
* `[F]_0 = [∏_x (1 + ξ_xη_x) F]` with pure derivatives (`berezin_eq_berR`);
  `∏_x (1 + ξ_xη_x) ↦ exp(-c² ∑_x ψ_xψ̄_x)`.
* `phiC_exponent`: with `β_{xy} = nnW β`, constant field `h`,
  `phiC (∑_x ξ_xη_x - H_{β,h}) = -(ψ, (-Δ + m²) ψ̄) - V(Λ)` with
  `V = (z, y, a, b) = (0, βc² - 1, (1+h)c² - m², βc⁴)`.  For `c² = (1+s₀)/β` this is
  `Vh β h m² s₀ = (0, s₀, (1+s₀)(1+h)/β - m², (1+s₀)²/β)` — exactly `e:quartic-rescale`
  (`a₀ = (1+s₀)(1+h)/β - m²`, `b₀ = (1+s₀)²/β`, `s₀` in the `y` slot, `z = 0`).
* `omega_eq_berN`: `⟨G⟩_C = det C · ε(∏_x ∂_{ψ_x}∂_{ψ̄_x} e^{-(ψ, C⁻¹ψ̄)} G)`.
* **`bridge_expect`**: `[F]_{β,h} = (β/(1+s₀))^{|Λ|} det(-Δ+m²) ⟨e^{-V(Λ)} φ(F)⟩_C`;
  **`bridge_Z`** (`e:ZbetahuNN`), **`bridge_avg`** (no `Z ≠ 0` hypothesis needed).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step

section General

variable {Λ : Type*} [DecidableEq Λ]

/-- `ξ_x ↦ c ψ̄_x`, `η_x ↦ c ψ_x` on the generators. -/
def vC (c : ℝ) : H02.Gen Λ →ₗ[ℝ] Grassmann.V Λ where
  toFun v a := (c : ℂ) * ((if a.2 = 1 then v (Sum.inr a.1) else v (Sum.inl a.1) : ℝ) : ℂ)
  map_add' v w := by funext a; simp only [Pi.add_apply]; split_ifs <;> push_cast <;> ring
  map_smul' r v := by
    funext a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul]
    split_ifs <;> push_cast <;> ring

/-- The generator map into `𝒩(Λ)`. -/
def fC (c : ℝ) : H02.Gen Λ →ₗ[ℝ] N Λ where
  toFun v := ExteriorAlgebra.ι ℂ (vC c v)
  map_add' v w := by simp
  map_smul' r v := by rw [map_smul, RingHom.id_apply, LinearMap.map_smul_of_tower]

/-- The algebra map `φ_c : Ω^{2Λ} → 𝒩(Λ)`, `ξ_x ↦ c ψ̄_x`, `η_x ↦ c ψ_x`. -/
def phiC (c : ℝ) : H02.Grassmann Λ →ₐ[ℝ] N Λ :=
  ExteriorAlgebra.lift ℝ ⟨fC c, fun v => ExteriorAlgebra.ι_sq_zero _⟩

theorem phiC_ι (c : ℝ) (v : H02.Gen Λ) :
    phiC c (ExteriorAlgebra.ι ℝ v) = ExteriorAlgebra.ι ℂ (vC c v) :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

theorem real_smul_eq (r : ℝ) (y : N Λ) : r • y = (r : ℂ) • y := by
  rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ (N Λ)]; rfl

theorem algebraMap_real_eq (r : ℝ) : algebraMap ℝ (N Λ) r = algebraMap ℂ (N Λ) (r : ℂ) :=
  IsScalarTower.algebraMap_apply ℝ ℂ (N Λ) r

theorem vC_inl (c : ℝ) (x : Λ) : vC c (Pi.single (Sum.inl x) 1) = (c : ℂ) • ev (x, -1) := by
  funext ⟨y, σ⟩
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simp [vC, ev, Pi.single_apply, Prod.ext_iff, one_ne_neg_one_units]
  · by_cases h : y = x
    · subst h; simp [vC, ev, Pi.single_apply, (one_ne_neg_one_units).symm]
    · simp [vC, ev, Pi.single_apply, h, (one_ne_neg_one_units).symm]

theorem vC_inr (c : ℝ) (x : Λ) : vC c (Pi.single (Sum.inr x) 1) = (c : ℂ) • ev (x, 1) := by
  funext ⟨y, σ⟩
  rcases Int.units_eq_one_or σ with rfl | rfl
  · by_cases h : y = x
    · subst h; simp [vC, ev, Pi.single_apply]
    · simp [vC, ev, Pi.single_apply, h]
  · simp [vC, ev, Pi.single_apply, Prod.ext_iff, (one_ne_neg_one_units).symm]

theorem phiC_ξ (c : ℝ) (x : Λ) : phiC c (H02.ξ x) = (c : ℂ) • psibar x := by
  rw [H02.ξ, phiC_ι, vC_inl, map_smul]; rfl

theorem phiC_η (c : ℝ) (x : Λ) : phiC c (H02.η x) = (c : ℂ) • psi x := by
  rw [H02.η, phiC_ι, vC_inr, map_smul]; rfl

/-- `φ_c(ξ_x η_y) = c² ψ̄_x ψ_y`. -/
theorem phiC_ξη (c : ℝ) (x y : Λ) :
    phiC c (H02.ξ x * H02.η y) = ((c ^ 2 : ℝ) : ℂ) • (psibar x * psi y) := by
  rw [map_mul, phiC_ξ, phiC_η, smul_mul_smul_comm,
    show ((c : ℂ) * c) = ((c ^ 2 : ℝ) : ℂ) by push_cast; ring]

theorem psibar_mul_psi' (x y : Λ) : psibar x * psi y = -(psi y * psibar x) := by
  simp only [psibar, psi, ψ]; exact ι_anticomm _ _

/-- `φ_c(ξ_x η_y) = -c² ψ_y ψ̄_x`. -/
theorem phiC_ξη' (c : ℝ) (x y : Λ) :
    phiC c (H02.ξ x * H02.η y) = -(((c ^ 2 : ℝ) : ℂ) • (psi y * psibar x)) := by
  rw [phiC_ξη, psibar_mul_psi', smul_neg]

/-- `φ_c(z_x) = 1 + c² ψ_x ψ̄_x`. -/
theorem phiC_z (c : ℝ) (x : Λ) :
    phiC c (H02.z x) = 1 + ((c ^ 2 : ℝ) : ℂ) • (psi x * psibar x) := by
  rw [H02.z, map_sub, map_one, phiC_ξη', sub_neg_eq_add]

/-- `φ_c(ξ_a η_a ξ_b η_b) = c⁴ ψ_a ψ̄_a ψ_b ψ̄_b`. -/
theorem phiC_ξηξη (c : ℝ) (a b : Λ) :
    phiC c (H02.ξ a * H02.η a * (H02.ξ b * H02.η b)) =
      ((c ^ 4 : ℝ) : ℂ) • (psi a * psibar a * (psi b * psibar b)) := by
  rw [map_mul, phiC_ξη', phiC_ξη', neg_mul_neg, smul_mul_smul_comm,
    show (((c ^ 2 : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ)) = ((c ^ 4 : ℝ) : ℂ) by push_cast; ring]

theorem phiC_inv' (c : ℝ) (F : H02.Grassmann Λ) :
    phiC c (H02.inv' F) = Grassmann.inv' (phiC c F) := by
  have : (phiC c).comp (H02.inv' : H02.Grassmann Λ →ₐ[ℝ] _) =
      ((Grassmann.inv' : N Λ →ₐ[ℂ] N Λ).restrictScalars ℝ).comp (phiC c) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [phiC_ι, H02.inv'_ι, Grassmann.inv'_ι]
  exact congrArg (fun f : H02.Grassmann Λ →ₐ[ℝ] N Λ => f F) this

/-- `ε(φ_c F) = [F]|_{ξ=η=0}`. -/
theorem ε_phiC (c : ℝ) (F : H02.Grassmann Λ) :
    ε (phiC c F) = ((ExteriorAlgebra.algebraMapInv F : ℝ) : ℂ) := by
  have : ((ε : N Λ →ₐ[ℂ] ℂ).restrictScalars ℝ).comp (phiC c) =
      (Algebra.ofId ℝ ℂ).comp (ExteriorAlgebra.algebraMapInv : H02.Grassmann Λ →ₐ[ℝ] ℝ) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp [phiC_ι]
  exact congrArg (fun f : H02.Grassmann Λ →ₐ[ℝ] ℂ => f F) this

theorem D_algebraMap_real (a : Sf Λ) (r : ℝ) : D a (algebraMap ℝ (N Λ) r) = 0 := by
  rw [algebraMap_real_eq]; simp [D]

theorem smul_phiC_contract (c : ℝ) (σ : ℤˣ) (s : Λ ⊕ Λ) (x : Λ)
    (hv : ∀ v : H02.Gen Λ, (c : ℂ) * (v s : ℂ) = vC c v (x, σ)) (F : H02.Grassmann Λ) :
    (c : ℂ) • phiC c (CliffordAlgebra.contractLeft
        (LinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) s) F) = D (x, σ) (phiC c F) := by
  induction F using CliffordAlgebra.induction with
  | algebraMap r =>
    simp only [CliffordAlgebra.contractLeft_algebraMap, map_zero, smul_zero, AlgHom.commutes,
      D_algebraMap_real]
  | ι v =>
    rw [CliffordAlgebra.contractLeft_ι, AlgHom.commutes, phiC_ι, D, CliffordAlgebra.contractLeft_ι,
      algebraMap_real_eq, Algebra.smul_def, ← map_mul, LinearMap.proj_apply,
      LinearMap.proj_apply, ← hv v]
  | mul a b ha hb =>
    simp only [H02.contractLeft_mul, map_add, map_mul, smul_add]
    rw [← smul_mul_assoc, ha, ← mul_smul_comm, hb, phiC_inv', D_mul]
  | add a b ha hb => simp only [map_add, smul_add, ha, hb]

/-- `c φ_c(∂_{ξ_x} F) = ∂_{ψ̄_x} φ_c(F)`. -/
theorem phiC_dξ (c : ℝ) (x : Λ) (F : H02.Grassmann Λ) :
    (c : ℂ) • phiC c (H02.dξ x F) = D (x, -1) (phiC c F) :=
  smul_phiC_contract c (-1) (Sum.inl x) x
    (fun v => by simp [vC, (one_ne_neg_one_units).symm]) F

/-- `c φ_c(∂_{η_x} F) = ∂_{ψ_x} φ_c(F)`. -/
theorem phiC_dη (c : ℝ) (x : Λ) (F : H02.Grassmann Λ) :
    (c : ℂ) • phiC c (H02.dη x F) = D (x, 1) (phiC c F) :=
  smul_phiC_contract c 1 (Sum.inr x) x (fun v => by simp [vC]) F

/-! ### Pure Berezin integrals -/

/-- `∏_{x ∈ l} ∂_{ψ_x} ∂_{ψ̄_x}` on `𝒩(Λ)` (for each `x`, `∂_{ψ̄_x}` first). -/
def berN (l : List Λ) : N Λ →ₗ[ℂ] N Λ :=
  l.foldr (fun x T => D (x, 1) ∘ₗ D (x, -1) ∘ₗ T) LinearMap.id

/-- `∏_{x ∈ l} ∂_{η_x} ∂_{ξ_x}` on `Ω^{2Λ}` (for each `x`, `∂_{ξ_x}` first). -/
def berR (l : List Λ) : H02.Grassmann Λ →ₗ[ℝ] H02.Grassmann Λ :=
  l.foldr (fun x T => H02.dη x ∘ₗ H02.dξ x ∘ₗ T) LinearMap.id

theorem berN_cons (x : Λ) (l : List Λ) (F : N Λ) :
    berN (x :: l) F = D (x, 1) (D (x, -1) (berN l F)) := rfl

theorem berR_cons (x : Λ) (l : List Λ) (F : H02.Grassmann Λ) :
    berR (x :: l) F = H02.dη x (H02.dξ x (berR l F)) := rfl

theorem phiC_berR (c : ℝ) (l : List Λ) (F : H02.Grassmann Λ) :
    (((c ^ 2) ^ l.length : ℝ) : ℂ) • phiC c (berR l F) = berN l (phiC c F) := by
  induction l with
  | nil => simp [berR, berN]
  | cons x l ih =>
    rw [berR_cons, berN_cons, ← ih, List.length_cons, map_smul, map_smul,
      ← phiC_dξ, map_smul, ← phiC_dη, smul_smul, smul_smul]
    congr 1; push_cast; ring

theorem berR_dd_comm (l : List Λ) (x : Λ) (G : H02.Grassmann Λ) :
    H02.dη x (H02.dξ x (berR l G)) = berR l (H02.dη x (H02.dξ x G)) := by
  induction l with
  | nil => rfl
  | cons y l ih => rw [berR_cons, berR_cons, H02.dd_comm, ih]

/-- `∏_{j ∈ l} (1 + ξ_j η_j)`. -/
def Pl (l : List Λ) : H02.Grassmann Λ := (l.map fun j => 1 + H02.ξ j * H02.η j).prod

theorem isFree_Pl {i : Λ} {l : List Λ} (hi : i ∉ l) : H02.IsFree i (Pl l) := by
  induction l with
  | nil => simpa [Pl] using H02.isFree_algebraMap i 1
  | cons j l ih =>
    rw [List.mem_cons, not_or] at hi
    simp only [Pl, List.map_cons, List.prod_cons]
    exact (H02.isFree_w (Ne.symm hi.1)).mul (ih hi.2)

/-- Pulling out the volume form: `∏_{x ∈ l} ∂_{η_x}∂_{ξ_x} z_x⁻¹ F = ∏_{x ∈ l} ∂_{η_x}∂_{ξ_x}
(∏_{x ∈ l} (1 + ξ_x η_x) F)`. -/
theorem berezin_eq_berR : ∀ {l : List Λ}, l.Nodup → ∀ F : H02.Grassmann Λ,
    H02.berezin l F = berR l (Pl l * F)
  | [], _, F => by simp [Pl, berR]
  | i :: l, hl, F => by
    rw [List.nodup_cons] at hl
    rw [H02.berezin_cons, berezin_eq_berR hl.2, ← H02.intStep_free_mul (isFree_Pl hl.1),
      H02.intStep_apply, ← berR_dd_comm, berR_cons]
    simp only [Pl, List.map_cons, List.prod_cons, mul_assoc]

variable [Fintype Λ]

/-- `c^{2|Λ|} [F]_0 = ε(∏_x ∂_{ψ_x}∂_{ψ̄_x} φ_c(∏_x (1 + ξ_xη_x) F))`. -/
theorem int0_eq_berN (c : ℝ) (F : H02.Grassmann Λ) :
    (((c ^ 2) ^ Fintype.card Λ : ℝ) : ℂ) * (H02.int0 F : ℂ) =
      ε (berN (univ : Finset Λ).toList (phiC c (Pl (univ : Finset Λ).toList * F))) := by
  rw [H02.int0, berezin_eq_berR (nodup_toList _) F, ← ε_phiC c, ← phiC_berR, map_smul,
    smul_eq_mul, length_toList, card_univ]

theorem isNilpotent_quad (A : Matrix Λ Λ ℝ) : IsNilpotent (quad A) := by
  have hev : ∀ (a b : Sf Λ) (c : ℂ), Grassmann.inv' (c • (ψ a * ψ b)) = c • (ψ a * ψ b) := by
    simp
  refine Commute.isNilpotent_sum (fun x _ => ?_) fun x x' _ _ => ?_
  · refine Commute.isNilpotent_sum (fun y _ => ?_) fun y y' _ _ => ?_
    · exact ⟨2, by rw [pow_two, smul_mul_smul, ψ, ψ, ιι_sq, smul_zero]⟩
    · exact Grassmann.mul_comm_of_even (hev _ _ _) _
  · exact Grassmann.mul_comm_of_even (by simp [map_sum, AlgHom.map_smul_of_tower]) _

theorem inv'_quad (A : Matrix Λ Λ ℝ) : Grassmann.inv' (quad A) = quad A := by
  simp [quad, map_sum, AlgHom.map_smul_of_tower]

theorem berL_inclζ_eq (l : List Λ) (F : N Λ) : berL l (inclζ F) = inclζ (berN l F) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [berL_cons, ih, LinearMap.comp_apply, D_inclζ, D_inclζ]; rfl

/-- `⟨G⟩_C = det C · ε(∏_x ∂_{ψ_x}∂_{ψ̄_x} e^{-(ψ, C⁻¹ ψ̄)} G)`. -/
theorem omega_eq_berN (C : Matrix Λ Λ ℝ) (hC : IsUnit C.det) (G : N Λ) :
    omega C G = (C.det : ℂ) *
      ε (berN (univ : Finset Λ).toList (IsNilpotent.exp (-quad C⁻¹) * G)) := by
  have h1 := EC_inclζ C G
  rw [EC_eq_berezin C hC, ← inclζ_quad, ← map_neg,
    ← IsNilpotent.map_exp (isNilpotent_quad C⁻¹).neg (inclζ : N Λ →ₐ[ℂ] N (Λ ⊕ Λ)), ← map_mul,
    berezinζ_eq, berL_inclζ_eq,
    proj_inclζ, Algebra.smul_def, ← map_mul] at h1
  have h2 := congrArg (ε : N Λ →ₐ[ℂ] ℂ) h1
  simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h2
  exact h2.symm

end General

/-! ### The torus -/

variable {d L N : ℕ} [NeZero L]

/-- The couplings `(z, y, a, b) = (0, s₀, (1+s₀)(1+h)/β - m², (1+s₀)²/β)` of
`e:quartic-rescale`. -/
def Vh (β h msq s₀ : ℝ) : Vcoup :=
  ⟨0, (s₀ : ℂ), (((1 + s₀) * (1 + h) / β - msq : ℝ) : ℂ), (((1 + s₀) ^ 2 / β : ℝ) : ℂ)⟩

/-- The couplings `(0, βc² - 1, (1+h)c² - m², βc⁴)` for a general `c`. -/
def Vc (β h msq c : ℝ) : Vcoup :=
  ⟨0, ((β * c ^ 2 - 1 : ℝ) : ℂ), (((1 + h) * c ^ 2 - msq : ℝ) : ℂ), ((β * c ^ 4 : ℝ) : ℂ)⟩

theorem Vc_eq_Vh {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) :
    Vc β h msq (Real.sqrt ((1 + s₀) / β)) = Vh β h msq s₀ := by
  have hc : Real.sqrt ((1 + s₀) / β) ^ 2 = (1 + s₀) / β :=
    Real.sq_sqrt (div_nonneg (by linarith) hβ.le)
  have hc4 : Real.sqrt ((1 + s₀) / β) ^ 4 = ((1 + s₀) / β) ^ 2 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hc]
  unfold Vc Vh
  rw [hc, hc4]
  congr 2 <;> (field_simp; try ring)

/-! #### The action in `ψ` variables -/

theorem dot_self' {Λ : Type*} [DecidableEq Λ] (i : Λ) : H02.dot i i = -1 := by
  have := congrArg H02.cv (H02.Xc_self i)
  rw [H02.coe_Xc, map_zero] at this
  exact eq_neg_of_add_eq_zero_right this

theorem one_add_dot {Λ : Type*} [DecidableEq Λ] (i j : Λ) :
    1 + H02.dot i j = (H02.ξ i - H02.ξ j) * (H02.η i - H02.η j) -
      H02.ξ i * H02.η i * (H02.ξ j * H02.η j) := by
  simp only [H02.dot, H02.z]; noncomm_ring

/-- `-H_{β,h} = ½ ∑_{ij} β_{ij} (1 + u_i·u_j) + ∑_i h_i ξ_i η_i` (any weights). -/
theorem neg_action {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (w : Λ → Λ → ℝ) (h : Λ → ℝ) :
    -H02.action w h = (1 / 2 : ℝ) • ∑ i, ∑ j, w i j • (1 + H02.dot i j) +
      ∑ i, h i • (H02.ξ i * H02.η i) := by
  have e1 : ∀ i j : Λ, H02.dot i i - H02.dot i j - H02.dot j i + H02.dot j j =
      (-2 : ℝ) • (1 + H02.dot i j) := by
    intro i j
    rw [dot_self', dot_self', H02.dot_comm j i]
    module
  have e2 : ∀ i : Λ, H02.z i - 1 = -(H02.ξ i * H02.η i) := fun i => by simp [H02.z]
  simp only [H02.action, e1, e2]
  have h3 : ∑ i, ∑ j, w i j • ((-2 : ℝ) • (1 + H02.dot i j)) =
      (-2 : ℝ) • ∑ i, ∑ j, w i j • (1 + H02.dot i j) := by
    simp only [Finset.smul_sum, smul_comm (-2 : ℝ)]
  rw [h3, smul_smul]
  simp only [smul_neg, Finset.sum_neg_distrib]
  rw [neg_add, neg_neg, ← neg_smul]
  norm_num

theorem neg_action_nnW (β h : ℝ) :
    -H02.action (nnW d L N β) (fun _ => h) = (1 / 2 : ℝ) • ∑ x, β • ∑ e : Dir d,
      (1 + H02.dot x (x + dirVec e)) + ∑ x, h • (H02.ξ x * H02.η x) := by
  rw [neg_action]
  simp only [sum_nnW_mul]

/-- `(ψ̄_x - ψ̄_{x+e})(ψ_x - ψ_{x+e}) = -(∇_eψ)_x (∇_eψ̄)_x`. -/
theorem psibar_sub_mul (e : Dir d) (x : Lam d L N) :
    (psibar x - psibar (x + dirVec e)) * (psi x - psi (x + dirVec e)) =
      -(grad e x * gradbar e x) := by
  have h : ∀ u v : V (Lam d L N), ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ v =
      -(ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ u) := ι_anticomm
  have := h (ev (x, -1) - ev (x + dirVec e, -1)) (ev (x, 1) - ev (x + dirVec e, 1))
  simp only [map_sub] at this
  rw [grad, gradbar]
  simp only [psibar, psi, ψ]
  rw [this]; noncomm_ring

theorem pp_mul_psi (x : Lam d L N) : psi x * psibar x * psi x = 0 := by
  rw [mul_assoc, psibar_mul_psi', mul_neg, ← mul_assoc]
  simp [psi, ψ, ExteriorAlgebra.ι_sq_zero]

theorem pp_mul_psibar (x : Lam d L N) : psi x * psibar x * psibar x = 0 := by
  rw [mul_assoc]; simp [psibar, ψ, ExteriorAlgebra.ι_sq_zero]

theorem inv'_pp (x : Lam d L N) : Grassmann.inv' (psi x * psibar x) = psi x * psibar x := by
  simp [psi, psibar]

/-- `ψ_xψ̄_x ψ_{x+e}ψ̄_{x+e} = ψ_xψ̄_x (∇_eψ)_x (∇_eψ̄)_x`. -/
theorem pp_mul_pp (e : Dir d) (x : Lam d L N) :
    psi x * psibar x * (psi (x + dirVec e) * psibar (x + dirVec e)) =
      psi x * psibar x * (grad e x * gradbar e x) := by
  have h1 : psi x * psibar x * (psi (x + dirVec e) * psibar x) = 0 := by
    rw [← mul_assoc, Grassmann.mul_comm_of_even (inv'_pp x) (psi (x + dirVec e)), mul_assoc,
      pp_mul_psibar, mul_zero]
  have h2 : psi x * psibar x * (psi x * psibar (x + dirVec e)) = 0 := by
    rw [← mul_assoc, pp_mul_psi, zero_mul]
  have h3 : psi x * psibar x * (psi x * psibar x) = 0 := by
    rw [← mul_assoc, pp_mul_psi, zero_mul]
  rw [grad, gradbar]
  have : (psi (x + dirVec e) - psi x) * (psibar (x + dirVec e) - psibar x) =
      psi (x + dirVec e) * psibar (x + dirVec e) - psi (x + dirVec e) * psibar x -
        psi x * psibar (x + dirVec e) + psi x * psibar x := by noncomm_ring
  rw [this, mul_add, mul_sub, mul_sub, h1, h2, h3]; abel

theorem phiC_one_add_dot (c : ℝ) (e : Dir d) (x : Lam d L N) :
    phiC c (1 + H02.dot x (x + dirVec e)) =
      -(((c ^ 2 : ℝ) : ℂ) • (grad e x * gradbar e x)) -
        ((c ^ 4 : ℝ) : ℂ) • (psi x * psibar x * (grad e x * gradbar e x)) := by
  rw [one_add_dot, map_sub, phiC_ξηξη, map_mul, map_sub, map_sub, phiC_ξ, phiC_ξ, phiC_η, phiC_η,
    ← smul_sub, ← smul_sub, smul_mul_smul_comm, psibar_sub_mul, pp_mul_pp, smul_neg,
    show ((c : ℂ) * c) = ((c ^ 2 : ℝ) : ℂ) by push_cast; ring]

theorem sum_dir_grad (x : Lam d L N) :
    ∑ e : Dir d, grad e x * gradbar e x = (2 : ℂ) • gradSq x := by
  rw [gradSq, smul_smul]; norm_num

theorem negLap_psibar_eq (x : Lam d L N) :
    ∑ y, ((FRD.negLap x y : ℝ) : ℂ) • psibar y =
      (2 * (d : ℂ)) • psibar x - ∑ e : Dir d, psibar (x + dirVec e) := by
  have h1 : ∀ y, ((FRD.negLap x y : ℝ) : ℂ) • psibar y =
      (if x = y then (2 * (d : ℂ)) • psibar y else 0) -
        ∑ e : Dir d, if y = x + dirVec e then psibar y else 0 := by
    intro y
    simp only [FRD.negLap]
    push_cast
    rw [sub_smul, Finset.sum_smul]
    congr 1
    · split_ifs <;> simp
    · exact sum_congr rfl fun e _ => by split_ifs <;> simp
  rw [sum_congr rfl fun y _ => h1 y, sum_sub_distrib, sum_ite_eq, sum_comm]
  simp only [mem_univ, if_true, sum_ite_eq', if_true]

theorem negLapPsibar_eq (x : Lam d L N) :
    -lapPsibar x = (2 * (d : ℂ)) • psibar x - ∑ e : Dir d, psibar (x + dirVec e) := by
  have hs : ∑ e : Dir d, psibar (x - dirVec e) = ∑ e : Dir d, psibar (x + dirVec e) :=
    FRD.sum_dir_shift (fun y => psibar y) x
  have h1 : -lapPsibar x = (1 / 2 : ℂ) • ∑ e : Dir d,
      ((2 : ℂ) • psibar x - psibar (x - dirVec e) - psibar (x + dirVec e)) := by
    rw [lapPsibar, neg_smul, neg_neg]
    congr 1
    refine sum_congr rfl fun e _ => ?_
    rw [gradbar, gradbar, sub_add_cancel, two_smul]; abel
  rw [h1, sum_sub_distrib, sum_sub_distrib, hs, sum_const, card_univ, Fintype.card_sum,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  push_cast
  module

theorem negLap_psibar (x : Lam d L N) :
    ∑ y, ((FRD.negLap x y : ℝ) : ℂ) • psibar y = -lapPsibar x := by
  rw [negLap_psibar_eq, negLapPsibar_eq]

/-- `(ψ, (-Δ + m²) ψ̄) = ∑_x (∇ψ)_x(∇ψ̄)_x + m² ∑_x ψ_x ψ̄_x`. -/
theorem quad_negLap_add (msq : ℝ) :
    quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) =
      ∑ x : Lam d L N, gradSq x + (msq : ℂ) • ∑ x : Lam d L N, psi x * psibar x := by
  have h : ∀ x : Lam d L N, ∑ y, (((FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) x y : ℝ) : ℂ) •
      (ψ (x, 1) * ψ (y, -1)) = psi x * (-lapPsibar x) + (msq : ℂ) • (psi x * psibar x) := by
    intro x
    have e1 : ∀ y, (((FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) x y : ℝ) : ℂ) •
        (ψ (x, 1) * ψ (y, -1)) = psi x * (((FRD.negLap x y : ℝ) : ℂ) • psibar y) +
          (if x = y then (msq : ℂ) • (psi x * psibar y) else 0) := by
      intro y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      split_ifs <;> simp [add_smul, mul_smul_comm, psi, psibar]
    rw [sum_congr rfl fun y _ => e1 y, sum_add_distrib, ← Finset.mul_sum, negLap_psibar,
      sum_ite_eq]
    simp
  rw [quad, sum_congr rfl fun x _ => h x, sum_add_distrib, Psi4.sum_mul_negLapPsibar,
    Finset.smul_sum]

theorem phiC_exponent_pt (β c h msq : ℝ) (x : Lam d L N) :
    phiC c (H02.ξ x * H02.η x) +
        (1 / 2 : ℝ) • (β • phiC c (∑ e : Dir d, (1 + H02.dot x (x + dirVec e)))) +
        h • phiC c (H02.ξ x * H02.η x) =
      -(gradSq x + (msq : ℂ) • (psi x * psibar x)) -
        ((Vc β h msq c).y • gradSq x +
          ((Vc β h msq c).z / 2) • ((-lapPsi x) * psibar x + psi x * (-lapPsibar x)) +
          (Vc β h msq c).a • (psi x * psibar x) +
          (Vc β h msq c).b • (psi x * psibar x * gradSq x)) := by
  rw [map_sum, sum_congr rfl fun e _ => phiC_one_add_dot c e x, sum_sub_distrib,
    sum_neg_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.mul_sum, sum_dir_grad,
    phiC_ξη', real_smul_eq, real_smul_eq, real_smul_eq]
  simp only [Vc, zero_div, zero_smul, add_zero, mul_smul_comm]
  push_cast
  module

/-- **The action identity.** With `β_{xy} = nnW β` and constant field `h`,
`φ_c(∑_x ξ_xη_x - H_{β,h}) = -(ψ, (-Δ+m²)ψ̄) - V(Λ)`, `V = (0, βc² - 1, (1+h)c² - m², βc⁴)`. -/
theorem phiC_exponent (β c h msq : ℝ) :
    phiC c (∑ x : Lam d L N, H02.ξ x * H02.η x - H02.action (nnW d L N β) (fun _ => h)) =
      -quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) -
        (Vc β h msq c).eval (univ : Finset (Lam d L N)) := by
  have hL : phiC c (∑ x : Lam d L N, H02.ξ x * H02.η x -
      H02.action (nnW d L N β) (fun _ => h)) = ∑ x : Lam d L N,
      (phiC c (H02.ξ x * H02.η x) +
        (1 / 2 : ℝ) • (β • phiC c (∑ e : Dir d, (1 + H02.dot x (x + dirVec e)))) +
        h • phiC c (H02.ξ x * H02.η x)) := by
    rw [sub_eq_add_neg, neg_action_nnW]
    simp only [map_add, map_sum, map_smul, Finset.smul_sum, Finset.sum_add_distrib, add_assoc]
  have hR : -quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) -
      (Vc β h msq c).eval (univ : Finset (Lam d L N)) = ∑ x : Lam d L N,
      (-(gradSq x + (msq : ℂ) • (psi x * psibar x)) -
        ((Vc β h msq c).y • gradSq x +
          ((Vc β h msq c).z / 2) • ((-lapPsi x) * psibar x + psi x * (-lapPsibar x)) +
          (Vc β h msq c).a • (psi x * psibar x) +
          (Vc β h msq c).b • (psi x * psibar x * gradSq x))) := by
    rw [quad_negLap_add, Vcoup.eval, Finset.smul_sum, ← sum_add_distrib, ← sum_neg_distrib,
      ← sum_sub_distrib]
  rw [hL, hR]
  exact sum_congr rfl fun x _ => phiC_exponent_pt β c h msq x

theorem sum_ξη_sub_action {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (w : Λ → Λ → ℝ)
    (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    ∑ x : Λ, H02.ξ x * H02.η x - H02.action w h = H02.cv (∑ x : Λ, H02.pc x x + H02.W w hw h) := by
  rw [H02.action_eq w hw h, map_add, map_sum]
  simp [sub_eq_add_neg]

theorem isNilpotent_sum_pc {Λ : Type*} [DecidableEq Λ] [Fintype Λ] :
    IsNilpotent (∑ x : Λ, H02.pc x x) :=
  isNilpotent_sum fun i _ => H02.isNilpotent_of_mul_self (H02.pc_sq i)

theorem isNilpotent_ξη_sub_action {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (w : Λ → Λ → ℝ)
    (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    IsNilpotent (∑ x : Λ, H02.ξ x * H02.η x - H02.action w h) := by
  rw [sum_ξη_sub_action w hw h]
  exact ((Commute.all _ _).isNilpotent_add isNilpotent_sum_pc (H02.isNilpotent_W w hw h)).map
    H02.cv

/-- `∏_x (1 + ξ_xη_x) e^{-H_{β,h}} = e^{∑_x ξ_xη_x - H_{β,h}}`. -/
theorem Pl_mul_exp {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (w : Λ → Λ → ℝ)
    (hw : ∀ i j, w i j = w j i) (h : Λ → ℝ) :
    Pl (univ : Finset Λ).toList * IsNilpotent.exp (-H02.action w h) =
      IsNilpotent.exp (∑ x : Λ, H02.ξ x * H02.η x - H02.action w h) := by
  have hP : Pl (univ : Finset Λ).toList = H02.cv (IsNilpotent.exp (∑ x : Λ, H02.pc x x)) := by
    rw [H02.exp_sum _ _ fun i _ => H02.isNilpotent_of_mul_self (H02.pc_sq i),
      Finset.prod_congr rfl fun i _ => H02.exp_eq_one_add (H02.pc_sq i),
      ← Finset.prod_map_toList, map_list_prod, List.map_map, Pl]
    congr 1
    try (refine List.map_congr_left fun x _ => ?_; simp)
  have hW := H02.isNilpotent_W w hw h
  rw [hP, sum_ξη_sub_action w hw h, H02.action_eq w hw h, neg_neg,
    ← IsNilpotent.map_exp hW H02.cv, ← map_mul,
    ← IsNilpotent.exp_add_of_commute (Commute.all _ _) isNilpotent_sum_pc hW,
    IsNilpotent.map_exp ((Commute.all _ _).isNilpotent_add isNilpotent_sum_pc hW) H02.cv]

/-- **The density identity**: `φ_c(∏_x (1+ξ_xη_x) e^{-H_{β,h}}) = e^{-(ψ,(-Δ+m²)ψ̄)} e^{-V(Λ)}`. -/
theorem phiC_density (β c h msq : ℝ) :
    phiC c (Pl (univ : Finset (Lam d L N)).toList *
        IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h))) =
      IsNilpotent.exp (-quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ)) *
        (gexp (-VE (Vc β h msq c) (univ : Finset (Lam d L N))) : Alg d L N) := by
  have hY := isNilpotent_ξη_sub_action (nnW d L N β) (nnW_symm β) (fun _ => h)
  rw [Pl_mul_exp _ (nnW_symm β), IsNilpotent.map_exp hY (phiC c), phiC_exponent β c h msq]
  have hq : IsNilpotent (-quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ)) :=
    (isNilpotent_quad _).neg
  have hcomm : Commute (phiC c (∑ x : Lam d L N, H02.ξ x * H02.η x -
      H02.action (nnW d L N β) (fun _ => h)))
      (quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ)) :=
    (Grassmann.mul_comm_of_even (inv'_quad _) _).symm
  have hVn : IsNilpotent (-(Vc β h msq c).eval (univ : Finset (Lam d L N))) := by
    have : -(Vc β h msq c).eval (univ : Finset (Lam d L N)) =
        phiC c (∑ x : Lam d L N, H02.ξ x * H02.η x - H02.action (nnW d L N β) (fun _ => h)) +
          quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ) := by
      rw [phiC_exponent]; abel
    rw [this]
    exact hcomm.isNilpotent_add (hY.map (phiC c)) (isNilpotent_quad _)
  have hVE : IsNilpotent (-VE (Vc β h msq c) (univ : Finset (Lam d L N))) := by
    obtain ⟨k, hk⟩ := hVn
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hg : ((gexp (-VE (Vc β h msq c) (univ : Finset (Lam d L N))) : EvR (Lam d L N)) :
      Alg d L N) = IsNilpotent.exp (-(Vc β h msq c).eval (univ : Finset (Lam d L N))) := by
    have := IsNilpotent.map_exp hVE (Ev (Lam d L N)).val
    simpa [gexp] using this
  have hcomm2 : Commute (-quad (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ))
      (-(Vc β h msq c).eval (univ : Finset (Lam d L N))) :=
    Grassmann.mul_comm_of_even (by rw [map_neg, inv'_quad]) _
  rw [hg, sub_eq_add_neg, IsNilpotent.exp_add_of_commute hcomm2 hq hVn]

/-! ### The bridge -/

theorem expect_mul_comm (β h : ℝ) (F G : H02.Grassmann (Lam d L N)) :
    G * IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h)) =
      IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h)) * G := by
  have hn : IsNilpotent (-H02.action (nnW d L N β) (fun _ => h)) := by
    rw [H02.action_eq _ (nnW_symm β), neg_neg]
    exact (H02.isNilpotent_W _ _ _).map H02.cv
  have hEv : H02.inv' (IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h))) =
      IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h)) := by
    rw [IsNilpotent.map_exp hn H02.inv', H02.inv'_action]
  exact (H02.mul_comm_of_even hEv G).symm

/-- **Bridge** (`e:h02-psi`, `e:xietapsi`, `e:quartic-rescale`): for `β > 0`, `s₀ > -1`,
`m² > 0`, with `c = √((1+s₀)/β)`,
`[F]_{β,h} = (β/(1+s₀))^{|Λ|} det(-Δ+m²) ⟨e^{-V(Λ)} φ_c(F)⟩_C`, `C = (-Δ+m²)^{-1}`,
`V = Vh β h m² s₀ = (0, s₀, (1+s₀)(1+h)/β - m², (1+s₀)²/β)`. -/
theorem bridge_expect {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq)
    (F : H02.Grassmann (Lam d L N)) :
    ((H02.expect (nnW d L N β) (fun _ => h) F : ℝ) : ℂ) =
      (((β / (1 + s₀)) ^ Fintype.card (Lam d L N) *
          (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det : ℝ) : ℂ) *
        omega (Suscept.Cov d L N msq)
          ((gexp (-VE (Vh β h msq s₀) (univ : Finset (Lam d L N))) : Alg d L N) * phiC (Real.sqrt ((1 + s₀) / β)) F) := by
  have hc2 : Real.sqrt ((1 + s₀) / β) ^ 2 = (1 + s₀) / β :=
    Real.sq_sqrt (div_nonneg (by linarith) hβ.le)
  have hA : IsUnit (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det :=
    FRD.isUnit_det_negLap_add hmsq
  have hCdet : IsUnit (Suscept.Cov d L N msq).det := Matrix.isUnit_nonsing_inv_det _ hA
  have hCinv : (Suscept.Cov d L N msq)⁻¹ = FRD.negLap + msq • 1 := by
    rw [Suscept.Cov, Matrix.nonsing_inv_nonsing_inv _ hA]
  have hdetC : (Suscept.Cov d L N msq).det *
      (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det = 1 := by
    exact Matrix.det_nonsing_inv_mul_det _ hA
  have key := int0_eq_berN (Real.sqrt ((1 + s₀) / β))
    (F * IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h)))
  have hPFE : Pl (univ : Finset (Lam d L N)).toList *
      (F * IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h))) =
      (Pl (univ : Finset (Lam d L N)).toList *
        IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h))) * F := by
    rw [expect_mul_comm β h F F, mul_assoc]
  rw [hPFE, map_mul, phiC_density β _ h msq, Vc_eq_Vh hβ hs, mul_assoc, hc2] at key
  rw [omega_eq_berN _ hCdet, hCinv, ← key, H02.expect, Complex.ofReal_mul]
  have h1 : ((((1 + s₀) / β) ^ Fintype.card (Lam d L N) : ℝ) : ℂ) *
      (((β / (1 + s₀)) ^ Fintype.card (Lam d L N) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← mul_pow, div_mul_div_comm, mul_comm (1 + s₀) β,
      div_self (mul_pos hβ (by linarith)).ne', one_pow, Complex.ofReal_one]
  have h2 : ((Suscept.Cov d L N msq).det : ℂ) *
      ((FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det : ℂ) = 1 := by
    exact_mod_cast hdetC
  set I : ℂ := (H02.int0 (F * IsNilpotent.exp (-H02.action (nnW d L N β) (fun _ => h))) : ℂ)
  linear_combination (-(I * (((Suscept.Cov d L N msq).det : ℂ) *
      ((FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det : ℂ)))) * h1 + (-I) * h2

theorem bridge_const_ne_zero {β s₀ msq : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq) :
    (((β / (1 + s₀)) ^ Fintype.card (Lam d L N) *
      (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det : ℝ) : ℂ) ≠ 0 := by
  have := FRD.det_negLap_add_pos (d := d) (n := L ^ N) hmsq
  have : 0 < (β / (1 + s₀)) ^ Fintype.card (Lam d L N) *
      (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det :=
    mul_pos (pow_pos (div_pos hβ (by linarith)) _) this
  exact_mod_cast this.ne'

/-- **Bridge for the partition function** (`e:ZbetahuNN`):
`Z_{β,h} = (β/(1+s₀))^{|Λ|} det(-Δ+m²) Z_{m²,s₀,a₀,b₀}`. -/
theorem bridge_Z {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq) :
    ((H02.expect (nnW d L N β) (fun _ => h) 1 : ℝ) : ℂ) =
      (((β / (1 + s₀)) ^ Fintype.card (Lam d L N) *
          (FRD.negLap + msq • 1 : Matrix (Lam d L N) (Lam d L N) ℝ).det : ℝ) : ℂ) *
        Obs.Zb (Suscept.Cov d L N msq) (VE (Vh β h msq s₀) (univ : Finset (Lam d L N))) := by
  rw [bridge_expect hβ hs hmsq, map_one, mul_one, Obs.Zb]

/-- **Bridge for normalised expectations**: `⟨F⟩_{β,h} = ⟨φ_c(F)⟩_{m², s₀, a₀, b₀}` (no
hypothesis `Z ≠ 0` is needed: both sides are ratios with the same non-zero factor). -/
theorem bridge_avg {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq)
    (F : H02.Grassmann (Lam d L N)) :
    ((H02.avg (nnW d L N β) (fun _ => h) F : ℝ) : ℂ) =
      Obs.avg (Suscept.Cov d L N msq) (VE (Vh β h msq s₀) (univ : Finset (Lam d L N)))
        (phiC (Real.sqrt ((1 + s₀) / β)) F) := by
  rw [H02.avg, Complex.ofReal_div, bridge_expect hβ hs hmsq, bridge_expect hβ hs hmsq, map_one,
    mul_one, Obs.avg, mul_div_mul_left _ _ (bridge_const_ne_zero hβ hs hmsq)]

theorem avg_smul (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : EvR (Lam d L N)) (k : ℂ)
    (F : Alg d L N) : Obs.avg C Vb (k • F) = k * Obs.avg C Vb F := by
  rw [Obs.avg, Obs.avg, mul_smul_comm, Obs.omega_smul', mul_div_assoc]

/-- `⟨ξ_a η_b⟩_{β,h} = (1+s₀)/β · ⟨ψ̄_a ψ_b⟩_{m², s₀, a₀, b₀}`. -/
theorem bridge_avg_ξη {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq)
    (a b : Lam d L N) :
    ((H02.avg (nnW d L N β) (fun _ => h) (H02.ξ a * H02.η b) : ℝ) : ℂ) =
      (((1 + s₀) / β : ℝ) : ℂ) *
        Obs.avg (Suscept.Cov d L N msq) (VE (Vh β h msq s₀) (univ : Finset (Lam d L N))) (psibar a * psi b) := by
  rw [bridge_avg hβ hs hmsq, phiC_ξη, avg_smul, Real.sq_sqrt (div_nonneg (by linarith) hβ.le)]

/-- `⟨ξ_aη_a ξ_bη_b⟩_{β,h} = ((1+s₀)/β)² ⟨ψ̄_aψ_a ψ̄_bψ_b⟩_{m², s₀, a₀, b₀}`. -/
theorem bridge_avg_ξηξη {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq)
    (a b : Lam d L N) :
    ((H02.avg (nnW d L N β) (fun _ => h)
        (H02.ξ a * H02.η a * (H02.ξ b * H02.η b)) : ℝ) : ℂ) =
      (((1 + s₀) / β : ℝ) : ℂ) ^ 2 *
        Obs.avg (Suscept.Cov d L N msq) (VE (Vh β h msq s₀) (univ : Finset (Lam d L N)))
          (psibar a * psi a * (psibar b * psi b)) := by
  rw [bridge_avg hβ hs hmsq, map_mul, phiC_ξη, phiC_ξη, smul_mul_smul_comm, avg_smul,
    Real.sq_sqrt (div_nonneg (by linarith) hβ.le)]
  push_cast; ring

theorem avg_one_sub_smul (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : EvR (Lam d L N))
    (hZ : Obs.Zb C Vb ≠ 0) (k : ℂ) (X : Alg d L N) :
    Obs.avg C Vb (1 - k • X) = 1 - k * Obs.avg C Vb X := by
  have hZ' : omega C ((gexp (-Vb) : EvR (Lam d L N)) : Alg d L N) ≠ 0 := hZ
  have e : omega C (((gexp (-Vb) : EvR (Lam d L N)) : Alg d L N) * (1 - k • X)) =
      omega C ((gexp (-Vb) : EvR (Lam d L N)) : Alg d L N) -
        k * omega C (((gexp (-Vb) : EvR (Lam d L N)) : Alg d L N) * X) := by
    rw [mul_sub, mul_one, mul_smul_comm, sub_eq_add_neg, Grassmann.omega_add, ← neg_smul,
      Obs.omega_smul']
    ring
  rw [Obs.avg, Obs.avg, e]
  field_simp

/-- `⟨z_a⟩_{β,h} = 1 - (1+s₀)/β · ⟨ψ̄_a ψ_a⟩_{m², s₀, a₀, b₀}` (`e:ward-pf-1`), when
`Z_{m²,s₀,a₀,b₀} ≠ 0`. -/
theorem bridge_avg_z {β h msq s₀ : ℝ} (hβ : 0 < β) (hs : -1 < s₀) (hmsq : 0 < msq)
    (hZ : Obs.Zb (Suscept.Cov d L N msq) (VE (Vh β h msq s₀) (univ : Finset (Lam d L N))) ≠ 0) (a : Lam d L N) :
    ((H02.avg (nnW d L N β) (fun _ => h) (H02.z a) : ℝ) : ℂ) =
      1 - (((1 + s₀) / β : ℝ) : ℂ) *
        Obs.avg (Suscept.Cov d L N msq) (VE (Vh β h msq s₀) (univ : Finset (Lam d L N))) (psibar a * psi a) := by
  rw [bridge_avg hβ hs hmsq, H02.z, map_sub, map_one, phiC_ξη,
    Real.sq_sqrt (div_nonneg (by linarith) hβ.le), avg_one_sub_smul _ _ hZ]

end

end Ward
