import Grassmann.Torus

/-!
# Complex conjugation on the Grassmann algebra

`conjN : 𝒩(Λ) →+* 𝒩(Λ)` is the coefficientwise complex conjugation: the ring homomorphism with
`conjN ψ_a = ψ_a` and `conjN (c • F) = c̄ • conjN F` (`conjN_smul`), so that
`(conjN F)_z = conj F_z` (`coeff_conjN`).  It is constructed as the lift of
`v ↦ ι (conj ∘ v)` into a copy of `𝒩(Λ)` whose `ℂ`-algebra structure is twisted by conjugation.

It commutes with every operation with real coefficients: the derivatives `D a`, the grade
involution, the maps `ExteriorAlgebra.map f` for real `f` (`θ`, the inclusions, `proj`), `ℒ_C`,
`e^{ℒ_C}` and `𝔼_C` for real `C`; `⟨conjN F⟩_C = conj ⟨F⟩_C`, and the `T` norms are invariant.
-/

namespace Grassmann

noncomputable section

open CliffordAlgebra ExteriorAlgebra Finset

variable {Λ : Type*}

/-- Complex conjugation of a vector of generators. -/
def conjV (v : V Λ) : V Λ := fun a => starRingEnd ℂ (v a)

@[simp] theorem conjV_apply (v : V Λ) (a : Sf Λ) : conjV v a = starRingEnd ℂ (v a) := rfl

theorem conjV_conjV (v : V Λ) : conjV (conjV v) = v := by ext a; simp

theorem conjV_add (v w : V Λ) : conjV (v + w) = conjV v + conjV w := by ext a; simp

theorem conjV_smul (c : ℂ) (v : V Λ) : conjV (c • v) = starRingEnd ℂ c • conjV v := by
  ext a; simp

/-- `𝒩(Λ)` with the conjugated `ℂ`-algebra structure. -/
def NTw (Λ : Type*) := N Λ

instance : Ring (NTw Λ) := inferInstanceAs (Ring (N Λ))

instance instSMulNTw : SMul ℂ (NTw Λ) :=
  ⟨fun c x => @HSMul.hSMul ℂ (N Λ) (N Λ) _ (starRingEnd ℂ c) x⟩

instance instAlgebraNTw : Algebra ℂ (NTw Λ) where
  algebraMap := ((algebraMap ℂ (N Λ)).comp (starRingEnd ℂ) : ℂ →+* N Λ)
  commutes' c x := Algebra.commutes (R := ℂ) (A := N Λ) (starRingEnd ℂ c) x
  smul_def' c x := Algebra.smul_def (R := ℂ) (A := N Λ) (starRingEnd ℂ c) x

/-- `v ↦ ι (conj ∘ v)` as a `ℂ`-linear map into the twisted algebra. -/
def conjι : V Λ →ₗ[ℂ] NTw Λ where
  toFun v := (ι ℂ (conjV v) : N Λ)
  map_add' v w := by
    show (ι ℂ (conjV (v + w)) : N Λ) = ι ℂ (conjV v) + ι ℂ (conjV w)
    rw [conjV_add, map_add]
  map_smul' c v := by
    show (ι ℂ (conjV (c • v)) : N Λ) = @HSMul.hSMul ℂ (N Λ) (N Λ) _ (starRingEnd ℂ c) (ι ℂ (conjV v))
    rw [conjV_smul, map_smul]

/-- The conjugation as an algebra map into the twisted algebra. -/
def conjNa : N Λ →ₐ[ℂ] NTw Λ := ExteriorAlgebra.lift ℂ ⟨conjι, fun v => by
  show (ι ℂ (conjV v) * ι ℂ (conjV v) : N Λ) = 0
  exact ExteriorAlgebra.ι_sq_zero _⟩

/-- **Complex conjugation** `𝒩(Λ) → 𝒩(Λ)`, coefficientwise. -/
def conjN : N Λ →+* N Λ := (conjNa : N Λ →ₐ[ℂ] NTw Λ).toRingHom

theorem conjN_apply (F : N Λ) : conjN F = (conjNa F : N Λ) := rfl

@[simp] theorem conjN_ι (v : V Λ) : conjN (ι ℂ v : N Λ) = ι ℂ (conjV v) := by
  rw [conjN_apply, conjNa, ExteriorAlgebra.lift_ι_apply]; rfl

@[simp] theorem conjN_algebraMap (c : ℂ) :
    conjN (algebraMap ℂ (N Λ) c) = algebraMap ℂ (N Λ) (starRingEnd ℂ c) := by
  rw [conjN_apply, AlgHom.commutes]; rfl

theorem conjN_smul (c : ℂ) (F : N Λ) : conjN (c • F) = starRingEnd ℂ c • conjN F := by
  rw [conjN_apply, map_smul]; rfl

@[simp] theorem conjN_ofReal_smul (r : ℝ) (F : N Λ) : conjN ((r : ℂ) • F) = (r : ℂ) • conjN F := by
  rw [conjN_smul, Complex.conj_ofReal]

theorem conjN_conjN (F : N Λ) : conjN (conjN F) = F := by
  induction F using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [conjV_conjV]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

variable [DecidableEq Λ]

theorem conjV_ev (a : Sf Λ) : conjV (ev a : V Λ) = ev a := by
  ext b; simp only [conjV_apply, ev, Pi.single_apply]; split_ifs <;> simp

@[simp] theorem conjN_ψ (a : Sf Λ) : conjN (ψ a : N Λ) = ψ a := by
  rw [ψ, conjN_ι, conjV_ev]

@[simp] theorem conjN_psi (x : Λ) : conjN (psi x : N Λ) = psi x := conjN_ψ _

@[simp] theorem conjN_psibar (x : Λ) : conjN (psibar x : N Λ) = psibar x := conjN_ψ _

/-! ### Commutation with real operations -/

theorem conjN_inv' (F : N Λ) : conjN (inv' F) = inv' (conjN F) := by
  induction F using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ε_conjN (F : N Λ) : ε (conjN F) = starRingEnd ℂ (ε F) := by
  induction F using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- A functional is *real* if it commutes with conjugation. -/
def RealDual (φ : Module.Dual ℂ (V Λ)) : Prop := ∀ v, φ (conjV v) = starRingEnd ℂ (φ v)

theorem realDual_coord (a : Sf Λ) : RealDual (coord a : Module.Dual ℂ (V Λ)) := fun _ => rfl

theorem conjN_contractLeft {φ : Module.Dual ℂ (V Λ)} (hφ : RealDual φ) (F : N Λ) :
    conjN (contractLeft φ F) = contractLeft φ (conjN F) := by
  induction F using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [contractLeft_ι, hφ m]
  | mul a b ha hb =>
    rw [contractLeft_mul, map_mul, contractLeft_mul, map_add, map_mul, map_mul, ha, hb,
      conjN_inv']
  | add a b ha hb => simp only [map_add, ha, hb]

theorem conjN_D (a : Sf Λ) (F : N Λ) : conjN (D a F) = D a (conjN F) :=
  conjN_contractLeft (realDual_coord a) F

theorem conjN_contr {n : ℕ} (φ : Fin n → Module.Dual ℂ (V Λ)) (hφ : ∀ i, RealDual (φ i))
    (F : N Λ) : conjN (contr φ F) = contr φ (conjN F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [contr_succ, contr_succ, ih (Fin.tail φ) (fun i => hφ _), conjN_contractLeft (hφ 0)]

theorem conjN_Dseq {n : ℕ} (z : Fin n → Sf Λ) (F : N Λ) : conjN (Dseq z F) = Dseq z (conjN F) :=
  conjN_contr _ (fun i => realDual_coord (z i)) F

@[simp] theorem coeff_conjN (F : N Λ) {n : ℕ} (z : Fin n → Sf Λ) :
    coeff (conjN F) z = starRingEnd ℂ (coeff F z) := by
  rw [coeff, ← conjN_Dseq, ε_conjN, coeff]

/-- A linear map of generators is *real* if it commutes with conjugation. -/
def RealLin {Λ' : Type*} (f : V Λ →ₗ[ℂ] V Λ') : Prop := ∀ v, f (conjV v) = conjV (f v)

theorem conjN_map {Λ' : Type*} {f : V Λ →ₗ[ℂ] V Λ'} (hf : RealLin f) (F : N Λ) :
    conjN (ExteriorAlgebra.map f F) = ExteriorAlgebra.map f (conjN F) := by
  induction F using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp [ExteriorAlgebra.map_apply_ι, hf m]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem realLin_thetaV : RealLin (thetaV : V Λ →ₗ[ℂ] V (Λ ⊕ Λ)) := fun _ => rfl

theorem realLin_inlV : RealLin (inlV : V Λ →ₗ[ℂ] V (Λ ⊕ Λ)) := fun v => by
  ext ⟨b, σ⟩; cases b <;> simp [inlV]

theorem realLin_projV : RealLin (projV : V (Λ ⊕ Λ) →ₗ[ℂ] V Λ) := fun _ => rfl

theorem conjN_theta (F : N Λ) : conjN (theta F) = theta (conjN F) := conjN_map realLin_thetaV F

theorem conjN_proj (F : N (Λ ⊕ Λ)) : conjN (proj F) = proj (conjN F) := conjN_map realLin_projV F

/-! ### Gaussian expectations for real covariances -/

/-- The exponential of a nilpotent endomorphism commutes with every additive map commuting with
the endomorphism. -/
theorem exp_apply_comm {M M' : Type*} [AddCommGroup M] [Module ℂ M] [Module ℚ M]
    [AddCommGroup M'] [Module ℂ M'] [Module ℚ M'] {f : Module.End ℂ M} {f' : Module.End ℂ M'}
    (hf : IsNilpotent f) (hf' : IsNilpotent f') (g : M →+ M') (h : ∀ m, g (f m) = f' (g m))
    (m : M) : g (IsNilpotent.exp f m) = IsNilpotent.exp f' (g m) := by
  obtain ⟨k, hk⟩ := hf
  obtain ⟨l, hl⟩ := hf'
  have hk' : f ^ max k l = 0 := pow_eq_zero_of_le (le_max_left _ _) hk
  have hl' : f' ^ max k l = 0 := pow_eq_zero_of_le (le_max_right _ _) hl
  have hp : ∀ i : ℕ, g ((f ^ i) m) = (f' ^ i) (g m) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]
  rw [IsNilpotent.exp_eq_sum hk', IsNilpotent.exp_eq_sum hl', LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_rat_smul, hp]

variable [Fintype Λ]

theorem conjN_Lζ (C : Matrix Λ Λ ℝ) (F : N (Λ ⊕ Λ)) : conjN (Lζ C F) = Lζ C (conjN F) := by
  simp only [Lζ_apply, map_sum, conjN_ofReal_smul, conjN_D]

theorem conjN_EC (C : Matrix Λ Λ ℝ) (F : N (Λ ⊕ Λ)) : conjN (EC C F) = EC C (conjN F) := by
  rw [EC, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, conjN_proj]
  congr 1
  exact exp_apply_comm (Lζ_isNilpotent C) (Lζ_isNilpotent C) conjN.toAddMonoidHom
    (fun m => conjN_Lζ C m) F

/-! ### The subalgebras `𝒩(X)` -/

theorem conjN_mem_NX {X : Set Λ} {F : N Λ} (hF : F ∈ NX X) : conjN F ∈ NX X := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [conjN_ψ]
    exact Algebra.subset_adjoin ⟨a, rfl⟩
  | algebraMap r => rw [conjN_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end

/-! ### Norms -/

section Norm

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- The complex conjugate of a test function. -/
def conjT (g : TestFn X) : TestFn X := fun n z => starRingEnd ℂ (g n z)

theorem nab_conjT {n : ℕ} (α : Fin n → E → ℕ) (g : TestFn X) (z : Fin n → Sf X) :
    nab α (conjT g n) z = starRingEnd ℂ (nab α (g n) z) :=
  nabla_comp_linear _ α Complex.conjAe.toAlgHom.toLinearMap (g n) z

theorem phiNorm_conjT (g : TestFn X) : phiNorm E p h ℓ (conjT g) = phiNorm E p h ℓ g := by
  simp only [phiNorm, phiTerm, nab_conjT, Complex.norm_conj]

theorem pair_conjN (F : N X) (g : TestFn X) :
    pair (conjN F) g = starRingEnd ℂ (pair F (conjT g)) := by
  simp [pair, conjT, map_sum, map_mul, map_inv₀, map_natCast]

theorem tNorm_conjN_le (F : N X) : tNorm E p h ℓ (conjN F) ≤ tNorm E p h ℓ F := by
  refine iSup₂_le fun g hg => ?_
  rw [pair_conjN, Complex.norm_conj]
  exact le_tNorm F (by rwa [phiNorm_conjT])

/-- **The `T` norms are invariant under conjugation.** -/
theorem tNorm_conjN (F : N X) : tNorm E p h ℓ (conjN F) = tNorm E p h ℓ F :=
  le_antisymm (tNorm_conjN_le F) (by simpa [conjN_conjN] using tNorm_conjN_le (conjN F))

theorem Tj_conjN {d : ℕ} [AddAction (Dir d → ℕ) X] (L : ℝ) (j : ℕ) (ℓ : ℝ) (F : N X) :
    Tj d L j ℓ (conjN F) = Tj d L j ℓ F := tNorm_conjN F

end Norm

end Grassmann
