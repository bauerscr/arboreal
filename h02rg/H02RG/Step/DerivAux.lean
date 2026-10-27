import Step.Hol
import Step.Continuity

/-!
# Holomorphy of the renormalisation group map in `(V_j, K_j)`

* `Vcoup` is made a complex vector space (componentwise operations), so that
  `(V, K) ∈ 𝒱^∅ ⊕ 𝒦_j` can be varied along complex lines `V + t V̇`, `K + t K̇`.
* `InK j` is a linear condition (`InK.add`, `InK.smul`, `InK.zero`, `InK.lin`).
* `Loc_{X,Y}` and `Q(B)` are linear; hence `(V, K) ↦ (u_{j+1}, V_{j+1})` is **linear** on
  `𝒱^∅ ⊕ 𝒦_j` (`uVnext_lin`, `uVnext_line`).
* **Holomorphy** (`Knext_hol`, `uVnext_hol`): if `e ↦ V(e)` and `e ↦ K(e)` are holomorphic
  families (on a complex normed space `E`) with `K(e) ∈ 𝒦_j`, then
  `e ↦ K_{j+1}(V(e), K(e))(U)` is coefficient-wise holomorphic, and so are the coupling
  constants `e ↦ (u_{j+1}, V_{j+1})(V(e), K(e))`.  This is the notion of analyticity of the
  paper ("`F ∘ g` analytic for analytic `g`"), and it shows that `Φ_{j+1}` is entire.
* `DKnext j C V K V̇ K̇ = d/dt K_{j+1}(V + t V̇, K + t K̇)|_{t=0}`, the directional derivative, is
  linear in the direction (`DKnext_lin`), by two-variable holomorphy.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

/-! ### `Vcoup` as a complex vector space -/

/-- The coordinates `(z, y, a, b)` of the coupling constants. -/
def Vcoup.equivP : Vcoup ≃ ℂ × ℂ × ℂ × ℂ where
  toFun V := (V.z, V.y, V.a, V.b)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup Vcoup := Vcoup.equivP.addCommGroup

instance : Module ℂ Vcoup := Vcoup.equivP.module ℂ

namespace Vcoup

theorem ext' {V W : Vcoup} (hz : V.z = W.z) (hy : V.y = W.y) (ha : V.a = W.a) (hb : V.b = W.b) :
    V = W := by
  cases V; cases W; simp_all

@[simp] theorem zero_z : (0 : Vcoup).z = 0 := rfl
@[simp] theorem zero_y : (0 : Vcoup).y = 0 := rfl
@[simp] theorem zero_a : (0 : Vcoup).a = 0 := rfl
@[simp] theorem zero_b : (0 : Vcoup).b = 0 := rfl
@[simp] theorem add_z (V W : Vcoup) : (V + W).z = V.z + W.z := rfl
@[simp] theorem add_y (V W : Vcoup) : (V + W).y = V.y + W.y := rfl
@[simp] theorem add_a (V W : Vcoup) : (V + W).a = V.a + W.a := rfl
@[simp] theorem add_b (V W : Vcoup) : (V + W).b = V.b + W.b := rfl
@[simp] theorem smul_z (c : ℂ) (V : Vcoup) : (c • V).z = c * V.z := rfl
@[simp] theorem smul_y (c : ℂ) (V : Vcoup) : (c • V).y = c * V.y := rfl
@[simp] theorem smul_a (c : ℂ) (V : Vcoup) : (c • V).a = c * V.a := rfl
@[simp] theorem smul_b (c : ℂ) (V : Vcoup) : (c • V).b = c * V.b := rfl

end Vcoup

variable {d L N : ℕ} [NeZero L]

open Coup

theorem eval_add (V W : Vcoup) (X : Finset (Lam d L N)) :
    (V + W).eval X = V.eval X + W.eval X := by
  have h : V + W = Vlin 1 1 V W := Vcoup.ext' (by simp [Vlin]) (by simp [Vlin])
    (by simp [Vlin]) (by simp [Vlin])
  rw [h, eval_lin, one_smul, one_smul]

theorem eval_smul (c : ℂ) (V : Vcoup) (X : Finset (Lam d L N)) :
    (c • V).eval X = c • V.eval X := by
  have h : c • V = Vlin c 0 V 0 := Vcoup.ext' (by simp [Vlin]) (by simp [Vlin])
    (by simp [Vlin]) (by simp [Vlin])
  rw [h, eval_lin, zero_smul, add_zero]

/-! ### Linearity of `Loc` -/

theorem locCoef_add (X : Finset (Lam d L N)) (F G : Alg d L N) :
    locCoef X (F + G) = locCoef X F + locCoef X G := by
  unfold locCoef
  rw [← Matrix.add_vecMul]
  congr 1
  funext β
  simp [mu_add]

theorem locCoef_smul (X : Finset (Lam d L N)) (c : ℂ) (F : Alg d L N) :
    locCoef X (c • F) = c • locCoef X F := by
  unfold locCoef
  rw [← Matrix.smul_vecMul]
  congr 1
  funext β
  simp [mu_smul]

/-- `Loc_{X,Y}` as a linear map. -/
def LocL (X Y : Finset (Lam d L N)) : Alg d L N →ₗ[ℂ] Alg d L N where
  toFun := LocXY X Y
  map_add' F G := by
    simp only [LocXY, map_add, locCoef_add, Pi.add_apply, add_smul, sum_add_distrib, add_mul,
      add_div]
    abel
  map_smul' c F := by
    simp only [LocXY, map_smul, locCoef_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      smul_add, smul_sum, smul_smul]
    congr 1
    ring_nf

/-- `Loc_{X,Y}` on even elements as a linear map. -/
def LocEL (X Y : Finset (Lam d L N)) : EvR (Lam d L N) →ₗ[ℂ] EvR (Lam d L N) where
  toFun := LocE X Y
  map_add' F G := Subtype.ext (by simp only [coe_LocE, Subalgebra.coe_add]; exact map_add (LocL X Y) _ _)
  map_smul' c F := Subtype.ext (by
    simp only [coe_LocE, Subalgebra.coe_smul, RingHom.id_apply]; exact map_smul (LocL X Y) _ _)

theorem LocE_add (X Y : Finset (Lam d L N)) (F G : EvR (Lam d L N)) :
    LocE X Y (F + G) = LocE X Y F + LocE X Y G := map_add (LocEL X Y) F G

theorem LocE_smul (X Y : Finset (Lam d L N)) (c : ℂ) (F : EvR (Lam d L N)) :
    LocE X Y (c • F) = c • LocE X Y F := map_smul (LocEL X Y) c F

/-! ### `𝒦_j` is a linear space -/

theorem InK.zero (j : ℕ) : InK j (0 : Act d L N) where
  loc X _ := by simp [zero_mem]
  sym X _ := fun n z _ => by simp
  jinv X _ := by simp
  aut T _ _ X _ := by simp

theorem InK.add {j : ℕ} {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') : InK j (K + K') where
  loc X hX := by simpa using add_mem (hK.loc X hX) (hK'.loc X hX)
  sym X hX := fun n z hz => by simp [hK.sym X hX n z hz, hK'.sym X hX n z hz]
  jinv X hX := by simp [hK.jinv X hX, hK'.jinv X hX]
  aut T hT hP X hX := by simp [hK.aut T hT hP X hX, hK'.aut T hT hP X hX]

theorem InK.smul {j : ℕ} {K : Act d L N} (hK : InK j K) (c : ℂ) : InK j (c • K) where
  loc X hX := by simpa using Subalgebra.smul_mem _ (hK.loc X hX) c
  sym X hX := fun n z hz => by simp [hK.sym X hX n z hz]
  jinv X hX := by simp [hK.jinv X hX]
  aut T hT hP X hX := by simp [hK.aut T hT hP X hX]

theorem InK.lin {j : ℕ} {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') (a b : ℂ) :
    InK j (a • K + b • K') := (hK.smul a).add (hK'.smul b)

/-! ### Linearity of `Q` and of the coupling constants -/

theorem Qb_lin (j : ℕ) (K K' : Act d L N) (a b : ℂ) (bb : Fin d → ℕ) :
    Qb j (a • K + b • K') bb = a • Qb j K bb + b • Qb j K' bb := by
  classical
  unfold Step.Qb
  split_ifs
  · simp only [Pi.add_apply, Pi.smul_apply, LocE_add, LocE_smul, sum_add_distrib, smul_sum]
  · simp

/-- The coupling constants as a vector (`cvec`) are linear and injective. -/
theorem cvec_lin (a b : ℂ) (p q : ℂ × Vcoup) : cvec (a • p + b • q) = a • cvec p + b • cvec q := by
  funext i
  fin_cases i <;> simp [cvec]

theorem cvec_injective : Function.Injective (cvec : ℂ × Vcoup → Fin 5 → ℂ) := by
  intro p q h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  have h2 := congr_fun h 2
  have h3 := congr_fun h 3
  have h4 := congr_fun h 4
  simp [cvec] at h0 h1 h2 h3 h4
  exact Prod.ext h0 (Vcoup.ext' h1 h2 h3 h4)

theorem three_le_L (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) : 3 ≤ L := le_trans (by
  calc 3 ≤ 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)) hL

/-- The map `𝔼_C θ (V(B) - Q(B))` of `e:V+-def`. -/
theorem Gnext_lin (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V W : Vcoup) (K K' : Act d L N)
    (a b : ℂ) :
    EC C (theta ((a • V + b • W).eval (blockSet j 0) - (Qb j (a • K + b • K') 0 : Alg d L N))) =
      a • EC C (theta (V.eval (blockSet j 0) - (Qb j K 0 : Alg d L N))) +
        b • EC C (theta (W.eval (blockSet j 0) - (Qb j K' 0 : Alg d L N))) := by
  rw [Qb_lin, eval_add, eval_smul, eval_smul]
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, map_sub, map_add, map_smul, smul_sub]
  abel

/-- **The coupling constants `(u_{j+1}, V_{j+1})` are linear in `(V_j, K_j) ∈ 𝒱^∅ ⊕ 𝒦_j`.** -/
theorem uVnext_lin (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V W : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') (a b : ℂ) :
    uVnext j C (a • V + b • W) (a • K + b • K') = a • uVnext j C V K + b • uVnext j C W K' := by
  have hLN : 3 ≤ L ^ N := (three_le_L hd hL).trans (Nat.le_self_pow (by omega) L)
  obtain ⟨Ψ, hΨ⟩ := exists_coupInv hd hLN (mem_blockIdx.1 (zero_mem_blockIdx j))
    (patch_blockSet hj (three_le_L hd hL) 0)
  have hmem : ∀ (V : Vcoup) {K : Act d L N}, InK j K →
      EC C (theta (V.eval (blockSet j 0) - (Qb j K 0 : Alg d L N))) ∈ VXspace (blockSet j 0) :=
    fun V K hK => EC_theta_VXspace hC hCs
      (VXspace_sub (eval_mem_VXspace V _) (Qb_mem hd hL hK (zero_mem_blockIdx j)))
  refine cvec_injective ?_
  rw [cvec_lin]
  unfold uVnext
  rw [← hΨ _ (hmem _ (hK.lin hK' a b)), ← hΨ _ (hmem V hK), ← hΨ _ (hmem W hK'), Gnext_lin,
    map_add, map_smul, map_smul]

theorem uVnext_line (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V V' : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') (t : ℂ) :
    uVnext j C (V + t • V') (K + t • K') = uVnext j C V K + t • uVnext j C V' K' := by
  simpa using uVnext_lin hd hL hj hC hCs V V' hK hK' 1 t


/-! ### Holomorphic families -/

section HolFam

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A holomorphic family of coupling constants. -/
structure HolV (W : E → Vcoup) : Prop where
  z : Differentiable ℂ fun e => (W e).z
  y : Differentiable ℂ fun e => (W e).y
  a : Differentiable ℂ fun e => (W e).a
  b : Differentiable ℂ fun e => (W e).b

/-- A (coefficient-wise) holomorphic family of polymer activities. -/
def HolK (K : E → Act d L N) : Prop := ∀ X, HolE (fun e => K e X)

theorem HolV.eval {W : E → Vcoup} (hW : HolV W) (X : Finset (Lam d L N)) :
    Hol (fun e => (W e).eval X) := by
  have hz2 : Differentiable ℂ fun e => (W e).z / 2 := by
    simpa [div_eq_mul_inv] using hW.z.mul_const (2⁻¹ : ℂ)
  simp only [eval_eq_sum, Vsum]
  exact Hol.sum _ fun x _ => (((Hol.smul hW.y (Hol.const _)).add
    (Hol.smul hz2 (Hol.const _))).add (Hol.smul hW.a (Hol.const _))).add
    (Hol.smul hW.b (Hol.const _))

theorem HolV.VE {W : E → Vcoup} (hW : HolV W) (X : Finset (Lam d L N)) :
    HolE (fun e => VE (W e) X) := hW.eval X

theorem HolK.LocE {K : E → Act d L N} (hK : HolK K) (X Y Z : Finset (Lam d L N)) :
    HolE (fun e => LocE Y Z (K e X)) := (hK X).map (LocEL Y Z)

theorem HolK.Qb {K : E → Act d L N} (hK : HolK K) (j : ℕ) (b : Fin d → ℕ) :
    HolE (fun e => Qb j (K e) b) := by
  classical
  unfold Step.Qb
  split_ifs
  · exact HolE.sum _ fun X _ => hK.LocE _ _ _
  · exact HolE.const _

theorem HolK.Jb {K : E → Act d L N} (hK : HolK K) (j : ℕ) (b : Fin d → ℕ)
    (X : Finset (Lam d L N)) : HolE (fun e => Jb j (K e) b X) := by
  classical
  unfold Step.Jb
  split_ifs
  · exact (HolE.sum _ fun Y _ => hK.LocE _ _ _).neg
  · exact hK.LocE _ _ _
  · exact HolE.const _

theorem HolK.Kext {K : E → Act d L N} (hK : HolK K) (j : ℕ) (X : Finset (Lam d L N)) :
    HolE (fun e => Kext j (K e) X) := by
  unfold Step.Kext
  exact HolE.prod _ fun Y _ => hK Y

/-- **Holomorphy of the coupling constants**: `e ↦ (u_{j+1}, V_{j+1})(V(e), K(e))` is holomorphic
for holomorphic families `V(e)`, `K(e) ∈ 𝒦_j`. -/
theorem uVnext_hol (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    {W : E → Vcoup} {K : E → Act d L N} (hW : HolV W) (hK : HolK K) (hKj : ∀ e, InK j (K e)) :
    Differentiable ℂ (fun e => (uVnext j C (W e) (K e)).1) ∧
      HolV (fun e => (uVnext j C (W e) (K e)).2) := by
  have hLN : 3 ≤ L ^ N := (three_le_L hd hL).trans (Nat.le_self_pow (by omega) L)
  obtain ⟨Ψ, hΨ⟩ := exists_coupInv hd hLN (mem_blockIdx.1 (zero_mem_blockIdx j))
    (patch_blockSet hj (three_le_L hd hL) 0)
  have hG : Hol (fun e => EC C (theta ((W e).eval (blockSet j 0) -
      (Qb j (K e) 0 : Alg d L N)))) :=
    Hol.EC C (((hW.eval _).sub (hK.Qb j 0)).map theta.toLinearMap)
  have key : ∀ i : Fin 5, Differentiable ℂ (fun e => cvec (uVnext j C (W e) (K e)) i) := by
    intro i
    have h := hG.lin ((LinearMap.proj i).comp Ψ)
    have e : (fun e => ((LinearMap.proj i).comp Ψ) (EC C (theta ((W e).eval (blockSet j 0) -
        (Qb j (K e) 0 : Alg d L N))))) = fun e => cvec (uVnext j C (W e) (K e)) i := by
      funext e
      have hmem := EC_theta_VXspace hC hCs
        (VXspace_sub (eval_mem_VXspace (W e) _) (Qb_mem hd hL (hKj e) (zero_mem_blockIdx j)))
      show LinearMap.proj (R := ℂ) i (Ψ _) = _
      rw [hΨ _ hmem]
      rfl
    rwa [e] at h
  exact ⟨key 0, ⟨key 1, key 2, key 3, key 4⟩⟩

/-- **Holomorphy of `K_{j+1}`**: `e ↦ K_{j+1}(V(e), K(e))(U)` is coefficient-wise holomorphic
for holomorphic families `V(e)`, `K(e) ∈ 𝒦_j`. -/
theorem Knext_hol (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    {W : E → Vcoup} {K : E → Act d L N} (hW : HolV W) (hK : HolK K) (hKj : ∀ e, InK j (K e))
    (U : Finset (Lam d L N)) : HolE (fun e => Knext j C (W e) (K e) U) := by
  obtain ⟨hu, hU⟩ := uVnext_hol hd hL hj hC hCs hW hK hKj
  have hI : ∀ b, HolE (fun e => Inext j C (W e) (K e) b) := fun b => by
    unfold Inext
    exact HolE.smul ((hu.mul (differentiable_const _)).neg.cexp)
      (HolE.gexp (hU.VE _).neg fun e => by simp [eval_ε0])
  have hIP : ∀ X, HolE (fun e => InextPow j C (W e) (K e) X) := fun X => by
    unfold InextPow
    exact HolE.prod _ fun b _ => hI b
  have hdI : ∀ X, HolE (fun e => dIPow j C (W e) (K e) X) := fun X => by
    unfold dIPow dI
    exact HolE.prod _ fun b _ =>
      (HolE.gexp (hW.VE _).neg fun e => by simp [eval_ε0]).thetaE.sub (hI b).inclE
  have hKt : ∀ Z, HolE (fun e => Ktil j C (W e) (K e) Z) := fun Z => by
    unfold Ktil
    exact HolE.sum _ fun Y _ => (hK.Kext j _).thetaE.mul (hdI Y)
  have hKc : ∀ X, HolE (fun e => Kchk j C (W e) (K e) X) := fun X => by
    unfold Kchk KchkC
    exact HolE.prod _ fun Z _ => (hKt Z).sub (HolE.sum _ fun b _ => (hK.Jb j b Z).thetaE)
  unfold Knext
  exact HolE.smul (hu.mul (differentiable_const _)).cexp
    (HolE.sum _ fun g _ => (hIP _).mul (HolE.ECE C ((hKc g.2).mul
      (HolE.prod _ fun p _ => (hK.Jb j p.1 p.2).thetaE))))


/-! ### Lines, planes and directional derivatives -/

theorem HolV.plane (V V₁ V₂ : Vcoup) : HolV (fun p : ℂ × ℂ => V + p.1 • V₁ + p.2 • V₂) := by
  have h : ∀ c c₁ c₂ : ℂ, Differentiable ℂ fun p : ℂ × ℂ => c + p.1 * c₁ + p.2 * c₂ :=
    fun c c₁ c₂ => ((differentiable_const _).add (differentiable_fst.mul_const _)).add
      (differentiable_snd.mul_const _)
  exact ⟨by simpa using h V.z V₁.z V₂.z, by simpa using h V.y V₁.y V₂.y,
    by simpa using h V.a V₁.a V₂.a, by simpa using h V.b V₁.b V₂.b⟩

theorem HolK.plane (K K₁ K₂ : Act d L N) :
    HolK (fun p : ℂ × ℂ => K + p.1 • K₁ + p.2 • K₂) := fun X => by
  have h : Hol (fun p : ℂ × ℂ => (K X : Alg d L N) + p.1 • (K₁ X : Alg d L N) +
      p.2 • (K₂ X : Alg d L N)) :=
    ((Hol.const _).add (Hol.smul differentiable_fst (Hol.const _))).add
      (Hol.smul differentiable_snd (Hol.const _))
  refine h.congr fun p => ?_
  simp

theorem HolV.line (V V' : Vcoup) : HolV (fun t : ℂ => V + t • V') := by
  have h : ∀ c c' : ℂ, Differentiable ℂ fun t : ℂ => c + t * c' :=
    fun c c' => (differentiable_const _).add (differentiable_id.mul_const _)
  exact ⟨by simp [h V.z V'.z], by simp [h V.y V'.y], by simp [h V.a V'.a],
    by simp [h V.b V'.b]⟩

theorem HolK.line (K K' : Act d L N) : HolK (fun t : ℂ => K + t • K') := fun X => by
  have h : Hol (fun t : ℂ => (K X : Alg d L N) + t • (K' X : Alg d L N)) :=
    (Hol.const _).add (Hol.smul differentiable_id (Hol.const _))
  refine h.congr fun p => ?_
  simp

/-- The directional derivative `D_{(V̇, K̇)} K_{j+1}|_{(V, K)} = d/dt K_{j+1}(V + t V̇, K + t K̇)|_{t=0}`
(as a polymer activity at scale `j + 1`). -/
def DKnext (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (V' : Vcoup) (K' : Act d L N) : Act d L N :=
  fun U => derivE (fun t : ℂ => Knext j C (V + t • V') (K + t • K') U) 0

theorem Knext_line_hol (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V V' : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') (U : Finset (Lam d L N)) :
    HolE (fun t : ℂ => Knext j C (V + t • V') (K + t • K') U) :=
  Knext_hol hd hL hj hC hCs (HolV.line V V') (HolK.line K K') (fun t => hK.add (hK'.smul t)) U

theorem pair_DKnext (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V V' : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') (U : Finset (Lam d L N))
    (g : TestFn (Lam d L N)) :
    pair (DKnext j C V K V' K' U : Alg d L N) g =
      deriv (fun t : ℂ => pair (Knext j C (V + t • V') (K + t • K') U : Alg d L N) g) 0 :=
  pair_derivE (Knext_line_hol hd hL hj hC hCs V V' hK hK' U) g 0

theorem coeff_DKnext (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V V' : Vcoup) {K K' : Act d L N} (hK : InK j K) (hK' : InK j K') (U : Finset (Lam d L N))
    {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff (DKnext j C V K V' K' U : Alg d L N) z =
      deriv (fun t : ℂ => coeff (Knext j C (V + t • V') (K + t • K') U : Alg d L N) z) 0 :=
  coeff_derivE (Knext_line_hol hd hL hj hC hCs V V' hK hK' U) 0 z

/-- The derivative along a line through `0` in `ℂ²` is the Fréchet derivative. -/
theorem deriv_line2 {φ : ℂ × ℂ → ℂ} (hφ : Differentiable ℂ φ) (a b : ℂ) :
    deriv (fun t : ℂ => φ (t * a, t * b)) 0 = fderiv ℂ φ 0 (a, b) := by
  have h1 : HasDerivAt (fun t : ℂ => (t * a, t * b)) (a, b) 0 := by
    simpa using (hasDerivAt_mul_const a).prodMk (hasDerivAt_mul_const b)
  have h2 : HasFDerivAt φ (fderiv ℂ φ 0) ((fun t : ℂ => (t * a, t * b)) 0) := by
    have e0 : (fun t : ℂ => (t * a, t * b)) 0 = 0 := by simp
    rw [e0]; exact (hφ 0).hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

/-- **The derivative `D K_{j+1}|_{(V,K)}` is linear in the direction.** -/
theorem DKnext_lin (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : CovInv C) (hCs : ∀ x y, C x y = C y x)
    (V V₁ V₂ : Vcoup) {K K₁ K₂ : Act d L N} (hK : InK j K) (hK₁ : InK j K₁) (hK₂ : InK j K₂)
    (a b : ℂ) :
    DKnext j C V K (a • V₁ + b • V₂) (a • K₁ + b • K₂) =
      a • DKnext j C V K V₁ K₁ + b • DKnext j C V K V₂ K₂ := by
  funext U
  apply Subtype.ext
  refine ext_coeff fun n z => ?_
  set φ : ℂ × ℂ → ℂ := fun p => coeff (Knext j C (V + p.1 • V₁ + p.2 • V₂)
    (K + p.1 • K₁ + p.2 • K₂) U : Alg d L N) z with hφdef
  have hφ : Differentiable ℂ φ := Knext_hol hd hL hj hC hCs (HolV.plane V V₁ V₂)
    (HolK.plane K K₁ K₂) (fun p => (hK.add (hK₁.smul _)).add (hK₂.smul _)) U n z
  have e : ∀ a b : ℂ, coeff (DKnext j C V K (a • V₁ + b • V₂) (a • K₁ + b • K₂) U : Alg d L N) z
      = fderiv ℂ φ 0 (a, b) := by
    intro a b
    rw [coeff_DKnext hd hL hj hC hCs V _ hK (hK₁.lin hK₂ a b), ← deriv_line2 hφ a b]
    congr 1
    funext t
    simp only [hφdef, smul_add, smul_smul, add_assoc]
  have h1 : DKnext j C V K V₁ K₁ = DKnext j C V K ((1 : ℂ) • V₁ + (0 : ℂ) • V₂)
      ((1 : ℂ) • K₁ + (0 : ℂ) • K₂) := by simp
  have h2 : DKnext j C V K V₂ K₂ = DKnext j C V K ((0 : ℂ) • V₁ + (1 : ℂ) • V₂)
      ((0 : ℂ) • K₁ + (1 : ℂ) • K₂) := by simp
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Subalgebra.coe_add, Subalgebra.coe_smul,
    Subalgebra.coe_smul, coeff_add, coeff_smul, coeff_smul, h1, h2, e, e, e]
  have hab : ((a, b) : ℂ × ℂ) = a • ((1 : ℂ), (0 : ℂ)) + b • ((0 : ℂ), (1 : ℂ)) := by
    ext <;> simp
  rw [hab, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end HolFam

end

end Step
