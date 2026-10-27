import Step.ContinuityAux
import Step.FRDCov

/-!
# Continuity of the renormalisation group map in the covariance (Theorem `thm:step`)

The maps `(V_j, K_j) ↦ (u_{j+1}, V_{j+1}, K_{j+1})` depend continuously on the covariance
`C_{j+1}`, hence on `m² ≥ 0` (`Knext_continuousOn_msq`, `uVnext_continuousOn_msq`).
Since the Grassmann algebra carries no topology here, continuity of an element-valued map is
stated coefficient-wise: every coefficient `F_z` (`Grassmann.coeff`) is continuous.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

open Coup

/-! ### Auxiliary results -/

/-- `V(X)` is coefficient-wise continuous if the coupling constants are continuous. -/
theorem CC.eval {S : Set ℝ} {W : ℝ → Vcoup} (hz : ContinuousOn (fun m => (W m).z) S)
    (hy : ContinuousOn (fun m => (W m).y) S) (ha : ContinuousOn (fun m => (W m).a) S)
    (hb : ContinuousOn (fun m => (W m).b) S) (X : Finset (Lam d L N)) :
    CC S (fun m => (W m).eval X) := by
  simp only [eval_eq_sum, Vsum]
  exact CC.sum _ fun x _ => (((CC.smul hy (CC.const _)).add
    (CC.smul (hz.div_const 2) (CC.const _))).add (CC.smul ha (CC.const _))).add
    (CC.smul hb (CC.const _))

/-- `(u, V) ↦ u|B| + V(B)` as a linear map on `ℂ^5`. -/
def PhiB (B : Finset (Lam d L N)) : (Fin 5 → ℂ) →ₗ[ℂ] Alg d L N where
  toFun c := (c 0 * B.card) • (1 : Alg d L N) + (⟨c 1, c 2, c 3, c 4⟩ : Vcoup).eval B
  map_add' c c' := by
    have := eval_lin 1 1 (⟨c 1, c 2, c 3, c 4⟩ : Vcoup) ⟨c' 1, c' 2, c' 3, c' 4⟩ B
    simp only [Vlin, one_mul, one_smul] at this
    simp only [Pi.add_apply, this, add_mul, add_smul]
    abel
  map_smul' r c := by
    have := eval_lin r 0 (⟨c 1, c 2, c 3, c 4⟩ : Vcoup) ⟨0, 0, 0, 0⟩ B
    simp only [Vlin, mul_zero, add_zero, zero_smul] at this
    simp only [Pi.smul_apply, smul_eq_mul, this, RingHom.id_apply, smul_add, mul_assoc, smul_smul]

/-- The coupling constants as a vector. -/
def cvec (p : ℂ × Vcoup) : Fin 5 → ℂ := ![p.1, p.2.z, p.2.y, p.2.a, p.2.b]

theorem PhiB_cvec (B : Finset (Lam d L N)) (u : ℂ) (V : Vcoup) :
    PhiB B (cvec (u, V)) = (u * B.card) • (1 : Alg d L N) + V.eval B := by
  cases V; rfl

theorem PhiB_injective (hd : 1 ≤ d) (hLN : 3 ≤ L ^ N) {B : Finset (Lam d L N)}
    (hB : B.Nonempty) (hBp : Patch B) : Function.Injective (PhiB B) := by
  intro c c' h
  obtain ⟨h0, hV⟩ := coup_injective hd hLN hB hBp (V := ⟨c 1, c 2, c 3, c 4⟩)
    (V' := ⟨c' 1, c' 2, c' 3, c' 4⟩) h
  simp only [Vcoup.mk.injEq] at hV
  obtain ⟨h1, h2, h3, h4⟩ := hV
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- A linear left inverse of `(u, V) ↦ u|B| + V(B)`: it recovers `coupOf F B` from `F`. -/
theorem exists_coupInv (hd : 1 ≤ d) (hLN : 3 ≤ L ^ N) {B : Finset (Lam d L N)}
    (hB : B.Nonempty) (hBp : Patch B) :
    ∃ Ψ : Alg d L N →ₗ[ℂ] (Fin 5 → ℂ), ∀ F ∈ VXspace B, Ψ F = cvec (coupOf F B) := by
  obtain ⟨Ψ, hΨ⟩ := (PhiB B).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (PhiB_injective hd hLN hB hBp))
  refine ⟨Ψ, fun F hF => ?_⟩
  have h := LinearMap.congr_fun hΨ (cvec (coupOf F B))
  rw [LinearMap.comp_apply, PhiB_cvec, ← coupOf_spec hF] at h
  exact h

/-- Continuity in a parameter, for the coupling constants and the polymer activities, when the
covariance depends continuously on the parameter and is invariant and symmetric. -/
theorem uVnext_continuousOn (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {S : Set ℝ} (Cm : ℝ → Matrix (Lam d L N) (Lam d L N) ℝ)
    (hC : ∀ x y, ContinuousOn (fun m => Cm m x y) S) (hinv : ∀ m ∈ S, CovInv (Cm m))
    (hsym : ∀ m ∈ S, ∀ x y, Cm m x y = Cm m y x) (V : Vcoup) {K : Act d L N} (hK : InK j K) :
    ContinuousOn (fun m => (uVnext j (Cm m) V K).1) S ∧
      ContinuousOn (fun m => (uVnext j (Cm m) V K).2.z) S ∧
      ContinuousOn (fun m => (uVnext j (Cm m) V K).2.y) S ∧
      ContinuousOn (fun m => (uVnext j (Cm m) V K).2.a) S ∧
      ContinuousOn (fun m => (uVnext j (Cm m) V K).2.b) S := by
  have h3 : 3 ≤ L := le_trans (by
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)) hL
  have hLN : 3 ≤ L ^ N := h3.trans (Nat.le_self_pow (by omega) L)
  obtain ⟨Ψ, hΨ⟩ := exists_coupInv hd hLN (mem_blockIdx.1 (zero_mem_blockIdx j))
    (patch_blockSet hj h3 0)
  have hG : CC S (fun m => EC (Cm m) (theta (V.eval (blockSet j 0) - (Qb j K 0 : Alg d L N)))) :=
    CC.EC hC (CC.const _)
  have key : ∀ i : Fin 5, ContinuousOn (fun m => cvec (uVnext j (Cm m) V K) i) S := fun i =>
    (hG.lin ((LinearMap.proj i).comp Ψ)).congr fun m hm => by
      have hmem := EC_theta_VXspace (hinv m hm) (hsym m hm)
        (VXspace_sub (eval_mem_VXspace V _) (Qb_mem hd hL hK (zero_mem_blockIdx j)))
      show _ = LinearMap.proj (R := ℂ) i (Ψ _)
      rw [hΨ _ hmem]
      rfl
  exact ⟨key 0, key 1, key 2, key 3, key 4⟩

theorem Knext_continuousOn (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j < N)
    {S : Set ℝ} (Cm : ℝ → Matrix (Lam d L N) (Lam d L N) ℝ)
    (hC : ∀ x y, ContinuousOn (fun m => Cm m x y) S) (hinv : ∀ m ∈ S, CovInv (Cm m))
    (hsym : ∀ m ∈ S, ∀ x y, Cm m x y = Cm m y x) (V : Vcoup) {K : Act d L N} (hK : InK j K)
    (U : Finset (Lam d L N)) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    ContinuousOn (fun m => coeff (Knext j (Cm m) V K U : Alg d L N) z) S := by
  obtain ⟨hu, hz, hy, ha, hb⟩ := uVnext_continuousOn hd hL hj Cm hC hinv hsym V hK
  have hVE : ∀ X, CCE S (fun m => -(VE (uVnext j (Cm m) V K).2 X : EvR (Lam d L N))) :=
    fun X => CCE.neg (CC.eval hz hy ha hb X)
  have hI : ∀ b, CCE S (fun m => Inext j (Cm m) V K b) := fun b => by
    unfold Inext
    exact CCE.smul (Complex.continuous_exp.comp_continuousOn (hu.mul continuousOn_const).neg)
      (CCE.gexp (hVE _) fun m _ => by simp [eval_ε0])
  have hIP : ∀ X, CCE S (fun m => InextPow j (Cm m) V K X) := fun X => by
    unfold InextPow
    exact CCE.prod _ fun b _ => hI b
  have hdI : ∀ X, CCE S (fun m => dIPow j (Cm m) V K X) := fun X => by
    unfold dIPow dI
    exact CCE.prod _ fun b _ => (CCE.const _).sub (hI b).inclE
  have hKt : ∀ W, CCE S (fun m => Ktil j (Cm m) V K W) := fun W => by
    unfold Ktil
    exact CCE.sum _ fun Y _ => (CCE.const _).mul (hdI Y)
  have hKc : ∀ X, CCE S (fun m => Kchk j (Cm m) V K X) := fun X => by
    unfold Kchk KchkC
    exact CCE.prod _ fun W _ => (hKt W).sub (CCE.const _)
  have hKn : CCE S (fun m => Knext j (Cm m) V K U) := by
    unfold Knext
    exact CCE.smul (Complex.continuous_exp.comp_continuousOn (hu.mul continuousOn_const))
      (CCE.sum _ fun g _ => (hIP _).mul (CCE.ECE hC ((hKc g.2).mul (CCE.const _))))
  exact hKn n z

theorem hC_frd (hd : 3 ≤ d) {j : ℕ} (x y : Lam d L N) :
    ContinuousOn (fun msq => Cfrd d L N msq j x y) (Set.Ici 0) :=
  Cj_continuousOn stdPt (by omega) (Nat.cast_nonneg L) (j + 1) x y

theorem hinv_frd (j : ℕ) : ∀ msq ∈ Set.Ici (0 : ℝ), CovInv (Cfrd d L N msq j) :=
  fun msq _ T hT x y => Cfrd_inv msq j T hT x y

theorem hsym_frd (j : ℕ) :
    ∀ msq ∈ Set.Ici (0 : ℝ), ∀ x y : Lam d L N, Cfrd d L N msq j x y = Cfrd d L N msq j y x :=
  fun msq hm x y => by
    simpa using ((Cj_posSemidef stdPt (Set.mem_Ici.1 hm) (Nat.cast_nonneg L) (j + 1)
      (d := d) (n := L ^ N)).1.apply x y).symm

/-- **Theorem `thm:step`**, continuity in `m² ≥ 0` for the covariances of Section `sec:frd`
(`j + 1 < N`). -/
theorem Knext_continuousOn_msq (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N)
    (V : Vcoup) {K : Act d L N} (hK : InK j K) (U : Finset (Lam d L N)) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) :
    ContinuousOn (fun msq => coeff (Knext j (Cfrd d L N msq j) V K U : Alg d L N) z)
      (Set.Ici 0) := by
  refine Knext_continuousOn (by omega) hL (by omega) (fun msq => Cfrd d L N msq j)
    (hC_frd hd) (hinv_frd j) (hsym_frd j) V hK U z

theorem uVnext_continuousOn_msq (hd : 3 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 1 < N)
    (V : Vcoup) {K : Act d L N} (hK : InK j K) :
    ContinuousOn (fun msq => (uVnext j (Cfrd d L N msq j) V K).1) (Set.Ici 0) ∧
      ContinuousOn (fun msq => (uVnext j (Cfrd d L N msq j) V K).2.z) (Set.Ici 0) ∧
      ContinuousOn (fun msq => (uVnext j (Cfrd d L N msq j) V K).2.y) (Set.Ici 0) ∧
      ContinuousOn (fun msq => (uVnext j (Cfrd d L N msq j) V K).2.a) (Set.Ici 0) ∧
      ContinuousOn (fun msq => (uVnext j (Cfrd d L N msq j) V K).2.b) (Set.Ici 0) := by
  exact uVnext_continuousOn (by omega) hL (by omega) (fun msq => Cfrd d L N msq j)
    (hC_frd hd) (hinv_frd j) (hsym_frd j) V hK

end

end Step
