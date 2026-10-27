import Step2.Coup.CoupQuad2

/-!
# Degree bounds (`h02uv-outline.tex`, Proposition `prop:C4b`(b))

`DegLe n F`: all coefficients of `F` of order `> n` vanish.

* `DegLe.mul`: degrees add under products;
* `DegLe.lop`: `𝓛_C` lowers the degree by `2`; `DegLe.exp_sub`: `e^{𝓛_C} F - F` has degree
  `≤ n` if `F` has degree `≤ n + 2`;
* `DegLe.fc`: `F_C(A, B)` has degree `≤ n + m + 2` if `A`, `B` have degrees `≤ n + 2`, `m + 2`;
* `mu4_of_degLe`: the quartic pairing vanishes on polynomials of degree `≤ 3`.

Consequence (`FlowSeq.betaQ_self_g_quad`): in `q_{j,j}` the `g`-component of a pair of quadratic
couplings vanishes. So there are no `ν²`, `νz`, … terms in the `g`-flow.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Matrix

section General

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem degLe_psiPow {m : ℕ} (z : Fin m → Sf I) : DegLe m (psiPow z) :=
  fun k w hk => coeff_ιMulti_of_ne _ w (by omega)

theorem degLe_one (n : ℕ) : DegLe n (1 : N I) := by
  intro m z hm
  have : (1 : N I) = ExteriorAlgebra.ιMulti ℂ 0 (Fin.elim0 : Fin 0 → V I) := by
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  rw [this]
  exact coeff_ιMulti_of_ne _ _ (by omega)

/-- **Degrees add under products.** -/
theorem _root_.Grassmann.DegLe.mul {n n' : ℕ} {x y : N I} (hx : DegLe n x) (hy : DegLe n' y) :
    DegLe (n + n') (x * y) := by
  rw [sum_coeff x, sum_coeff y, sum_mul]
  refine DegLe.sum _ fun m _ => ?_
  rw [sum_mul]
  refine DegLe.sum _ fun z _ => ?_
  rw [mul_sum]
  refine DegLe.sum _ fun m' _ => ?_
  rw [mul_sum]
  refine DegLe.sum _ fun w _ => ?_
  rw [smul_mul_smul_comm, psiPow_mul_psiPow]
  by_cases hm : m ≤ n
  · by_cases hm' : m' ≤ n'
    · exact ((degLe_psiPow _).mono (by omega)).smul _
    · rw [hy m' w (by omega), mul_zero, mul_zero, zero_smul]; exact DegLe.zero _
  · rw [hx m z (by omega), mul_zero, zero_mul, zero_smul]; exact DegLe.zero _

variable (C : Matrix I I ℂ)

/-- `𝓛_C` lowers the degree by `2`. -/
theorem _root_.Grassmann.DegLe.lop {n : ℕ} {F : N I} (hF : DegLe (n + 2) F) : DegLe n (Grassmann.LopC C F) := by
  rw [Grassmann.LopC_apply]
  exact DegLe.sum _ fun x _ => DegLe.sum _ fun y _ => ((hF.D _).D _).smul _

theorem _root_.Grassmann.DegLe.lop' {n : ℕ} {F : N I} (hF : DegLe n F) : DegLe n (Grassmann.LopC C F) :=
  ((hF.mono (by omega : n ≤ n + 2)).lop C)

theorem _root_.Grassmann.DegLe.lopPow {n : ℕ} {F : N I} (hF : DegLe n F) : ∀ i, DegLe n ((Grassmann.LopC C ^ i) F)
  | 0 => by simpa using hF
  | i + 1 => by rw [pow_succ', Module.End.mul_apply]; exact (hF.lopPow i).lop' C

/-- `e^{𝓛_C} F - F` has degree `≤ n` if `F` has degree `≤ n + 2`. -/
theorem _root_.Grassmann.DegLe.exp_sub {n : ℕ} {F : N I} (hF : DegLe (n + 2) F) :
    DegLe n (Grassmann.expLC C F - F) := by
  obtain ⟨k, hk⟩ := Grassmann.LopC_isNilpotent C
  have hk' : LopC C ^ (k + 1) = 0 := pow_eq_zero_of_le (Nat.le_succ k) hk
  rw [Grassmann.expLC, IsNilpotent.exp_eq_sum hk', LinearMap.sum_apply, sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Module.End.one_apply, add_sub_cancel_right]
  refine DegLe.sum _ fun i _ => ?_
  rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ, pow_succ, Module.End.mul_apply]
  exact ((hF.lop C).lopPow C i).smul _

theorem _root_.Grassmann.DegLe.exp {n : ℕ} {F : N I} (hF : DegLe n F) : DegLe n (Grassmann.expLC C F) := by
  have h := (hF.mono (by omega : n ≤ n + 2)).exp_sub C
  have : expLC C F = (Grassmann.expLC C F - F) + F := by abel
  rw [this]; exact h.add hF

/-- **`F_C(A, B)` has degree `≤ n + m + 2`.** -/
theorem _root_.Grassmann.DegLe.fc {n m : ℕ} {A B : N I} (hA : DegLe (n + 2) A) (hB : DegLe (m + 2) B) :
    DegLe (n + m + 2) (Grassmann.FC C A B) := by
  set a := Grassmann.expLC (-C) A - A
  set b := Grassmann.expLC (-C) B - B
  have ha : DegLe n a := hA.exp_sub (-C)
  have hb : DegLe m b := hB.exp_sub (-C)
  have hP : DegLe (n + m + 2 + 2) (Grassmann.expLC (-C) A * Grassmann.expLC (-C) B) := by
    have := (hA.exp (-C)).mul (hB.exp (-C))
    exact this.mono (by omega)
  have e : Grassmann.FC C A B = (Grassmann.expLC C (Grassmann.expLC (-C) A * Grassmann.expLC (-C) B) -
      Grassmann.expLC (-C) A * Grassmann.expLC (-C) B) + (A * b + a * B + a * b) := by
    rw [Grassmann.FC, show Grassmann.expLC (-C) A = A + a from (add_sub_cancel A _).symm,
      show Grassmann.expLC (-C) B = B + b from (add_sub_cancel B _).symm]
    noncomm_ring
  rw [e]
  refine (hP.exp_sub C).add ((DegLe.add ?_ ?_).add ?_)
  · exact (hA.mul hb).mono (by omega)
  · exact (ha.mul hB).mono (by omega)
  · exact (ha.mul hb).mono (by omega)

end General

variable {d L N : ℕ} [NeZero L]

/-- **The quartic pairing only sees degree `4`.** -/
theorem mu4_of_degLe {F : Alg d L N} (hF : DegLe 3 F) (b : Lam d L N) (i k : Fin d) :
    mu4 b i k F = 0 :=
  sum_eq_zero fun x _ => by rw [cf4, hF 4 _ (by norm_num), zero_mul]

theorem Loc4sXY_of_degLe {F : Alg d L N} (hF : DegLe 3 F) (X Y : Finset (Lam d L N)) :
    Loc4sXY X Y F = 0 := by
  simp [Loc4sXY, mu4_of_degLe hF]

theorem mu4_Loc2sXY_of_degLe {F : Alg d L N} (hF : DegLe 3 F) (X Y : Finset (Lam d L N))
    (b : Lam d L N) (i k : Fin d) : mu4 b i k (Loc2sXY X Y F) = 0 := by
  rw [Loc2sXY, Loc4sXY_of_degLe hF, add_zero, mu4_LocXY]

theorem degLe_monoSet (M : Mono d) (Y : Finset (Lam d L N)) : DegLe 2 (monoSet M Y) :=
  fun n z hn => coeff_monoSet_of_ne M Y z (by omega)

/-- A coupling polynomial without quartic part has degree `≤ 2`. -/
theorem degLe_VcoupL_quad (Y : Finset (Lam d L N)) {v : Fin 4 → ℂ} (hv : v 3 = 0) :
    DegLe 2 (VcoupL Y v) := by
  show DegLe 2 (Vcoup (Coup.ofVec v) Y)
  rw [Vcoup, unif]
  refine ((DegLe.smul (degLe_one 2) _).add (DegLe.sum _ fun M _ =>
    (degLe_monoSet M Y).smul _)).add ?_
  have : ∀ i k : Fin d, coupE (Coup.ofVec v) i k = 0 := fun i k => by
    simp [coupE, Coup.ofVec, hv]
  simp only [this, zero_smul, sum_const_zero]
  exact DegLe.zero _

theorem degLe_VcoupL (Y : Finset (Lam d L N)) (v : Fin 4 → ℂ) : DegLe 4 (VcoupL Y v) := by
  show DegLe 4 (Vcoup (Coup.ofVec v) Y)
  rw [Vcoup, unif]
  refine ((DegLe.smul (degLe_one 4) _).add (DegLe.sum _ fun M _ =>
    ((degLe_monoSet M Y).mono (by norm_num)).smul _)).add ?_
  refine DegLe.sum _ fun i _ => DegLe.sum _ fun k _ => DegLe.smul ?_ _
  refine DegLe.sum _ fun x _ => ?_
  refine mono4s_cases i k x (DegLe 4) (fun _ _ => DegLe.add) (fun _ _ h h' => ?_)
    (fun c _ h => h.smul c) (fun e e' => ?_)
  · have := h.add (h'.smul (-1)); rwa [neg_one_smul, ← sub_eq_add_neg] at this
  · intro n z hn
    exact coeff_ιMulti_of_ne _ z (by omega)

theorem cvec4_g (X : Finset (Lam d L N)) (i₀ : Fin d) (F : Alg d L N) :
    cvec4 X i₀ F 3 = mu4 (base X) i₀ i₀ F / X.card := rfl

theorem degLe_SrcF_quad (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {u v : Fin 4 → ℂ}
    (hu : u 3 = 0) (hv : v 3 = 0) (b' : Fin d → ℕ) :
    DegLe 2 (SrcF j C LinearMap.id (VfamL j u) (VfamL j v) b' : Alg d L N) := by
  simp only [SrcF, LinearMap.id_apply, Subalgebra.coe_smul, coe_FCE,
    AddSubmonoidClass.coe_finsetSum]
  refine DegLe.smul ?_ _
  exact DegLe.fc (n := 0) (m := 0) C (degLe_VcoupL_quad _ hu)
    (DegLe.sum _ fun b'' _ => degLe_VcoupL_quad _ hv)

namespace FlowSeq

variable (D : FlowSeq d L N)

/-- **`prop:C4b`(b), first part**: in `q_{j,j}`, a pair of couplings without quartic part
contributes nothing to the `g`-component. -/
theorem betaQ_self_g_quad (j : ℕ) (b : Fin d → ℕ) (i₀ : Fin d) {u v : Fin 4 → ℂ}
    (hu : u 3 = 0) (hv : v 3 = 0) : D.betaQ j j b i₀ u v 3 = 0 := by
  unfold betaQ
  rw [if_pos rfl]
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply]
  rw [cvec4_g]
  simp only [LS0L, LinearMap.mk₂_apply, LS0, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
    coe_Loc2E]
  rw [mu4_Loc2sXY_of_degLe, zero_div]
  rw [AddSubmonoidClass.coe_finsetSum]
  exact (DegLe.sum _ fun b' _ => degLe_SrcF_quad j (D.C j) hu hv b').mono (by norm_num)

/-- **`prop:C4b`(b) at the current step**: with `u = u_q + u_g e_g`,
`q_{j,j}(u)_g = u_g² q(e_g)_g + u_g (β(e_g, u_q) + β(u_q, e_g))_g`. There are no terms that are
quadratic in the quadratic couplings. -/
theorem betaQ_self_g (j : ℕ) (b : Fin d → ℕ) (i₀ : Fin d) (u : Fin 4 → ℂ) :
    D.betaQ j j b i₀ u u 3 = u 3 ^ 2 * D.betaQ j j b i₀ (Pi.single 3 1) (Pi.single 3 1) 3 +
      u 3 * (D.betaQ j j b i₀ (Pi.single 3 1) (u - u 3 • Pi.single 3 1) 3 +
        D.betaQ j j b i₀ (u - u 3 • Pi.single 3 1) (Pi.single 3 1) 3) := by
  set eg : Fin 4 → ℂ := Pi.single 3 1
  set uq : Fin 4 → ℂ := u - u 3 • eg
  have huq : uq 3 = 0 := by simp [uq, eg]
  have hu : u = uq + u 3 • eg := by simp [uq]
  have h0 := D.betaQ_self_g_quad j b i₀ huq huq
  conv_lhs => rw [hu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, h0]
  ring

end FlowSeq

end

end Step2
