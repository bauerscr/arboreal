import PtCorr2.Zero.ChainHist
import Step2.Map.Conj2

/-!
# Reality of the raw step (`ExactStep`, part 1)

For a real raw state (`RealSt`: `z, y, Z, ζ, w^{(1)}, u` real, `𝒲^{lin}` conjugation-invariant),
real coordinates `(ǧ, μ)` and conjugation-invariant `(D, K)`, the raw step `rawStep` has real output
(`rawStep_real`): `RealSt` of the new state, `D_{j+1}`, `K_{j+1}` invariant, and `ν_{j+1}`,
`ǧ_{j+1}` real. The covariance `Γ^int_{j+1}` is real for a real dressed history (`kern_real`,
`frd_Gint_real`), and the map commutes with conjugation (`Step2/Map/Conj2`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Step2 Step

local notation "cj" => starRingEnd ℂ

variable {L N : ℕ} [NeZero L]

/-! ### Scalars -/

theorem cj_clampDisk {r : ℝ} {u : ℂ} (hu : cj u = u) : cj (clampDisk r u) = clampDisk r u := by
  unfold clampDisk; rw [map_mul, hu, Complex.conj_ofReal]

theorem cj_csq {w : ℂ} (hw : cj w = w) (hpos : 0 ≤ w.re) : cj (csq w) = csq w := by
  have e : w = ((w.re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.1 hw).symm
  unfold csq
  rw [e, show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hpos,
    Complex.conj_ofReal]

/-! ### Families -/

theorem conjF_VfamL (k : ℕ) {v : Fin 4 → ℂ} (hv : ∀ i, cj (v i) = v i) :
    conjF (VfamL (d := 2) (L := L) (N := N) k v) = VfamL k v := by
  funext b
  refine Subtype.ext ?_
  show conjN (Vcoup (Coup.ofVec v) (blockSet k b)) = Vcoup (Coup.ofVec v) (blockSet k b)
  rw [conjN_Vcoup]
  congr 1
  simp only [Coup.conj, Coup.ofVec, hv]

theorem conjA_Kflat (j : ℕ) (Δ : Fam 2 L N) (K : Act 2 L N) :
    conjA (Kflat j Δ K) = Kflat j (conjF Δ) (conjA K) := by
  funext Y
  simp only [conjA_apply, Kflat, map_mul, conjF]
  rw [← bpow_conj]
  simp only [conjE_gexp]

theorem conjF_add (A B : Fam 2 L N) : conjF (A + B) = conjF A + conjF B := by
  funext b; simp [conjF, map_add]

theorem conjE_sigE {Λ : Type*} [DecidableEq Λ] {r : ℂ} (hr : cj r = r) (x : EvR Λ) :
    conjE (sigE r x) = sigE r (conjE x) := by
  have hf : RealLin (r • LinearMap.id : V Λ →ₗ[ℂ] V Λ) := fun v => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, conjV_smul, hr]
  exact conjE_mapE hf x

theorem conjF_sigF {r : ℂ} (hr : cj r = r) (F : Fam 2 L N) : conjF (sigF r F) = sigF r (conjF F) :=
  funext fun b => conjE_sigE hr _

theorem conjA_sigK {r : ℂ} (hr : cj r = r) (K : Act 2 L N) : conjA (sigK r K) = sigK r (conjA K) :=
  funext fun X => conjE_sigE hr _

theorem conjA_Kconn (k : ℕ) (K : Act 2 L N) : conjA (Kconn k K) = Kconn k (conjA K) := by
  funext X; simp only [conjA_apply, Kconn]; split_ifs <;> simp

theorem WlinNext_conj (j : ℕ) {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} (hC : ∀ x y, cj (C x y) = C x y)
    (V Wl : Fam 2 L N) : conjF (WlinNext j C V Wl) = WlinNext j C (conjF V) (conjF Wl) := by
  funext c
  simp only [conjF, WlinNext_eq, map_sum]
  exact sum_congr rfl fun b _ => (Wp_conj j hC V Wl b).symm

/-! ### The raw state -/

/-- A real raw state. -/
structure RealSt (st : RawSt 2 L N) : Prop where
  z : cj st.z = st.z
  y : cj st.y = st.y
  Z : cj st.Z = st.Z
  ζ : ∀ i, cj (st.ζ i) = st.ζ i
  w1 : cj st.w1 = st.w1
  u : cj st.u = st.u
  Wl : conjF st.Wl = st.Wl

section Step

variable (R : RGPar 2 L N) (j : ℕ) {st : RawSt 2 L N} (H : RealSt st) (g μ : ℝ)
include H

theorem real_stZeta : cj (stZeta R st) = stZeta R st := by
  unfold stZeta absorbZeta
  exact cj_clampDisk (by rw [map_div₀, map_add, H.z, H.y, H.Z])

theorem real_stZ' : cj (stZ' R st) = stZ' R st := by
  unfold stZ'; rw [map_mul, map_add, map_one, H.Z, real_stZeta R H]

theorem real_stA : cj (stA R st) = stA R st := by
  unfold stA; rw [map_mul, H.Z, real_stZeta R H]

theorem real_stYc : cj (stYc R st) = stYc R st := by
  unfold stYc; rw [map_mul, H.Z, cj_clampDisk (by rw [map_div₀, H.y, H.Z])]

theorem real_ζ' (i : ℕ) : cj (Function.update st.ζ j (stZeta R st) i) =
    Function.update st.ζ j (stZeta R st) i := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact real_stZeta R H
  · rw [Function.update_of_ne hi]; exact H.ζ i

theorem real_stCov (x y : Lam 2 L N) : cj (stCov R j st x y) = stCov R j st x y :=
  kern_real (DressedFRD.frd_Gint_real R.P fun i _ => real_ζ' R j H i) (x - y)

theorem real_stNu : cj (stNu R j st μ) = stNu R j st μ := by
  unfold stNu
  rw [map_div₀, map_mul, real_stZ' R H, Complex.conj_ofReal, map_pow, Complex.conj_natCast]

theorem real_stGr : cj (stGr R j st g μ) = stGr R j st g μ := by
  unfold stGr nCor
  rw [map_div₀, Complex.conj_ofReal, map_add, map_one,
    cj_clampDisk (by rw [map_mul, map_mul, real_stNu R j H, H.w1, map_ofNat])]

theorem conjF_stVf : conjF (stVf R j st g μ) = stVf R j st g μ := by
  unfold stVf
  refine conjF_VfamL j fun i => ?_
  fin_cases i <;>
  simp [map_sub, map_add, map_mul, H.z, H.y, real_stYc R H, real_stA R H, real_stNu R j H,
    real_stGr R j H, real_stZ' R H, Complex.conj_ofReal]

theorem conjF_stDelta : conjF (stDelta R j st) = stDelta R j st := by
  unfold stDelta
  refine conjF_VfamL j fun i => ?_
  fin_cases i <;> simp [map_sub, map_mul, real_stYc R H, real_stA R H, Complex.conj_ofReal]

theorem real_stW1 : cj (stW1 R j st) = stW1 R j st := by
  unfold stW1
  rw [map_add, H.w1, map_sum]
  exact congrArg _ (sum_congr rfl fun x _ => real_stCov R j H x 0)

variable {D : Fam 2 L N} {K : Act 2 L N} (hD : conjF D = D) (hK : conjA K = K)
include hD hK

theorem conjE_Vnext2_st (c : Fin 2 → ℕ) :
    conjE (Vnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) c) =
      Vnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) c := by
  have h := Vnext2_conj j (real_stCov R j H) (stVf R j st g μ) (st.Wl + D)
    (Kflat j (stDelta R j st) K) c
  rw [conjF_stVf R j H, conjF_add, H.Wl, hD, conjA_Kflat, conjF_stDelta R j H, hK] at h
  exact h.symm

theorem real_stCv (a : Fin 4) : cj (stCv R j st g μ D K a) = stCv R j st g μ D K a := by
  unfold stCv
  rw [← cvec4_conjN, ← coe_conjE, conjE_Vnext2_st R j H g μ hD hK]

/-- **The raw step preserves reality.** -/
theorem rawStep_real (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1) :
    RealSt (rawStep R j st g μ D K).st ∧ conjF (rawStep R j st g μ D K).D = (rawStep R j st g μ D K).D ∧
      conjA (rawStep R j st g μ D K).K = (rawStep R j st g μ D K).K ∧
      cj (rawStep R j st g μ D K).nu = (rawStep R j st g μ D K).nu ∧
      cj (rawStep R j st g μ D K).g = (rawStep R j st g μ D K).g := by
  have hC := real_stCov R j H
  have hζ2 : cj (stZeta2 R j st g μ D K) = stZeta2 R j st g μ D K := by
    unfold stZeta2 absorbZeta
    exact cj_clampDisk (by rw [map_div₀, map_add, real_stCv R j H g μ hD hK,
      real_stCv R j H g μ hD hK, real_stZ' R H])
  have hZ2 : cj (stZ2 R j st g μ D K) = stZ2 R j st g μ D K := by
    unfold stZ2; rw [map_mul, map_add, map_one, real_stZ' R H, hζ2]
  have hWl : conjF (WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl) =
      WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl := by
    rw [WlinNext_conj j hC, conjF_stVf R j H, H.Wl]
  refine ⟨⟨real_stCv R j H g μ hD hK 0, real_stCv R j H g μ hD hK 1, real_stZ' R H,
    real_ζ' R j H, real_stW1 R j H, ?_, hWl⟩, ?_, ?_, ?_, ?_⟩
  · -- `u' = u csq(1 + ζ_j)`
    show cj (st.u * csq (1 + absorbZeta R st.Z (st.z + st.y))) =
      st.u * csq (1 + absorbZeta R st.Z (st.z + st.y))
    have hz : cj (1 + absorbZeta R st.Z (st.z + st.y)) = 1 + absorbZeta R st.Z (st.z + st.y) := by
      rw [map_add, map_one]; exact congrArg _ (real_stZeta R H)
    have hre : 0 ≤ (1 + absorbZeta R st.Z (st.z + st.y)).re := by
      have h1 := absorb_le R hρ0 st.Z (st.z + st.y)
      have h2 := Complex.abs_re_le_norm (absorbZeta R st.Z (st.z + st.y))
      rw [Complex.add_re, Complex.one_re]
      have := (abs_le.1 (h2.trans h1)).1
      linarith
    rw [map_mul, H.u, cj_csq hz hre]
  · rw [rawStep_D]
    unfold Dnext
    funext c
    rw [show conjF (fun c => Wnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) c -
        WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl c) c =
        conjE (Wnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) c) -
          conjE (WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl c) from map_sub _ _ _,
      ← Wnext2_conj j hC, conjF_stVf R j H, conjF_add, H.Wl, hD]
    exact congrArg _ (congrFun hWl c)
  · rw [rawStep_K, conjA_Kconn]
    congr 1
    funext U
    rw [conjA_apply, ← Kplus_conj j hC, conjF_stVf R j H, conjF_add, H.Wl, hD, conjA_Kflat,
      conjF_stDelta R j H, hK]
  · rw [rawStep_nu, map_div₀, map_mul, real_stCv R j H g μ hD hK, hZ2, map_pow,
      Complex.conj_natCast]
  · rw [rawStep_g, map_mul, map_div₀, map_pow, real_stCv R j H g μ hD hK, hZ2, map_add, map_one]
    unfold nCor
    rw [cj_clampDisk (by rw [map_mul, map_mul, real_stCv R j H g μ hD hK, real_stW1 R j H,
      map_ofNat])]

end Step

end

end PtCorr2
