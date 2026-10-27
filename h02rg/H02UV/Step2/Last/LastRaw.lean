import Step2.Last.LastCoup

/-!
# The step at `j = N - 2`: the raw step on the coordinate spaces

* `RawHyp` (namespace `Step2.Last`): the copy of `Step2.RawHyp` with `j + 1 < N` and
  `L > 2^{d+4} + 4` in place of `j + 2 < N`; the outputs `W^lin_{j+1}`, `D_{j+1}`, `K_{j+1}` lie in
  the coordinate spaces of scale `j + 1` (`WlinNext_mem`, `Dnext_mem`, `Kconn_mem`).
* `ValidCore R j`: `ValidAt R j` with `j + 1 < N` in place of `j + 2 < N`;
  `ValidAtL R j = (L > 2^{d+4} + 4) ∧ ValidCore R j`. `ValidAt.toValidAtL`: `ValidAt` implies
  `ValidAtL` for `L > 2^{d+4} + 4`, so `ValidAtL` covers every step `j ≤ N - 2`
  (`validAtL_concrete` in `Step2.Last.FlowLastBand` for the concrete decomposition).
* `RawInv.stepL`: the analogue of `RawInv.step` (the invariants propagate along every history)
  under `ValidAtL`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace Last

/-- The hypotheses of the raw step. -/
structure RawHyp (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N) : Prop where
  hd : 1 ≤ d
  hL : 2 ^ (d + 3) + 8 * d < L
  hj2 : j + 1 < N
  hLg : 2 ^ (d + 4) + 4 < L
  hC : GoodCov2 j ℓ C
  hCt : TInv C
  hCs : CSym C
  hCsym : ∀ x y, C x y = C y x
  hV : V ∈ BSub (L := L) (N := N) j
  hV0 : ∀ b, ε (V b : Alg d L N) = 0

namespace RawHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V : Fam d L N}
  (H : RawHyp j ℓ C V)
include H

theorem hL' : 2 ^ (d + 3) ≤ L := by have := H.hL; omega

/-- **`∑_B W'(V, W)(B)` is in `BSub (j + 1)`.** -/
theorem sumWp_mem {W : Fam d L N} (hW : W ∈ BSub (L := L) (N := N) j) :
    (fun c => ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V W b) ∈
      BSub (L := L) (N := N) (j + 1) := by
  refine ⟨inF_sumWp H.hd H.hL' (by have := H.hj2; omega) H.hC H.hV.1 hW.1,
    sumWp_cov H.hd H.hL' H.hj2 H.hLg H.hC H.hCt H.hV.1 hW.1 H.hV.2.1 hW.2.1, ?_, ?_, ?_⟩
  · intro T hT hP1 c hc
    have S : SymHyp j ℓ C V W (0 : Act d L N) T :=
      ⟨H.hd, H.hL', H.hj2, H.hLg, H.hC, H.hCs, H.hV.1, hW.1, H.hV0, ⟨fun X _ => zero_mem _,
        fun X _ n z _ => by simp⟩, H.hV.2.2.1, hW.2.2.1, fun T _ _ X => by simp, hT, hP1⟩
    show AE T (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V W b) =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) (bmap (j + 1) T c)), Wp j C V W b
    rw [map_sum, ← img_blockSet_bmap hT (by have := H.hj2; omega) hP1 hc,
      blocks_img_bmap S.hP, sum_image fun b hb b' hb' e => bmap_injOn hT S.hj S.hP
        (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
    exact sum_congr rfl fun b hb => S.AE_Wp (mem_blockIdx_of_mem_blocks hb)
  · intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b hb => Wp_J H.hCsym H.hL (by have := H.hj2; omega)
      H.hV.2.2.2.1 hW.2.2.2.1 (mem_blockIdx_of_mem_blocks hb)
  · intro c hc
    simp [blockSet_eq_empty hc, blocks]

theorem WlinNext_mem {Wl : Fam d L N} (hWl : Wl ∈ BSub (L := L) (N := N) j) :
    WlinNext j C V Wl ∈ BSub (L := L) (N := N) (j + 1) := by
  have e : WlinNext j C V Wl = fun c =>
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V Wl b :=
    funext (WlinNext_eq j C V Wl)
  rw [e]; exact H.sumWp_mem hWl

/-- **`𝒲_{j+1} = Wnext2(V, W)` is in `BSub (j + 1)`.** -/
theorem Wnext2_mem {W : Fam d L N} (hW : W ∈ BSub (L := L) (N := N) j) :
    Wnext2 j C V W ∈ BSub (L := L) (N := N) (j + 1) := by
  refine ⟨Wnext2_inF H.hd H.hL' (by have := H.hj2; omega) H.hC H.hV.1 hW.1,
    Wnext2_cov H.hd H.hL' H.hj2 H.hLg H.hC H.hCt H.hV.1 hW.1 H.hV.2.1 hW.2.1,
    Wnext2_latsym (K := (0 : Act d L N)) H.hd H.hL' H.hj2 H.hLg H.hC H.hCs H.hV.1 hW.1 H.hV0
      ⟨fun X _ => zero_mem _, fun X _ n z _ => by simp⟩ H.hV.2.2.1 hW.2.2.1 (fun T _ _ X => by simp),
    Wnext2_J H.hCsym H.hL (by have := H.hj2; omega) H.hV.2.2.2.1 hW.2.2.2.1, fun c hc => ?_⟩
  simp [Wnext2, blockSet_eq_empty hc, blocks]

/-- **`D_{j+1}` is in `BSub (j + 1)`.** -/
theorem Dnext_mem {Wl D : Fam d L N} (hWl : Wl ∈ BSub (L := L) (N := N) j)
    (hD : D ∈ BSub (L := L) (N := N) j) :
    Dnext j C V Wl D ∈ BSub (L := L) (N := N) (j + 1) := by
  have e : Dnext j C V Wl D = Wnext2 j C V (Wl + D) - WlinNext j C V Wl := rfl
  rw [e]
  exact sub_mem (H.Wnext2_mem (add_mem hWl hD)) (H.WlinNext_mem hWl)

end RawHyp

namespace RawHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V : Fam d L N}
  (H : RawHyp j ℓ C V)
include H

/-- **`K_{j+1}` (on connected polymers) is in `ASub (j + 1)`.** -/
theorem Kconn_mem {W : Fam d L N} {K : Act d L N} (hW : W ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) :
    Kconn (j + 1) (Kplus j C V W K) ∈ ASub (L := L) (N := N) (j + 1) := by
  have hj1 : j + 1 ≤ N := by have := H.hj2; omega
  have hI := InK2_Kplus H.hd H.hL' (by have := H.hj2; omega) H.hC H.hV.1 hW.1 H.hV0 hK.1
  have hcov := Kplus_cov H.hd H.hL' H.hj2 H.hLg H.hC H.hCt H.hV.1 hW.1 H.hV0 hK.1 H.hV.2.1 hW.2.1 hK.2.1
  have hsym := Kplus_latsym H.hd H.hL' H.hj2 H.hLg H.hC H.hCs H.hV.1 hW.1 H.hV0 hK.1 H.hV.2.2.1
    hW.2.2.1 hK.2.2.1
  have hJ := Kplus_J H.hCsym H.hL (by have := H.hj2; omega) H.hV.2.2.2.1 hW.2.2.2.1 hK.2.2.2.1
  refine ⟨⟨fun X hX => ?_, fun X hX => ?_⟩, fun t ht X => ?_, fun T hT hP X => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · simp only [Kconn, if_pos hX]; exact hI.loc X hX
  · simp only [Kconn, if_pos hX]; exact hI.sym X hX
  · have hP := Flow.presBlocks_transl' hj1 t ht
    have hiff := PresBlocks.isConn_img (IsGen.transl t) hj1 hP (X := X)
    simp only [Kconn]
    by_cases hX : IsConn (j + 1) X
    · rw [if_pos (hiff.2 hX), if_pos hX]; exact hcov t ht X
    · rw [if_neg (fun h => hX (hiff.1 h)), if_neg hX]; simp
  · have hiff := PresBlocks.isConn_img hT hj1 hP (X := X)
    simp only [Kconn]
    by_cases hX : IsConn (j + 1) X
    · rw [if_pos (hiff.2 hX), if_pos hX]; exact hsym T hT hP X
    · rw [if_neg (fun h => hX (hiff.1 h)), if_neg hX]; simp
  · simp only [Kconn, if_pos hX]; exact hJ X hX
  · simp only [Kconn, if_neg hX]

end RawHyp

end Last

/-- `ValidAt R j` with `j + 1 < N` in place of `j + 2 < N`. -/
def ValidCore (R : RGPar d L N) (j : ℕ) : Prop :=
  j + 1 < N ∧ 1 ≤ d ∧ 2 ^ (d + 3) + 8 * d < L ∧ 0 ≤ R.ρ ∧ R.ρ ≤ 1 / 8 ∧ 0 < R.ℓ ∧
  ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ R.ρ) →
    GoodCov2 j (fscale (∏ i ∈ range (j + 1), (1 + ζ i)) * R.ℓ / 4) (rawCov R j ζ) ∧
      TInv (rawCov R j ζ) ∧ CSym (rawCov R j ζ) ∧ ∀ x y, rawCov R j ζ x y = rawCov R j ζ y x

/-- **Validity of the parameters at scale `j ≤ N - 2`**: `ValidAt` with `j + 1 < N`, at the
price of `L > 2^{d+4} + 4`. -/
def ValidAtL (R : RGPar d L N) (j : ℕ) : Prop := 2 ^ (d + 4) + 4 < L ∧ ValidCore R j

theorem ValidAt.toValidCore {R : RGPar d L N} {j : ℕ} (h : ValidAt R j) : ValidCore R j :=
  ⟨by have := h.1; omega, h.2⟩

theorem ValidAt.toValidAtL {R : RGPar d L N} {j : ℕ} (hLg : 2 ^ (d + 4) + 4 < L)
    (h : ValidAt R j) : ValidAtL R j := ⟨hLg, h.toValidCore⟩

namespace RawInv

variable {R : RGPar d L N} {j : ℕ} {st : RawSt d L N}

/-- The covariance of step `j` has the properties of `ValidCore` (cf. `RawInv.cov`). -/
theorem covL (hV : ValidCore R j) (H : RawInv R j st) :
    GoodCov2 j (fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) * R.ℓ / 4)
        (rawCov R j (zeta' R j st)) ∧ TInv (rawCov R j (zeta' R j st)) ∧
      CSym (rawCov R j (zeta' R j st)) ∧
      ∀ x y, rawCov R j (zeta' R j st) x y = rawCov R j (zeta' R j st) y x := by
  have h := hV.2.2.2.2.2.2 _ (zeta'_le hV.2.2.2.1 H)
  rwa [prod_zeta' H] at h

/-- **The step hypotheses hold along every history** (`ValidAtL`, cf. `RawInv.step`), and the invariants propagate. -/
theorem stepL (hV : ValidAtL R j) (H : RawInv R j st) (g μ : ℝ) {D : Fam d L N} {K : Act d L N}
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j) :
    let out := rawStep R j st g μ D K
    RawInv R (j + 1) out.st ∧ out.D ∈ BSub (L := L) (N := N) (j + 1) ∧
      out.K ∈ ASub (L := L) (N := N) (j + 1) := by
  intro out
  obtain ⟨hLg, hV⟩ := hV
  obtain ⟨hC, hCt, hCs, hCsym⟩ := covL hV H
  have hV' := hV
  obtain ⟨hj2, hd, hL, hρ, -, -, -⟩ := hV'
  have hjN : j < N := by omega
  set a : ℂ := st.Z * absorbZeta R st.Z (st.z + st.y)
  set yc : ℂ := st.Z * clampDisk R.ρ (st.y / st.Z)
  set Z1 : ℂ := st.Z * (1 + absorbZeta R st.Z (st.z + st.y))
  have hRH : Last.RawHyp j _ (rawCov R j (zeta' R j st))
      (VfamL j ![st.z + yc - a, st.y - yc,
        (μ : ℂ) * Z1 / (L : ℂ) ^ (2 * j) - a * R.msq,
        (g : ℂ) / (1 + nCor ((μ : ℂ) * Z1 / (L : ℂ) ^ (2 * j)) st.w1) * Z1 ^ 2]) :=
    ⟨hd, hL, hj2, hLg, hC, hCt, hCs, hCsym, VfamL_mem hd hL hjN _, eps_VfamL j _⟩
  have hΔ := VfamL_mem (L := L) (N := N) hd hL hjN ![a - yc, yc, a * R.msq, 0]
  have hKf := Kflat_mem hjN hΔ (eps_VfamL j _) hK
  refine ⟨⟨(prod_zeta' H).symm, zeta'_le hρ H, fun i hi => ?_, hRH.WlinNext_mem H.hWl, ?_⟩,
    hRH.Dnext_mem H.hWl hD, hRH.Kconn_mem (add_mem H.hWl hD) hKf⟩
  · show Function.update st.ζ j _ i = 0
    rw [Function.update_of_ne (by omega), H.hζ0 i (by omega)]
  · show (st.u * csq (1 + absorbZeta R st.Z (st.z + st.y))) ^ 2 =
      st.Z * (1 + absorbZeta R st.Z (st.z + st.y))
    rw [mul_pow, csq_sq, H.hu]

end RawInv

end

end Step2
