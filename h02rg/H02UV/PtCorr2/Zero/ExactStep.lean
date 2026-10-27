import PtCorr2.Zero.RealStep

/-!
# Exactness of one raw step (`ExactStep`, part 2)

If the output couplings `ν_{j+1}`, `ǧ_{j+1}` of `rawStep` are real, then the next step,
started from the output state with the coordinates `(Re ǧ_{j+1}, Re ν_{j+1})` and the output
`(D_{j+1}, K_{j+1})`, has exactly the output `Z_{j+1}` of the step as its input (`exactStep_of`):

* the coupling reconstruction (`Vnext2_st`, `stVf_add_stDelta_next`):
  `V♭_{j+1} + Δ_{j+1} = V_{κ_{j+1}} = V_{j+1}` on every `(j+1)`-block;
* `𝒲^{lin}_{j+1} + D_{j+1} = 𝒲_{j+1}` (definition of `Dnext`), so the block factors agree:
  `I_{j+1}(B_+) = ∏_{B ⊆ B_+} e^{-V_{j+1}(B)}(1 + 𝒲_{j+1}(B))` (`It_eq_Ib`);
* `Kext(Kconn K) = Kext K` on polymers (components are connected);
* `Γ_{j+1}` depends only on `ζ_{≤ j}` (`DressedFRD.Data.Gam_congr`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Step2 Step

local notation "cj" => starRingEnd ℂ

variable {L N : ℕ} [NeZero L]

variable (R : RGPar 2 L N) {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} {D : Fam 2 L N} {K : Act 2 L N}

/-- **The output `V_{j+1}` is the coupling polynomial of the read-off couplings.** -/
theorem Vnext2_st (hV : ValidAtL R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) :
    ∀ c ∈ blockIdx (L := L) (N := N) (j + 1),
      (Vnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) c :
        Alg 2 L N) = Vcoup (Coup.ofVec (stCv R j st g μ D K)) (blockSet (j + 1) c) := by
  obtain ⟨hLg, hVc⟩ := hV
  obtain ⟨hC, -, hCs, hCsym⟩ := RawInv.covL hVc H
  obtain ⟨hj1, -, hL8, -, -, -, -⟩ := hVc
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num : 1 ≤ 2) hCs hCsym
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN (stKap R j st g μ).toVec
  have hKf := Kflat_mem hjN (VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN _)
    (eps_stDelta R j st) hK
  have hW := add_mem H.hWl hD
  have hVf := stVf_eq_kap R j st g μ
  have HC : Last.CoupHyp j _ (stCov R j st) (stVf R j st g μ) (st.Wl + D)
      (Kflat j (stDelta R j st) K) (stKap R j st g μ) c₀ δ :=
    { hd := by norm_num, hL8 := hL8, hj2 := hj1, hLg := hLg, hC := hC, hCs := hCs,
      hCsym := hCsym, hc₀ := hc₀, hδ := hδ, hδ' := hδ', hV := by rw [hVf]; exact hVm.1,
      hW := hW.1, hK := hKf.1, hVs := by rw [hVf]; exact hVm.2.2.1, hWs := hW.2.2.1,
      hKs := hKf.2.2.1, hVJ := by rw [hVf]; exact hVm.2.2.2.1, hWJ := hW.2.2.2.1,
      hKJ := hKf.2.2.2.1, hVκ := fun b => by rw [hVf]; rfl }
  obtain ⟨κp, hrep⟩ := HC.Vnext2_coup
  have h0 := zero_mem_blockIdx (d := 2) (L := L) (N := N) (j + 1)
  have hcv := cvec4_Vcoup_block hL8 (by omega : j + 1 < N) R.i₀ κp
  rw [← hrep 0 h0] at hcv
  have e : stCv R j st g μ D K = κp.toVec := hcv
  intro c hc
  rw [hrep c hc, e, Coup.ofVec_toVec]

/-- **Coupling reconstruction**: the next step's `V♭ + Δ`, built from the output state with the
real coordinates `(Re ǧ_{j+1}, Re ν_{j+1})`, is the coupling polynomial of the read-off couplings. -/
theorem stVf_add_stDelta_next (hZ : st.Z ≠ 0) (hρ0 : 0 ≤ R.ρ) (hρ1 : R.ρ < 1)
    (hnu : cj (rawStep R j st g μ D K).nu = (rawStep R j st g μ D K).nu)
    (hg : cj (rawStep R j st g μ D K).g = (rawStep R j st g μ D K).g) :
    stVf R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re
        (rawStep R j st g μ D K).nu.re + stDelta R (j + 1) (rawStep R j st g μ D K).st =
      VfamL (j + 1) (stCv R j st g μ D K) := by
  have hnu' : (((rawStep R j st g μ D K).nu.re : ℝ) : ℂ) = (rawStep R j st g μ D K).nu := Complex.conj_eq_iff_re.1 hnu
  have hg' : (((rawStep R j st g μ D K).g.re : ℝ) : ℂ) = (rawStep R j st g μ D K).g := Complex.conj_eq_iff_re.1 hg
  have hZ1 : stZ' R st ≠ 0 :=
    mul_ne_zero hZ (Step2.one_add_ne_zero ((absorb_le R hρ0 _ _).trans_lt hρ1))
  have hZ2 : stZ2 R j st g μ D K ≠ 0 :=
    mul_ne_zero hZ1 (Step2.one_add_ne_zero ((absorb_le R hρ0 _ _).trans_lt hρ1))
  have eZ : stZ' R (rawStep R j st g μ D K).st = stZ2 R j st g μ D K := rfl
  have hL0 : ((L : ℂ) ^ (2 * (j + 1))) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  have eNu : stNu R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).nu.re = stCv R j st g μ D K 2 := by
    unfold stNu
    rw [hnu', eZ, rawStep_nu]
    field_simp
  have eGr : stGr R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re (rawStep R j st g μ D K).nu.re * stZ' R (rawStep R j st g μ D K).st ^ 2 =
      stCv R j st g μ D K 3 := by
    unfold stGr
    rw [hg', eNu, eZ, rawStep_g, show (rawStep R j st g μ D K).st.w1 = stW1 R j st from rfl]
    have := one_add_nCor_ne' (stCv R j st g μ D K 2) (stW1 R j st)
    field_simp
  unfold stVf stDelta
  rw [← map_add]
  congr 1
  funext i
  fin_cases i
  · show (rawStep R j st g μ D K).st.z + stYc R (rawStep R j st g μ D K).st - stA R (rawStep R j st g μ D K).st + (stA R (rawStep R j st g μ D K).st - stYc R (rawStep R j st g μ D K).st) =
      stCv R j st g μ D K 0
    rw [show (rawStep R j st g μ D K).st.z = stCv R j st g μ D K 0 from rfl]; ring
  · show (rawStep R j st g μ D K).st.y - stYc R (rawStep R j st g μ D K).st + stYc R (rawStep R j st g μ D K).st = stCv R j st g μ D K 1
    rw [show (rawStep R j st g μ D K).st.y = stCv R j st g μ D K 1 from rfl]; ring
  · show stNu R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).nu.re - stA R (rawStep R j st g μ D K).st * R.msq + stA R (rawStep R j st g μ D K).st * R.msq =
      stCv R j st g μ D K 2
    rw [eNu]; ring
  · show stGr R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re (rawStep R j st g μ D K).nu.re * stZ' R (rawStep R j st g μ D K).st ^ 2 + 0 = stCv R j st g μ D K 3
    rw [eGr, add_zero]

/-- The block factor of scale `j + 1` is the product of the block factors of scale `j`. -/
theorem It_eq_Ib (c : Fin 2 → ℕ) (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : Fam 2 L N)
    (K' : Act 2 L N) (V' W' : Fam 2 L N) (hV' : V' c = Vnext2 j C V W K' c)
    (hW' : W' c = Wnext2 j C V W c) :
    It j C V W K' c = Ib V' W' c := by
  rw [It, Ib, hV', hW', Wnext2, add_sub_cancel, Vnext2, bpow, ← sum_neg_distrib,
    gexp_sum_of_ε _ _ fun b _ => by simp [ε_Vp],
    ← prod_mul_distrib]
  rfl

/-- **Exactness of one raw step** (real output couplings). -/
theorem exactStep_of (hV : ValidAtL R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (hρ1 : R.ρ < 1)
    (hnu : cj (rawStep R j st g μ D K).nu = (rawStep R j st g μ D K).nu)
    (hg : cj (rawStep R j st g μ D K).g = (rawStep R j st g μ D K).g) :
    ExactStep R j st g μ D K (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re
      (rawStep R j st g μ D K).nu.re (rawStep R j st g μ D K).D (rawStep R j st g μ D K).K := by
  have hρ0 : 0 ≤ R.ρ := hV.2.2.2.2.1
  have hZ : st.Z ≠ 0 := H.Z_ne_zero hρ1
  have hrec := stVf_add_stDelta_next R hZ hρ0 hρ1 hnu hg
  have hVn := Vnext2_st R (g := g) (μ := μ) hV H hD hK
  refine ⟨?_, ?_⟩
  · unfold Zout Zin gZ
    refine sum_congr rfl fun X hX => ?_
    have hXp := (mem_Pj.1 hX).2
    congr 1
    · unfold bpow
      refine prod_congr rfl fun c hc => ?_
      have hcI : c ∈ blockIdx (L := L) (N := N) (j + 1) := mem_blockIdx_of_mem_blocks hc
      refine It_eq_Ib c _ _ _ _ _ _ ?_ ?_
      · refine Subtype.ext ?_
        rw [hVn c hcI]
        show ((stVf R (j + 1) (rawStep R j st g μ D K).st (rawStep R j st g μ D K).g.re (rawStep R j st g μ D K).nu.re + stDelta R (j + 1) (rawStep R j st g μ D K).st) c :
          Alg 2 L N) = _
        rw [hrec]; rfl
      · show WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl c +
          (Wnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) c -
            WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl c) = _
        abel
    · show Kext (j + 1) (Kplus j (stCov R j st) (stVf R j st g μ) (st.Wl + D)
          (Kflat j (stDelta R j st) K)) X = Kext (j + 1) (Kconn (j + 1) (Kplus j (stCov R j st)
            (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K))) X
      exact Kext_congr hXp fun Y hY _ => by simp [Kconn, hY]
  · have hζ : ∀ i < j + 1, (stData R j st).ζ i =
        Function.update (rawStep R j st g μ D K).st.ζ (j + 1) (stZeta R (rawStep R j st g μ D K).st) i := fun i hi => by
      rw [Function.update_of_ne (by omega)]; rfl
    exact (DressedFRD.Data.Gam_congr hζ).symm

end

end PtCorr2
