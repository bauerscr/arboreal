import Step2.D2.D2HV3
import Step2.D2.D2LDress
import Step2.Flow.FlowF1

/-!
# The normalised past sum as polarised bubbles plus the tadpole

For the dressed data `D` (`DressedFRD.Data 2 (L^N)`), the flow sequence with `C_k = kmat Γ^int_k`,
`s ≡ 1`, and `z = Z_{j+1}`:

  `z² (q_{j,j} + ∑_{k<j} b_{j,k}) = 2 𝔅x(w'_j, C'_{j+1}) + 𝔅x(C'_{j+1}, C'_{j+1})
      + 16 (C'_{j+1}(e₀) - C'_{j+1}(0)) ŵ'_j(0)`

(`past_sum_bubX`), with `w'_j = ∑_{k ≤ j} (Z_{j+1}/Z_k) C'_k` (`wp`), `C'_k = Z_k Γ^int_{k-1}` (`Cp`)
and `𝔅x` of the `ℤ²` kernels truncated at `R = L^{j+1}`.
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

variable {L N : ℕ} [NeZero L]

local notation "Λ2" => Lam 2 L N

theorem kmat_add' (w w' : DressedFRD.Sym 2 (L ^ N)) :
    DressedFRD.kmat (w + w') = DressedFRD.kmat w + DressedFRD.kmat w' := by
  funext x y; simp [DressedFRD.kmat, DressedFRD.kern_add]

theorem kmat_sum {ι : Type*} (s : Finset ι) (w : ι → DressedFRD.Sym 2 (L ^ N)) :
    DressedFRD.kmat (∑ i ∈ s, w i) = ∑ i ∈ s, DressedFRD.kmat (w i) := by
  funext x y
  simp only [DressedFRD.kmat, DressedFRD.kern_sum, Matrix.sum_apply]

theorem sum_kern_eq (w : DressedFRD.Sym 2 (L ^ N)) : ∑ x : Λ2, DressedFRD.kern w x = w 0 := by
  have h := DressedFRD.sum_kern_mul_conj w 0
  simpa [char_zero_left] using h

/-- Lattice symmetry: the nearest-neighbour values of an invariant kernel agree. -/
theorem kern_dirVec_eq {w : DressedFRD.Sym 2 (L ^ N)} (hw : w ∈ symSub) (e : Dir 2) :
    DressedFRD.kern w (dirVec e : Λ2) = DressedFRD.kern w (dirVec (Sum.inl 0)) := by
  have hneg : ∀ i : Fin 2, DressedFRD.kern w (dirVec (Sum.inr i) : Λ2) =
      DressedFRD.kern w (dirVec (Sum.inl i)) := fun i => by
    rw [dirVec_inr_eq, kern_neg_of_symMem hw]
  have h10 : DressedFRD.kern w (dirVec (Sum.inl 1) : Λ2) =
      DressedFRD.kern w (dirVec (Sum.inl 0)) := by
    have e : FRD.symm (n := L ^ N) (Equiv.swap (0 : Fin 2) 1) (fun _ => 1) (dirVec (Sum.inl 0)) =
        dirVec (Sum.inl 1) := by
      funext i; fin_cases i <;> simp [FRD.symm, co, dirVec, Equiv.swap_apply_of_ne_of_ne]
    rw [← e, kern_symm' hw]
  rcases e with i | i
  · fin_cases i
    · rfl
    · exact h10
  · rw [hneg]
    fin_cases i
    · rfl
    · exact h10

theorem kmat_CovH {w : DressedFRD.Sym 2 (L ^ N)} (hw : w ∈ symSub) {r : ℕ}
    (hr : DressedFRD.rng w ≤ r) (h2r : 2 * r < L ^ N) : CovH (DressedFRD.kmat w) r where
  htr x y t := by simp [DressedFRD.kmat]
  hsym x y := kmat_symm hw x y
  hr x y h := DressedFRD.kern_eq_zero_of_rng_lt (by omega)
  h2r := h2r

/-- `β^q_{j,j}` only sees `C_j`. -/
theorem betaQ_self_congr {D D' : FlowSeq 2 L N} {j : ℕ} (h : D.C j = D'.C j) (b : Fin 2 → ℕ)
    (i₀ : Fin 2) : D.betaQ j j b i₀ = D'.betaQ j j b i₀ := by
  unfold FlowSeq.betaQ
  simp only [if_pos rfl, h, if_true]

theorem wp_eq_smul (D : DressedFRD.Data 2 (L ^ N)) (hZ : ∀ i, D.Z i ≠ 0) (j : ℕ) :
    wp D j = D.Z (j + 1) • ∑ k ∈ range j, D.Gint k := by
  unfold wp Cp
  rw [smul_sum]
  have e : ∀ k ∈ Icc 1 j, (D.Z (j + 1) / D.Z k) • (D.Z k • D.Gint (k - 1)) =
      D.Z (j + 1) • D.Gint (k - 1) := fun k _ => by
    rw [smul_smul, div_mul_cancel₀ _ (hZ k)]
  rw [sum_congr rfl e]
  refine sum_nbij' (fun k => k - 1) (fun k => k + 1) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => rfl)
  · simp only [mem_Icc] at hk; simp only [mem_range]; omega
  · simp only [mem_range] at hk; simp only [mem_Icc]; omega
  · simp only [mem_Icc] at hk; omega
  · simp

theorem rng_le_of_two_lt {w : DressedFRD.Sym 2 (L ^ N)} {k j : ℕ} (hkj : k ≤ j)
    (h : 2 * DressedFRD.rng w < L ^ (k + 1)) : DressedFRD.rng w ≤ L ^ (j + 1) := by
  have : L ^ (k + 1) ≤ L ^ (j + 1) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L))
    (by omega)
  omega

set_option maxHeartbeats 2000000 in
/-- **The normalised past sum as polarised bubbles plus the tadpole.** -/
theorem past_sum_bubX (D : DressedFRD.Data 2 (L ^ N)) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {j : ℕ}
    (hjN : j + 1 < N) (hC : ∀ k π s m, D.C k (symmDual π s m) = D.C k m)
    (hrng : ∀ k ≤ j, 2 * DressedFRD.rng (D.Gint k) < L ^ (k + 1)) (hZ : ∀ i, D.Z i ≠ 0)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hG : ∀ i ≤ j, GoodCov2 i ℓ (DressedFRD.kmat (D.Gint i)))
    (κ : ℕ → Coup) :
    D.Z (j + 1) ^ 2 *
      ((⟨fun k => DressedFRD.kmat (D.Gint k), fun _ => 1, κ⟩ : FlowSeq 2 L N).betaQ j j 0 0
          (eC 3) (eC 3) 3 +
        ∑ k ∈ range j, (⟨fun k => DressedFRD.kmat (D.Gint k), fun _ => 1, κ⟩ :
          FlowSeq 2 L N).beta j k 0 0 (eC 3) (eC 3) 3) =
      2 * bubX (cKer (L ^ (j + 1)) (wp D j)) (cKer (L ^ (j + 1)) (Cp D (j + 1))) +
        bubX (cKer (L ^ (j + 1)) (Cp D (j + 1))) (cKer (L ^ (j + 1)) (Cp D (j + 1))) +
        16 * (DressedFRD.kern (Cp D (j + 1)) (dirVec (Sum.inl 0)) -
          DressedFRD.kern (Cp D (j + 1)) 0) * wp D j 0 := by
  set R := L ^ (j + 1) with hRdef
  set z := D.Z (j + 1)
  set FS : FlowSeq 2 L N := ⟨fun k => DressedFRD.kmat (D.Gint k), fun _ => 1, κ⟩
  set FT : FlowSeq 2 L N :=
    ⟨fun k => if k ≤ j then DressedFRD.kmat (D.Gint k) else 0, fun _ => 1, κ⟩
  set W := ∑ k ∈ range j, D.Gint k
  set G := D.Gint j
  have hsym : ∀ k, D.Gint k ∈ symSub := fun k => DData.Gint_symMem hC k
  have hWs : W ∈ symSub := Subring.sum_mem _ fun k _ => hsym k
  have hGR : DressedFRD.rng G ≤ R := rng_le_of_two_lt le_rfl (hrng j le_rfl)
  have hWR : DressedFRD.rng W ≤ R := DressedFRD.rng_sum_le _ _ fun k hk =>
    rng_le_of_two_lt (by have := mem_range.1 hk; omega) (hrng k (by have := mem_range.1 hk; omega))
  have hWGR : DressedFRD.rng (W + G) ≤ R := (DressedFRD.rng_add_le _ _).trans (max_le hWR hGR)
  have hb : (0 : Fin 2 → ℕ) ∈ blockIdx (L := L) (N := N) j := zero_mem_blockIdx j
  have hne : (Bp (L := L) (N := N) j (0 : Fin 2 → ℕ)).Nonempty := (isSmall_clo (isSmall_blockSet_of_mem hb)).2.1.1
  have hreg := region_of_size (d := 2) (by norm_num) hL hjN hb
  have hX3 : ∀ x ∈ Bp (L := L) (N := N) j (0 : Fin 2 → ℕ),
      2 * (supNorm (x - base (Bp (L := L) (N := N) j (0 : Fin 2 → ℕ))) + R + 3) < L ^ N :=
      fun x hx => by
    have := hreg x hx; omega
  have hn : 2 * (R + 4) < L ^ N := by
    obtain ⟨x, hx⟩ := hne; have := hreg x hx; omega
  -- the truncated sequence
  have hFTgood : ∀ i, GoodCov2 i ℓ (FT.C i) := fun i => by
    have hFTC : FT.C i = if i ≤ j then DressedFRD.kmat (D.Gint i) else 0 := rfl
    by_cases hi : i ≤ j
    · rw [hFTC, if_pos hi]; exact hG i hi
    · rw [hFTC, if_neg hi]; exact goodCov2_zero i hℓ
  have hpast := FT.past_sum_eq (by norm_num) hL (fun _ => rfl) hjN hFTgood hb 0
  have hFTC : ∀ i, FT.C i = if i ≤ j then DressedFRD.kmat (D.Gint i) else 0 := fun i => rfl
  have hFSC : ∀ i, FS.C i = DressedFRD.kmat (D.Gint i) := fun i => rfl
  have hbeta : ∀ k ∈ range j, FS.beta j k 0 0 = FT.beta j k 0 0 := fun k hk =>
    FlowSeq.beta_congr (D := FS) (D' := FT) (j := j) (k := k)
      (by have := mem_range.1 hk; omega)
      (fun i _ hi => by rw [hFTC, if_pos hi, hFSC]) (fun _ _ _ => rfl) 0 0
  have hbetaQ : FS.betaQ j j 0 0 = FT.betaQ j j 0 0 :=
    betaQ_self_congr (D := FS) (D' := FT) (j := j) (by rw [hFTC, if_pos le_rfl, hFSC]) 0 0
  have hsumC : ∑ k ∈ range j, FT.C k = DressedFRD.kmat W := by
    rw [kmat_sum]
    exact sum_congr rfl fun k hk => by rw [hFTC, if_pos (by have := mem_range.1 hk; omega)]
  have hCj : FT.C j = DressedFRD.kmat G := by rw [hFTC, if_pos le_rfl]
  rw [hsumC, hCj, ← kmat_add'] at hpast
  rw [negBub_kmat (Subring.add_mem _ hWs (hsym j)) hWGR hn hne hX3,
    negBub_kmat hWs hWR hn hne hX3] at hpast
  -- the tadpole
  have hT := tadT_eq (d := 2) hL (by omega : j < N) hb 0 (w := DressedFRD.kmat W)
    (C := DressedFRD.kmat G) (kmat_CovH hWs hWR (by omega))
    (fun x hx => hreg x hx)
    (c₀ := DressedFRD.kern G 0) (δ := DressedFRD.kern G (dirVec (Sum.inl 0)) - DressedFRD.kern G 0)
    (fun x => by simp [DressedFRD.kmat])
    (fun x e => by
      simp only [DressedFRD.kmat, add_sub_cancel_left]
      rw [kern_dirVec_eq (hsym j)]; ring)
    (fun x e => by
      simp only [DressedFRD.kmat, sub_add_cancel_left]
      rw [kern_neg_of_symMem (hsym j), kern_dirVec_eq (hsym j)]; ring)
  rw [hT] at hpast
  have hsumW : ∑ x : Λ2, DressedFRD.kmat W x 0 = W 0 := by
    simp only [DressedFRD.kmat, sub_zero]; exact sum_kern_eq W
  rw [hsumW] at hpast
  -- assemble
  rw [hbetaQ, sum_congr rfl fun k hk => by rw [hbeta k hk], add_comm (FT.betaQ _ _ _ _ _ _ _),
    hpast]
  have hcW := cKer_hfs R W
  have hcG := cKer_hfs R G
  rw [cKer_add, bubX_add_add hcW hcG]
  have hwp : wp D j = z • W := wp_eq_smul D hZ j
  have hCp : Cp D (j + 1) = z • G := by simp [Cp, z, G]
  rw [hwp, hCp, cKer_smul, cKer_smul, bubX_smul_left, bubX_smul_right, bubX_smul_left,
    bubX_smul_right, DressedFRD.kern_smul, DressedFRD.kern_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end

end Step2