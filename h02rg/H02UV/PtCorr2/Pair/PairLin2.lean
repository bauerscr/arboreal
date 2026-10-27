import PtCorr2.Pair.PairLin1
import PtCorr2.Restart.RestartPairB

/-!
# Pair linearity, part 4: the `rpcOut`-type output through `W`, locality of the difference datum

Case (2). Inputs for the exact pair-difference identity at `h = 0` (`Spin2/Pair/PairLin2`).

* `pl2_sE_smul`, …, **`pl2_nX_smul`**: the normalised components `n_•` are invariant under a
  nonzero scalar (`W_m = (∏ ch)·W_k`).
* **`pl2_plOut_W`** (pure): `W = e^{−u}Y` with `n_aW = n_bW = 0`, `s_∅W ≠ 0`:
  `plOut_{−ε(u_b)}(u, Y) = −n_{ab}W − ε(u_{ab})`.
* **`pl2_diff_locInv`**: `ObsLocInv` is closed under `plDiffSt` (componentwise supports).
* **`pl2_rrSt_locInv_core`**: locality of the relocated state `rrSt` with the block couplings
  `β_B = m₂(V(B)_a)` (no pure-form hypothesis: `V(B)_a = α_B + β_Bψ̄_aψ_a` may carry constants).
* `pl2_W_hist`, `pl2_WTop_hist`: the history restarted at `m` from its own state has the same `W`
  as the history from `0`.
* `pl2_prj_init`: equal `b`-points give equal `σ_b` projections of the initial states.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

/-! ### Scalars -/

section Pure

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem pl2_sE_smul (c : ℂ) (F : OE .two Λ) : sE (c • F) = c * sE F := by
  unfold sE; simp only [SetLike.val_smul, SA.smul_e, map_smul, smul_eq_mul]

theorem pl2_sA_smul (c : ℂ) (F : OE .two Λ) : sA (c • F) = c * sA F := by
  unfold sA; simp only [SetLike.val_smul, SA.smul_a, map_smul, smul_eq_mul]

theorem pl2_sB_smul (c : ℂ) (F : OE .two Λ) : sB (c • F) = c * sB F := by
  unfold sB; simp only [SetLike.val_smul, SA.smul_b, map_smul, smul_eq_mul]

theorem pl2_sAB_smul (c : ℂ) (F : OE .two Λ) : sAB (c • F) = c * sAB F := by
  unfold sAB; simp only [SetLike.val_smul, SA.smul_ab, map_smul, smul_eq_mul]

/-- **The normalised components are invariant under a nonzero scalar.** -/
theorem pl2_nX_smul {c : ℂ} (hc : c ≠ 0) (F : OE .two Λ) :
    (sE (c • F) ≠ 0 ↔ sE F ≠ 0) ∧ nA (c • F) = nA F ∧ nB (c • F) = nB F ∧
      nAB (c • F) = nAB F := by
  unfold nA nB nAB
  rw [pl2_sE_smul, pl2_sA_smul, pl2_sB_smul, pl2_sAB_smul, mul_div_mul_left _ _ hc,
    mul_div_mul_left _ _ hc, mul_div_mul_left _ _ hc]
  exact ⟨⟨fun h h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero hc h⟩, rfl, rfl, rfl⟩

/-- **The `rpcOut`-type output through `W`** (pure): for `W = e^{−u}Y` with vanishing one-point
parts, `plOut_{−ε(u_b)}(u, Y) = −n_{ab}W − ε(u_{ab})`. -/
theorem pl2_plOut_W {u Y : OE .two Λ} (hu : bulk u = 0) (hs : sE (oexp (-u) * Y) ≠ 0)
    (hA : nA (oexp (-u) * Y) = 0) (hB : nB (oexp (-u) * Y) = 0) :
    plOut (-ε (u : SA .two Λ).b) u Y = -nAB (oexp (-u) * Y) - ε (u : SA .two Λ).ab := by
  set W := oexp (-u) * Y with hW
  have hY : Y = oexp u * W := (pl_oexp_neg_mul hu Y).symm
  obtain ⟨e1, a1, b1, ab1⟩ := pl_sX_oexp_obs hu
  have hA' : sA W = 0 := by
    unfold nA at hA; rcases div_eq_zero_iff.1 hA with h | h
    · exact h
    · exact absurd h hs
  have hB' : sB W = 0 := by
    unfold nB at hB; rcases div_eq_zero_iff.1 hB with h | h
    · exact h
    · exact absurd h hs
  have y1 : sAB Y = sAB W + ε (u : SA .two Λ).a * sB W + ε (u : SA .two Λ).b * sA W +
      (ε (u : SA .two Λ).ab + ε (u : SA .two Λ).a * ε (u : SA .two Λ).b) * sE W := by
    rw [hY, sAB_mul, e1, a1, b1, ab1]; ring
  have s1 : sE Y = sE W := by rw [hY, sE_mul, e1, one_mul]
  unfold plOut nAB
  rw [y1, s1, hA', hB']
  field_simp
  ring

end Pure

/-! ### Locality of the difference datum -/

section Loc

variable {L N : ℕ} [NeZero L]

theorem pl2_diffO_mem {Λ : Type*} [DecidableEq Λ] {T : Subalgebra ℂ (Grassmann.N Λ)}
    {pa pb : Prop} {F G : OE .two Λ} (hF : F ∈ compSub T pa pb) (hG : G ∈ compSub T pa pb) :
    plDiffO F G ∈ compSub T pa pb := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hF
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hG
  refine ⟨g1, sub_mem f2 g2, g3, sub_mem f4 g4, fun h => ?_, fun h => ?_⟩
  · show (F : SA .two Λ).a - (G : SA .two Λ).a = 0 ∧ (F : SA .two Λ).ab - (G : SA .two Λ).ab = 0
    rw [(f5 h).1, (f5 h).2, (g5 h).1, (g5 h).2, sub_zero]; exact ⟨rfl, rfl⟩
  · show (G : SA .two Λ).b = 0 ∧ (F : SA .two Λ).ab - (G : SA .two Λ).ab = 0
    rw [(f6 h).2, (g6 h).1, (g6 h).2, sub_zero]; exact ⟨rfl, rfl⟩

/-- **Locality is closed under `plDiffSt`.** -/
theorem pl2_diff_locInv {P : ObsPts 2 L N} {j : ℕ} {o₁ o₂ : ObsSt .two L N}
    (h₁ : ObsLocInv P j o₁) (h₂ : ObsLocInv P j o₂) : ObsLocInv P j (plDiffSt o₁ o₂) where
  V b := pl2_diffO_mem (h₁.V b) (h₂.V b)
  W b := pl2_diffO_mem (h₁.W b) (h₂.W b)
  K Y hY := pl2_diffO_mem (h₁.K Y hY) (h₂.K Y hY)

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
  (a' : Lam 2 L N)

/-- The block couplings `β_B = m₂(V(B)_a)` of a state. -/
def pl2Beta (o : ObsSt .two L N) : (Fin 2 → ℕ) → ℂ :=
  fun b => mass2 ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a

theorem pl2Beta_zero {P : ObsPts 2 L N} {o : ObsSt .two L N} (H : ObsLocInv P j o)
    (b : Fin 2 → ℕ) (ha : P.a ∉ nbhd j (blockSet (L := L) (N := N) j b)) : pl2Beta o b = 0 := by
  unfold pl2Beta
  rw [((H.V b).2.2.2.2.1 ha).1]
  exact map_zero (mass2L (d := 2) (L := L) (N := N))

/-- **Locality of the relocated state** (copy of `rrSt_obsLocInv` with `β_B = 0` off the
neighbourhood of `P.a` as the hypothesis). -/
theorem pl2_rrSt_locInv {P P' : ObsPts 2 L N} {o : ObsSt .two L N} (H : ObsLocInv P j o)
    (β : (Fin 2 → ℕ) → ℂ) (hPa : P'.a = a') (hab : blk j P.a = blk j a') (hPb : P.b = P'.b)
    (hβ0 : ∀ b, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → β b = 0)
    (hVb : ∀ b, ((stVf R j st g μ b + stDelta R j st b : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N)))
    (hWb : ∀ b, (((st.Wl + D) b : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N)))
    (hKb : ∀ Y, IsConn j Y → ((K Y : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j Y : Set (Lam 2 L N))) :
    ObsLocInv P' j (rrSt R j st g μ D K P.a a' β o) := by
  have H' := H.rs_reloc (P' := P') (by rw [hPa, hab]) hPb
  have hD : ∀ b, rrD P.a a' β b ∈ osub P' (nbhd j (blockSet (L := L) (N := N) j b)) :=
    fun b => rrD_mem_osub hPa hab (hβ0 b)
  have hV' : ∀ b, o.V b - rrD P.a a' β b ∈ osub P' (nbhd j (blockSet (L := L) (N := N) j b)) :=
    fun b => sub_mem (H'.V b) (hD b)
  refine ⟨hV', H'.W, fun Y hY => ?_⟩
  refine add_mem (H'.K Y hY) (Subalgebra.sum_mem _ fun b hb => ?_)
  have hsub : nbhd j (blockSet (L := L) (N := N) j b) ⊆ nbhd j Y :=
    nbhd_mono (blockSet_subset hY.1 hb)
  have hmono := osub_mono (c := Obs.Case.two) (P := P') hsub
  refine mul_mem (mul_mem (neg_mem (hmono (hD b))) (hmono ?_)) ?_
  · refine mul_mem (oexp_mem (neg_mem (add_mem (rr_emb_mem_osub P' (hVb b)) (hV' b))))
      (add_mem (one_mem _) (add_mem (rr_emb_mem_osub P' (hWb b)) (H'.W b)))
  · refine prod_mem fun Z hZ => ?_
    have hYp : IsPolymer j (Y \ blockSet j b) := IsPolymer.sdiff hY.1 (isPolymer_blockSet j b)
    have hZc := isConn_of_mem_comp hYp hZ
    have hZY : Z ⊆ Y := (subset_of_mem_comp hZ).trans sdiff_subset
    exact osub_mono (nbhd_mono hZY)
      (add_mem (rr_emb_mem_osub P' (hKb Z hZc)) (H'.K Z hZc))

/-- **Locality of the relocated state with `β = pl2Beta o`** from the raw-step invariants. -/
theorem pl2_rrSt_locInv_core {P P' : ObsPts 2 L N} {o : ObsSt .two L N} (H : ObsLocInv P j o)
    (hPa : P'.a = a') (hab : blk j P.a = blk j a') (hPb : P.b = P'.b)
    (hV : ValidCore R j) (HR : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) :
    ObsLocInv P' j (rrSt R j st g μ D K P.a a' (pl2Beta o) o) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem HR.hWl hD).1
  exact pl2_rrSt_locInv R j st g μ D K a' H _ hPa hab hPb (fun b hb => pl2Beta_zero j H b hb)
    (fun b => add_mem (hVm.1.loc b) (hΔm.1.loc b)) (fun b => hW.loc b)
    (fun Y hY => hK.1.loc Y hY)

end Loc

/-! ### Histories restarted from their own state; initial projections -/

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N)

theorem pl2_W_hist (o₀ : ObsSt .two L N) (m : ℕ) (t : Hist.Seq (Xs R)) {k : ℕ} (hk : m ≤ k) :
    plW R P m (obsHist R P o₀ m t) k t = plW R P 0 o₀ k t := by
  unfold plW ZhOF
  rw [rpb_histFrom_obsHist R P o₀ m t k hk, obsHistFrom_zero]

theorem pl2_WTop_hist (o₀ : ObsSt .two L N) (m Nh : ℕ) (t : Hist.Seq (Xs R)) (hk : m ≤ Nh + 1) :
    plWTop R P m (obsHist R P o₀ m t) Nh t = plWTop R P 0 o₀ Nh t := by
  unfold plWTop lastOF zmOF finOF
  rw [rpb_histFrom_obsHist R P o₀ m t (Nh + 1) hk, obsHistFrom_zero]

/-- The history from `0` at scale `0`: `plW = e^{−u_0}ω_{Γ_0}Z_0`. -/
theorem pl2_W_zero (o₀ : ObsSt .two L N) (hu : o₀.u = 0) (t : Hist.Seq (Xs R)) :
    plW R P 0 o₀ 0 t = omegaCO (Γh R 0 t) (ZhO R P o₀ 0 t) := by
  unfold plW
  rw [obsHistFrom_self, hu, neg_zero, oexp_zero, one_mul]
  rfl

/-- Equal `b`-points give equal `σ_b` projections of the initial states. -/
theorem pl2_prj_init (V : OCoup .two) {P P' : ObsPts 2 L N} (hb : P.b = P'.b) :
    prjSt false (obsInit .two V P) = prjSt false (obsInit .two V P') := by
  obtain ⟨a, y, X⟩ := P
  obtain ⟨a', y', X'⟩ := P'
  obtain rfl : y = y' := hb
  unfold prjSt obsInit
  simp only [ObsSt.mk.injEq]
  refine ⟨funext fun b => Subtype.ext (SA.ext rfl rfl rfl rfl), ?_, ?_, ?_⟩ <;> trivial

end Hist

end

end PtCorr2
