import PtCorr2.Restart.RerepZ
import PtCorr2.Obs.LinearHist
import PtCorr2.Restart.RestartLoc

/-!
# Re-representation of the relocated coupling at scale `m`; the restart identity (B3, T6 input)

Case (2), `d = 2`. At scale `j` the observable coupling of a datum `o` with Loc point `a` is
`V(B)_a = β_B ψ̄_aψ_a` (`Loc2Form`; `β_B = m₂(V(B)_a)`). To restart with the Loc point `a'` (same
`j`-block) we move `σ_aβ_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})` exactly into the polymer activity:

* `rrD a a' β B = σ_a β_B (ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})` (pure `σ_a`, so `rrD·rrD = 0`);
* **`rrSt`**: `V'(B) = V(B) − rrD(B)` (so `V'(B)_a = β_Bψ̄_{a'}ψ_{a'}`, `rrSt_V_a`), `𝒲' = 𝒲`,
  `K'(Y) = K(Y) + ∑_{B ⊆ Y} δ(B) (K♭ + K)^{Y∖B}`, `δ(B) = −rrD(B) I'(B)`,
  `I'(B) = e^{−(V♭+Δ+V')(B)}(1 + 𝒲(B))`, `u' = u`;
* **`rr_ZinO`**: the integrand is unchanged, `Z_j(o) = Z_j(rrSt o)` (`rr_gZO_V`);
* **`rrSt_obsLocInv`**: `ObsLocInv P j o` (plus bulk locality of `V♭ + Δ`, `𝒲`, `K`) gives
  `ObsLocInv P' j (rrSt o)` for `P'.a = a'` in the block of `a = P.a`; `rrSt_isObs`;
* **`rr_corr_a`, `rr_corr_norm`**: the `σ_a` part of a correction term is
  `−β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'}) I'(B)_∅ (K♭+K)^{Y∖B}_∅`, of `T_j(ℓ)` norm
  `≤ |β_B|·2d|a−a'|_∞ℓ²L^{-j} ‖I'(B)_∅‖ ‖(K♭+K)^{Y∖B}_∅‖` (`reloc_pbp`);
* `betaTot2_rrSt`: the total coupling `β = ∑_B m₂(V(B)_a)` is unchanged.

**The restart identity** (`rr_restart_identity`): with `t` a trajectory as in `hist_omegaOF_from`,
for data `o` (Loc point `P.a`) and `o'` (Loc point `P'.a`) at scale `m`,

  `Π'^{≥m}_P(o)_a − Π'^{≥m}_{P'}(o')_a = Π'^{≥m}_{P'}(rrSt o − o')_a`,

i.e. the difference of the `σ_a` parts of the two chains is the `σ_a` part of the chain of the
**difference datum** `δ = rrSt o − o'`, which has Loc point `P'.a` in every block.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

/-! ### The relocation element -/

section Elem

variable {d : ℕ}

/-- `σ_a β(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})` as a four-tuple. -/
def rrDS (a a' : Lam d L N) (β : ℂ) : SA .two (Lam d L N) := ⟨0, β • (pbp a - pbp a'), 0, 0⟩

theorem rrDS_mem (a a' : Lam d L N) (β : ℂ) : rrDS a a' β ∈ OEv .two (Lam d L N) := by
  refine mem_OEv.2 ⟨by simp [rrDS], ?_, by simp [rrDS], by simp [rrDS]⟩
  show inv' (β • (pbp a - pbp a')) = Case.s .two • (β • (pbp a - pbp a'))
  rw [map_smul, map_sub, pbp, pbp, inv'_psibar_psi, inv'_psibar_psi, Case.s_two, one_smul]

/-- **The relocation element** `σ_a β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})` of the block `B`. -/
def rrD (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) : OE .two (Lam d L N) :=
  ⟨rrDS a a' (β b), rrDS_mem a a' (β b)⟩

@[simp] theorem rrD_e (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) :
    ((rrD a a' β b : OE .two (Lam d L N)) : SA .two (Lam d L N)).e = 0 := rfl
@[simp] theorem rrD_a (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) :
    ((rrD a a' β b : OE .two (Lam d L N)) : SA .two (Lam d L N)).a = β b • (pbp a - pbp a') := rfl
@[simp] theorem rrD_b (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) :
    ((rrD a a' β b : OE .two (Lam d L N)) : SA .two (Lam d L N)).b = 0 := rfl
@[simp] theorem rrD_ab (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) :
    ((rrD a a' β b : OE .two (Lam d L N)) : SA .two (Lam d L N)).ab = 0 := rfl

theorem bulk_rrD (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) :
    bulk (rrD a a' β b) = 0 := Subtype.ext rfl

theorem rrD_mul_rrD (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b b' : Fin d → ℕ) :
    rrD a a' β b * rrD a a' β b' = 0 :=
  Subtype.ext (SA.ext (by simp) (by simp [Case.tau]) (by simp [Case.tau]) (by simp [Case.tau]))

/-- The `σ_a` part of `−rrD(B)·G·H`: `−β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'}) G_∅ H_∅`. -/
theorem rr_corr_a (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ)
    (G H : OE .two (Lam d L N)) :
    ((-rrD a a' β b * G * H : OE .two (Lam d L N)) : SA .two (Lam d L N)).a =
      (-1 : ℂ) • ((β b • (pbp a - pbp a')) * ((G : SA .two (Lam d L N)).e *
        (H : SA .two (Lam d L N)).e)) := by
  simp [Case.tau, mul_assoc]

theorem rr_corr_e (a a' : Lam d L N) (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ)
    (G H : OE .two (Lam d L N)) :
    bulk (-rrD a a' β b * G * H : OE .two (Lam d L N)) = 0 := by
  rw [map_mul, map_mul, map_neg, bulk_rrD, neg_zero, zero_mul, zero_mul]

/-- **The norm of a correction term** (`reloc_pbp`). -/
theorem rr_corr_norm (hd : 1 ≤ d) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a a' : Lam d L N)
    (β : (Fin d → ℕ) → ℂ) (b : Fin d → ℕ) (G H : OE .two (Lam d L N)) :
    Tj d (L : ℝ) j ℓ ((-rrD a a' β b * G * H : OE .two (Lam d L N)) : SA .two (Lam d L N)).a ≤
      ENNReal.ofReal (‖β b‖ * (2 * d * supNorm (a - a') * ℓ ^ 2 / (L : ℝ) ^ j)) *
        (Tj d (L : ℝ) j ℓ (G : SA .two (Lam d L N)).e * Tj d (L : ℝ) j ℓ (H : SA .two (Lam d L N)).e) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  rw [rr_corr_a]
  refine (tNorm_smul_le _ _).trans ?_
  rw [norm_neg, norm_one, ENNReal.ofReal_one, one_mul]
  refine (tNorm_mul_le hh hℓ _ _).trans ?_
  gcongr
  · exact reloc_coupling hd hℓ (β b) a a'
  · exact tNorm_mul_le hh hℓ _ _

end Elem

/-! ### The re-represented state -/

section St

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
  (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)

/-- The full block polynomial `V♭ + Δ + V` of the input `Z_j` (as in `ZinO`). -/
def rrVf (o : ObsSt .two L N) : OFam .two 2 L N :=
  fun b => emb (stVf R j st g μ b + stDelta R j st b) + o.V b

/-- The correction `δ(B) = −rrD(B) I'(B)` with `I'` the relocated block factor. -/
def rrDel (o : ObsSt .two L N) : OFam .two 2 L N :=
  fun b => -rrD a a' β b *
    IbO (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') + (o.V b' - rrD a a' β b'))
      (fullW st D o) b

/-- **The re-represented state**: Loc point `a'` in the coupling, the difference moved into `K`. -/
def rrSt (o : ObsSt .two L N) : ObsSt .two L N :=
  ⟨fun b => o.V b - rrD a a' β b, o.W,
    fun Y => o.K Y + ∑ b ∈ blocks j Y,
      rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K) (Y \ blockSet j b), o.u⟩

theorem rrSt_V_a (o : ObsSt .two L N) (b : Fin 2 → ℕ) :
    (((rrSt R j st g μ D K a a' β o).V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a - β b • (pbp a - pbp a') := rfl

/-- **The relocated coupling**: `V(B)_a = β_Bψ̄_aψ_a ⟹ V'(B)_a = β_Bψ̄_{a'}ψ_{a'}`. -/
theorem rrSt_V_a_eq {o : ObsSt .two L N} {b : Fin 2 → ℕ}
    (h : ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = β b • pbp a) :
    (((rrSt R j st g μ D K a a' β o).V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a =
      β b • pbp a' := by
  rw [rrSt_V_a, h, smul_sub, sub_sub_cancel]

/-- The total coupling `∑_B m₂(V(B)_a)` is unchanged. -/
theorem betaTot2_rrSt (o : ObsSt .two L N) (k : ℕ) :
    betaTot2 k (rrSt R j st g μ D K a a' β o).V = betaTot2 k o.V := by
  unfold betaTot2
  refine sum_congr rfl fun b _ => ?_
  rw [rrSt_V_a, Obs2.mass2_sub, mass2_smul, Obs2.mass2_sub, mass2_pbp, mass2_pbp, sub_self, mul_zero,
    sub_zero]

theorem rrSt_isObs {o : ObsSt .two L N} (ho : o.IsObs) : (rrSt R j st g μ D K a a' β o).IsObs where
  V b := by
    show bulk (o.V b - rrD a a' β b) = 0
    rw [map_sub, ho.V b, bulk_rrD, sub_zero]
  W b := ho.W b
  K Y := by
    show bulk (o.K Y + _) = 0
    rw [map_add, ho.K Y, zero_add, map_sum]
    exact sum_eq_zero fun b _ => by rw [rrDel]; exact rr_corr_e _ _ _ _ _ _
  u := ho.u

theorem rr_gZO_congr {j : ℕ} (I : OFam .two 2 L N) {K₁ K₂ : OAct .two 2 L N}
    (h : ∀ Y, IsConn j Y → K₁ Y = K₂ Y) : gZO j I K₁ = gZO j I K₂ :=
  sum_congr rfl fun X hX => by rw [rr_KextO_congr j h (mem_Pj.1 hX).2]

/-- **The integrand is unchanged**: `Z_j(o) = Z_j(rrSt o)`. -/
theorem rr_ZinO (o : ObsSt .two L N) :
    ZinO R j st g μ D K o = ZinO R j st g μ D K (rrSt R j st g μ D K a a' β o) := by
  have hΔ : ∀ b, rrVf R j st g μ o b -
      (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') + (o.V b' - rrD a a' β b')) b =
      rrD a a' β b := fun b => by simp only [rrVf]; abel
  unfold ZinO
  rw [show (fun b => emb (stVf R j st g μ b + stDelta R j st b) + o.V b) = rrVf R j st g μ o from
      rfl,
    rr_gZO_V j (fullW st D o) (embF K + o.K) (fun b => by rw [hΔ, bulk_rrD])
      (fun b b' => by rw [hΔ, hΔ, rrD_mul_rrD])]
  refine rr_gZO_congr _ fun Y hY => ?_
  simp only [rrK]
  rw [KextO, comp_of_isConn hY, prod_singleton]
  show (embF K + o.K : OAct .two 2 L N) Y + _ = embF K Y + (o.K Y + _)
  rw [Pi.add_apply, add_assoc]
  congr 2
  refine sum_congr rfl fun b _ => ?_
  rw [hΔ]
  rfl

/-! ### Locality -/

variable {R j st g μ D K a a' β}

theorem rr_emb_mem_osub (P : ObsPts 2 L N) {S : Finset (Lam 2 L N)} {x : Step.EvR (Lam 2 L N)}
    (hx : (x : Alg 2 L N) ∈ NX (S : Set (Lam 2 L N))) : (emb x : OE .two (Lam 2 L N)) ∈ osub P S :=
  ⟨by simpa using hx, by simp, by simp, by simp, fun _ => ⟨by simp, by simp⟩,
    fun _ => ⟨by simp, by simp⟩⟩

theorem rr_beta_zero {P : ObsPts 2 L N} {S : Finset (Lam 2 L N)} {F : OE .two (Lam 2 L N)}
    (hF : F ∈ osub P S) {βb : ℂ} (h : (F : SA .two (Lam 2 L N)).a = βb • pbp P.a)
    (ha : P.a ∉ S) : βb = 0 := by
  have h0 := (hF.2.2.2.2.1 ha).1
  rw [h] at h0
  have := congrArg mass2 h0
  rwa [mass2_smul, mass2_pbp, mul_one, show mass2 (0 : Alg 2 L N) = 0 from
    map_zero (mass2L (d := 2) (L := L) (N := N))] at this

theorem rrD_mem_osub {P P' : ObsPts 2 L N} (hPa : P'.a = a') (hab : blk j P.a = blk j a')
    {b : Fin 2 → ℕ} (hβ : P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → β b = 0) :
    rrD P.a a' β b ∈ osub P' (nbhd j (blockSet (L := L) (N := N) j b)) := by
  by_cases ha : P.a ∈ nbhd j (blockSet (L := L) (N := N) j b)
  · have ha' : a' ∈ nbhd j (blockSet (L := L) (N := N) j b) := (rs_mem_nbhd_iff hab).1 ha
    refine ⟨by simp, ?_, by simp, by simp, fun h => absurd (hPa ▸ ha') h, fun _ => ⟨by simp, by simp⟩⟩
    rw [rrD_a]
    exact Subalgebra.smul_mem _ (sub_mem (pbp_mem ha) (pbp_mem ha')) _
  · have h0 := hβ ha
    refine ⟨by simp, by simp [h0], by simp, by simp, fun _ => ⟨by simp [h0], by simp⟩,
      fun _ => ⟨by simp, by simp⟩⟩

/-- **Locality of the re-represented state** (Loc point `a' = P'.a` in the block of `P.a`). -/
theorem rrSt_obsLocInv {P P' : ObsPts 2 L N} {o : ObsSt .two L N} (H : ObsLocInv P j o)
    (hPa : P'.a = a') (hab : blk j P.a = blk j a') (hPb : P.b = P'.b)
    (hβ : ∀ b, ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = β b • pbp P.a)
    (hVb : ∀ b, ((stVf R j st g μ b + stDelta R j st b : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N)))
    (hWb : ∀ b, (((st.Wl + D) b : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam 2 L N)))
    (hKb : ∀ Y, IsConn j Y → ((K Y : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      NX (nbhd j Y : Set (Lam 2 L N))) :
    ObsLocInv P' j (rrSt R j st g μ D K P.a a' β o) := by
  have H' := H.rs_reloc (P' := P') (by rw [hPa, hab]) hPb
  have hβ0 : ∀ b, P.a ∉ nbhd j (blockSet (L := L) (N := N) j b) → β b = 0 :=
    fun b hb => rr_beta_zero (H.V b) (hβ b) hb
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


/-- **Locality of the re-represented state from the raw-step invariants** (the bulk locality of
`V♭ + Δ`, `𝒲`, `K` as in `olocS_full`). -/
theorem rrSt_obsLocInv_core {P P' : ObsPts 2 L N} {o : ObsSt .two L N} (H : ObsLocInv P j o)
    (hPa : P'.a = a') (hab : blk j P.a = blk j a') (hPb : P.b = P'.b)
    (hβ : ∀ b, ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = β b • pbp P.a)
    (hV : ValidCore R j) (HR : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) :
    ObsLocInv P' j (rrSt R j st g μ D K P.a a' β o) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem HR.hWl hD).1
  exact rrSt_obsLocInv H hPa hab hPb hβ (fun b => add_mem (hVm.1.loc b) (hΔm.1.loc b))
    (fun b => hW.loc b) (fun Y hY => hK.1.loc Y hY)

end St


/-! ### Sizes of the difference datum -/

section Sizes

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
  (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)

/-- **The coupling of the difference datum**: `β^δ = β^o − β^{o'}` (`β = ∑_B m₂(V(B)_a)`). -/
theorem rr_delta_beta (o o' : ObsSt .two L N) (k : ℕ) :
    betaTot2 k (subSt (rrSt R j st g μ D K a a' β o) o').V = betaTot2 k o.V - betaTot2 k o'.V := by
  rw [← betaTot2_rrSt R j st g μ D K a a' β o k]
  unfold betaTot2
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  show mass2 (((rrSt R j st g μ D K a a' β o).V b - o'.V b : OE .two (Lam 2 L N)) :
    SA .two (Lam 2 L N)).a = _
  rw [show (((rrSt R j st g μ D K a a' β o).V b - o'.V b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = (((rrSt R j st g μ D K a a' β o).V b : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).a - ((o'.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a from rfl,
    Obs2.mass2_sub]

/-- **The activity of the difference datum** (`σ_a` part): `K^δ(Y)_a = K^o(Y)_a − K^{o'}(Y)_a +
∑_{B ⊆ Y}(δ(B)(K♭ + K^o)^{Y∖B})_a`. -/
theorem rr_delta_K_a (o o' : ObsSt .two L N) (Y : Finset (Lam 2 L N)) :
    (((subSt (rrSt R j st g μ D K a a' β o) o').K Y : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a = (((o.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a +
        ∑ b ∈ blocks j Y, ((rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K)
          (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a) -
      ((o'.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a := by
  rw [← SA.sum_a, ← AddSubmonoidClass.coe_finsetSum, ← SA.add_a, ← Subalgebra.coe_add, ← SA.sub_a,
    ← Subalgebra.coe_sub]
  rfl

/-- **The size of the difference activity** (`T_j(ℓ)` norm of the `σ_a` part; `rr_corr_norm`). -/
theorem rr_delta_K_norm {ℓ : ℝ} (hℓ : 0 < ℓ) (o o' : ObsSt .two L N) (Y : Finset (Lam 2 L N)) :
    Tj 2 (L : ℝ) j ℓ (((subSt (rrSt R j st g μ D K a a' β o) o').K Y : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a ≤
      Tj 2 (L : ℝ) j ℓ ((o.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a +
        ∑ b ∈ blocks j Y,
          ENNReal.ofReal (‖β b‖ * (2 * ((2 : ℕ) : ℝ) * supNorm (a - a') * ℓ ^ 2 / (L : ℝ) ^ j)) *
            (Tj 2 (L : ℝ) j ℓ ((IbO (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') +
              (o.V b' - rrD a a' β b')) (fullW st D o) b : OE .two (Lam 2 L N)) :
                SA .two (Lam 2 L N)).e *
              Tj 2 (L : ℝ) j ℓ ((KextO j (embF K + o.K) (Y \ blockSet j b) :
                OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).e) +
      Tj 2 (L : ℝ) j ℓ ((o'.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a := by
  rw [rr_delta_K_a]
  refine (tNorm_sub_le _ _).trans (add_le_add ((tNorm_add_le _ _).trans
    (add_le_add le_rfl ((tNorm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)))) le_rfl)
  exact rr_corr_norm (d := 2) (by norm_num) hℓ a a' β b _ _

end Sizes

/-! ### The restart identity -/

section Ident

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `rrSt` with the step data of scale `m` along the history `t` (the inputs of `ZhOF`). -/
def rrStH (m : ℕ) (t : Hist.Seq (Xs R)) (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)
    (o : ObsSt .two L N) : ObsSt .two L N :=
  rrSt R m (rawHist R m t) (t m).1 (t m).2.1 (rawD R (rawHist R m t).u (t m).2.2)
    (rawK R (rawHist R m t).u (t m).2.2) a a' β o

theorem rr_ZhOF (P P' : ObsPts 2 L N) (m : ℕ) (t : Hist.Seq (Xs R)) (a a' : Lam 2 L N)
    (β : (Fin 2 → ℕ) → ℂ) (o : ObsSt .two L N) :
    ZhOF R P m o m t = ZhOF R P' m (rrStH R m t a a' β o) m t := by
  rw [ZhOF, ZhOF, obsHistFrom_self, obsHistFrom_self]
  exact rr_ZinO R m _ _ _ _ _ a a' β o

set_option maxHeartbeats 400000 in
/-- **The restart identity** (exact): the difference of the `σ_a` parts of the chains `Π'^{≥m}` of
the datum `o` (Loc point `P.a`) and of the datum `o'` (Loc point `P'.a`) is the `σ_a` part of the
chain of the difference datum `rrStH o − o'` (Loc point `P'.a`). -/
theorem rr_restart_identity {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {m : ℕ} (hmN : m ≤ Nh) (P P' : ObsPts 2 L N)
    (β : (Fin 2 → ℕ) → ℂ) {o o' : ObsSt .two L N} (ho : o.IsObs) (ho' : o'.IsObs)
    (hl : ObsLocInv P m o)
    (hl'' : ObsLocInv P' m (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o)) :
    (prodHiF R P m o Nh m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        (prodHiF R P' m o' Nh m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a =
      (prodHiF R P' m (subSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o) o')
        Nh m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a := by
  have hr : (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o).IsObs :=
    rrSt_isObs _ _ _ _ _ _ _ _ _ _ ho
  have e1 := hist_omegaOF_from R P m o hN hρ1 hspl hm0 hm hV hVL b μ₀ ho hl le_rfl hmN
  have e2 := hist_omegaOF_from R P' m (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o)
    hN hρ1 hspl hm0 hm hV hVL b μ₀ hr hl'' le_rfl hmN
  rw [lin_prodHiF_sub R P' m hr ho', ← e1, ← e2, ← rr_ZhOF R P P' m _ P.a P'.a β o]


set_option maxHeartbeats 400000 in
/-- **The restart identity along the trajectory**, with the locality of the re-represented datum
derived (`rrSt_obsLocInv_core`): for `o` with Loc form `V(B)_a = β_Bψ̄_aψ_a` (`a = P.a`) and
`P'.a` in the `m`-block of `P.a`, `P'.b = P.b`. -/
theorem rr_restart_identity' {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {m : ℕ} (hmN : m ≤ Nh) (P P' : ObsPts 2 L N)
    (hab : blk m P.a = blk m P'.a) (hPb : P.b = P'.b)
    (β : (Fin 2 → ℕ) → ℂ) {o o' : ObsSt .two L N} (ho : o.IsObs) (ho' : o'.IsObs)
    (hl : ObsLocInv P m o)
    (hβ : ∀ b, ((o.V b : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).a = β b • pbp P.a) :
    (prodHiF R P m o Nh m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        (prodHiF R P' m o' Nh m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a =
      (prodHiF R P' m (subSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o) o')
        Nh m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a := by
  have hcore : ValidCore R m := by
    rcases Nat.lt_or_ge m Nh with h | h
    · exact (hV m h).toValidCore
    · rw [show m = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) m (by omega)
  exact rr_restart_identity R hN hρ1 hspl hm0 hm hV hVL b μ₀ hmN P P' β ho ho' hl
    (rrSt_obsLocInv_core hl rfl hab hPb hβ hcore hRI (rawD_mem R _ _) (rawK_mem R _ _))

end Ident

end

end PtCorr2
