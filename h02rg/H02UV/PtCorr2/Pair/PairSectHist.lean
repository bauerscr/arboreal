import PtCorr2.Pair.PairReduce
import Obs2.Pair.PairSect

/-!
# The reduced state at coalescence (PR1 along the history)

At scale `j` the input with sources is `Z_j = gZO j I K` (`ZinO`), `I(B) = e^{-(V♭+Δ+V^{obs})(B)}
(1 + 𝒲(B) + 𝒲^{obs}(B))` (`inI`), `K = K + K^{obs}` (`inK`). Let `D` be a connected `j`-polymer
containing every block whose small-set neighbourhood contains `a` or `b` (**`DCov P j D`**). By
locality (`ObsLocInv`) the observable parts of `V^{obs}(B)`, `𝒲^{obs}(B)` (`B ⊄ D`) and of
`K^{obs}(Y)` (`Y` connected, disjoint from `D`) vanish, so `Obs2.gZO_sect` applies:

* **`redSt`**: the reduced state `V' = 𝒲' = 0`, `u' = 0`, `K'(Y) = π_{ab}(zLoc Y)` for `Y ⊇ D`
  (`zLoc Y = ∑_{A ∈ 𝒮_Y} I^{Y∖A}K^A`, the configurations whose `D`-component is `Y`), else `0`;
* **`zinO_sect`**: `SectEq (Z_j(o)) (Z_j(o'))`;
* `redSt_isObs`, `obsAbInv_redSt` (no `σ_a`, `σ_b` parts), **`obsLocInv_redSt`** (locality, from
  the locality of the full inputs `olocS_in`).

Along the history (**`pairSect_hist`**) this is the input `PairSectRed` of `Spin2.Pair.PairRed2`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### The covering polymer -/

/-- **`D` covers the coalescence region**: a connected `j`-polymer containing every `j`-block
whose small-set neighbourhood contains `a` or `b`. -/
def DCov (P : ObsPts 2 L N) (j : ℕ) (D : Finset (Lam 2 L N)) : Prop :=
  IsConn j D ∧ ∀ c : Fin 2 → ℕ, (P.a ∈ nbhd j (blockSet (L := L) (N := N) j c) ∨
    P.b ∈ nbhd j (blockSet (L := L) (N := N) j c)) → c ∈ blocks j D

theorem DCov.mem_nbhd_block {P : ObsPts 2 L N} {j : ℕ} {D : Finset (Lam 2 L N)} (h : DCov P j D)
    {x : Lam 2 L N} (hx : x = P.a ∨ x = P.b) {Y : Finset (Lam 2 L N)} (hY : x ∈ nbhd j Y) :
    ∃ y ∈ Y, y ∈ D := by
  classical
  simp only [nbhd, mem_filter, mem_univ, true_and] at hY
  obtain ⟨S, hS, hxS, c, hc, hcS⟩ := hY
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
  have hn : x ∈ nbhd j (blockSet (L := L) (N := N) j (blk j y)) := by
    simp only [nbhd, mem_filter, mem_univ, true_and]
    exact ⟨S, hS, hxS, blk j y, blk_mem_blocks (mem_blockSet_blk j y), hcS⟩
  have hcD := h.2 (blk j y) (by rcases hx with rfl | rfl; exacts [Or.inl hn, Or.inr hn])
  exact ⟨y, hy, mem_of_blk_mem h.1.1 hcD⟩

theorem DCov.a_mem {P : ObsPts 2 L N} {j : ℕ} {D : Finset (Lam 2 L N)} (h : DCov P j D) :
    P.a ∈ D := by
  obtain ⟨y, hy, hyD⟩ := h.mem_nbhd_block (Or.inl rfl)
    (subset_nbhd (isPolymer_blockSet j (blk j P.a)) (mem_blockSet_blk j P.a))
  exact mem_of_blk_mem h.1.1 (by rw [← (mem_blockSet.1 hy)]; exact blk_mem_blocks hyD)

/-- An observable element supported away from `a` and `b` vanishes. -/
theorem eq_zero_of_osub {P : ObsPts 2 L N} {S : Finset (Lam 2 L N)} {F : OE c (Lam 2 L N)}
    (hF : F ∈ osub P S) (h0 : bulk F = 0) (ha : P.a ∉ S) (hb : P.b ∉ S) : F = 0 := by
  obtain ⟨-, -, -, -, h5, h6⟩ := hF
  refine Subtype.ext (SA.ext ?_ (h5 ha).1 (h6 hb).1 (h5 ha).2)
  rw [← coe_bulk, h0]; rfl

theorem πab_mem_osub {P : ObsPts 2 L N} {S : Finset (Lam 2 L N)} {F : OE c (Lam 2 L N)}
    (hF : F ∈ osub P S) : πab F ∈ osub P S := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := hF
  rw [mem_compSub, coe_πab, piab_apply]
  exact ⟨zero_mem _, zero_mem _, zero_mem _, h4, fun ha => ⟨rfl, (h5 ha).2⟩,
    fun hb => ⟨rfl, (h6 hb).2⟩⟩

/-! ### The reduced state of one step -/

section Red

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (Dw : Fam 2 L N) (K : Act 2 L N) (o : ObsSt c L N) (D : Finset (Lam 2 L N))

/-- The block potentials of `Z_j`: `V♭ + Δ + V^{obs}`. -/
def inV : OFam c 2 L N := fun b => emb (stVf R j st g μ b + stDelta R j st b) + o.V b

/-- The block factors of `Z_j`. -/
def inI : OFam c 2 L N := IbO (inV R j st g μ o) (fullW st Dw o)

/-- The activity of `Z_j`. -/
def inK : OAct c 2 L N := embF K + o.K

/-- **The reduced state** at scale `j`: no `V`, `𝒲`, `u`; the activity `K'(Y) = π_{ab}(zLoc Y)` on
the polymers `Y ⊇ D`. -/
def redSt : ObsSt c L N where
  V := 0
  W := 0
  K := kRed j D P.a (inI R j st g μ Dw o) (inK K o)
  u := 0

theorem redSt_isObs : (redSt R P j st g μ Dw K o D).IsObs where
  V _ := map_zero _
  W _ := map_zero _
  K _ := bulk_kRed _ _ _
  u := map_zero _

theorem obsAbInv_redSt : ObsAbInv j (redSt R P j st g μ Dw K o D) where
  V _ := zero_mem _
  W _ := zero_mem _
  K Y _ := kRed_mem_ab _ _ Y
  u := zero_mem _

variable {R P j st g μ Dw K o D}

/-- **The sector identity at scale `j`**: `SectEq (Z_j(o)) (Z_j(o'))`. -/
theorem zinO_sect (ho : o.IsObs) (hl : ObsLocInv P j o) (hD : DCov P j D) :
    SectEq (ZinO R j st g μ Dw K o) (ZinO R j st g μ Dw K (redSt R P j st g μ Dw K o D)) := by
  have hblk : ∀ b, b ∉ blocks j D → ∀ y ∈ nbhd j (blockSet (L := L) (N := N) j b),
      y = P.a ∨ y = P.b → False := by
    intro b hb y hy hyab
    obtain ⟨z, hz, hzD⟩ := hD.mem_nbhd_block hyab hy
    exact hb (by rw [← mem_blockSet.1 hz]; exact blk_mem_blocks hzD)
  have hV0 : ∀ b, b ∉ blocks j D → o.V b = 0 := fun b hb =>
    eq_zero_of_osub (hl.V b) (ho.V b) (fun ha => hblk b hb _ ha (Or.inl rfl))
      (fun h => hblk b hb _ h (Or.inr rfl))
  have hW0 : ∀ b, b ∉ blocks j D → o.W b = 0 := fun b hb =>
    eq_zero_of_osub (hl.W b) (ho.W b) (fun ha => hblk b hb _ ha (Or.inl rfl))
      (fun h => hblk b hb _ h (Or.inr rfl))
  have hK0 : ∀ Y, IsConn j Y → Disjoint Y D → o.K Y = 0 := by
    intro Y hY hdis
    have hn : ∀ x, x = P.a ∨ x = P.b → x ∉ nbhd j Y := by
      intro x hx hxY
      obtain ⟨y, hy, hyD⟩ := hD.mem_nbhd_block hx hxY
      exact disjoint_left.1 hdis hy hyD
    exact eq_zero_of_osub (hl.K Y hY) (ho.K Y) (hn _ (Or.inl rfl)) (hn _ (Or.inr rfl))
  have H := gZO_sect hD.1 hD.a_mem (inI R j st g μ Dw o)
    (IbO (inV R j st g μ (redSt R P j st g μ Dw K o D))
      (fullW st Dw (redSt R P j st g μ Dw K o D))) (inK K o) (embF K)
    (fun b => mul_mem (Obs2.oexp_mem (neg_mem (add_mem ⟨_, rfl⟩ (zero_mem _))))
      (add_mem (one_mem _) (add_mem ⟨_, rfl⟩ (zero_mem _))))
    (fun b => by
      rw [inI, bulk_IbO, bulk_IbO]
      have e1 : bulkF (inV R j st g μ (redSt R P j st g μ Dw K o D)) =
          bulkF (inV R j st g μ o) := funext fun b' => by
        show bulk (emb _ + (0 : OE c (Lam 2 L N))) = bulk (emb _ + o.V b')
        simp only [map_add, ho.V b', map_zero]
      have e2 : bulkF (fullW st Dw (redSt R P j st g μ Dw K o D)) = bulkF (fullW st Dw o) :=
        funext fun b' => by
          show bulk (embF (st.Wl + Dw) b' + (0 : OE c (Lam 2 L N))) =
            bulk (embF (st.Wl + Dw) b' + o.W b')
          simp only [map_add, ho.W b', map_zero]
      rw [e1, e2])
    (fun b hb => by
      show oexp (-(emb (stVf R j st g μ b + stDelta R j st b) + o.V b)) *
          (1 + (embF (st.Wl + Dw) b + o.W b)) =
        oexp (-(emb (stVf R j st g μ b + stDelta R j st b) + (0 : OE c (Lam 2 L N)))) *
          (1 + (embF (st.Wl + Dw) b + (0 : OE c (Lam 2 L N))))
      rw [hV0 b hb, hW0 b hb])
    (fun Y => ⟨_, rfl⟩)
    (fun Y => by simp [inK, ho.K Y])
    (fun Y hY hdis => by simp [inK, hK0 Y hY hdis])
  exact H

/-- The full inputs of `Z_j` are local. -/
theorem olocS_in (hV : ValidCore R j) (H : RawInv R j st) (hDw : Dw ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (ho : ObsLocInv P j o) :
    OLocS P j (inV R j st g μ o) (fullW st Dw o) (inK K o) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem H.hWl hDw).1
  refine ⟨fun b => add_mem (emb_mem_osub ?_) (ho.V b),
    fun b => add_mem (emb_mem_osub (hW.loc b)) (ho.W b),
    fun Y hY => add_mem (emb_mem_osub (hK.1.loc Y hY)) (ho.K Y hY)⟩
  exact add_mem (hVm.1.loc b) (hΔm.1.loc b)

/-- **The reduced state is local.** -/
theorem obsLocInv_redSt (hV : ValidCore R j) (H : RawInv R j st)
    (hDw : Dw ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (ho : ObsLocInv P j o) : ObsLocInv P j (redSt R P j st g μ Dw K o D) := by
  have HL := olocS_in (g := g) (μ := μ) hV H hDw hK ho
  refine ⟨fun _ => zero_mem _, fun _ => zero_mem _, fun Y hY => ?_⟩
  show kRed j D P.a (inI R j st g μ Dw o) (inK K o) Y ∈ _
  by_cases hDY : D ⊆ Y
  · rw [kRed_of_sub _ _ hDY]
    refine πab_mem_osub (sum_mem fun A hA => mul_mem (prod_mem fun b hb => ?_)
      (prod_mem fun Z hZ => ?_))
    · have hAY := (mem_sY.1 hA).1
      have hbY : blockSet (L := L) (N := N) j b ⊆ Y :=
        blockSet_subset hY.1 (image_subset_image sdiff_subset hb)
      exact osub_mono (nbhd_mono hbY) (mul_mem (Obs2.oexp_mem (neg_mem (HL.hV b)))
        (add_mem (one_mem _) (HL.hW b)))
    · have hAY := (mem_sY.1 hA).1
      exact osub_mono (nbhd_mono ((subset_of_mem_comp hZ).trans hAY.1))
        (HL.hK Z (isConn_of_mem_comp hAY.2 hZ))
  · rw [kRed_of_not _ _ hDY]; exact zero_mem _

end Red

/-! ### Along the history -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- **The reduced state at scale `j` along the history.** -/
def redHist (j : ℕ) (D : Finset (Lam 2 L N)) (t : Hist.Seq (Xs R)) : ObsSt c L N :=
  redSt R P j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t) D

variable {R P o₀}

/-- **PR1 along the history**: the reduced state is observable, local, without one-point parts,
and its input has the `∅` and `σ_aσ_b` components of the input of the history at scale `j`. -/
theorem pairSect_hist {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (ho₀ : o₀.IsObs) (h0 : ObsLocInv P 0 o₀) (t : Hist.Seq (Xs R)) {j : ℕ} (hj : j ≤ Nh)
    {D : Finset (Lam 2 L N)} (hD : DCov P j D) :
    (redHist R P o₀ j D t).IsObs ∧ ObsLocInv P j (redHist R P o₀ j D t) ∧
      ObsAbInv j (redHist R P o₀ j D t) ∧
      SectEq (ZhO R P o₀ j t) (ZhOF R P j (redHist R P o₀ j D t) j t) := by
  have hcore : ∀ i ≤ Nh, ValidCore R i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t
  have hl : ObsLocInv P j (obsHist R P o₀ j t) :=
    obsLocInv_hist R P o₀ h0 t j fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩
  refine ⟨redSt_isObs _ _ _ _ _ _ _ _ _ _, obsLocInv_redSt (hcore j hj) (hRI j (by omega))
    (rawD_mem R _ _) (rawK_mem R _ _) hl, obsAbInv_redSt _ _ _ _ _ _ _ _ _ _, ?_⟩
  unfold ZhOF
  rw [obsHistFrom_self]
  exact zinO_sect (obsHist_isObs R P o₀ ho₀ j t) hl hD

end Hist

end

end PtCorr2
