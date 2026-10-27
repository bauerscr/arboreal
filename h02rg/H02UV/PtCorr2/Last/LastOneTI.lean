import PtCorr2.Pair.PairZero
import Step2.Map.WCov
import Step2.Map.LocAut
import Obs.Transl
import Obs2.Flow.GamRem
import PtCorr2.Obs.ObsHistLast

/-!
# The last step, one-point part: translation invariance kills the block remainders

At the last scale (`j + 1 = N`, `B_+ = Λ`) the bulk inputs are translation covariant
(`FamCovG`), the covariance is translation invariant (`TInv`), and every `j`-block is the
translate of the block `0` (`bmap_corner_zero`). Hence the bulk scalars of the block factors do
not depend on the block:

* `Sb_TI0`: `εS(B)`, `m₂S(B)`, `m₂V'_B` are those of the block `0` (`Sb_transl`, `Vpr_transl`);
* `LS_TI0`: `m₂Loc_{Λ,B}S(Λ)` is that of the block `0` (`autAlg_Loc2sXY_right`: translating
  the target block of `Loc_{X,·}` is the automorphism);
* **`eps_Wp_TI`**: `ε𝒲_N(B)_∅ = εS(B) - εS(Λ)|B|/|Λ| = 0`.

With `∑_Bε𝒲_N(B)_a = 0`, `∑_B m₂𝒲_N(B)_a = 0` (the pointed `loc^a` puts the whole one-point
part of `S(Λ)` on the block of `a`: `eps_total_LS`, `total_W_mass`), the remainder of `blkF_a`
collapses (`remCa_of_TI`, pure algebra):

* **`finO_last_TI`**: `P₀ = ∏_B(1 + ε𝒲_N(B)_∅) = 1`, `c2(F_N)_a = β_N + c2K_N(Λ)_a`,
  `ε(F_N)_a = εK_N(Λ)_a`;
* **`betaN_last`**: `β_N = β - β·m₂F_C(ψ̄_aψ_a, V'(Λ)_∅) - ∑_B m₂(𝔼θ𝒲(B))_a` (no `Q` at the last
  scale; `total_step_pt`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

/-! ### Pure algebra -/

section AlgTI

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

/-- **The remainder of `blkF_a` with block-independent bulk scalars**: if `ε𝒲_{i,∅} = 0`,
`c2V_{i,∅} = v`, `c2(e^{-V_i}(1 + 𝒲_i))_∅ = u` on all blocks and `∑_ic2𝒲_{i,a} = ∑_iε𝒲_{i,a} = 0`,
then `P₀ = 1` and `remCa = c2K_a`. -/
theorem remCa_of_TI (S : Finset ι) (V W : ι → OE .two (Lam d L N)) (K : OE .two (Lam d L N))
    {v u : ℂ}
    (hVe : ∀ i ∈ S, ε ((V i : SA .two (Lam d L N)).e) = 0)
    (hWe : ∀ i ∈ S, ε ((W i : SA .two (Lam d L N)).e) = 0)
    (hv : ∀ i ∈ S, Suscept.c2 ((V i : SA .two (Lam d L N)).e) = v)
    (hu : ∀ i ∈ S, c2E (bulk (oexp (-V i) * (1 + W i))) = u)
    (hWa2 : ∑ i ∈ S, Suscept.c2 ((W i : SA .two (Lam d L N)).a) = 0)
    (hWa0 : ∑ i ∈ S, ε ((W i : SA .two (Lam d L N)).a) = 0) :
    blkP0 S W = 1 ∧ remCa S V W K = Suscept.c2 ((K : SA .two (Lam d L N)).a) := by
  have hQ : ∀ i ∈ S, ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e)) = 1 := fun i _ =>
    prod_eq_one fun k hk => by rw [hWe k (mem_of_mem_erase hk), add_zero]
  have hE : ∀ k ∈ S, epsR (bulk (oexp (-V k) * (1 + W k))) = 1 := by
    intro k hk
    obtain ⟨h1, -, -⟩ := oexp_neg_cmp (hVe k hk)
    obtain ⟨g1, -⟩ := eps_c2_gexp_neg (V := bulk (V k)) (hVe k hk)
    rw [map_mul, map_mul, h1, show epsR (gexp (-bulk (V k))) = 1 from g1, one_mul,
      eps_bulk_one_add, hWe k hk, add_zero]
  have hC : ∀ i ∈ S, c2E (∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))) =
      ((S.erase i).card : ℂ) * u := by
    intro i _
    rw [c2_prodE]
    have h : ∀ k ∈ S.erase i, c2E (bulk (oexp (-V k) * (1 + W k))) *
        ∏ k' ∈ (S.erase i).erase k, epsR (bulk (oexp (-V k') * (1 + W k'))) = u := by
      intro k hk
      rw [hu k (mem_of_mem_erase hk), prod_eq_one fun k' hk' =>
        hE k' (mem_of_mem_erase (mem_of_mem_erase hk')), mul_one]
    rw [sum_congr rfl h, sum_const, nsmul_eq_mul]
  have hcard : ∀ i ∈ S, ((S.erase i).card : ℂ) = (S.card : ℂ) - 1 := fun i hi => by
    rw [card_erase_of_mem hi, Nat.cast_sub (card_pos.2 ⟨i, hi⟩), Nat.cast_one]
  refine ⟨prod_eq_one fun k hk => by rw [hWe k hk, add_zero], ?_⟩
  unfold remCa
  have hs : ∀ i ∈ S, (Suscept.c2 ((W i : SA .two (Lam d L N)).a) -
      Suscept.c2 ((V i : SA .two (Lam d L N)).e) * ε ((W i : SA .two (Lam d L N)).a)) *
        ∏ k ∈ S.erase i, (1 + ε ((W k : SA .two (Lam d L N)).e)) +
      ε ((W i : SA .two (Lam d L N)).a) *
        c2E (∏ k ∈ S.erase i, bulk (oexp (-V k) * (1 + W k))) =
      Suscept.c2 ((W i : SA .two (Lam d L N)).a) +
        (((S.card : ℂ) - 1) * u - v) * ε ((W i : SA .two (Lam d L N)).a) := by
    intro i hi
    rw [hQ i hi, hC i hi, hcard i hi, hv i hi]; ring
  rw [sum_congr rfl hs, sum_add_distrib, ← mul_sum, hWa2, hWa0]; ring

end AlgTI

/-! ### Translation invariance of the bulk block scalars at the last scale -/

section BulkTI

variable {d : ℕ} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V W : Fam d L N}

/-- `εS(B)`, `m₂S(B)`, `m₂V'_B` do not depend on the block (any `j ≤ N`). -/
theorem Sb_TI0 (hj : j ≤ N) (hC : TInv C) (hV : FamCovG j V) (hW : FamCovG j W)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    ε (Sb j C V W b : Alg d L N) = ε (Sb j C V W 0 : Alg d L N) ∧
      mass2 (Sb j C V W b : Alg d L N) = mass2 (Sb j C V W 0 : Alg d L N) ∧
      mass2 (Vpr C V b : Alg d L N) = mass2 (Vpr C V 0 : Alg d L N) := by
  have ht : ∀ i, L ^ j ∣ (co (corner (L := L) (N := N) j b) i).val := fun i =>
    dvd_val_corner hj b i
  have e := bmap_corner_zero hj hb
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  have h1 := Sb_transl hj hC hV hW ht h0
  have h2 := Vpr_transl hC hV ht h0
  rw [e] at h1 h2
  refine ⟨by rw [h1, ε_autAlg], ?_, ?_⟩
  · rw [h1]; exact mass2_autAlg (AffAut.transl _) _
  · rw [h2]; exact mass2_autAlg (AffAut.transl _) _

/-- Translating the target block of `Loc_{X,·}` is the automorphism. -/
theorem autAlg_Loc2sXY_right (t : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    autAlg (Equiv.addRight t) (Loc2sXY X Y F) = Loc2sXY X ((AffAut.transl t).img Y) F := by
  have hc : ((AffAut.transl t).img Y).card = Y.card := card_map _
  have hm : ∀ M, autAlg (Equiv.addRight t) (monoSet M Y) =
      monoSet M ((AffAut.transl t).img Y) := fun M => by
    have h := AffAut.autAlg_monoSet (AffAut.transl t) M Y
    exact h.trans (by simp [AffAut.transl])
  have h4 : ∀ i k, autAlg (Equiv.addRight t) (mono4sSet i k Y) =
      mono4sSet i k ((AffAut.transl t).img Y) := fun i k => by
    have h := (sperm_transl t).autAlg_mono4sSet i k Y
    exact h.trans (by simp)
  simp only [Loc2sXY, LocXY, Loc4sXY, map_add, map_smul, map_one, map_sum, hc, hm, h4]

theorem clo_last (hj : j + 1 = N) {X : Finset (Lam d L N)} (hX : X.Nonempty) :
    clo j X = univ := by
  subst hj
  ext x
  simp only [clo, mem_filter, mem_univ, true_and, iff_true]
  obtain ⟨y, hy⟩ := hX
  exact mem_blocks.2 ⟨y, hy, by rw [LastN.blk_top, LastN.blk_top]⟩

/-- `m₂Loc_{Λ,B}S(Λ)` does not depend on the block (last scale). -/
theorem LS_TI0 (hj : j + 1 = N)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    mass2 (LS j C V W b : Alg d L N) = mass2 (LS j C V W 0 : Alg d L N) := by
  have hjN : j ≤ N := by omega
  have ht : ∀ i, L ^ j ∣ (co (corner (L := L) (N := N) j b) i).val := fun i =>
    dvd_val_corner hjN b i
  have e := bmap_corner_zero hjN hb
  have h0 := zero_mem_blockIdx (d := d) (L := L) (N := N) j
  have hP := Flow.presBlocks_transl' hjN _ ht
  have hY : (AffAut.transl (corner (L := L) (N := N) j b)).img (blockSet j 0) = blockSet j b := by
    rw [img_blockSet_bmap (IsGen.transl _) hjN hP h0, e]
  have hB : ∀ b' ∈ blockIdx (d := d) (L := L) (N := N) j, Bp (L := L) (N := N) j b' = univ :=
    fun b' hb' => clo_last hj (mem_blockIdx.1 hb')
  rw [LS, LS, coe_Loc2E, coe_Loc2E, hB b hb, hB 0 h0, ← hY, ← autAlg_Loc2sXY_right]
  exact mass2_autAlg (AffAut.transl _) _

/-- **`ε𝒲_N(B)_∅ = 0`** at the last scale. -/
theorem eps_Wp_TI (hj : j + 1 = N) (hC : TInv C) (hV : FamCovG j V) (hW : FamCovG j W)
    {b : Fin d → ℕ} (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    ε (Wp j C V W b : Alg d L N) = 0 := by
  have hjN : j ≤ N := by omega
  have hB : Bp (L := L) (N := N) j b = univ := clo_last hj (mem_blockIdx.1 hb)
  have e : ε (Wp j C V W b : Alg d L N) =
      ε (Sb j C V W b : Alg d L N) - ε (SX j C V W univ : Alg d L N) *
        (blockSet (L := L) (N := N) j b).card / (univ : Finset (Lam d L N)).card := by
    rw [Wp, Subalgebra.coe_sub, map_sub, LS, coe_Loc2E, hB, Loc2sXY, map_add, eps_LocXY,
      eps_Loc4sXY, add_zero]
  have hS : ε (SX j C V W univ : Alg d L N) =
      ((blockIdx (d := d) (L := L) (N := N) j).card : ℂ) * ε (Sb j C V W 0 : Alg d L N) := by
    rw [SX, AddSubmonoidClass.coe_finsetSum, map_sum,
      show blocks j (univ : Finset (Lam d L N)) = blockIdx (d := d) (L := L) (N := N) j from rfl,
      sum_congr rfl fun b' hb' => (Sb_TI0 hjN hC hV hW hb').1, sum_const, nsmul_eq_mul]
  have hcU : ((univ : Finset (Lam d L N)).card : ℂ) =
      ((blockIdx (d := d) (L := L) (N := N) j).card : ℂ) * ((L ^ (j * d) : ℕ) : ℂ) := by
    rw [card_polymer (isPolymer_univ j),
      show blocks j (univ : Finset (Lam d L N)) = blockIdx (d := d) (L := L) (N := N) j from rfl,
      sum_congr rfl fun b' hb' => card_blockSet hjN hb', sum_const, smul_eq_mul]
    push_cast; ring
  have hcY : ((blockSet (L := L) (N := N) j b).card : ℂ) = ((L ^ (j * d) : ℕ) : ℂ) := by
    rw [card_blockSet hjN hb]
  have hn : ((blockIdx (d := d) (L := L) (N := N) j).card : ℂ) ≠ 0 := by
    exact_mod_cast (card_pos.2 ⟨b, hb⟩).ne'
  have hl : ((L ^ (j * d) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (NeZero.ne L)
  rw [e, hS, hcU, hcY, (Sb_TI0 hjN hC hV hW hb).1]
  field_simp
  ring

end BulkTI

/-! ### The observable last step -/

section ObsTI

variable {d : ℕ} (P : ObsPts d L N) {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

theorem mass2_sub' (F G : Alg d L N) : mass2 (F - G) = mass2 F - mass2 G :=
  map_sub (mass2L (d := d) (L := L) (N := N)) F G

/-- `c2V_N(B)_∅ = -m₂V'_B + m₂Loc_{Λ,B}S(Λ)` (no `Q` at the last scale). -/
theorem c2_VpO_e_last (hj : j + 1 = N) (b : Fin d → ℕ) :
    Suscept.c2 ((VpO P j C V W K b : SA .two (Lam d L N)).e) =
      -mass2 (Vpr C (bulkF V) b : Alg d L N) +
        mass2 (LS j C (bulkF V) (bulkF W) b : Alg d L N) := by
  show Suscept.c2 ((bulk (VpO P j C V W K b) : EvR (Lam d L N)) : Alg d L N) = _
  have hQ : (EthE C (Q2 j (bulkF K) b) : Alg d L N) = 0 := by
    rw [Q2, if_neg (by omega), coe_EthE]; exact map_zero _
  rw [bulk_VpO, ← neg_neg (Suscept.c2 _), ← mass2_eq_neg_c2, Vp, uVp, AddSubgroupClass.coe_sub,
    AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, hQ, sub_zero, mass2_sub', mass2_sub',
    Subalgebra.coe_algebraMap, mass2_algebraMap, sub_zero]
  ring

/-- `c2𝒲_N(B)_∅ = -m₂S(B) + m₂Loc_{Λ,B}S(Λ)`. -/
theorem c2_WpO_e (b : Fin d → ℕ) :
    Suscept.c2 ((WpO P j C V W b : SA .two (Lam d L N)).e) =
      -mass2 (Sb j C (bulkF V) (bulkF W) b : Alg d L N) +
        mass2 (LS j C (bulkF V) (bulkF W) b : Alg d L N) := by
  show Suscept.c2 ((bulk (WpO P j C V W b) : EvR (Lam d L N)) : Alg d L N) = _
  rw [bulk_WpO, ← neg_neg (Suscept.c2 _), ← mass2_eq_neg_c2, Wp, AddSubgroupClass.coe_sub,
    mass2_sub']
  ring

/-- The bulk `c2` of a block factor: `c2(e^{-V}(1 + 𝒲))_∅ = c2𝒲_∅ - c2V_∅` (`εV_∅ = ε𝒲_∅ = 0`). -/
theorem c2E_block_bulk {V1 W1 : OE .two (Lam d L N)} (hVe : ε ((V1 : SA .two (Lam d L N)).e) = 0)
    (hWe : ε ((W1 : SA .two (Lam d L N)).e) = 0) :
    c2E (bulk (oexp (-V1) * (1 + W1))) =
      Suscept.c2 ((W1 : SA .two (Lam d L N)).e) - Suscept.c2 ((V1 : SA .two (Lam d L N)).e) := by
  obtain ⟨h1, -, -⟩ := oexp_neg_cmp hVe
  obtain ⟨g1, g2⟩ := eps_c2_gexp_neg (V := bulk V1) hVe
  have eg : epsR (gexp (-bulk V1)) = 1 := g1
  have cg : c2E (gexp (-bulk V1)) = -Suscept.c2 ((V1 : SA .two (Lam d L N)).e) := g2
  rw [map_mul, h1, c2E_mul, eg, cg, eps_bulk_one_add, c2E_bulk_one_add, hWe]
  ring

end ObsTI

section FinTI

open Step2.LastN

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N)
  (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt .two L N)

/-- **The one-point part of `F_N` at the last scale with translation invariance**: `P₀ = 1`,
`c2(F_N)_a = β_N + c2K_N(Λ)_a`, `ε(F_N)_a = εK_N(Λ)_a`, `β_N = ∑_B m₂(V_N(B)_a)`. -/
theorem finO_last_TI (hj : j + 1 = N) (ho : o.IsObs) (hCt : TInv (stCovN R j st))
    (hVc : FamCovG j (stVf R j st g μ)) (hWc : FamCovG j (st.Wl + D)) :
    let C := stCovN R j st
    let V := VpO P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o)
    let W := WpO P j C (fullV R j st g μ o) (fullW st D o)
    let KN := Knext2O P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) univ
    let S := blocks j (univ : Finset (Lam 2 L N))
    blkP0 S W = 1 ∧
      Suscept.c2 ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).a) =
        (∑ B ∈ S, mass2 ((V B : SA .two (Lam 2 L N)).a)) +
          Suscept.c2 ((KN : SA .two (Lam 2 L N)).a) ∧
      ε ((finO R P j st g μ D K o : SA .two (Lam 2 L N)).a) =
        ε ((KN : SA .two (Lam 2 L N)).a) := by
  intro C V W KN S
  obtain ⟨h1, h2⟩ := finO_last_a R P j st g μ D K o hj
  have hjN : j ≤ N := by omega
  set Vf := fullV R j st g μ o with hVfd
  set Wf := fullW st D o with hWfd
  have eV : bulkF Vf = stVf R j st g μ := bulkF_fullV R j st g μ ho
  have eW : bulkF Wf = st.Wl + D := bulkF_fullW st D ho
  have hVc' : FamCovG j (bulkF Vf) := by rw [eV]; exact hVc
  have hWc' : FamCovG j (bulkF Wf) := by rw [eW]; exact hWc
  have hVe : ∀ B ∈ S, ε ((V B : SA .two (Lam 2 L N)).e) = 0 := fun B _ => by
    show ε ((bulk (V B) : EvR (Lam 2 L N)) : Grassmann.N (Lam 2 L N)) = 0
    rw [bulk_VpO, Step2.ε_Vp]
  have hWe : ∀ B ∈ S, ε ((W B : SA .two (Lam 2 L N)).e) = 0 := fun B hB => by
    show ε ((bulk (W B) : EvR (Lam 2 L N)) : Grassmann.N (Lam 2 L N)) = 0
    rw [bulk_WpO]
    exact eps_Wp_TI hj hCt hVc' hWc' hB
  have h0 : (0 : Fin 2 → ℕ) ∈ S := zero_mem_blockIdx (d := 2) (L := L) (N := N) j
  have hv : ∀ B ∈ S, Suscept.c2 ((V B : SA .two (Lam 2 L N)).e) =
      Suscept.c2 ((V 0 : SA .two (Lam 2 L N)).e) := fun B hB => by
    show Suscept.c2 ((VpO P j C Vf Wf (fullK R j st K o) B : SA .two (Lam 2 L N)).e) =
      Suscept.c2 ((VpO P j C Vf Wf (fullK R j st K o) 0 : SA .two (Lam 2 L N)).e)
    rw [c2_VpO_e_last P C Vf Wf _ hj, c2_VpO_e_last P C Vf Wf _ hj,
      (Sb_TI0 hjN hCt hVc' hWc' hB).2.2, LS_TI0 (C := C) (V := bulkF Vf) (W := bulkF Wf) hj hB]
  have hu : ∀ B ∈ S, c2E (bulk (oexp (-V B) * (1 + W B))) =
      c2E (bulk (oexp (-V 0) * (1 + W 0))) := fun B hB => by
    rw [c2E_block_bulk (hVe B hB) (hWe B hB), c2E_block_bulk (hVe 0 h0) (hWe 0 h0)]
    show Suscept.c2 ((WpO P j C Vf Wf B : SA .two (Lam 2 L N)).e) -
        Suscept.c2 ((VpO P j C Vf Wf (fullK R j st K o) B : SA .two (Lam 2 L N)).e) =
      Suscept.c2 ((WpO P j C Vf Wf 0 : SA .two (Lam 2 L N)).e) -
        Suscept.c2 ((VpO P j C Vf Wf (fullK R j st K o) 0 : SA .two (Lam 2 L N)).e)
    rw [c2_VpO_e_last P C Vf Wf _ hj, c2_VpO_e_last P C Vf Wf _ hj, c2_WpO_e P C Vf Wf,
      c2_WpO_e P C Vf Wf, (Sb_TI0 hjN hCt hVc' hWc' hB).2.2, (Sb_TI0 hjN hCt hVc' hWc' hB).2.1,
      LS_TI0 (C := C) (V := bulkF Vf) (W := bulkF Wf) hj hB]
  have hWa2 : ∑ B ∈ S, Suscept.c2 ((W B : SA .two (Lam 2 L N)).a) = 0 := by
    have h := total_W_mass P j C Vf Wf mass2L (locMass_two P.a)
    have e : ∀ B, Suscept.c2 ((W B : SA .two (Lam 2 L N)).a) =
        -mass2L ((WpO P j C Vf Wf B : SA .two (Lam 2 L N)).a) := fun B => by
      show _ = -mass2 _
      rw [mass2_eq_neg_c2, neg_neg]
    rw [sum_congr rfl fun B _ => e B, sum_neg_distrib]
    show -(∑ B ∈ blockIdx (L := L) (N := N) j, _) = 0
    rw [h, neg_zero]
  have hWa0 : ∑ B ∈ S, ε ((W B : SA .two (Lam 2 L N)).a) = 0 := by
    have h := eps_total_LS P j C Vf Wf
    have e : ∀ B, ε ((W B : SA .two (Lam 2 L N)).a) =
        ε ((SbO j C Vf Wf B : SA .two (Lam 2 L N)).a) -
          ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j B)
            (blockSet (L := L) (N := N) j B)
            (SXO j C Vf Wf (Step2.Bp (L := L) (N := N) j B) : SA .two (Lam 2 L N)).a) :=
      fun B => by rw [← map_sub]; rfl
    rw [sum_congr rfl fun B _ => e B, sum_sub_distrib]
    show (∑ B ∈ blockIdx (L := L) (N := N) j, _) - (∑ B ∈ blockIdx (L := L) (N := N) j, _) = 0
    rw [h, sub_self]
  obtain ⟨hP0, hR⟩ := remCa_of_TI S V W KN hVe hWe hv hu hWa2 hWa0
  refine ⟨hP0, ?_, ?_⟩
  · rw [h1, hP0, hR, mul_one]
  · rw [h2]
    have hQ : ∀ B ∈ S, ∏ B' ∈ S.erase B, (1 + ε ((W B' : SA .two (Lam 2 L N)).e)) = 1 :=
      fun B _ => prod_eq_one fun B' hB' => by rw [hWe B' (mem_of_mem_erase hB'), add_zero]
    rw [sum_congr rfl fun B hB => by rw [hQ B hB, mul_one], hWa0, zero_add]

end FinTI

section BetaN

variable {d : ℕ} (P : ObsPts d L N) {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- **`β_N` of the last step**: `∑_Bm₂(V_N(B)_a) = β - β·m₂F_C(ψ̄_aψ_a, V'(Λ)_∅) -
∑_Bm₂(𝔼θ𝒲(B))_a` (`j + 1 = N`, no `Q`). -/
theorem betaN_last (hj : j + 1 = N) (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (VpO P j C V W K b : SA .two (Lam d L N)).a =
      betaTot2 j V - betaTot2 j V *
          mass2 (FC C (pbp P.a) (VprLO j C V : SA .two (Lam d L N)).e) -
        ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (W b) : SA .two (Lam d L N)).a := by
  have h := total_step_pt P j C V W K mass2L mass2_algebraMap (locMass_two P.a)
  obtain ⟨hF, hβ⟩ := VprLO_a_form P j C V hVa
  have e2 : ∑ b ∈ blockIdx (L := L) (N := N) j, mass2L (VprO C V b : SA .two (Lam d L N)).a =
      betaTot2 j V := by
    rw [← hβ, VprLO, AddSubmonoidClass.coe_finsetSum, sum_a]
    exact (map_sum mass2L _ _).symm
  have eQ : ∑ b ∈ blockIdx (L := L) (N := N) j,
      mass2L (EthO C (Q2O P j K b) : SA .two (Lam d L N)).a = 0 := by
    refine sum_eq_zero fun b _ => ?_
    rw [Q2O_last P hj K b]
    have h0 := (EthO_comp C (0 : OE .two (Lam d L N))).2.1 true
    simp only [cmp_true] at h0
    rw [h0]
    show mass2 (expLC C (0 : Alg d L N)) = 0
    rw [map_zero]; exact map_zero mass2L
  rw [e2, eQ, sub_zero] at h
  have e3 : mass2L (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e) =
      betaTot2 j V * mass2 (FC C (pbp P.a) (VprLO j C V : SA .two (Lam d L N)).e) := by
    show mass2 _ = _
    rw [mass2_FC_loc2 C hF, hβ]
  rw [e3] at h
  exact h

end BetaN

end

end PtCorr2
