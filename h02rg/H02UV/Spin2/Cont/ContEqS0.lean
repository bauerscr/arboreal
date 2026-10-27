import Spin2.Cont.ContEq1

set_option autoImplicit false

/-!
# B3, `r`-dependent form: a master construction with `1 ≤ C₀u` and `1 ≤ C₀o`

The scalar discharge needs `B = kB(θ₀(C₀o), C₁k, 8c_x) > 0` (the `σ_aσ_b` transient condition
`hQk` has `8B r_{ms}² Q₀` on the right) and `Γ_w > 0`, `c_{NS} ≥ 1` (to bound `w/s²M₀`, `k/s²M₀`).

* `eqs_kobsBounds_mono_C₀`, `eqs_kobs_bounds_one`: `KObsBounds` is monotone in `C₀`; `kobs_bounds`
  with `1 ≤ C₀`.
* `eqs_masterCore_exists`: copy of `masterCore_exists_C₀` with `eqs_kobs_bounds_one`
  (`1 ≤ C₀u`, `1 ≤ C₀o`).
* `eqs_one_le_cbnC`, `eqs_one_le_csN`: the counting constants are `≥ 1`.
* `MasterFacts.eqs_Bk_pos`, `MasterFacts.eqs_rdtΓ_pos`; **`eqs_master`**: one construction with
  `0 < c_{ab}`, `0 < B`, `0 < Γ_w`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **`KObsBounds` is monotone in `C₀`** (for `0 ≤ A`). -/
theorem eqs_kobsBounds_mono_C₀ {L : ℕ} [NeZero L] {A C₀ C₀' η ε₀ C₁ : ℝ} (hA : 0 ≤ A)
    (hC : C₀ ≤ C₀') (h : KObsBounds L A C₀ η ε₀ C₁) : KObsBounds L A C₀' η ε₀ C₁ := by
  intro N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 c P w hw hwa hwb o ho hl hs
    wl dd kb r m k cb ck hwl hdd hkb hr hm0 hk hcb hck hW hDn hKn hrr hwd hr1 hrε hkb' hk' hε
    hV' hW' hK1 U hU
  refine (h N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 c P w hw hwa hwb o ho hl hs
    wl dd kb r m k cb ck hwl hdd hkb hr hm0 hk hcb hck hW hDn hKn hrr hwd hr1 hrε hkb' hk' hε
    hV' hW' hK1 U hU).trans (ENNReal.ofReal_le_ofReal ?_)
  have hθ : 0 ≤ (L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η) :=
    add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
  have h8 : 0 ≤ 8 * k := by linarith
  have hX : 0 ≤ cb * r ^ 2 * m := by have := hr.le; have := hm0.le; positivity
  have t1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hθ) h8
  have t2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hθ) hX
  nlinarith

/-- **`kobs_bounds` with `1 ≤ C₀`.** -/
theorem eqs_kobs_bounds_one : ∃ (C₀ η : ℝ) (L₀ : ℕ), 1 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBounds L A C₀ η ε₀ C₁ := by
  obtain ⟨C₀, η, L₀, -, hη, h⟩ := kobs_bounds
  refine ⟨max C₀ 1, η, L₀, le_max_right _ _, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hA⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA' => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, hK⟩ := hA A hA'
  exact ⟨ε₀, C₁, hε₀, hC₁, eqs_kobsBounds_mono_C₀ (by linarith) (le_max_left _ _) hK⟩

set_option maxHeartbeats 4000000 in
/-- **The master construction with `1 ≤ C₀u` and `1 ≤ C₀o`** (copy of `masterCore_exists_C₀` with
`eqs_kobs_bounds_one`). -/
theorem eqs_masterCore_exists : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ D : MasterCore L, 1 ≤ D.C₀u ∧ 1 ≤ D.C₀o := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hnu⟩ := nu_sharp
  obtain ⟨Cpf, εpf, L₀p, hCpf, hPf⟩ := prod_raw_step
  obtain ⟨C₀o, ηo, L₀k, hC₀o1, hηo, hk⟩ := eqs_kobs_bounds_one
  have hC₀o : 0 ≤ C₀o := by linarith
  obtain ⟨Kw, L₀w, hKw, hw⟩ := wobs_bounds
  obtain ⟨C₀u, ηu, L₀u, hC₀u1, hηu, hku⟩ := kobs_bounds_U_one
  have hC₀u : 0 ≤ C₀u := by linarith
  obtain ⟨Lw, hLwB⟩ := wobs_raw_fullWU
  obtain ⟨Lj, hLj⟩ := PtCorr2.finG_jets_le
  obtain ⟨C₀a, ηa, L₀a, hC₀a, hηa, hka⟩ := kobs_bounds_ABL
  obtain ⟨Kwa, L₀wa, hKwa, hwa⟩ := wobs_bounds_AB
  obtain ⟨Ls, hLs⟩ := sxo_bounds_AB
  obtain ⟨La, hLad⟩ : ∃ La : ℕ, La = max (max L₀a L₀wa) (⌈144 * C₀a + 1⌉₊) := ⟨_, rfl⟩
  have hLa0 : L₀a ≤ La := hLad ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLa1 : L₀wa ≤ La := hLad ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLa2 : 144 * C₀a + 1 ≤ (La : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (hLad ▸ le_max_right _ _ : ⌈144 * C₀a + 1⌉₊ ≤ La))
  obtain ⟨Lu, hLud⟩ : ∃ Lu : ℕ, Lu = max L₀u (⌈144 * (3 * C₀u) + 1⌉₊) := ⟨_, rfl⟩
  have hLu0 : L₀u ≤ Lu := hLud ▸ le_max_left _ _
  have hLu1 : 144 * (3 * C₀u) + 1 ≤ (Lu : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (hLud ▸ le_max_right _ _ : ⌈144 * (3 * C₀u) + 1⌉₊ ≤ Lu))
  obtain ⟨Lo, hLod⟩ : ∃ Lo : ℕ, Lo = max (max L₀k L₀w)
      (max (⌈144 * C₀o + 12 * Kw⌉₊ + 8) (max L₀p ⌈prodLb⌉₊)) := ⟨_, rfl⟩
  have hLk : L₀k ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLw' : L₀w ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLp : L₀p ≤ Lo := hLod ▸ le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hLb : prodLb ≤ (Lo : ℝ) := by
    have h1 : ⌈prodLb⌉₊ ≤ Lo := hLod ▸ le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hLc8 : ⌈144 * C₀o + 12 * Kw⌉₊ + 8 ≤ Lo :=
    hLod ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hLc : 144 * C₀o + 12 * Kw + 8 ≤ (Lo : ℝ) := by
    have h2 := Nat.le_ceil (144 * C₀o + 12 * Kw)
    have h3 : ((⌈144 * C₀o + 12 * Kw⌉₊ + 8 : ℕ) : ℝ) ≤ Lo := by exact_mod_cast hLc8
    push_cast at h3
    linarith
  have h7 : 7 ≤ Lo := by omega
  obtain ⟨L₀, hL₀⟩ := thm_flow_masterLZW (allAReq C₀o ηo Lo C₀u ηu Lu Lj C₀a ηa La)
    (fun L => by
      obtain ⟨A₀, hA₀⟩ := obsAReq_ev hC₀o hηo hk hLk (by linarith) L
      obtain ⟨A₁, hA₁⟩ := kabAReq_ev hC₀u hηu hku hLu0 hLu1 L
      obtain ⟨A₃, hA₃⟩ := abwAReq_ev hC₀a hηa hka hLa0 hLa2 L
      by_cases hLL : Lj ≤ L ∧ L ≠ 0
      · haveI : NeZero L := ⟨hLL.2⟩
        obtain ⟨A₂, -, hA₂'⟩ := hLj L hLL.1
        refine ⟨max (max (max 2 (max A₀ A₁)) (2 * A₂)) A₃, fun A hA' => ?_⟩
        have hA := le_trans (le_max_left _ _) hA'
        refine ⟨⟨⟨?_, hA₀ A ?_, hA₁ A ?_⟩, fun _ _ => hA₂' (A / 2) ?_⟩,
          hA₃ A (le_trans (le_max_right _ _) hA')⟩
        · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
        · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
            (le_max_left _ _)) hA
        · exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
            (le_max_left _ _)) hA
        · have := le_trans (le_max_right _ _) hA; linarith
      · refine ⟨max (max 2 (max A₀ A₁)) A₃, fun A hA' => ?_⟩
        have hA := le_trans (le_max_left _ _) hA'
        exact ⟨⟨⟨le_trans (le_max_left _ _) hA,
          hA₀ A (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA),
          hA₁ A (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA)⟩,
          fun h hL => absurd ⟨hL, h.out⟩ hLL⟩, hA₃ A (le_trans (le_max_right _ _) hA')⟩)
    (fun L A c c' ε => allEReq Cq Cl cS C₀o ηo Kw Lo Cpf εpf C₀u ηu Lu C₀a ηa Kwa La L A c c' ε ∧
      pairEReq Cq Cl cS C₀o ηo Kw Lo Cpf εpf C₀u ηu Lu C₀a ηa Kwa La L A c c' ε)
    (fun L A c c' => ((c2RelReqU_ev Cq Cl cS Cpf εpf hw hLw' h7
      (fun L _ hL => (hPf L (hLp.trans hL)).1) L A c c').and
        ((gbEReq_ev L A c c').and ((topReq_ev L A c c').and ((abwEReq_ev hwa hLa1 L A c c').and
          (abwEReqV_ev hwa hLa1 L A c c'))))).and
      (pairEReq_ev Cq Cl cS Cpf εpf hw hLw' h7 (fun L _ hL => (hPf L (hLp.trans hL)).1) hwa hLa1
        L A c c'))
    (fun L ℓ ρ Cf cm ε => ∀ _h : NeZero L, h0EReq L ℓ ρ Cf cm ε)
    (fun L ℓ ρ Cf cm => by
      by_cases hL0 : L = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd hL0 h.out
      · haveI : NeZero L := ⟨hL0⟩
        filter_upwards [h0EReq_ev L ℓ ρ Cf cm] with ε hε
        exact fun _ => hε)
  obtain ⟨-, -, Lwp, hLwp⟩ := cw_wpo_spec
  refine ⟨max Lwp (max L₀ (max Lo (max 49 (max ⌈pauliL0 2⌉₊ (max gbL0 (max Lu (max Lw
    (max Lj (max La (max Ls ⌈12 * Kwa⌉₊)))))))))), fun L _ hL' => ?_⟩
  have hLwpL : Lwp ≤ L := le_trans (le_max_left _ _) hL'
  have hL := le_trans (le_max_right _ _) hL'
  have hL₀L : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLo : Lo ≤ L := by omega
  have hL49 : 49 ≤ L := by omega
  have hLpl : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by
    have : ⌈pauliL0 2⌉₊ ≤ L := by omega
    exact_mod_cast this)
  have hLg : gbL0 ≤ L := by omega
  have hLuL : Lu ≤ L := by omega
  have hLwL : Lw ≤ L := by omega
  have hLjL : Lj ≤ L := by omega
  have hLaL : La ≤ L := by omega
  have hLsL : Ls ≤ L := by omega
  have hLwa : Kwa / L ≤ 1 / 12 := by
    have h1 : ⌈12 * Kwa⌉₊ ≤ L := by omega
    have h2 : 12 * Kwa ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have h3 : (0 : ℝ) < L := Nat.cast_pos.2 (by omega)
    rw [div_le_iff₀ h3]; linarith
  have hlog := log_ge_gbLog hLg
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hNu := hnu L hL8 hLpl
  obtain ⟨Cw, hCw, hWw⟩ := hLwB L hLwL
  obtain ⟨-, hPB⟩ := hPf L (hLp.trans hLo)
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp,
    ⟨⟨⟨hA2, hAx, hAu⟩, hAJ'⟩, hAa⟩, ⟨hcmF, hH0E⟩, hVC, hLV, hZT, hWin, hGD, hSpD, hGN, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx,
    hXm⟩ := hL₀ L hL₀L
  have hAJ := hAJ' inferInstance hLjL
  obtain ⟨ζbar, K, cS2, ε₀, C₁k, C₁w, ε₁, ε₀a, C₁ka, C₁wa, ε₁a,
    ⟨hζ0, hK, hcS2, hLc', hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp,
    hε₀, hC₁k, hKB, hsmk, hεε, hεk, hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab⟩, hEaB, hpowF, hloopF⟩ :=
    (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).2 hLo hAx hLuL hAu (by omega) hAa
  obtain ⟨ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, -⟩ := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.1 (by omega)
  have htopR := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.2.1
  have hEa := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.2.2.1
  have hEv := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.2.2.2
  set c := cR (⟨Pc, 0, ℓ, A, 0, ρ⟩ : RGPar 2 L 1) ((L : ℝ) ^ 2) cm C₂x with hc
  exact ⟨
    ⟨Cq, Cl, cS, hCq, hCl, hcS, hNu, Cpf, εpf, hCpf, hPB, C₀o, ηo, hC₀o, hηo, Kw, hKw, C₀u, ηu,
      hC₀u, hηu, Cw, hCw, hWw, Lo, Lu, hLo, hLuL, hLc, hLb, hL49, hLpl, hlog, ℓ, A, ρ, κ, cg, cm,
      cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hA2, hAx, hAu, hAJ, hVC, hLV, hZT, C₀x,
      ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hXm, c, hc, ζbar, K, cS2, hζ0, hK, hcS2, hLc',
      hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp, ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁,
      hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab, ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, htopR,
      C₀a, ηa, Kwa, La, hC₀a, hηa, hKwa, hLaL, hLwa, hAa, hEa, hLs L hLsL, hEv, hWin, hGD, hSpD, hGN, hcmF, hH0E inferInstance,
      ε₀a, C₁ka, C₁wa, ε₁a, hEaB, hLwp L hLwpL, hpowF, hloopF⟩
  , hC₀u1, hC₀o1⟩

/-- The counting constant `c_bn` of `card_blocks_near 2` is `≥ 1`. -/
theorem eqs_one_le_cbnC : 1 ≤ cbnC := by
  have h := Classical.choose_spec (Obs2.card_blocks_near 2) 1 0 0 (0 : Lam 2 1 0)
    (blockIdx (L := 1) (N := 0) 0) subset_rfl
  refine le_trans ?_ h
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨blk 0 (0 : Lam 2 1 0), Finset.mem_filter.2 ⟨?_, ?_⟩⟩
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · exact subset_nbhd (isPolymer_blockSet 0 _) (mem_blockSet_blk 0 _)

/-- The counting constant `c_{NS}` of `card_small_near 2` is `≥ 1`. -/
theorem eqs_one_le_csN : 1 ≤ PtCorr2.csN 2 := by
  have h := Classical.choose_spec (Obs2.card_small_near 2) 1 0 0 (0 : Lam 2 1 0)
  refine le_trans ?_ h
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨blockSet 0 (blk 0 (0 : Lam 2 1 0)), Finset.mem_filter.2 ⟨mem_smallSets.2
    (isSmall_blockSet 0 _), ?_⟩⟩
  exact subset_nbhd (isPolymer_blockSet 0 _) (mem_blockSet_blk 0 _)

variable {L : ℕ} [NeZero L]

/-- `Γ_w > 0` (`Γ_w ≥ c_bn ≥ 1`). -/
theorem MasterCore.eqs_rdtΓ_pos (D : MasterCore L) (hc : 0 ≤ D.c) (hε : 0 ≤ D.ε) :
    0 < D.rdtΓ := by
  obtain ⟨-, -, -, -, -, -, hBk, -, -, -⟩ := D.consts_nonneg
  have hcP : 0 ≤ D.cP := by
    show 0 ≤ (cbnC : ℝ) * D.Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := D.hCpf L; positivity
  have hb : (1 : ℝ) ≤ cbnC := by exact_mod_cast eqs_one_le_cbnC
  have hC : 1 ≤ D.rdtC := by
    unfold MasterCore.rdtC
    have : (0 : ℝ) ≤ 1280 * Obs2.locK 2 ^ 2 * (8 / (7 * L)) := by positivity
    nlinarith
  have t1 : 0 ≤ 8 * (PtCorr2.csN 2 : ℝ) * (120 * D.Bk * (D.c * D.ε)) := by positivity
  have t3 : 0 ≤ 5 * D.cP * (D.c * D.ε) := by positivity
  unfold MasterCore.rdtΓ
  linarith

/-- `B > 0` when `1 ≤ C₀o`. -/
theorem MasterCore.eqs_Bk_pos (D : MasterCore L) (h : 1 ≤ D.C₀o) : 0 < D.Bk := by
  unfold MasterCore.Bk kB
  have hA2 := D.hA2
  have hL : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hθ : 0 < kθ0 L D.A D.C₀o D.ηo := by
    unfold kθ0
    exact mul_pos (by linarith) (add_pos_of_pos_of_nonneg (by positivity)
      (Real.rpow_nonneg (by linarith) _))
  have hcx : 0 < cx D.κ D.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id D.hC2
    unfold cx; exact div_pos (by linarith) (by linarith)
  have hC₁ := D.hC₁k
  positivity

/-- **One master construction with `0 < c_{ab}`, `0 < B`** (and `1 ≤ C₀u`, `1 ≤ C₀o`). -/
theorem eqs_master : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ M : MasterFacts L, 1 ≤ M.core.C₀u ∧ 1 ≤ M.core.C₀o ∧ 0 < M.k2cab ∧ 0 < M.core.Bk := by
  obtain ⟨L₀, h⟩ := eqs_masterCore_exists
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨D, hD, hD'⟩ := h L hL
  exact ⟨D.toFacts, hD, hD', D.toFacts.k2cab_pos_of hD, D.eqs_Bk_pos hD'⟩

end

end Spin2
