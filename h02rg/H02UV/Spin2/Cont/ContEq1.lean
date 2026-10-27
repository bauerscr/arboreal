import Spin2.Master.MasterAllFacts
import Spin2.Cont.ContK2c

set_option autoImplicit false

/-!
# B3, T6, final assembly: `0 < c_{ab}` without editing the master construction

* **`kobsBoundsU_mono_C₀`**: `KObsBoundsU L A C₀ η ε₀ C₁` is monotone in `C₀` (for `0 ≤ A`);
  `C₀` enters only through `θ₀ = C₀(L²/L³ + (A/2)^{−η})`, multiplying a nonnegative quantity.
* **`kobs_bounds_U_one`**: `kobs_bounds_U` with `1 ≤ C₀` (enlarge `C₀` to `max C₀ 1`).
* **`masterCore_exists_C₀`**: a copy of `masterCore_exists` run with `kobs_bounds_U_one`; it
  produces a `MasterCore` with `1 ≤ C₀u`.
* **`MasterFacts.k2cab_pos_of`**, **`thm_master_all_cab`**: for that construction `0 < c_{ab}`
  (`c_{ab} = 10·kB2(θ₀, C₁, c_x, 8B)`, `θ₀ > 0`, `c_x > 0`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **`KObsBoundsU` is monotone in `C₀`** (for `0 ≤ A`). -/
theorem kobsBoundsU_mono_C₀ {L : ℕ} [NeZero L] {A C₀ C₀' η ε₀ C₁ : ℝ} (hA : 0 ≤ A)
    (hC : C₀ ≤ C₀') (h : KObsBoundsU L A C₀ η ε₀ C₁) : KObsBoundsU L A C₀' η ε₀ C₁ := by
  intro N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 c P w hw hwa hwb hwab o ho hl hs hab
    wl dd kb r m k₁ k₂ hwl hdd hkb hr hm0 hrm hk₁ hk₂ hW hDn hKn hrr hwd hε hε' hVb hWb hK1 hK2 U hU
  refine (h N R j hV st hI g μ D K hD hK hm hg ηz h1 h2 h3 h4 c P w hw hwa hwb hwab o ho hl hs hab
    wl dd kb r m k₁ k₂ hwl hdd hkb hr hm0 hrm hk₁ hk₂ hW hDn hKn hrr hwd hε hε' hVb hWb hK1 hK2 U
    hU).trans (ENNReal.ofReal_le_ofReal ?_)
  have hX : 0 ≤ 8 * kb + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) := by
    have : 0 ≤ r / m := div_nonneg hr.le hm0.le
    positivity
  have hθ : 0 ≤ (L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η) :=
    add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _)
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hθ) hX
  linarith

/-- **`kobs_bounds_U` with `1 ≤ C₀`.** -/
theorem kobs_bounds_U_one : ∃ (C₀ η : ℝ) (L₀ : ℕ), 1 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsU L A C₀ η ε₀ C₁ := by
  obtain ⟨C₀, η, L₀, -, hη, h⟩ := kobs_bounds_U
  refine ⟨max C₀ 1, η, L₀, le_max_right _ _, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, hA⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA' => ?_⟩
  obtain ⟨ε₀, C₁, hε₀, hC₁, hK⟩ := hA A hA'
  exact ⟨ε₀, C₁, hε₀, hC₁, kobsBoundsU_mono_C₀ (by linarith) (le_max_left _ _) hK⟩

set_option maxHeartbeats 4000000 in
/-- **The master construction with `1 ≤ C₀u`** (copy of `masterCore_exists` with
`kobs_bounds_U_one`). -/
theorem masterCore_exists_C₀ : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ D : MasterCore L, 1 ≤ D.C₀u := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hnu⟩ := nu_sharp
  obtain ⟨Cpf, εpf, L₀p, hCpf, hPf⟩ := prod_raw_step
  obtain ⟨C₀o, ηo, L₀k, hC₀o, hηo, hk⟩ := kobs_bounds
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
  , hC₀u1⟩

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- **`0 < c_{ab}` when `1 ≤ C₀u`.** -/
theorem k2cab_pos_of (h : 1 ≤ M.core.C₀u) : 0 < M.k2cab := by
  obtain ⟨-, hC₁, -⟩ := Classical.choose_spec (Classical.choose_spec M.k2_cab_spec)
  unfold k2cab kB2
  have hA2 := M.core.hA2
  have hL : (0 : ℝ) < L := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))
  have hθ : 0 < kθ0 L M.core.A M.core.C₀u M.core.ηu := by
    unfold kθ0
    exact mul_pos (by linarith) (add_pos_of_pos_of_nonneg (by positivity)
      (Real.rpow_nonneg (by linarith) _))
  have hcx : 0 < cx M.core.κ M.core.cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id M.core.hC2
    unfold cx; exact div_pos (by linarith) (by linarith)
  have hB := M.core.consts_nonneg.2.2.2.2.2.2.1
  positivity

end MasterFacts

/-- **One master construction with `0 < c_{ab}`.** -/
theorem thm_master_all_cab : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ M : MasterFacts L, 1 ≤ M.core.C₀u ∧ 0 < M.k2cab := by
  obtain ⟨L₀, h⟩ := masterCore_exists_C₀
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨D, hD⟩ := h L hL
  exact ⟨D.toFacts, hD, D.toFacts.k2cab_pos_of hD⟩

end

end Spin2
