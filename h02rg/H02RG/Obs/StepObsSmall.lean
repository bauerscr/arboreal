import Obs.StepObsSmallAux

/-!
# Theorem `thm:step-obs`: the small set contribution (`SmallObsStmt'`)

**`obs_smallset_bound_proof'`**: the corrected small-set statement `SmallObsStmt'` of
`Obs.StepObsFix` (with the separation hypothesis `SepHyp` and the disconnected two-block terms
`LpairG` moved from the large-set sum, `e:Kquad-obs`).

The proof follows the text (`lem:Pjj+1`, `lem:smallset-Vobs1`, `lem:smallset-Vobs`,
`lem:smallset-Kobs`, `e:Kblock-obs`, `e:Ksmallset-obs`):
`π_obs (𝓛_𝒮(U) + 𝓛_pair(U)) = ∑_{X ∈ I(U)} π_obs(pre(U, X) T(X))` (`sumS_eq`), and each summand
is `pre (Lt + r) + pre^∅ m + π_obs(pre) T^∅` (`term_decomp`) with
* `Lt = 𝔼 θ π_obs (1 - Loc_X) K(X)` bounded by `prop:Loc-obs` (ii) (`Lt_bound`, `lem:smallset-Kobs`);
  only the `O(1)` small sets containing `a` or `b` contribute;
* `m` the `P^obs(B, B')` parts of the single-block (`Mb_eq`) and two-block (`pair_eq`) terms, which
  cancel up to the differences of the bulk prefactors (`cancel_bound`, using `SepHyp`);
* `r` the remainder, which is second order with a factor `‖V^∅‖ + ‖K^∅‖` or `‖K^obs‖` (`r_bound`);
* `π_obs(pre) T^∅`, bounded by `e:uobs+`, `e:vobs+` and Step's small-set bounds.

The statement `SmallObsStmt` of `Obs.StepObsStmt` is false (see `Obs.StepObsFix`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

set_option maxHeartbeats 16000000 in
/-- **The small set estimate** (corrected statement `SmallObsStmt'`). -/
theorem obs_smallset_bound_proof' {d : ℕ} (hd : 3 ≤ d) : SmallObsStmt' d := by
  classical
  obtain ⟨M, εb, LB, hM1, hεb0, hεb1, hLB, hBB⟩ := block_bounds hd
  obtain ⟨Cl, Ll, hCl, hLt⟩ := Lt_bound hd
  obtain ⟨C₂, ε₁, Lt, hC₂, hε₁, htb⟩ := term_bound hd
  obtain ⟨c₀, Lp, hc₀, hLp, hpert⟩ := pert12 hd
  obtain ⟨c₀', Lpo, hc₀', hc₀'1, hLpo, hpertO⟩ := pert12_obs hd
  obtain ⟨cs, hcs⟩ := card_small_containing d
  obtain ⟨c₁, hc₁⟩ := card_Iset d (by omega)
  set G : ℝ := 2 ^ (2 ^ d) with hG
  set C₀ : ℝ := 2 * cs * G * (max Cl 0 + 1) +
    (((c₁ : ℝ) + 1) * (G * (30 * 2 ^ d) + G * 4 * (3 * C₂ + M ^ 2)) + 16) * M ^ 5 with hC₀
  have hG1 : (1 : ℝ) ≤ G := one_le_pow₀ (by norm_num)
  have hCl' : 0 ≤ max Cl 0 + 1 := by positivity
  refine ⟨C₀, 12 * d, max (max LB Ll) (max Lt (max Lp Lpo)), by positivity, ?_⟩
  intro L _ hL
  have hLB' : LB ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLl' : Ll ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLt' : Lt ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLp' : Lp ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLpo' : Lpo ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLB.trans hLB')
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  refine ⟨1, le_rfl, fun A hA => ?_⟩
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK1 : 1 ≤ K₂ := one_le_K₂ hd
  have hK0 : 0 ≤ K₂ := by linarith
  have hLd1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL1
  set δ₀ : ℝ := min (min εb ε₁) (min c₀ c₀') with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (lt_min hεb0 hε₁) (lt_min hc₀ hc₀')
  have hδ₀1 : δ₀ ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans hεb1)
  set ε₀ : ℝ := δ₀ / (10 * M * K₂ * (L : ℝ) ^ d) with hε₀
  have hden : 1 ≤ 10 * M * K₂ * (L : ℝ) ^ d := by
    have : 1 ≤ M * K₂ := one_le_mul_of_one_le_of_one_le hM1 hK1
    nlinarith
  refine ⟨ε₀, by positivity, ?_⟩
  intro N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b h hsep hbk hob U hU
  have hab := h.hab
  have hCsym := symm_of_goodCov h.cov a b
  obtain ⟨hvb, hkb, hvb0, hkb0, ht⟩ := real_of_le (by positivity) hbk
  obtain ⟨hvo, hko, hvo0, hko0, hs⟩ := real_of_le (by positivity) hob
  set vb := (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb).toReal with hvb_def
  set kb := (Knorm j (ellj d L ℓ₀ j) A (bulkK K)).toReal with hkb_def
  set vo := (VnormObs c ℓ₀ a b j Vo).toReal with hvo_def
  set ko := (KnormObs c ℓ₀ a b j A K).toReal with hko_def
  set t := vb + kb with ht_def
  set s := vo + ko with hs_def
  set W : ℝ := M * K₂ with hW
  have hW1 : 1 ≤ W := one_le_mul_of_one_le_of_one_le hM1 hK1
  have ht0 : 0 ≤ t := by positivity
  have hs0 : 0 ≤ s := by positivity
  -- smallness
  have hεd : ε₀ * (10 * M * K₂ * (L : ℝ) ^ d) = δ₀ := by
    rw [hε₀]; field_simp
  have htL : t * (L : ℝ) ^ d ≤ δ₀ := by
    have : t * (10 * M * K₂ * (L : ℝ) ^ d) ≤ δ₀ := by rw [← hεd]; gcongr
    nlinarith [mul_nonneg ht0 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ d)]
  have hsL : K₂ * s * (L : ℝ) ^ d ≤ δ₀ := by
    have : s * (10 * M * K₂ * (L : ℝ) ^ d) ≤ δ₀ := by rw [← hεd]; gcongr
    have h1 : K₂ * s * (L : ℝ) ^ d ≤ s * (10 * M * K₂ * (L : ℝ) ^ d) := by
      have : 0 ≤ K₂ * s * (L : ℝ) ^ d := by positivity
      nlinarith
    linarith
  have hWs : W * s ≤ 1 / 10 := by
    have : s * (10 * M * K₂ * (L : ℝ) ^ d) ≤ δ₀ := by rw [← hεd]; gcongr
    have h2 : 10 * (W * s) ≤ s * (10 * M * K₂ * (L : ℝ) ^ d) := by
      rw [hW]; have : 0 ≤ M * K₂ * s := by positivity
      nlinarith
    linarith
  have hMt : M * t ≤ 1 / 10 := by
    have : t * (10 * M * K₂ * (L : ℝ) ^ d) ≤ δ₀ := by rw [← hεd]; gcongr
    have h2 : 10 * (M * t) ≤ t * (10 * M * K₂ * (L : ℝ) ^ d) := by
      have : 0 ≤ M * t := by positivity
      have : 1 ≤ K₂ * (L : ℝ) ^ d := one_le_mul_of_one_le_of_one_le hK1 hLd1
      nlinarith
    linarith
  have ht1 : t ≤ 1 := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith
  have hvos : vo ≤ s := by linarith
  have hkos : ko ≤ s := by linarith
  have htd : t ≤ δ₀ / (L : ℝ) ^ d := by rw [le_div_iff₀ (by positivity)]; exact htL
  have hsd : K₂ * s ≤ δ₀ / (L : ℝ) ^ d := by rw [le_div_iff₀ (by positivity)]; exact hsL
  have hδd : δ₀ / (L : ℝ) ^ d ≤ δ₀ := div_le_self hδ₀0.le hLd1
  have hδb : δ₀ ≤ εb := (min_le_left _ _).trans (min_le_left _ _)
  have hδ1 : δ₀ ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hδc : δ₀ ≤ c₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ₀ ≤ c₀' := (min_le_right _ _).trans (min_le_right _ _)
  -- ENNReal forms
  have hbulkE : ∀ r : ℝ, t ≤ r → Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb +
      Knorm j (ellj d L ℓ₀ j) A (bulkK K) ≤ ENNReal.ofReal r := by
    intro r hr
    rw [hvb, hkb, ← ENNReal.ofReal_add hvb0 hkb0]; exact ENNReal.ofReal_le_ofReal hr
  have hobsE : ∀ r : ℝ, K₂ * s ≤ r → ENNReal.ofReal K₂ *
      (VnormObs c ℓ₀ a b j Vo + KnormObs c ℓ₀ a b j A K) ≤ ENNReal.ofReal r := by
    intro r hr
    rw [hvo, hko, ← ENNReal.ofReal_add hvo0 hko0, ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal hr
  -- block bounds
  have hε₀δ : ε₀ ≤ δ₀ := div_le_self hδ₀0.le hden
  obtain ⟨hpoly, hblk⟩ := hBB L hLB' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h vb kb vo ko
    hvb0 hkb0 hvo0 hko0 hvb hkb hvo hko (ht.trans (hε₀δ.trans hδb)) (hsd.trans (hδd.trans hδb))
  simp only [← hK₂] at hpoly hblk
  set e : ℝ := M * t with he_def
  set o : ℝ := 5 * W * s with ho_def
  set α : ℝ := 3 * W * s with hα_def
  set y : ℝ := W * (ko + t) with hy_def
  set q : ℝ := M * ko with hq_def
  set ρ : ℝ := W * s * t with hρ_def
  have hM0 : 0 ≤ M := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hKW : K₂ ≤ W := by rw [hW]; nlinarith
  -- the block bounds in the form of `r_bound`
  have hvh : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmj c ℓ₀ a b j (Vhat j Vo K a b p) ≤ ENNReal.ofReal (vo + M * ko) := by
    intro p hp
    obtain ⟨hV, hQ, -⟩ := hblk p hp
    exact nn_sub hvo0 (by positivity) hV hQ
  have hbl : ∀ p ∈ blockIdx (L := L) (N := N) j,
      nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p))) ≤ ENNReal.ofReal e ∧
      nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p)) ≤ ENNReal.ofReal o ∧
      nrmD c ℓ₀ a b j (Aq j C Vo K a b p) ≤ ENNReal.ofReal α ∧
      nrmD c ℓ₀ a b j (Yq j C Vb Vo K a b p) ≤ ENNReal.ofReal y ∧
      nrmD c ℓ₀ a b j (dIo j C Vb Vo K a b p) ≤ 1 ∧
      nrmj c ℓ₀ a b j (Vobs j Vo a b p) ≤ ENNReal.ofReal vo ∧
      nrmj c ℓ₀ a b j (QobsO a b j K p) ≤ ENNReal.ofReal q ∧
      nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤ ENNReal.ofReal ρ := by
    intro p hp
    obtain ⟨hV, hQ, hρ', he', -⟩ := hblk p hp
    have hρ : nrmD c ℓ₀ a b j (rhoO j C Vb Vo K a b p) ≤ ENNReal.ofReal ρ :=
      hρ'.trans (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hρ_def, hW])))
    have hvt : nrmj c ℓ₀ a b (j + 1) (vt j C Vo K a b p) ≤ ENNReal.ofReal (W * s) :=
      (hpoly _ (isPolymer_blockSet j p)).1.trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hW])))
    have ho : nrmD c ℓ₀ a b j (πobs (dIo j C Vb Vo K a b p)) ≤ ENNReal.ofReal o := by
      refine (o_bound hd hL4 hℓ₀ hvo0 (by positivity) (by positivity) hV hvt hρ).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have h1 : K₂ * (vo + vo * vo) ≤ 2 * (W * s) := by
        have : vo * vo ≤ vo := by nlinarith
        have : K₂ * (vo + vo * vo) ≤ K₂ * (2 * s) := by gcongr; linarith
        nlinarith
      have h2 : W * s * (W * s) ≤ W * s := by
        have := mul_le_mul_of_nonneg_left (hWs.trans (by norm_num : (1 : ℝ) / 10 ≤ 1))
          (by positivity : 0 ≤ W * s)
        linarith
      have h3 : ρ ≤ W * s := by rw [hρ_def]; nlinarith
      rw [ho_def]; nlinarith
    refine ⟨he', ho, ?_, ?_, ?_, hV, hQ, hρ⟩
    · refine (A_bound hd hL4 hℓ₀ (by positivity) (by positivity) (hvh p hp) hvt).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have : K₂ * (vo + M * ko) ≤ W * s := by
        rw [hW]; have : vo + M * ko ≤ M * s := by nlinarith
        nlinarith
      rw [hα_def]; nlinarith
    · refine (Y_bound hd hL4 hℓ₀ (by positivity) (by positivity) hQ hρ).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have h1 : K₂ * q = W * ko := by rw [hq_def, hW]; ring
      have h2 : ρ ≤ W * t := by rw [hρ_def]; nlinarith
      rw [hy_def, h1]; nlinarith
    · have e1 := eq_emb_add_πobs (dIo j C Vb Vo K a b p)
      calc nrmD c ℓ₀ a b j (dIo j C Vb Vo K a b p)
          = nrmD c ℓ₀ a b j (emb (bulk (dIo j C Vb Vo K a b p)) +
              πobs (dIo j C Vb Vo K a b p)) := by rw [← e1]
        _ ≤ ENNReal.ofReal (e + o) := dn_add (by positivity) (by positivity) he' ho
        _ ≤ 1 := by
            rw [← ENNReal.ofReal_one]; refine ENNReal.ofReal_le_ofReal ?_
            rw [he_def, ho_def]; nlinarith
  have hUp : IsPolymer j U := IsPolymer.of_succ hU.1
  have hLdpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hhj : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓj := ellj_pos (d := d) hL0 hℓ₀ (j + 1)
  have hGE : ∀ n : ℕ, n ≤ 2 ^ d → (2 : ENNReal) ^ n ≤ ENNReal.ofReal G := by
    intro n hn
    rw [hG, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hn
  -- the prefactors
  have hpre : ∀ X ∈ Iset j U,
      nrmj c ℓ₀ a b (j + 1) (prefG j (obsI j C Vb Vo K a b) U X) ≤ ENNReal.ofReal G := by
    intro X hX
    obtain ⟨hcl, hXp, -, -⟩ := mem_Iset hX
    refine (hpertO L hLpo' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h
      (hbulkE _ (htd.trans (div_le_div_of_nonneg_right hδc' hLdpos.le)))
      (hobsE _ (hsd.trans (div_le_div_of_nonneg_right hδc' hLdpos.le))) X U hXp hcl).trans ?_
    exact hGE _ (nb_Iset (by omega) hX).1
  have hβ : ∀ X ∈ Iset j U, Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
      ((pref j C Vb (bulkK K) U X : EvR (Lam d L N)) : Alg d L N) ≤ 2 ^ nb j X := by
    intro X hX
    obtain ⟨hcl, hXp, -, -⟩ := mem_Iset hX
    exact hpert L hLp' N j hj ℓ₀ hℓ₀ C h.cov Vb (bulkK K) A hA h.bulk
      (hbulkE _ (htd.trans (div_le_div_of_nonneg_right hδc hLdpos.le))) X U hXp hcl
  have hπpre : ∀ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1)
      (πobs (prefG j (obsI j C Vb Vo K a b) U X)) ≤ ENNReal.ofReal (G * (4 * (W * s))) := by
    intro X hX
    obtain ⟨hcl, hXp, -, -⟩ := mem_Iset hX
    have hWb : nrmj c ℓ₀ a b (j + 1) (uObsX j C Vo K a b U -
        splitO c (nextObs C j Vo K a b) a b (U \ X)) ≤ ENNReal.ofReal (2 * (W * s)) := by
      refine (nn_sub (by positivity) (by positivity) (hpoly U hUp).2
        (hpoly _ (IsPolymer.sdiff hUp hXp)).1).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hW]; ring
    refine (πobs_pref_bound (by omega) hℓ₀ hUp hXp (by positivity) (hβ X hX) hWb).trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (hGE _ (nb_Iset (by omega) hX).1) (ENNReal.ofReal_le_ofReal ?_)
    have := exp_sub_one_le_two_mul (by positivity : (0 : ℝ) ≤ 2 * (W * s)) (by linarith)
    linarith
  -- the bulk parts of the summands
  have hbT : ∀ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1) (emb (bulk (TX j C Vb Vo K a b X))) ≤
      ENNReal.ofReal ((3 * C₂ + M ^ 2) * t) := by
    intro X hX
    obtain ⟨hcl, hXp, -, hXs⟩ := mem_Iset hX
    rw [nrmj_emb]
    by_cases hc : IsConn j X
    · have hsm : IsSmall j X := hXs.resolve_right (fun h' => h'.2 hc.2)
      rw [bulk_TX_small hc]
      refine (htb L hLt' N j hj ℓ₀ hℓ₀ C h.cov Vb (bulkK K) A hA h.bulk
        (hbulkE _ (ht.trans (hε₀δ.trans hδ1))) X hsm).trans ?_
      rw [hvb, hkb, ← ENNReal.ofReal_pow hvb0, ← ENNReal.ofReal_pow hkb0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have hf1 : (if j + 1 < N then (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-dplus d) else 1) ≤ 1 := by
        split_ifs
        · have h1 : (L : ℝ) ^ (-(d : ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
          have h2 : (L : ℝ) ^ (-dplus d) ≤ 1 := by
            refine Real.rpow_le_one_of_one_le_of_nonpos hL1 ?_
            have : 0 ≤ dplus d := by
              unfold dplus
              have : (3 : ℝ) ≤ d := by exact_mod_cast hd
              exact le_min (by linarith) (by norm_num)
            linarith
          exact mul_le_one₀ h1 (by positivity) h2
        · exact le_rfl
      have hf0 : 0 ≤ (if j + 1 < N then (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-dplus d) else 1) := by
        split_ifs <;> positivity
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₂,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hvb1 : vb ≤ 1 := by linarith
      have hkb1 : kb ≤ 1 := by linarith
      have e1 : C₂ * (if j + 1 < N then (L : ℝ) ^ (-(d : ℝ)) * (L : ℝ) ^ (-dplus d) else 1) * kb ≤
          C₂ * kb := by
        have := mul_le_mul_of_nonneg_left hf1 hC₂
        nlinarith
      have e2 : C₂ * (vb ^ 2 + kb ^ 2) ≤ C₂ * (vb + kb) := by
        gcongr <;> nlinarith
      nlinarith
    · have h2 : nb j X = 2 := by
        rcases hXs with h' | h'
        · exact absurd ⟨h'.1, h'.2.1⟩ hc
        · exact h'.1
      rw [bulk_TX_pair hc]
      refine (tNorm_EC_le hhj hℓj h.cov.psd h.cov.norm _).trans ?_
      refine (tNorm_prod_le hhj hℓj _ _).trans ?_
      have : ∀ p ∈ blocks j X, Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
          ((dI j C Vb (bulkK K) p : EvR (Lam d L N ⊕ Lam d L N)) :
            Grassmann.N (Lam d L N ⊕ Lam d L N)) ≤ ENNReal.ofReal e := by
        intro p hp
        have := (hbl p (mem_blockIdx_of_mem_blocks hp)).1
        rwa [nrmD_emb, bulk_dIo] at this
      refine (prod_le_prod' this).trans ?_
      rw [prod_const, ← ENNReal.ofReal_pow (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show (blocks j X).card = nb j X from rfl, h2, he_def]
      have : M ^ 2 * t ^ 2 ≤ M ^ 2 * t := by
        have := mul_le_mul_of_nonneg_left (show t ^ 2 ≤ t by nlinarith) (sq_nonneg M)
        linarith
      nlinarith [mul_nonneg hC₂ ht0]
  -- piece 1: `lem:smallset-Kobs`
  set f' : ℝ := if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hf'
  have hf'0 : 0 ≤ f' := by rw [hf']; split_ifs <;> positivity
  set F : Finset (Finset (Lam d L N)) :=
    (smallSets (L := L) (N := N) j).filter (fun X => blockSet j (blk j a) ⊆ X) ∪
      (smallSets (L := L) (N := N) j).filter (fun X => blockSet j (blk j b) ⊆ X) with hF
  have hFc : F.card ≤ 2 * cs := by
    refine (card_union_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (hcs L N j _ (mem_image.2 ⟨a, mem_univ _, rfl⟩))
      (hcs L N j _ (mem_image.2 ⟨b, mem_univ _, rfl⟩))
  have hP1x : ∀ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1)
      (prefG j (obsI j C Vb Vo K a b) U X * LtX j C K a b X) ≤
        if X ∈ F then ENNReal.ofReal (G * (Cl * f' * ko)) else 0 := by
    intro X hX
    obtain ⟨-, -, -, hXs⟩ := mem_Iset hX
    by_cases hc : IsConn j X
    · have hsm : IsSmall j X := hXs.resolve_right (fun h' => h'.2 hc.2)
      obtain ⟨hb1, hb2⟩ := hLt L hLl' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA h X hsm
      by_cases hab' : a ∈ X ∨ b ∈ X
      · have hXF : X ∈ F := by
          rcases hab' with ha' | hb'
          · exact mem_union_left _ (mem_filter.2 ⟨mem_smallSets.2 hsm,
              blockSet_subset hsm.1 (blk_mem_blocks ha')⟩)
          · exact mem_union_right _ (mem_filter.2 ⟨mem_smallSets.2 hsm,
              blockSet_subset hsm.1 (blk_mem_blocks hb')⟩)
        rw [if_pos hXF, LtX, if_pos hc]
        refine (nrmj_mul_le (by omega) hℓ₀ _ _ _).trans ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul' (hpre X hX) (hb1.trans (le_of_eq ?_))
        rw [hko, ← ENNReal.ofReal_mul (by positivity)]
      · push Not at hab'
        rw [LtX, if_pos hc, hb2 hab'.1 hab'.2, map_zero, map_zero, mul_zero, nrmj_zero]
        exact zero_le
    · rw [LtX, if_neg hc, mul_zero, nrmj_zero]; exact zero_le
  have hP1 : ∑ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1)
      (prefG j (obsI j C Vb Vo K a b) U X * LtX j C K a b X) ≤
        ENNReal.ofReal (2 * cs * (G * (Cl * f' * ko))) := by
    refine (sum_le_sum hP1x).trans ?_
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * cs by positivity)]
    refine mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ((Iset j U).filter (fun X => X ∈ F)).card ≤ 2 * cs :=
      (card_le_card fun X hX => (mem_filter.1 hX).2).trans hFc
    exact_mod_cast this
  -- piece 2: the remainders
  set Q : ℝ := (ko + t) * (t + s) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hP2 : ∑ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1)
      (prefG j (obsI j C Vb Vo K a b) U X * (πobs (TX j C Vb Vo K a b X) - LtX j C K a b X -
        mX j C Vo K a b X)) ≤
        ((Iset j U).card : ENNReal) * ENNReal.ofReal (G * (30 * 2 ^ d * W ^ 3 * Q)) := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun X hX => ?_
    refine (nrmj_mul_le (by omega) hℓ₀ _ _ _).trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (hpre X hX) ((r_bound hd hL4 hℓ₀ h (by positivity) (by positivity)
      (by positivity) (by positivity) hvo0 (by positivity) (by positivity) hbl hX).trans
      (ENNReal.ofReal_le_ofReal ?_))
    exact real_R d hW1 hM1 hK1 rfl ht0 hko0 hvo0 hvos hkos
  -- piece 4: the bulk parts
  have hP4 : ∑ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1)
      (πobs (prefG j (obsI j C Vb Vo K a b) U X) * emb (bulk (TX j C Vb Vo K a b X))) ≤
        ((Iset j U).card : ENNReal) *
          ENNReal.ofReal (G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t)) := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun X hX => ?_
    refine (nrmj_mul_le (by omega) hℓ₀ _ _ _).trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' (hπpre X hX) (hbT X hX)
  -- piece 3: the cancellation
  have hpaI : blk j a ∈ blockIdx (L := L) (N := N) j := mem_image.2 ⟨a, mem_univ _, rfl⟩
  have hpbI : blk j b ∈ blockIdx (L := L) (N := N) j := mem_image.2 ⟨b, mem_univ _, rfl⟩
  set π : ℝ := 2 * K₂ ^ 2 * (vo + M * ko) * (vo + M * ko) with hπ_def
  have hπ : nrmj c ℓ₀ a b (j + 1) (PobsBB C j Vo K a b (blk j a) (blk j b)) ≤
      ENNReal.ofReal π := by
    rw [PobsBB]
    exact (nrmj_half_le' _).trans
      (nn_ECT hd hL4 hℓ₀ h.cov (by positivity) (hvh _ hpaI) (hvh _ hpbI))
  have hδ : blk (j + 1) a = blk (j + 1) b → blk j a ≠ blk j b →
      clo j (blockSet (L := L) (N := N) j (blk j a)) = U →
      ∀ q ∈ ({blk j a, blk j b} : Finset (Fin d → ℕ)),
      nrmj c ℓ₀ a b (j + 1) (emb (bulk (prefG j (obsI j C Vb Vo K a b) U (blockSet j q))) -
        emb (bulk (prefG j (obsI j C Vb Vo K a b) U
          (blockSet j (blk j a) ∪ blockSet j (blk j b))))) ≤ ENNReal.ofReal (4 * (M * t)) := by
    intro hs1' hpab hUa q hq
    have haBa : a ∈ blockSet (L := L) (N := N) j (blk j a) := Loc.mem_blockSet.2 rfl
    have hbBb : b ∈ blockSet (L := L) (N := N) j (blk j b) := Loc.mem_blockSet.2 rfl
    have hcab : blocks (j + 1) (blockSet (L := L) (N := N) j (blk j a) ∪ blockSet j (blk j b)) =
        blocks (j + 1) (blockSet (L := L) (N := N) j (blk j a)) := by
      rw [blocks_union, clo_blockSet_eq haBa, clo_blockSet_eq hbBb, hs1', union_self]
    have hclab : clo j (blockSet (L := L) (N := N) j (blk j a) ∪ blockSet j (blk j b)) = U :=
      (clo_congr hcab).trans hUa
    have hsubU : blockSet (L := L) (N := N) j (blk j a) ∪ blockSet j (blk j b) ⊆ U :=
      hclab ▸ subset_clo j _
    have hpolab : IsPolymer j (blockSet (L := L) (N := N) j (blk j a) ∪ blockSet j (blk j b)) :=
      IsPolymer.union (isPolymer_blockSet j _) (isPolymer_blockSet j _)
    have hnbab : nb j (blockSet (L := L) (N := N) j (blk j a) ∪ blockSet j (blk j b)) = 2 := by
      rw [nb, blocks_union, blocks_blockSet_of_mem haBa, blocks_blockSet_of_mem hbBb]
      exact card_pair hpab
    have hprefab : Tj d (L : ℝ) (j + 1) (ellj d L ℓ₀ (j + 1))
        ((pref j C Vb (bulkK K) U (blockSet j (blk j a) ∪ blockSet j (blk j b)) :
          EvR (Lam d L N)) : Alg d L N) ≤ 4 := by
      refine (hpert L hLp' N j hj ℓ₀ hℓ₀ C h.cov Vb (bulkK K) A hA h.bulk
        (hbulkE _ (htd.trans (div_le_div_of_nonneg_right hδc hLdpos.le))) _ U hpolab
        hclab).trans ?_
      rw [hnbab]; norm_num
    have key : ∀ q q' : Fin d → ℕ, q ≠ q' → q' ∈ blockIdx (L := L) (N := N) j →
        blockSet (L := L) (N := N) j q ∪ blockSet j q' =
          blockSet j (blk j a) ∪ blockSet j (blk j b) →
        nrmj c ℓ₀ a b (j + 1) (emb (bulk (prefG j (obsI j C Vb Vo K a b) U (blockSet j q))) -
          emb (bulk (prefG j (obsI j C Vb Vo K a b) U
            (blockSet j (blk j a) ∪ blockSet j (blk j b))))) ≤ ENNReal.ofReal (4 * (M * t)) := by
      intro q q' hqq hq'I hun
      have hsub : blockSet (L := L) (N := N) j q' ⊆ U :=
        (subset_union_right.trans hun.le).trans hsubU
      have hne : (blockSet (L := L) (N := N) j q').Nonempty := by
        obtain ⟨x, -, hx⟩ := mem_image.1 hq'I
        exact ⟨x, Loc.mem_blockSet.2 hx⟩
      rw [← map_sub, nrmj_emb, bulk_prefG j C Vb Vo K a b _ _ hUp,
        bulk_prefG j C Vb Vo K a b _ _ hUp, ← hun, pref_diff hqq hUp hsub hne, hun]
      refine (tNorm_mul_le' hhj hℓj _ _).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      exact mul_le_mul' hprefab (hblk q' hq'I).2.2.2.2
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact key _ _ hpab hpbI rfl
    · exact key _ _ (Ne.symm hpab) hpaI (union_comm _ _)
  have hP3 := cancel_bound (Vb := Vb) hd hℓ₀ hab hsep hCsym.symm (U := U) (by positivity)
    (by positivity) hπ hδ
  -- assembling
  by_cases hIe : Iset j U = ∅
  · rw [sumS_eq, hIe, sum_empty, map_zero, wnormO, nrmj_zero, mul_zero]; exact zero_le
  obtain ⟨X₀, hX₀⟩ := nonempty_iff_ne_empty.2 hIe
  have hw1 : nb (j + 1) U - 2 ^ d = 0 := Nat.sub_eq_zero_of_le (nb_Iset (by omega) hX₀).2
  rw [wnormO, hw1, pow_zero, ENNReal.ofReal_one, one_mul, sumS_eq]
  have hsplit : πobs (∑ X ∈ Iset j U, prefG j (obsI j C Vb Vo K a b) U X * TX j C Vb Vo K a b X) =
      ∑ X ∈ Iset j U, prefG j (obsI j C Vb Vo K a b) U X * LtX j C K a b X +
      ∑ X ∈ Iset j U, prefG j (obsI j C Vb Vo K a b) U X * (πobs (TX j C Vb Vo K a b X) -
        LtX j C K a b X - mX j C Vo K a b X) +
      ∑ X ∈ Iset j U, emb (bulk (prefG j (obsI j C Vb Vo K a b) U X)) * mX j C Vo K a b X +
      ∑ X ∈ Iset j U, πobs (prefG j (obsI j C Vb Vo K a b) U X) *
        emb (bulk (TX j C Vb Vo K a b X)) := by
    rw [map_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun X _ => by rw [term_decomp, mul_add]
  rw [hsplit]
  have hsum : ∀ (g : Finset (Lam d L N) → OE c (Lam d L N)), nrmj c ℓ₀ a b (j + 1)
      (∑ X ∈ Iset j U, g X) ≤ ∑ X ∈ Iset j U, nrmj c ℓ₀ a b (j + 1) (g X) :=
    fun g => nrmj_sum_le _ _ _
  have hn := hc₁ L N j U hU.1
  set n : ℝ := ((Iset j U).card : ℝ) with hn_def
  have hnR : n ≤ ((c₁ : ℝ) + 1) * ((L : ℝ) ^ d) ^ 2 := by
    have : (((Iset j U).card : ℕ) : ℝ) ≤ (c₁ : ℝ) * (L : ℝ) ^ d + ((L : ℝ) ^ d) ^ 2 := by
      exact_mod_cast hn
    have h2 : (L : ℝ) ^ d ≤ ((L : ℝ) ^ d) ^ 2 := by nlinarith
    nlinarith [(Nat.cast_nonneg c₁ : (0 : ℝ) ≤ c₁)]
  have hcardE : ((Iset j U).card : ENNReal) = ENNReal.ofReal n := by
    rw [hn_def, ENNReal.ofReal_natCast]
  have htot : nrmj c ℓ₀ a b (j + 1) (∑ X ∈ Iset j U, prefG j (obsI j C Vb Vo K a b) U X *
        LtX j C K a b X +
      ∑ X ∈ Iset j U, prefG j (obsI j C Vb Vo K a b) U X * (πobs (TX j C Vb Vo K a b X) -
        LtX j C K a b X - mX j C Vo K a b X) +
      ∑ X ∈ Iset j U, emb (bulk (prefG j (obsI j C Vb Vo K a b) U X)) * mX j C Vo K a b X +
      ∑ X ∈ Iset j U, πobs (prefG j (obsI j C Vb Vo K a b) U X) *
        emb (bulk (TX j C Vb Vo K a b X))) ≤
      ENNReal.ofReal (2 * cs * (G * (Cl * f' * ko)) + n * (G * (30 * 2 ^ d * W ^ 3 * Q)) +
        2 * (4 * (M * t) * π) + n * (G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t))) := by
    refine (nrmj_add_le _ _ _).trans ?_
    refine (add_le_add (nrmj_add_le _ _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (nrmj_add_le _ _ _) le_rfl) le_rfl).trans ?_
    refine (add_le_add (add_le_add (add_le_add ((hsum _).trans hP1) ((hsum _).trans hP2)) hP3)
      ((hsum _).trans hP4)).trans (le_of_eq ?_)
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have h1 : 0 ≤ 2 * cs * (G * (Cl * f' * ko)) := by positivity
    have hG0 : 0 ≤ G := by linarith
    have h2 : 0 ≤ n * (G * (30 * 2 ^ d * W ^ 3 * Q)) :=
      mul_nonneg hn0 (mul_nonneg hG0 (mul_nonneg (by positivity) hQ0))
    have h3 : 0 ≤ 2 * (4 * (M * t) * π) := by positivity
    have h4 : 0 ≤ n * (G * (4 * (W * s)) * ((3 * C₂ + M ^ 2) * t)) :=
      mul_nonneg hn0 (mul_nonneg (mul_nonneg hG0 (by positivity)) (by positivity))
    rw [hcardE, ← ENNReal.ofReal_mul hn0, ← ENNReal.ofReal_mul hn0,
      ← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg h1 h2) h3) h4]
  refine htot.trans ?_
  have hQeq : quadO (Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb)
      (VnormObs c ℓ₀ a b j Vo) (Knorm j (ellj d L ℓ₀ j) A (bulkK K))
      (KnormObs c ℓ₀ a b j A K) = ENNReal.ofReal Q := by
    rw [quadO, hvb, hvo, hkb, hko, ← ENNReal.ofReal_add hvb0 hkb0,
      ← ENNReal.ofReal_add (by positivity) hko0, ← ENNReal.ofReal_add hvb0 hvo0,
      ← ENNReal.ofReal_add (by positivity) hkb0, ← ENNReal.ofReal_add (by positivity) hko0,
      ← ENNReal.ofReal_mul (by positivity), hQ]
    congr 1; ring
  rw [hQeq, hko]
  have hpw : (L : ℝ) ^ (12 * d) = ((L : ℝ) ^ d) ^ 12 := by rw [← pow_mul, mul_comm]
  rw [hpw]
  have hKLL : K₂ ≤ ((L : ℝ) ^ d) ^ 2 := by
    rw [hK₂, ← pow_mul, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith)
  have hf : f' ≤ (if j + 1 < N then (L : ℝ) ^ (-dplus d) else ((L : ℝ) ^ d) ^ 12) := by
    rw [hf']
    split_ifs
    · exact le_rfl
    · exact hKLL.trans (pow_le_pow_right₀ hLd1 (by norm_num))
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hfp : 0 ≤ (if j + 1 < N then (L : ℝ) ^ (-dplus d) else ((L : ℝ) ^ d) ^ 12) := by
    split_ifs <;> positivity
  rw [← ENNReal.ofReal_mul (mul_nonneg hC₀0 hfp), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact final_real d hG1 hCl hC₂ hM1 hK1 hW hLd1 hKLL (Nat.cast_nonneg c₁) (Nat.cast_nonneg cs)
    (Nat.cast_nonneg _) hnR hf hf'0 ht0 hko0 hvo0 hvos hkos le_rfl hs1 hπ_def hQ

end

end Obs
