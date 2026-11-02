import H04RG.Loc.Contract

/-!
# Boundedness of the two-species localisation (`prop:Loc`(i))

* `Tj_emb_le`: putting a single-species element on one species does not increase the `T` norm
  (`pair_emb`: `⟨emb a G, g⟩ = ⟨G, g ∘ lab a⟩`);
* `LocSXY_eq_emb`: `LocS_{X,Y} F = emb 0 (Loc_{X,Y} (res 0 F)) + emb 1 (Loc_{X,Y} (res 1 F))
  - (F_∅ |Y|/|X|)·1` (the constant term is shared);
* `exists_LocSXY_bound`: `‖LocS_{X,Y} F‖_{T_j(ℓ)} ≤ C ‖F‖_{T_j(ℓ)}` for small `X`, `Y ⊆ X`, from
  the single-species bound `Loc.exists_LocXY_bound`.
-/

namespace H04RG.LocS

noncomputable section

open Finset Matrix Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- Pull a two-species test function back to species `a`. -/
def restrT (a : Fin 2) (g : TestFn (LamS d L N)) : TestFn (Lam d L N) :=
  fun n w => g n (lab a ∘ w)

theorem phiNorm_restrT_le (a : Fin 2) (p : ℕ) (h ℓ : ℝ) (g : TestFn (LamS d L N)) :
    phiNorm (Dir d) p h ℓ (restrT a g) ≤ phiNorm (Dir d) p h ℓ g := by
  refine iSup_le fun n => iSup_le fun w => iSup_le fun α => iSup_le fun hα => ?_
  refine le_trans (le_of_eq ?_) (phiTerm_le g (lab a ∘ w) α hα)
  have : nab α (restrT a g n) w = nab α (g n) (lab a ∘ w) :=
    nabla_comp_pi sh sh (fun _ => lab a) (fun _ b z => lab_sh a b z) α (g n) w
  simp only [phiTerm, this]

theorem pair_emb (a : Fin 2) (G : Alg d L N) (g : TestFn (LamS d L N)) :
    pair (emb a G) g = pair G (restrT a g) := by
  classical
  have hN : Nf (Lam d L N) ≤ Nf (LamS d L N) := by
    simp only [Nf, Fintype.card_prod, Fintype.card_fin]
    nlinarith [Fintype.card_pos (α := Lam d L N), Fintype.card_pos (α := ℤˣ)]
  have hin : ∀ n, (∑ z : Fin n → Sf (LamS d L N), coeff (emb a G) z * g n z) =
      ∑ w : Fin n → Sf (Lam d L N), coeff G w * restrT a g n w := by
    intro n
    simp only [coeff_emb_gen]
    rw [← sum_filter_add_sum_filter_not univ (fun z : Fin n → Sf (LamS d L N) => ∀ i, (z i).1.2 = a)]
    rw [sum_eq_zero (s := univ.filter fun z : Fin n → Sf (LamS d L N) => ¬∀ i, (z i).1.2 = a)
      (fun z hz => by rw [if_neg (mem_filter.1 hz).2, zero_mul]), add_zero]
    symm
    refine sum_bij' (fun w _ => lab a ∘ w) (fun z _ => unl ∘ z) (fun w _ => ?_) (fun z _ => ?_)
      (fun w _ => ?_) (fun z hz => ?_) (fun w _ => ?_)
    · simp [lab]
    · simp
    · rfl
    · funext i
      have h := (mem_filter.1 hz).2 i
      simp only [Function.comp_apply, lab, unl]
      rw [← h]
    · have hw : ∀ i, ((lab a ∘ w) i).1.2 = a := fun _ => rfl
      rw [if_pos hw]
      rfl
  rw [pair, pair]
  simp only [hin]
  rw [← sum_range_add_sum_Ico _ (Nat.succ_le_succ hN)]
  rw [sum_eq_zero (s := Ico (Nf (Lam d L N) + 1) (Nf (LamS d L N) + 1)), add_zero]
  intro n hn
  have hn' : Nf (Lam d L N) < n := by have := (mem_Ico.1 hn).1; omega
  rw [sum_eq_zero fun w _ => by rw [coeff_eq_zero_of_lt _ w hn', zero_mul], mul_zero]

theorem tNorm_emb_le (a : Fin 2) (p : ℕ) (h ℓ : ℝ) (G : Alg d L N) :
    tNorm (Dir d) p h ℓ (emb a G) ≤ tNorm (Dir d) p h ℓ G := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  rw [pair_emb]
  exact le_iSup₂_of_le (restrT a g) ((phiNorm_restrT_le a p h ℓ g).trans hg) le_rfl

theorem Tj_emb_le (a : Fin 2) (Lr : ℝ) (j : ℕ) (ℓ : ℝ) (G : Alg d L N) :
    Tj d Lr j ℓ (emb a G) ≤ Tj d Lr j ℓ G :=
  tNorm_emb_le a _ _ ℓ G

/-- The two-species localisation in terms of the single-species one. -/
theorem LocSXY_eq_emb (X Y : Finset (Lam d L N)) (F : AlgS d L N) :
    LocSXY X Y F = emb 0 (LocXY X Y (res 0 F)) + emb 1 (LocXY X Y (res 1 F)) -
      (ε F * Y.card / X.card) • (1 : AlgS d L N) := by
  rw [LocSXY_eq, Fin.sum_univ_two, LocXY, LocXY, map_add, map_add, map_smul, map_smul, map_one,
    ε_res, ε_res]
  simp only [map_one]
  abel

set_option maxHeartbeats 800000 in
theorem exists_LocSXY_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (above (nbhd j X : Set (Lam d L N))), ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (LocSXY X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨Cb, hCb, hCbb⟩ := exists_LocXY_bound d hd
  refine ⟨2 * Cb + 1, by positivity, ?_⟩
  intro L _ hL N j hj X Y hX hYX F hF ℓ hℓ
  have hs : (0 : ℝ) < (L : ℝ) ^ j := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hne : X.Nonempty := hX.2.1.1
  set TF := Tj d (L : ℝ) j ℓ F
  -- the two species
  have hA : ∀ a : Fin 2, Tj d (L : ℝ) j ℓ (emb a (LocXY X Y (res a F))) ≤
      ENNReal.ofReal Cb * TF := fun a =>
    (Tj_emb_le a _ j ℓ _).trans ((hCbb L hL N j hj X Y hX hYX (res a F) (res_mem a hF) ℓ hℓ).trans
      (mul_le_mul_right (Tj_res_le a (L : ℝ) (Nat.cast_nonneg L) j ℓ hℓ F) _))
  -- the constant
  have hc : Tj d (L : ℝ) j ℓ ((ε F * Y.card / X.card) • (1 : AlgS d L N)) ≤ TF := by
    refine (tNorm_smul_le _ _).trans ?_
    have h1 : tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (1 : AlgS d L N) ≤ 1 := tNorm_one_le hs hℓ
    have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
    have hYXc : (Y.card : ℝ) ≤ X.card := by exact_mod_cast card_le_card hYX
    have h2 : ‖ε F * Y.card / X.card‖ ≤ ‖ε F‖ := by
      rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      rw [div_le_iff₀ hX0]
      exact mul_le_mul_of_nonneg_left hYXc (norm_nonneg _)
    have h3 : ‖ε F‖ ≤ TF.toReal := abs_eps_le hs hℓ F
    have hTF : TF ≠ ⊤ := tNorm_ne_top hs hℓ F
    calc ENNReal.ofReal ‖ε F * Y.card / X.card‖ * tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ 1
        ≤ ENNReal.ofReal ‖ε F * Y.card / X.card‖ * 1 := mul_le_mul_right h1 _
      _ ≤ ENNReal.ofReal TF.toReal := by
          rw [mul_one]; exact ENNReal.ofReal_le_ofReal (h2.trans h3)
      _ = TF := ENNReal.ofReal_toReal hTF
  rw [LocSXY_eq_emb]
  refine (tNorm_sub_le _ _).trans ?_
  refine (add_le_add (tNorm_add_le _ _) hc).trans ?_
  calc Tj d (L : ℝ) j ℓ (emb 0 (LocXY X Y (res 0 F))) + Tj d (L : ℝ) j ℓ (emb 1 (LocXY X Y (res 1 F))) +
        TF ≤ ENNReal.ofReal Cb * TF + ENNReal.ofReal Cb * TF + TF :=
        add_le_add (add_le_add (hA 0) (hA 1)) le_rfl
    _ = ENNReal.ofReal (2 * Cb + 1) * TF := by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_mul zero_le_two,
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        ring

end

end H04RG.LocS
