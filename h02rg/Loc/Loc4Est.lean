import Loc.Loc4Def
import Loc.EstContractGen

/-!
# Bounds for the quartic localisation

* `tNorm_mono4_le`: `‖mono4 i k x‖_{T(h,ℓ)} ≤ ℓ⁴ h^{-2}`;
* `exists_mu4_bound`: `|mu4 F| ≤ C ℓ^{-4} L^{2j} ‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩(X^□)`, `X` small: `mu4`
  is the pairing of `F` with a test function equal to `24 ℓ(x₀)_i ℓ(x₁)_k` (on the spin pattern
  `(+,-,+,-)`) on `X^□`, cut off smoothly at scale `L^j`;
* `exists_Loc4XY_bound`, `exists_Loc2XY_bound`: `prop:Loc`(i) for `Loc4XY` and for the `d = 2`
  localisation `Loc2XY = LocXY + Loc4XY`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d L N : ℕ} [NeZero L]

/-- Sums over sequences with a fixed spin pattern. -/
theorem sum_pattern {X : Type*} [Fintype X] {n : ℕ} (s : Fin n → ℤˣ)
    (f : (Fin n → Sf X) → ℂ) (hf : ∀ z, spins z ≠ s → f z = 0) :
    ∑ z, f z = ∑ x : Fin n → X, f fun r => (x r, s r) := by
  let e : (Fin n → X) × (Fin n → ℤˣ) ≃ (Fin n → Sf X) :=
    { toFun := fun q r => (q.1 r, q.2 r)
      invFun := fun z => (fun r => (z r).1, fun r => (z r).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_eq_single s]
  · rfl
  · intro t _ ht
    exact hf _ ht
  · simp

/-! ### The norm of the quartic monomials -/

theorem tNorm_Dψ_le {p : ℕ} {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) {a : Dir d → ℕ}
    (ha : Grassmann.mabs a ≤ p) (u : Sf (Lam d L N)) :
    tNorm (Dir d) p h ℓ (MonoEst.Dψ a u) ≤ ENNReal.ofReal (ℓ * (h ^ Grassmann.mabs a)⁻¹) :=
  tNorm_le fun _ hg => MonoEst.abs_pair_Dψ_le hh hℓ ha u hg

theorem tNorm_mono4_le {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (i k : Fin d)
    (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (mono4 i k x) ≤ ENNReal.ofReal (ℓ ^ 4 * (h ^ 2)⁻¹) := by
  have e1 : ψ (x + dirVec (Sum.inl i), 1) - ψ (x, 1) =
      MonoEst.Dψ (Pi.single (Sum.inl i) 1 : Dir d → ℕ) ((x, 1) : Sf (Lam d L N)) :=
    (MonoEst.Dψ_one_T _ x 1).symm
  have e2 : ψ (x + dirVec (Sum.inl k), -1) - ψ (x, -1) =
      MonoEst.Dψ (Pi.single (Sum.inl k) 1 : Dir d → ℕ) ((x, -1) : Sf (Lam d L N)) :=
    (MonoEst.Dψ_one_T _ x (-1)).symm
  have e3 : ∀ σ : ℤˣ, ψ ((x, σ) : Sf (Lam d L N)) =
      MonoEst.Dψ (0 : Dir d → ℕ) ((x, σ) : Sf (Lam d L N)) := fun σ =>
    (MonoEst.Dψ_zero _).symm
  rw [mono4_eq, e1, e2, e3 1, e3 (-1)]
  have h0 : Grassmann.mabs (0 : Dir d → ℕ) = 0 := by simp [Grassmann.mabs]
  have b1 := tNorm_Dψ_le (p := p) hh hℓ (a := (Pi.single (Sum.inl i) 1 : Dir d → ℕ))
    (by rw [mabs_single]; exact hp) ((x, 1) : Sf (Lam d L N))
  have b2 := tNorm_Dψ_le (p := p) hh hℓ (a := (Pi.single (Sum.inl k) 1 : Dir d → ℕ))
    (by rw [mabs_single]; exact hp) ((x, -1) : Sf (Lam d L N))
  have b3 := tNorm_Dψ_le (p := p) hh hℓ (a := (0 : Dir d → ℕ)) (by rw [h0]; omega)
    ((x, 1) : Sf (Lam d L N))
  have b4 := tNorm_Dψ_le (p := p) hh hℓ (a := (0 : Dir d → ℕ)) (by rw [h0]; omega)
    ((x, -1) : Sf (Lam d L N))
  rw [mabs_single] at b1 b2
  rw [h0] at b3 b4
  refine (tNorm_mul_le hh hℓ _ _).trans ?_
  refine (mul_le_mul' b1 ((tNorm_mul_le hh hℓ _ _).trans (mul_le_mul' b2
    ((tNorm_mul_le hh hℓ _ _).trans (mul_le_mul' b3 b4))))).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem toReal_tNorm_mono4Set_le {p : ℕ} (hp : 1 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ)
    (i k : Fin d) (Y : Finset (Lam d L N)) :
    (tNorm (Dir d) p h ℓ (mono4Set i k Y)).toReal ≤ Y.card * (ℓ ^ 4 * (h ^ 2)⁻¹) := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((tNorm_sum_le _ _).trans ?_)
  calc ∑ x ∈ Y, tNorm (Dir d) p h ℓ (mono4 i k x)
      ≤ ∑ _x ∈ Y, ENNReal.ofReal (ℓ ^ 4 * (h ^ 2)⁻¹) :=
        sum_le_sum fun x _ => tNorm_mono4_le hp hh hℓ i k x
    _ = ENNReal.ofReal (Y.card * (ℓ ^ 4 * (h ^ 2)⁻¹)) := by
        rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-! ### The bound on `mu4` -/

/-- The one-point factors of the test function for `mu4`. -/
def muH4 (κ κ' : Fin d) (R : ℝ) : Fin 4 → Sf (Zd d) → ℝ :=
  ![spinF 1 (fun u => 24 * cutP (Pi.single κ 1) R u), spinF (-1) (cutP (Pi.single κ' 1) R),
    spinF 1 (cutP 0 R), spinF (-1) (cutP 0 R)]

theorem cutP_single_eq {R : ℝ} (hR : 0 < R) (κ : Fin d) {u : Zd d} (hu : (supNormZ u : ℝ) ≤ R) :
    cutP (Pi.single κ 1) R u = (u κ : ℝ) := by
  rw [cutP_eq _ hR hu, prod_pow_single, pow_one]

theorem cutP_zero_eq {R : ℝ} (hR : 0 < R) {u : Zd d} (hu : (supNormZ u : ℝ) ≤ R) :
    cutP 0 R u = 1 := by
  rw [cutP_eq _ hR hu]; simp

theorem muH4_far (κ κ' : Fin d) {R : ℝ} (hR : 0 < R) (r : Fin 4) (y : Sf (Zd d))
    (hy : 2 * R ≤ (supNormZ y.1 : ℝ)) : muH4 κ κ' R r y = 0 := by
  fin_cases r <;> simp [muH4, spinF, cutP_eq_zero _ hR hy]

theorem muH4_eq_zero_of_far (κ κ' : Fin d) {R : ℝ} (hR : 0 < R) (w : Fin 4 → Sf (Zd d))
    (hw : ∃ k, 2 * R ≤ (supNormZ (w k).1 : ℝ)) : ∏ r, muH4 κ κ' R r (w r) = 0 := by
  obtain ⟨k, hk⟩ := hw
  exact prod_eq_zero (mem_univ k) (muH4_far κ κ' hR k (w k) hk)

theorem exists_mu4_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X : Finset (Lam d L N), IsSmall j X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ κ κ' : Fin d, ∀ ℓ : ℝ, 0 < ℓ →
      ‖mu4 (base X) κ κ' F‖ ≤
        C * (ℓ ^ 4)⁻¹ * ((L : ℝ) ^ j) ^ 2 * (Tj d (L : ℝ) j ℓ F).toReal := by
  obtain ⟨Cc, hCc0, hCc⟩ := exists_D1_cutP_bound d (pPhi d) 1
  refine ⟨24 * Cc ^ 4 * 4 ^ (d + 1), by positivity, ?_⟩
  intro L _ hL N j hj X hX F hF κ κ' ℓ hℓ
  set b := base X with hb
  set s : ℝ := (L : ℝ) ^ j with hs
  set R : ℝ := (rad d L j : ℝ) with hRdef
  have h2p : 0 < 2 ^ (d + 3) := by positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hs1 : 1 ≤ s := one_le_pow₀ hL1
  have hRs : R = 2 ^ (d + 1) * s := by simp [R, rad, s]
  have hR1 : 1 ≤ R := by rw [hRdef]; exact Nat.one_le_cast.2 (one_le_rad j)
  have hR0 : 0 < R := by linarith
  have hsR : s ≤ R := by
    rw [hRs]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
  set H := muH4 κ κ' R
  let g : TestFn (Lam d L N) := single 4 (fun z => ((∏ r, H r ((ρS b ∘ z) r) : ℝ) : ℂ))
  -- the pairing is `mu4`
  have hpair : pair F g = mu4 b κ κ' F := by
    rw [pair_single, sum_pattern pat4 _ (fun z hz => ?_)]
    · rw [mu4, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      by_cases hx : ∀ r, x r ∈ nbhd j X
      · have hu : ∀ r, (supNormZ (rep (x r - b)) : ℝ) ≤ R := fun r => by
          have := supNorm_nbhd_base hX (hx r)
          rw [supNormZ_rep_eq, hRdef]; exact_mod_cast this
        have c0 := cutP_single_eq hR0 κ (hu 0)
        have c1 := cutP_single_eq hR0 κ' (hu 1)
        have c2 := cutP_zero_eq hR0 (hu 2)
        have c3 := cutP_zero_eq hR0 (hu 3)
        simp [H, muH4, Fin.prod_univ_four, ρS, spinF, pat4, c0, c1, c2, c3, cf4, lift,
          Nat.factorial]
        ring
      · push Not at hx
        obtain ⟨r, hr⟩ := hx
        have h0 : coeff F (fun r => (x r, pat4 r)) = 0 :=
          coeff_eq_zero_of_mem_NX hF _ r (by simpa using hr)
        simp [cf4, h0]
    · have : ∃ r, (z r).2 ≠ pat4 r := by
        by_contra h; push Not at h; exact hz (funext h)
      obtain ⟨r, hr⟩ := this
      rw [prod_eq_zero (mem_univ r), Complex.ofReal_zero, mul_zero]
      fin_cases r <;> simp_all [H, muH4, spinF, ρS, pat4]
  -- the norm of the test function
  have hnorm : phiNorm (Dir d) (pPhi d) s ℓ g ≤
      ENNReal.ofReal (24 * Cc ^ 4 * 4 ^ (d + 1) * (ℓ ^ 4)⁻¹ * s ^ 2) := by
    refine phiNorm_single_le (by positivity) fun z α hα => ?_
    rw [nabla_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rw [nab_comp_ρS b (fun w => ∏ r, H r (w r)) (S := 2 * rad d L j) (P := pPhi d)
      (size_cond hL hj) (fun w ⟨k, hk⟩ => muH4_eq_zero_of_far κ κ' hR0 w ⟨k, by
        have : ((2 * rad d L j : ℕ) : ℝ) < supNormZ (w k).1 := by exact_mod_cast hk
        push_cast at this; linarith⟩) α hα z, nabla_prod]
    set u := ρS b ∘ z
    have hm : ∀ (r : Fin 4) (m : Fin d → ℕ), (∀ i, m i ≤ 1) →
        |D1 (fun b v => b +ᵥ v) (α r) (cutP m R) (u r).1| ≤
          Cc * R ^ (∑ i, m i) / R ^ mabs (α r) := fun r m hm =>
      hCc m hm R hR1 (α r) (hα r) (u r).1
    have hs1 : ∀ κ : Fin d, ∀ i, (Pi.single κ 1 : Fin d → ℕ) i ≤ 1 := fun κ i => by
      by_cases h : i = κ <;> simp [Pi.single_apply, h]
    have hD0 : |D1 sh (α 0) (H 0) (u 0)| ≤ 24 * (Cc * R ^ 1 / R ^ mabs (α 0)) := by
      show |D1 sh (α 0) (spinF 1 (fun u => 24 * cutP (Pi.single κ 1) R u)) (u 0)| ≤ _
      rw [D1_spinF]
      split_ifs
      · rw [D1_const_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
        have := hm 0 _ (hs1 κ)
        rw [sum_single'] at this
        exact mul_le_mul_of_nonneg_left this (by norm_num)
      · simp only [abs_zero]; positivity
    have hD1 : |D1 sh (α 1) (H 1) (u 1)| ≤ Cc * R ^ 1 / R ^ mabs (α 1) := by
      show |D1 sh (α 1) (spinF (-1) (cutP (Pi.single κ' 1) R)) (u 1)| ≤ _
      rw [D1_spinF]
      split_ifs
      · have := hm 1 _ (hs1 κ')
        rwa [sum_single'] at this
      · simp only [abs_zero]; positivity
    have hD2 : |D1 sh (α 2) (H 2) (u 2)| ≤ Cc * R ^ 0 / R ^ mabs (α 2) := by
      show |D1 sh (α 2) (spinF 1 (cutP 0 R)) (u 2)| ≤ _
      rw [D1_spinF]
      split_ifs
      · have := hm 2 0 (fun _ => zero_le_one)
        simpa using this
      · simp only [abs_zero]; positivity
    have hD3 : |D1 sh (α 3) (H 3) (u 3)| ≤ Cc * R ^ 0 / R ^ mabs (α 3) := by
      show |D1 sh (α 3) (spinF (-1) (cutP 0 R)) (u 3)| ≤ _
      rw [D1_spinF]
      split_ifs
      · have := hm 3 0 (fun _ => zero_le_one)
        simpa using this
      · simp only [abs_zero]; positivity
    have hord : ord α = mabs (α 0) + mabs (α 1) + mabs (α 2) + mabs (α 3) := by
      simp [ord, Fin.sum_univ_four]
    have hR2 : R ^ 2 ≤ 4 ^ (d + 1) * s ^ 2 := by
      rw [hRs, mul_pow]
      gcongr
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hsR' : s ^ ord α / R ^ ord α ≤ 1 :=
      (div_le_one (by positivity)).2 (pow_le_pow_left₀ (by linarith) hsR _)
    rw [abs_prod]
    rw [Fin.prod_univ_four]
    calc ℓ⁻¹ ^ 4 * s ^ ord α * (|D1 sh (α 0) (H 0) (u 0)| * |D1 sh (α 1) (H 1) (u 1)| *
          |D1 sh (α 2) (H 2) (u 2)| * |D1 sh (α 3) (H 3) (u 3)|)
        ≤ ℓ⁻¹ ^ 4 * s ^ ord α * (24 * (Cc * R ^ 1 / R ^ mabs (α 0)) *
          (Cc * R ^ 1 / R ^ mabs (α 1)) * (Cc * R ^ 0 / R ^ mabs (α 2)) *
          (Cc * R ^ 0 / R ^ mabs (α 3))) := by
          gcongr
      _ = 24 * Cc ^ 4 * (ℓ ^ 4)⁻¹ * R ^ 2 * (s ^ ord α / R ^ ord α) := by
          rw [hord, pow_add, pow_add, pow_add]
          field_simp
          ring
      _ ≤ 24 * Cc ^ 4 * (ℓ ^ 4)⁻¹ * (4 ^ (d + 1) * s ^ 2) * 1 := by gcongr
      _ = 24 * Cc ^ 4 * 4 ^ (d + 1) * (ℓ ^ 4)⁻¹ * s ^ 2 := by ring
  have := abs_pair_le (by positivity) hℓ F (by positivity) hnorm
  rw [hpair] at this
  calc ‖mu4 b κ κ' F‖ ≤ (tNorm (Dir d) (pPhi d) s ℓ F).toReal *
        (24 * Cc ^ 4 * 4 ^ (d + 1) * (ℓ ^ 4)⁻¹ * s ^ 2) := this
    _ = _ := by simp only [Tj, s]; ring

/-! ### `prop:Loc`(i) for the quartic part -/

theorem exists_Loc4XY_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (Loc4XY X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨K, hK0, hK⟩ := exists_mu4_bound d
  refine ⟨(d : ℝ) ^ 2 * K, by positivity, ?_⟩
  intro L _ hL N j hj X Y hX hYX F hF ℓ hℓ
  have hne : X.Nonempty := hX.2.1.1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold Tj
  rw [Loc4XY]
  set s : ℝ := (L : ℝ) ^ j
  have hs : 0 < s := by positivity
  set T : ℝ := (tNorm (Dir d) (pPhi d) s ℓ F).toReal
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  have hX0 : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
  have hYX' : (Y.card : ℝ) ≤ X.card := by exact_mod_cast card_le_card hYX
  have hp : 1 ≤ pPhi d := by simp [pPhi]; omega
  have hTF : tNorm (Dir d) (pPhi d) s ℓ F = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ F)).symm
  rw [hTF, ← ENNReal.ofReal_mul (by positivity)]
  have hmu : ∀ i k : Fin d, ‖mu4 (base X) i k F‖ ≤ K * (ℓ ^ 4)⁻¹ * s ^ 2 * T := fun i k =>
    hK L hL N j hj X hX F hF i k ℓ hℓ
  have hmono : ∀ i k : Fin d, (tNorm (Dir d) (pPhi d) s ℓ (mono4Set i k Y)).toReal ≤
      Y.card * (ℓ ^ 4 * (s ^ 2)⁻¹) := fun i k => toReal_tNorm_mono4Set_le hp hs hℓ i k Y
  clear_value s T
  have hterm : ∀ i k : Fin d, (tNorm (Dir d) (pPhi d) s ℓ
      ((mu4 (base X) i k F / X.card) • mono4Set i k Y)).toReal ≤ K * T := by
    intro i k
    have hsm := tNorm_smul_le (E := Dir d) (p := pPhi d) (h := s) (ℓ := ℓ)
      (mu4 (base X) i k F / X.card) (mono4Set i k Y)
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tNorm_ne_top hs hℓ _)) hsm).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), norm_div,
      Complex.norm_natCast]
    have h1 := hmu i k
    have h2 := hmono i k
    calc ‖mu4 (base X) i k F‖ / X.card * (tNorm (Dir d) (pPhi d) s ℓ (mono4Set i k Y)).toReal
        ≤ (K * (ℓ ^ 4)⁻¹ * s ^ 2 * T) / X.card * (Y.card * (ℓ ^ 4 * (s ^ 2)⁻¹)) := by
          gcongr
      _ = K * T * (Y.card / X.card) := by field_simp
      _ ≤ K * T * 1 := by
          gcongr
          exact (div_le_one hX0).2 hYX'
      _ = K * T := mul_one _
  refine (tNorm_sum_le _ _).trans ?_
  calc ∑ i, tNorm (Dir d) (pPhi d) s ℓ (∑ k, (mu4 (base X) i k F / X.card) • mono4Set i k Y)
      ≤ ∑ _i : Fin d, ∑ _k : Fin d, ENNReal.ofReal (K * T) := by
        refine sum_le_sum fun i _ => (tNorm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
        rw [← ENNReal.ofReal_toReal (tNorm_ne_top hs hℓ _)]
        exact ENNReal.ofReal_le_ofReal (hterm i k)
    _ = ENNReal.ofReal ((d : ℝ) ^ 2 * K * T) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring

/-- `prop:Loc`(i) for the localisation `Loc2XY = LocXY + Loc4XY` of `d = 2`. -/
theorem exists_Loc2XY_bound (d : ℕ) (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (Loc2XY X Y F) ≤ ENNReal.ofReal C * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C2, hC2, h2⟩ := exists_LocXY_bound d hd
  obtain ⟨C4, hC4, h4⟩ := exists_Loc4XY_bound d hd
  refine ⟨C2 + C4, by positivity, fun L _ hL N j hj X Y hX hYX F hF ℓ hℓ => ?_⟩
  refine (tNorm_add_le _ _).trans ?_
  rw [ENNReal.ofReal_add hC2 hC4, add_mul]
  exact add_le_add (h2 L hL N j hj X Y hX hYX F hF ℓ hℓ) (h4 L hL N j hj X Y hX hYX F hF ℓ hℓ)

end

end Loc
