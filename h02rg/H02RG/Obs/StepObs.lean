import Obs.StepObsCoupling
import Obs.StepObsFix
import Obs.StepObsSmall
import Obs.StepObsLarge
import Obs.StepObsNonlin

/-!
# Theorem `thm:step-obs` (Section `sec:tyler-renorm-group`)

`stepObs_of_components` proves Theorem `thm:step-obs` (`StepObsStatement`, see
`Obs.StepObsStmt`) from the three component estimates `SmallObsStmt'`, `LargeObsStmt'`
(`Obs.StepObsFix`; the original `SmallObsStmt`, `LargeObsStmt` are false as stated) and
`NonlinObsStmt`, and the coupling constant bounds of `Obs.StepObsCoupling`
(`Vobs_next_bounds`: `e:V+obs-bd`) and the preservation of the support hypotheses
(`InKO_KnextO`, `InKpt_KnextO`).  `stepObs` is the theorem, with the component estimates
`obs_smallset_bound'`, `obs_largeset_bound'` and `obs_nonlinear_bound_proof`, proved in
`Obs.StepObsSmall`, `Obs.StepObsLarge` and `Obs.StepObsNonlin`.

The assembly follows `Step.step`: `K_{j+1}(U) = (𝓛_{j+1,𝒮} + 𝓛_{pair})(U) +
(𝓛_{j+1,𝒫∖𝒮} - 𝓛_{pair})(U) + (𝓡¹ + 𝓡² + 𝓡³)(U)` (`Gen.KnextG_eq_decomp`, `Gen.LlinG_eq`,
`πobs_Llin_split`), `π_obs` is linear, and the
second-order factor `(‖V^∅‖ + ‖K^∅‖ + ‖K^obs‖)(‖V^∅‖ + ‖V^obs‖ + ‖K^∅‖ + ‖K^obs‖)` of the component
estimates is at most `4 (‖V^∅‖_j + ‖K_j‖_j)(‖V_j‖_j + ‖K_j‖_j)`.  The powers `L^m` of the component
estimates are absorbed by choosing `A ≥ L^m` and `A^{η/2} ≥ L^m`, so that the exponent of `A`
in the linear term is `η/2` (with `η` from the large set estimate).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

variable {d L N : ℕ} [NeZero L]

theorem wnormO_add_le {c : Case} {ℓ₀ : ℝ} {a b : Lam d L N} (j : ℕ) (A : ℝ)
    (U : Finset (Lam d L N)) (F G : OE c (Lam d L N)) :
    wnormO c ℓ₀ a b j A U (F + G) ≤ wnormO c ℓ₀ a b j A U F + wnormO c ℓ₀ a b j A U G := by
  unfold wnormO
  rw [← mul_add]
  gcongr
  exact nrmj_add_le j F G

set_option maxHeartbeats 2000000 in
/-- The decomposition `π_obs K_{j+1} = π_obs 𝓛_{𝒮} + π_obs 𝓛_{𝒫∖𝒮} + π_obs (𝓡¹ + 𝓡² + 𝓡³)`. -/
theorem πobs_KnextO_eq {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup)
    (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)
    (U : Finset (Lam d L N)) :
    πobs (KnextO j C Vb Vo K a b U) =
      πobs (LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U) +
        (πobs (LlinLG (obsA c C) j (obsI j C Vb Vo K a b) U) +
          πobs (R1G (obsA c C) j (obsI j C Vb Vo K a b) U +
            R2G (obsA c C) j (obsI j C Vb Vo K a b) U +
            R3G (obsA c C) j (obsI j C Vb Vo K a b) U)) := by
  have e1 : KnextO j C Vb Vo K a b U =
      LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U +
        LlinLG (obsA c C) j (obsI j C Vb Vo K a b) U +
        R1G (obsA c C) j (obsI j C Vb Vo K a b) U + R2G (obsA c C) j (obsI j C Vb Vo K a b) U +
        R3G (obsA c C) j (obsI j C Vb Vo K a b) U := by
    show KnextG (obsA c C) j (obsI j C Vb Vo K a b) U = _
    rw [KnextG_eq_decomp (obsA c C) j (obsI j C Vb Vo K a b) U,
      LlinG_eq (obsA c C) j (obsI j C Vb Vo K a b) U]
  rw [e1]
  simp only [map_add, add_assoc]

set_option maxHeartbeats 2000000 in
/-- The decomposition with the two-block terms moved to the small sets. -/
theorem πobs_KnextO_eq' {c : Case} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : Vcoup)
    (Vo : Coup c) (K : Finset (Lam d L N) → OE c (Lam d L N)) (a b : Lam d L N)
    (U : Finset (Lam d L N)) :
    πobs (KnextO j C Vb Vo K a b U) =
      πobs (LlinSG (obsA c C) j (obsI j C Vb Vo K a b) U +
          LpairG (obsA c C) j (obsI j C Vb Vo K a b) U) +
        (πobs (LlinLG (obsA c C) j (obsI j C Vb Vo K a b) U -
            LpairG (obsA c C) j (obsI j C Vb Vo K a b) U) +
          πobs (R1G (obsA c C) j (obsI j C Vb Vo K a b) U +
            R2G (obsA c C) j (obsI j C Vb Vo K a b) U +
            R3G (obsA c C) j (obsI j C Vb Vo K a b) U)) := by
  rw [πobs_KnextO_eq, ← add_assoc, πobs_Llin_split, add_assoc]

/-- The second-order factor of the component estimates. -/
theorem quadO_le {vb vo kb ko v k : ENNReal} (hvb : vb ≤ v) (hvo : vo ≤ v) (hkb : kb ≤ k)
    (hko : ko ≤ k) : quadO vb vo kb ko ≤ 4 * ((vb + k) * (v + k)) := by
  unfold quadO
  have h1 : vb + kb + ko ≤ 2 * (vb + k) := by
    calc vb + kb + ko ≤ vb + k + k := by gcongr
      _ ≤ 2 * (vb + k) := by rw [two_mul]; gcongr; exact le_add_self
  have h2 : vb + vo + kb + ko ≤ 2 * (v + k) := by
    calc vb + vo + kb + ko ≤ v + v + k + k := by gcongr
      _ = 2 * (v + k) := by ring
  calc (vb + kb + ko) * (vb + vo + kb + ko) ≤ 2 * (vb + k) * (2 * (v + k)) := by gcongr
    _ = 4 * ((vb + k) * (v + k)) := by ring

set_option maxHeartbeats 4000000 in
/-- **Theorem `thm:step-obs`** from the component estimates. -/
theorem stepObs_of_components {d : ℕ} (hd : 3 ≤ d) (hS : SmallObsStmt' d)
    (hLg : LargeObsStmt' d) (hN : NonlinObsStmt d) : StepObsStatement d := by
  obtain ⟨CS, mS, LS, hCS, hS⟩ := hS
  obtain ⟨CL, η, νL, mL, LL, hCL, hη, hνL, hLg⟩ := hLg
  obtain ⟨CN, νN, mN, LN, hCN, hνN, hN⟩ := hN
  obtain ⟨CV, LV, hCV, hLV, hV⟩ := Vobs_next_bounds hd
  set ν : ℝ := max νL νN + 1 with hν
  set M : ℕ := max mS (max mL mN) with hM
  set C₀ : ℝ := CV + CS + CL + 4 * (CS + CL + CN) + 1 with hC₀
  refine ⟨C₀, η / 2, ν, mS, max (max LS LL) (max LN LV), by positivity, by positivity,
    by positivity, ?_⟩
  intro L _ hL
  have hLS : LS ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLL : LL ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLN : LN ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLV' : LV ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.one_le
  obtain ⟨AS, hAS1, hS'⟩ := hS L hLS
  obtain ⟨AL, hAL1, hL'⟩ := hLg L hLL
  obtain ⟨AN, hAN1, hN'⟩ := hN L hLN
  refine ⟨max (max AS AL) (max AN (max ((L : ℝ) ^ M) ((L : ℝ) ^ (2 * (mL : ℝ) / η)))),
    le_trans hAS1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro A hA
  have hAAS : AS ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
  have hAAL : AL ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
  have hAAN : AN ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hALM : (L : ℝ) ^ M ≤ A :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hA
  have hALη : (L : ℝ) ^ (2 * (mL : ℝ) / η) ≤ A :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hA
  have hA1 : 1 ≤ A := hAS1.trans hAAS
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨εS, hεS, hS''⟩ := hS' A hAAS
  obtain ⟨εL, hεL, hL''⟩ := hL' A hAAL
  obtain ⟨εN, hεN, hN''⟩ := hN' A hAAN
  set K₂ : ℝ := (L : ℝ) ^ (2 * ((d : ℝ) - 2)) with hK₂
  have hK1 : 1 ≤ K₂ := one_le_K₂ hd
  refine ⟨min (min εS εL) (min εN (1 / K₂)), lt_min (lt_min hεS hεL) (lt_min hεN (by positivity)),
    ?_⟩
  intro N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b h hsep hb ho
  have hmin1 : ENNReal.ofReal (min (min εS εL) (min εN (1 / K₂))) ≤ ENNReal.ofReal εS :=
    ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (min_le_left _ _))
  have hmin2 : ENNReal.ofReal (min (min εS εL) (min εN (1 / K₂))) ≤ ENNReal.ofReal εL :=
    ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (min_le_right _ _))
  have hmin3 : ENNReal.ofReal (min (min εS εL) (min εN (1 / K₂))) ≤ ENNReal.ofReal εN :=
    ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_left _ _))
  have hmin4 : ENNReal.ofReal (min (min εS εL) (min εN (1 / K₂))) ≤ ENNReal.ofReal (1 / K₂) :=
    ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (min_le_right _ _))
  set vb := Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) Vb with hvb
  set kb := Knorm j (ellj d L ℓ₀ j) A (bulkK K) with hkb
  set vo := VnormObs c ℓ₀ a b j Vo with hvo
  set ko := KnormObs c ℓ₀ a b j A K with hko
  set v := VnormFull c ℓ₀ a b j Vb Vo with hv
  set k := KnormFull c ℓ₀ a b j A K with hk
  -- the coupling constants
  have hsm : ENNReal.ofReal K₂ * (vo + ko) ≤ 1 := by
    calc ENNReal.ofReal K₂ * (vo + ko) ≤ ENNReal.ofReal K₂ * ENNReal.ofReal (1 / K₂) := by
          gcongr; exact ho.trans hmin4
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (by linarith), mul_one_div_cancel (by linarith),
            ENNReal.ofReal_one]
  obtain ⟨-, -, hVΛ, hVB, -⟩ :=
    hV L hLV' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b A hA1 h hsm
  have hCVC : ENNReal.ofReal (CV * K₂) ≤ ENNReal.ofReal (C₀ * K₂) :=
    ENNReal.ofReal_le_ofReal (by gcongr; linarith)
  refine ⟨hVΛ.trans (by gcongr), fun p hp => (hVB p hp).trans (by gcongr),
    InKO_KnextO (by omega) h.loc, InKpt_KnextO h.hab h.pt, ?_⟩
  -- the bound on `K^obs_{j+1}`
  have hvb_le : vb ≤ v := (Vnorm_le_VnormFull j Vb Vo).1
  have hvo_le : vo ≤ v := (Vnorm_le_VnormFull j Vb Vo).2
  have hkb_le : kb ≤ k := Knorm_bulk_le_KnormFull j A K
  have hko_le : ko ≤ k := KnormObs_le_KnormFull j A K
  have hQ : quadO vb vo kb ko ≤ 4 * ((vb + k) * (v + k)) := quadO_le hvb_le hvo_le hkb_le hko_le
  set Q := quadO vb vo kb ko
  set f : ℝ := if j + 1 < N then (L : ℝ) ^ (-dplus d) else (L : ℝ) ^ mS with hf
  have hf0 : 0 ≤ f := by rw [hf]; split_ifs <;> positivity
  -- real inequalities
  have hLpow : ∀ m ≤ M, (L : ℝ) ^ m ≤ A := fun m hm =>
    (pow_le_pow_right₀ hL1 hm).trans hALM
  have hAν : ∀ x : ℝ, 0 ≤ x → x ≤ max νL νN → A * A ^ x ≤ A ^ ν := by
    intro x hx0 hx
    rw [← Real.rpow_one_add' hA0 (by linarith : (0 : ℝ) < 1 + x).ne']
    exact Real.rpow_le_rpow_of_exponent_le hA1 (by rw [hν]; linarith)
  have hLη : (L : ℝ) ^ mL * A ^ (-η) ≤ A ^ (-(η / 2)) := by
    have h1 : (L : ℝ) ^ mL ≤ A ^ (η / 2) := by
      have := Real.rpow_le_rpow (by positivity) hALη (by positivity : 0 ≤ η / 2)
      rwa [← Real.rpow_mul (by positivity), show 2 * (mL : ℝ) / η * (η / 2) = mL by
        field_simp, Real.rpow_natCast] at this
    calc (L : ℝ) ^ mL * A ^ (-η) ≤ A ^ (η / 2) * A ^ (-η) := by gcongr
      _ = A ^ (-(η / 2)) := by
          rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have eS : (CS * (L : ℝ) ^ mS) ≤ CS * A ^ ν := by
    have := hAν 0 le_rfl (le_max_of_le_left hνL.le)
    rw [Real.rpow_zero, mul_one] at this
    gcongr
    exact (hLpow mS (le_max_left _ _)).trans this
  have eL : CL * (L : ℝ) ^ mL * A ^ νL ≤ CL * A ^ ν := by
    rw [mul_assoc]; gcongr
    exact (mul_le_mul_of_nonneg_right (hLpow mL ((le_max_left _ _).trans (le_max_right _ _)))
      (by positivity)).trans (hAν νL hνL.le (le_max_left _ _))
  have eN : CN * (L : ℝ) ^ mN * A ^ νN ≤ CN * A ^ ν := by
    rw [mul_assoc]; gcongr
    exact (mul_le_mul_of_nonneg_right (hLpow mN ((le_max_right _ _).trans (le_max_right _ _)))
      (by positivity)).trans (hAν νN hνN.le (le_max_right _ _))
  have eLη : CL * (L : ℝ) ^ mL * A ^ (-η) ≤ CL * A ^ (-(η / 2)) := by
    rw [mul_assoc]; gcongr
  refine iSup₂_le fun U hU => ?_
  have hUc : IsConn (j + 1) U := by simpa [connSets] using hU
  have wS := hS'' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b h hsep (hb.trans hmin1) (ho.trans hmin1) U hUc
  have wL := hL'' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b h hsep (hb.trans hmin2) (ho.trans hmin2) U hUc
  have wN := hN'' N j hj ℓ₀ hℓ₀ c P C Vb Vo K a b h (hb.trans hmin3) (ho.trans hmin3) U hUc
  show wnormO c ℓ₀ a b (j + 1) A U (πobs (KnextO j C Vb Vo K a b U)) ≤ _
  rw [πobs_KnextO_eq']
  refine (wnormO_add_le _ _ _ _ _).trans ((add_le_add le_rfl (wnormO_add_le _ _ _ _ _)).trans
    ((add_le_add wS (add_le_add wL wN)).trans ?_))
  -- collect
  have hlin : ENNReal.ofReal (CS * f) * ko + ENNReal.ofReal (CL * (L : ℝ) ^ mL * A ^ (-η)) * ko ≤
      ENNReal.ofReal (C₀ * (f + A ^ (-(η / 2)))) * ko := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    gcongr
    have : 0 ≤ A ^ (-(η / 2)) := by positivity
    nlinarith
  have hquad : ENNReal.ofReal (CS * (L : ℝ) ^ mS) * Q +
      ENNReal.ofReal (CL * (L : ℝ) ^ mL * A ^ νL) * Q +
      ENNReal.ofReal (CN * (L : ℝ) ^ mN * A ^ νN) * Q ≤
      ENNReal.ofReal (C₀ * A ^ ν) * ((vb + k) * (v + k)) := by
    calc _ ≤ ENNReal.ofReal (CS * A ^ ν) * Q + ENNReal.ofReal (CL * A ^ ν) * Q +
          ENNReal.ofReal (CN * A ^ ν) * Q := by gcongr
      _ = ENNReal.ofReal ((CS + CL + CN) * A ^ ν) * Q := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2; ring
      _ ≤ ENNReal.ofReal ((CS + CL + CN) * A ^ ν) * (4 * ((vb + k) * (v + k))) := by gcongr
      _ = ENNReal.ofReal (4 * (CS + CL + CN) * A ^ ν) * ((vb + k) * (v + k)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
      _ ≤ _ := by
          gcongr
          have : 0 ≤ A ^ ν := by positivity
          nlinarith
  calc ENNReal.ofReal (CS * f) * ko + ENNReal.ofReal (CS * (L : ℝ) ^ mS) * Q +
        (ENNReal.ofReal (CL * (L : ℝ) ^ mL * A ^ (-η)) * ko +
            ENNReal.ofReal (CL * (L : ℝ) ^ mL * A ^ νL) * Q +
          ENNReal.ofReal (CN * (L : ℝ) ^ mN * A ^ νN) * Q)
      = (ENNReal.ofReal (CS * f) * ko + ENNReal.ofReal (CL * (L : ℝ) ^ mL * A ^ (-η)) * ko) +
        (ENNReal.ofReal (CS * (L : ℝ) ^ mS) * Q +
          ENNReal.ofReal (CL * (L : ℝ) ^ mL * A ^ νL) * Q +
          ENNReal.ofReal (CN * (L : ℝ) ^ mN * A ^ νN) * Q) := by ring
    _ ≤ _ := add_le_add hlin hquad

/-- The (corrected) small set estimate (`Obs.StepObsSmall`). -/
theorem obs_smallset_bound' {d : ℕ} (hd : 3 ≤ d) : SmallObsStmt' d :=
  obs_smallset_bound_proof' hd

/-- The (corrected) large set estimate (`Obs.StepObsLarge`). -/
theorem obs_largeset_bound' {d : ℕ} (hd : 3 ≤ d) : LargeObsStmt' d :=
  obs_largeset_bound_proof' hd

/-- **Theorem `thm:step-obs`**, assembled from the three component estimates
`obs_smallset_bound'`, `obs_largeset_bound'` and `obs_nonlinear_bound_proof`. -/
theorem stepObs {d : ℕ} (hd : 3 ≤ d) : StepObsStatement d :=
  stepObs_of_components hd (obs_smallset_bound' hd) (obs_largeset_bound' hd)
    (obs_nonlinear_bound_proof hd)

end

end Obs
