import Obs.StepObsCoupling
import Obs.StepObsFix

/-!
# Auxiliary estimates for the large set bound (`e:Kquad-obs`)

Generic facts about the observable norms `oT` used in `Obs.StepObsLarge`:
* `e:norm-obs-nonmon` in norm form: `‖π_obs (F G)‖ ≤ ‖F‖ ‖π_obs G‖ + ‖π_obs F‖ ‖G‖`
  (`oT_πobs_mul_le`) and its iteration over finite products (`oT_πobs_prod_le`);
* `‖∏ F_i - 1‖ ≤ e^{∑ t_i} - 1` if `‖F_i - 1‖ ≤ e^{t_i} - 1` (`oT_prod_sub_one_le`);
* `‖e^z e^F - 1‖ ≤ e^{|z| + r} - 1` (`oT_exp_oexp_sub_one_le`);
* `π_obs` commutes with `θ`, the inclusion and `𝔼_C`;
* the real inequalities replacing `Step.largeK_real`, `Step.largeD_real`.
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen

section Generic

variable {c : Case} {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E]
  [DecidableEq E] [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ} {w : Wt}

theorem πobs_mul_eq (F G : OE c X) : πobs (F * G) = F * πobs G + πobs F * emb (bulk G) := by
  rw [πobs_mul]
  conv_rhs => enter [1, 1]; rw [eq_emb_add_πobs F]
  ring

theorem oT_split (F : OE c X) :
    oT E p h ℓ w (F : SA c X) = tNorm E p h ℓ ((bulk F : EvR X) : N X) +
      oT E p h ℓ w (πobs F : SA c X) := by
  simp only [oT_def, coe_πobs, piobs_apply, coe_bulk, tNorm_zero']
  ring

theorem tNorm_bulk_le (F : OE c X) :
    tNorm E p h ℓ ((bulk F : EvR X) : N X) ≤ oT E p h ℓ w (F : SA c X) := by
  rw [oT_split (w := w)]; exact le_self_add

theorem oT_emb (x : EvR X) : oT E p h ℓ w ((emb x : OE c X) : SA c X) = tNorm E p h ℓ (x : N X) := by
  rw [coe_emb, oT_ofN]

/-- `e:norm-obs-nonmon` for two factors. -/
theorem oT_πobs_mul_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (F G : OE c X) :
    oT E p h ℓ w (πobs (F * G) : SA c X) ≤
      oT E p h ℓ w (F : SA c X) * oT E p h ℓ w (πobs G : SA c X) +
        oT E p h ℓ w (πobs F : SA c X) * oT E p h ℓ w (G : SA c X) := by
  rw [πobs_mul_eq]
  refine (oT_add_le _ _).trans (add_le_add (oT_mul_le hh hℓ hw _ _) ?_)
  refine (oT_mul_le hh hℓ hw _ _).trans ?_
  rw [oT_emb]
  gcongr
  exact tNorm_bulk_le G

/-- A sharper form: `‖π_obs (F G)‖ ≤ ‖F‖ ‖π_obs G‖ + ‖π_obs F‖ ‖G_∅‖`. -/
theorem oT_πobs_mul_le' (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (F G : OE c X) :
    oT E p h ℓ w (πobs (F * G) : SA c X) ≤
      oT E p h ℓ w (F : SA c X) * oT E p h ℓ w (πobs G : SA c X) +
        oT E p h ℓ w (πobs F : SA c X) * tNorm E p h ℓ ((bulk G : EvR X) : N X) := by
  rw [πobs_mul_eq]
  refine (oT_add_le _ _).trans (add_le_add (oT_mul_le hh hℓ hw _ _) ?_)
  refine (oT_mul_le hh hℓ hw _ _).trans ?_
  rw [oT_emb]

/-- `e:norm-obs-nonmon` for finite products. -/
theorem oT_πobs_prod_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → OE c X) (M τ : ι → ENNReal)
    (hM : ∀ i ∈ s, oT E p h ℓ w (f i : SA c X) ≤ M i)
    (hτ : ∀ i ∈ s, oT E p h ℓ w (πobs (f i) : SA c X) ≤ τ i) :
    oT E p h ℓ w (πobs (∏ i ∈ s, f i) : SA c X) ≤ ∑ i ∈ s, τ i * ∏ l ∈ s.erase i, M l := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sum_empty]
    have : πobs (1 : OE c X) = 0 := by
      rw [show (1 : OE c X) = emb 1 from (map_one _).symm, πobs_emb]
    rw [this]; simp [oT_zero]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, erase_insert ha]
    have ih' := ih (fun i hi => hM i (mem_insert_of_mem hi)) (fun i hi => hτ i (mem_insert_of_mem hi))
    have hP : oT E p h ℓ w ((∏ i ∈ s, f i : OE c X) : SA c X) ≤ ∏ i ∈ s, M i :=
      (oT_prod_le hh hℓ hw s f).trans (prod_le_prod' fun i hi => hM i (mem_insert_of_mem hi))
    refine (oT_πobs_mul_le hh hℓ hw _ _).trans ?_
    rw [add_comm]
    refine add_le_add (mul_le_mul' (hτ a (mem_insert_self a s)) hP) ?_
    refine (mul_le_mul' (hM a (mem_insert_self a s)) ih').trans (le_of_eq ?_)
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    rw [erase_insert_of_ne hai, prod_insert (fun h => ha (mem_of_mem_erase h))]
    ring

theorem oT_prod_sub_one_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → OE c X) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i)
    (hf : ∀ i ∈ s, oT E p h ℓ w ((f i - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp (t i) - 1)) :
    oT E p h ℓ w ((∏ i ∈ s, f i - 1 : OE c X) : SA c X) ≤
      ENNReal.ofReal (Real.exp (∑ i ∈ s, t i) - 1) := by
  induction s using Finset.induction_on with
  | empty => simp [oT_zero]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have ih' := ih (fun i hi => ht i (mem_insert_of_mem hi)) (fun i hi => hf i (mem_insert_of_mem hi))
    have hta := ht a (mem_insert_self a s)
    have hT : 0 ≤ ∑ i ∈ s, t i := sum_nonneg fun i hi => ht i (mem_insert_of_mem hi)
    have e : f a * ∏ i ∈ s, f i - 1 = f a * (∏ i ∈ s, f i - 1) + (f a - 1) := by ring
    have hfa : oT E p h ℓ w (f a : SA c X) ≤ ENNReal.ofReal (Real.exp (t a)) := by
      have e1 : f a = (f a - 1) + 1 := by ring
      rw [e1]
      refine (oT_add_le _ _).trans ((add_le_add (hf a (mem_insert_self a s))
        (oT_one_le hh hℓ)).trans (le_of_eq ?_))
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith [Real.add_one_le_exp (t a)])
        zero_le_one]
      congr 1; ring
    rw [e]
    refine (oT_add_le _ _).trans ((add_le_add ((oT_mul_le hh hℓ hw _ _).trans
      (mul_le_mul' hfa ih')) (hf a (mem_insert_self a s))).trans (le_of_eq ?_))
    have h1 : 0 ≤ Real.exp (∑ i ∈ s, t i) - 1 := by linarith [Real.add_one_le_exp (∑ i ∈ s, t i)]
    have h2 : 0 ≤ Real.exp (t a) - 1 := by linarith [Real.add_one_le_exp (t a)]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_add (by positivity) h2]
    congr 1
    rw [Real.exp_add]; ring

theorem oT_mul_sub_one_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (F G : OE c X) {t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hF : oT E p h ℓ w ((F - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp t₁ - 1))
    (hG : oT E p h ℓ w ((G - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp t₂ - 1)) :
    oT E p h ℓ w ((F * G - 1 : OE c X) : SA c X) ≤ ENNReal.ofReal (Real.exp (t₁ + t₂) - 1) := by
  have h := oT_prod_sub_one_le (E := E) (p := p) hh hℓ hw (univ : Finset Bool)
    (fun i => if i then F else G) (fun i => if i then t₁ else t₂)
    (fun i _ => by cases i <;> simpa) (fun i _ => by cases i <;> simpa)
  simp only [Fintype.prod_bool, Fintype.sum_bool, if_true] at h
  exact h

/-- `‖e^z e^F - 1‖ ≤ e^{|z| + r} - 1` if `‖F‖ ≤ r`. -/
theorem oT_exp_oexp_sub_one_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (z : ℂ) {F : OE c X}
    (hF : ε ((F : SA c X).e) = 0) {r : ℝ} (hr : 0 ≤ r)
    (hFr : oT E p h ℓ w (F : SA c X) ≤ ENNReal.ofReal r) :
    oT E p h ℓ w ((algebraMap ℂ (OE c X) (Complex.exp z) * oexp F - 1 : OE c X) : SA c X) ≤
      ENNReal.ofReal (Real.exp (‖z‖ + r) - 1) := by
  have e : algebraMap ℂ (OE c X) (Complex.exp z) * oexp F - 1 =
      Complex.exp z • (oexp F - 1) + (Complex.exp z - 1) • (1 : OE c X) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_sub, sub_smul, one_smul]
    abel
  rw [e]
  have h1 := oT_oexp_sub_one_le (E := E) (p := p) hh hℓ hw hF hr hFr
  have hz1 : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := Complex.norm_exp_le_exp_norm z
  have hz2 : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
    simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1
  have hr1 : 0 ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
  refine (oT_add_le _ _).trans ?_
  rw [show (((Complex.exp z • (oexp F - 1) : OE c X)) : SA c X) =
      Complex.exp z • (((oexp F - 1 : OE c X)) : SA c X) from rfl,
    show ((((Complex.exp z - 1) • (1 : OE c X) : OE c X)) : SA c X) =
      (Complex.exp z - 1) • ((1 : OE c X) : SA c X) from rfl, oT_smul, oT_smul]
  calc ENNReal.ofReal ‖Complex.exp z‖ * oT E p h ℓ w (((oexp F - 1 : OE c X)) : SA c X) +
        ENNReal.ofReal ‖Complex.exp z - 1‖ * oT E p h ℓ w ((1 : OE c X) : SA c X)
      ≤ ENNReal.ofReal (Real.exp ‖z‖) * ENNReal.ofReal (Real.exp r - 1) +
        ENNReal.ofReal (Real.exp ‖z‖ - 1) * 1 := by
        gcongr
        exact oT_one_le hh hℓ
    _ = ENNReal.ofReal (Real.exp (‖z‖ + r) - 1) := by
        rw [mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (by positivity)
            (by linarith [Real.add_one_le_exp ‖z‖, norm_nonneg z])]
        congr 1; rw [Real.exp_add]; ring

/-- `‖-G + ½ G²‖ ≤ s + s²/2`. -/
theorem oT_H_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) {G : OE c X} {s : ℝ} (hs : 0 ≤ s)
    (hGs : oT E p h ℓ w (G : SA c X) ≤ ENNReal.ofReal s) :
    oT E p h ℓ w ((-G + (1 / 2 : ℂ) • G ^ 2 : OE c X) : SA c X) ≤ ENNReal.ofReal (s + s ^ 2 / 2) := by
  refine (oT_add_le _ _).trans ?_
  rw [show (((1 / 2 : ℂ) • G ^ 2 : OE c X) : SA c X) = (1 / 2 : ℂ) • ((G ^ 2 : OE c X) : SA c X)
    from rfl, oT_smul, NegMemClass.coe_neg, oT_neg,
    ENNReal.ofReal_add hs (by positivity)]
  gcongr
  have h2 := (oT_pow_le hh hℓ hw G 2).trans (pow_le_pow_left' hGs 2)
  rw [← ENNReal.ofReal_pow hs] at h2
  calc ENNReal.ofReal ‖(1 / 2 : ℂ)‖ * oT E p h ℓ w ((G ^ 2 : OE c X) : SA c X)
      ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (s ^ 2) := by
        gcongr; norm_num
    _ = ENNReal.ofReal (s ^ 2 / 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

/-- `‖π_obs (e^z e^{-(x + G)})‖ ≤ e^{|z| + r} (s + s²/2)`. -/
theorem oT_πobs_exp_le (hh : 0 < h) (hℓ : 0 < ℓ) (hw : w.Sub) (z : ℂ)
    {x : EvR X} (hx : ε (x : Grassmann.N X) = 0) {G : OE c X} (hG : bulk G = 0) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hxr : tNorm E p h ℓ (x : Grassmann.N X) ≤ ENNReal.ofReal r)
    (hGs : oT E p h ℓ w (G : SA c X) ≤ ENNReal.ofReal s) :
    oT E p h ℓ w ((πobs (algebraMap ℂ (OE c X) (Complex.exp z) * oexp (-(emb x + G))) : OE c X) :
      SA c X) ≤ ENNReal.ofReal (Real.exp (‖z‖ + r) * (s + s ^ 2 / 2)) := by
  have e : πobs (algebraMap ℂ (OE c X) (Complex.exp z) * oexp (-(emb x + G))) =
      (πobs (algebraMap ℂ (OE c X) (Complex.exp z) * oexp (-(emb x + G))) -
        (-G + (1 / 2 : ℂ) • G ^ 2)) + (-G + (1 / 2 : ℂ) • G ^ 2) := by abel
  rw [e]
  refine (oT_add_le _ _).trans ((add_le_add (πobs_oexp_expansion_le hh hℓ hw z hx hG hr hs hxr hGs)
    (oT_H_le hh hℓ hw hs hGs)).trans (le_of_eq ?_))
  have h1 : 0 ≤ Real.exp (‖z‖ + r) - 1 := by
    linarith [Real.add_one_le_exp (‖z‖ + r), norm_nonneg z]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

end Generic

section Commute

variable {c : Case} {Λ : Type*} [DecidableEq Λ]

theorem πobs_thetaOL (F : OE c Λ) : πobs (thetaO F) = thetaO (πobs F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

theorem πobs_inclOL (F : OE c Λ) : πobs (inclO F) = inclO (πobs F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

theorem πobs_ECOL [Fintype Λ] (C : Matrix Λ Λ ℝ) (F : OE c (Λ ⊕ Λ)) :
    πobs (ECO C F) = ECO C (πobs F) := by
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_) <;> simp [piobs_apply]

end Commute

/-! ### Real inequalities -/

/-- The `K`-part (the analogue of `Step.largeK_real` with base `β`). -/
theorem largeK_real' {d n m P : ℕ} {A η β : ℝ} (hA : 1 ≤ A) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (hβ : 1 ≤ β) (hcomb : (1 + 2 * η) * (n : ℝ) ≤ m) (hm : 2 ^ d < m) (hmP : m ≤ P * n)
    (hAP : (β ^ 2) ^ P ≤ A ^ (η / 2 ^ d)) :
    A ^ (n - 2 ^ d) * β ^ m * β ^ (P * n) ≤ A ^ (-η) * A ^ (m - 2 ^ d) := by
  have hA0 : 0 < A := by linarith
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have h1 : β ^ m * β ^ (P * n) ≤ A ^ (η / 2 ^ d * n) := by
    calc β ^ m * β ^ (P * n) ≤ β ^ (P * n) * β ^ (P * n) := by
          gcongr
      _ = ((β ^ 2) ^ P) ^ n := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ (A ^ (η / 2 ^ d)) ^ n := by gcongr
      _ = A ^ (η / 2 ^ d * n) := by rw [← Real.rpow_mul_natCast hA0.le]
  have hexp : ((n - 2 ^ d : ℕ) : ℝ) + η / 2 ^ d * n ≤ -η + ((m - 2 ^ d : ℕ) : ℝ) := by
    have hm' : ((m - 2 ^ d : ℕ) : ℝ) = m - 2 ^ d := by
      rw [Nat.cast_sub hm.le]; push_cast; ring
    rw [hm']
    have hmR : (2 : ℝ) ^ d + 1 ≤ m := by exact_mod_cast hm
    by_cases hn : n ≤ 2 ^ d
    · rw [Nat.sub_eq_zero_of_le hn, Nat.cast_zero, zero_add]
      have hnR : (n : ℝ) ≤ 2 ^ d := by exact_mod_cast hn
      have : η / 2 ^ d * n ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hnR hη0.le
      linarith
    · push Not at hn
      rw [Nat.cast_sub hn.le]; push_cast
      have hn1 : (1 : ℝ) ≤ n := by
        have : 1 ≤ n := le_trans Nat.one_le_two_pow hn.le
        exact_mod_cast this
      have : η / 2 ^ d * n ≤ η * n := by
        gcongr
        exact div_le_self hη0.le h2d
      nlinarith
  have hβ0 : 0 ≤ β := by linarith
  calc A ^ (n - 2 ^ d) * β ^ m * β ^ (P * n) = A ^ (n - 2 ^ d) * (β ^ m * β ^ (P * n)) := by ring
    _ ≤ A ^ (((n - 2 ^ d : ℕ) : ℝ)) * A ^ (η / 2 ^ d * n) := by
      rw [Real.rpow_natCast]; gcongr
    _ = A ^ (((n - 2 ^ d : ℕ) : ℝ) + η / 2 ^ d * n) := (Real.rpow_add hA0 _ _).symm
    _ ≤ A ^ (-η + ((m - 2 ^ d : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hA hexp
    _ = A ^ (-η) * A ^ (m - 2 ^ d) := by rw [Real.rpow_add hA0, Real.rpow_natCast]

/-- The `δI`-part: `A^{(n - 2^d)_+} q^{m-2} 2^{P n} ≤ A` for `m ≥ 2`, `n ≤ m`, `q ≤ r^2`. -/
theorem largeD_real' {d n m P : ℕ} {A q r : ℝ} (hd : 2 ≤ d) (hA : 1 ≤ A) (hq : 0 ≤ q)
    (hr : r = 1 / (A * 2 ^ P)) (hqr : q ≤ r ^ 2) (hm2 : 2 ≤ m) (hnm : n ≤ m)
    (hAP : (2 : ℝ) ^ (P * 2 ^ d) ≤ A) :
    A ^ (n - 2 ^ d) * q ^ (m - 2) * 2 ^ (P * n) ≤ A := by
  have hA0 : 0 < A := by linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    exact one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by norm_num))
  have hq1 : q ≤ 1 := hqr.trans (pow_le_one₀ hr0.le hr1)
  by_cases hn : n ≤ 2 ^ d
  · rw [Nat.sub_eq_zero_of_le hn, pow_zero, one_mul]
    have h1 : q ^ (m - 2) ≤ 1 := pow_le_one₀ hq hq1
    have h2 : (2 : ℝ) ^ (P * n) ≤ A :=
      le_trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left P hn)) hAP
    calc q ^ (m - 2) * 2 ^ (P * n) ≤ 1 * A := by gcongr
      _ = A := one_mul A
  · push Not at hn
    have h4 : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    have h1 : q ^ (m - 2) ≤ r ^ n := by
      calc q ^ (m - 2) ≤ (r ^ 2) ^ (m - 2) := by gcongr
        _ = r ^ (2 * (m - 2)) := by rw [← pow_mul]
        _ ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1 (by omega)
    have h2 : A ^ (n - 2 ^ d) ≤ A ^ n := pow_le_pow_right₀ hA (Nat.sub_le _ _)
    have h3 : A ^ n * r ^ n * 2 ^ (P * n) = 1 := by
      rw [pow_mul, ← mul_pow, ← mul_pow, hr]
      rw [show A * (1 / (A * 2 ^ P)) * 2 ^ P = 1 by field_simp, one_pow]
    calc A ^ (n - 2 ^ d) * q ^ (m - 2) * 2 ^ (P * n)
        ≤ A ^ n * r ^ n * 2 ^ (P * n) := by gcongr
      _ = 1 := h3
      _ ≤ A := hA

end

end Obs
