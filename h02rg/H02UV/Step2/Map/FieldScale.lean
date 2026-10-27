import Step2.Coup.Est4
import Step2.Map.Spaces2

/-!
# Field rescaling of the irrelevant coordinates (causal field scales)

For `s > 0` the field rescaling `σ_s` (`sig`) satisfies `‖σ_s F‖_{T(ℓ)} = ‖F‖_{T(sℓ)}`
(`tNorm_sig_eq`). It preserves the admissible block families `BSub j` and activities `ASub j`
(`sigF_mem`, `sigK_mem`), and `Fnorm j ℓ (σ_s F) = Fnorm j (sℓ) F`, `Knorm j ℓ A (σ_s K) =
Knorm j (sℓ) A K`. So the coordinates `x_j = σ_{s_j}(D_j, K_j)` measured at a fixed field scale
`ℓ` are the raw `(D_j, K_j)` measured at the causal field scale `ℓ_j = s_j ℓ`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

section Gen

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

theorem sig_one_apply (F : Grassmann.N X) : sig (1 : ℂ) F = F := by
  rw [sig, one_smul, ExteriorAlgebra.map_id, AlgHom.id_apply]

theorem map_sig_comm (f : V X →ₗ[ℂ] V X) (r : ℂ) (F : Grassmann.N X) :
    ExteriorAlgebra.map f (sig r F) = sig r (ExteriorAlgebra.map f F) := by
  rw [sig, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map]
  congr 2
  ext v; simp

/-- `‖σ_s F‖_{T(ℓ)} ≤ ‖F‖_{T(sℓ)}` for `s > 0`. -/
theorem tNorm_sig_le_scale (hh : 0 ≤ h) (hℓ : 0 < ℓ) {s : ℝ} (hs : 0 < s) (F : Grassmann.N X) :
    tNorm E p h ℓ (sig (s : ℂ) F) ≤ tNorm E p h (s * ℓ) F := by
  refine iSup₂_le fun g hg => ?_
  set g' : TestFn X := fun n z => (s : ℂ) ^ n * g n z
  have hpair : pair (sig (s : ℂ) F) g = pair F g' := by
    unfold pair
    refine sum_congr rfl fun n _ => ?_
    congr 1
    refine sum_congr rfl fun z _ => ?_
    rw [coeff_sig]; simp only [g']; ring
  have hg' : phiNorm E p h (s * ℓ) g' ≤ 1 := by
    refine le_trans ?_ hg
    refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
    refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) (phiTerm_le g z α hα)
    unfold phiTerm
    have e : nab α (g' n) z = (s : ℂ) ^ n * nab α (g n) z := nab_const_mul α _ (g n) z
    rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_inv,
      mul_pow]
    have : s⁻¹ ^ n * s ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hs.ne', one_pow]
    calc s⁻¹ ^ n * ℓ⁻¹ ^ n * h ^ ord α * (s ^ n * ‖nab α (g n) z‖)
        = (s⁻¹ ^ n * s ^ n) * (ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖) := by ring
      _ = _ := by rw [this, one_mul]
  rw [hpair]
  exact le_iSup₂_of_le g' hg' le_rfl

/-- **`‖σ_s F‖_{T(ℓ)} = ‖F‖_{T(sℓ)}`** for `s > 0`. -/
theorem tNorm_sig_eq (hh : 0 ≤ h) (hℓ : 0 < ℓ) {s : ℝ} (hs : 0 < s) (F : Grassmann.N X) :
    tNorm E p h ℓ (sig (s : ℂ) F) = tNorm E p h (s * ℓ) F := by
  refine le_antisymm (tNorm_sig_le_scale hh hℓ hs F) ?_
  have h1 := tNorm_sig_le_scale (E := E) (p := p) hh (mul_pos hs hℓ) (inv_pos.2 hs)
    (sig (s : ℂ) F)
  rwa [sig_sig, ← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne', Complex.ofReal_one, sig_one_apply,
    ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] at h1

/-! ### Lipschitz dependence on the scale -/

/-- `(n + 1) xⁿ (1 - x) ≤ 1 - x^{n+1}` for `0 ≤ x ≤ 1`. -/
theorem pow_mul_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ n : ℕ, ((n : ℝ) + 1) * x ^ n * (1 - x) ≤ 1 - x ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_one_sub_le hx0 hx1 n
    have h1 : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 _
    have e : ((((n + 1 : ℕ) : ℝ)) + 1) * x ^ (n + 1) * (1 - x) =
        x * (((n : ℝ) + 1) * x ^ n * (1 - x)) + x ^ (n + 1) * (1 - x) := by push_cast; ring
    rw [e]
    have h3 := mul_le_mul_of_nonneg_left ih hx0
    have h4 : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have h5 : x ^ (n + 1) * (1 - x) ≤ 1 * (1 - x) := mul_le_mul_of_nonneg_right h4 (by linarith)
    have e2 : x ^ (n + 1 + 1) = x * x ^ (n + 1) := by ring
    nlinarith

/-- `|aⁿ - bⁿ| ≤ |a - b|/τ` for `0 ≤ a, b ≤ 1 - τ`. -/
theorem abs_pow_sub_pow_le {a b τ : ℝ} (hτ : 0 < τ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1 - τ)
    (hb1 : b ≤ 1 - τ) (n : ℕ) : |a ^ n - b ^ n| ≤ |a - b| / τ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  set x := 1 - τ with hx
  have hx0 : 0 ≤ x := ha.trans ha1
  have hx1 : x ≤ 1 := by linarith
  have hsum : |∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)| ≤ n * x ^ (n - 1) := by
    rw [abs_of_nonneg (sum_nonneg fun i _ => by positivity)]
    calc ∑ i ∈ range n, a ^ i * b ^ (n - 1 - i) ≤ ∑ _i ∈ range n, x ^ (n - 1) := by
          refine sum_le_sum fun i hi => ?_
          have hi' := mem_range.1 hi
          calc a ^ i * b ^ (n - 1 - i) ≤ x ^ i * x ^ (n - 1 - i) := by gcongr
            _ = x ^ (n - 1) := by rw [← pow_add]; congr 1; omega
      _ = n * x ^ (n - 1) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hkey : (n : ℝ) * x ^ (n - 1) * τ ≤ 1 := by
    have h := pow_mul_one_sub_le hx0 hx1 (n - 1)
    have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn]; push_cast; ring
    have hτx : τ = 1 - x := by rw [hx]; ring
    rw [hτx, ← hn1]
    have := pow_nonneg hx0 (n - 1 + 1)
    linarith
  have e := (Commute.all a b).geom_sum₂_mul n
  rw [← e, abs_mul, le_div_iff₀ hτ]
  calc |∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)| * |a - b| * τ
      ≤ (n * x ^ (n - 1)) * |a - b| * τ := by gcongr
    _ = (n * x ^ (n - 1) * τ) * |a - b| := by ring
    _ ≤ 1 * |a - b| := by gcongr
    _ = |a - b| := one_mul _

/-- **Lipschitz dependence on the scale**: `‖σ_a F - σ_b F‖_{T(ℓ)} ≤ (|a - b|/τ) ‖F‖_{T(ℓ)}` for
`0 ≤ a, b ≤ 1 - τ`. -/
theorem tNorm_sig_sub_le (hh : 0 < h) (hℓ : 0 < ℓ) {a b τ : ℝ} (hτ : 0 < τ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (ha1 : a ≤ 1 - τ) (hb1 : b ≤ 1 - τ) (F : Grassmann.N X) :
    tNorm E p h ℓ (sig (a : ℂ) F - sig (b : ℂ) F) ≤
      ENNReal.ofReal (|a - b| / τ) * tNorm E p h ℓ F := by
  rw [← ENNReal.ofReal_toReal (tNorm_ne_top hh hℓ F), ← ENNReal.ofReal_mul (by positivity)]
  refine tNorm_le fun g hg => ?_
  set g' : TestFn X := fun n z => ((a : ℂ) ^ n - (b : ℂ) ^ n) * g n z
  have hpair : pair (sig (a : ℂ) F - sig (b : ℂ) F) g = pair F g' := by
    unfold pair
    refine sum_congr rfl fun n _ => ?_
    congr 1
    refine sum_congr rfl fun z _ => ?_
    rw [coeff_sub', coeff_sig, coeff_sig]; simp only [g']; ring
  have hg' : phiNorm E p h ℓ g' ≤ ENNReal.ofReal (|a - b| / τ) := by
    refine phiNorm_le fun n z α hα => ?_
    unfold phiTerm
    have e : nab α (g' n) z = ((a : ℂ) ^ n - (b : ℂ) ^ n) * nab α (g n) z :=
      nab_const_mul α _ (g n) z
    have hc : ‖(a : ℂ) ^ n - (b : ℂ) ^ n‖ ≤ |a - b| / τ := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact abs_pow_sub_pow_le hτ ha hb ha1 hb1 n
    have h1 : phiTerm h ℓ g z α ≤ 1 :=
      phiTerm_le_of_phiNorm_le hh.le hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) z α hα
    unfold phiTerm at h1
    rw [e, norm_mul]
    calc ℓ⁻¹ ^ n * h ^ ord α * (‖(a : ℂ) ^ n - (b : ℂ) ^ n‖ * ‖nab α (g n) z‖)
        = ‖(a : ℂ) ^ n - (b : ℂ) ^ n‖ * (ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖) := by ring
      _ ≤ |a - b| / τ * 1 := by
          gcongr
      _ = |a - b| / τ := mul_one _
  rw [hpair]
  have := abs_pair_le hh hℓ F (by positivity) hg'
  linarith [mul_comm (|a - b| / τ) (tNorm E p h ℓ F).toReal]

end Gen

variable {d L N : ℕ} [NeZero L]

/-! ### Families and activities -/

/-- `σ_s` on a block family. -/
def sigF (r : ℂ) (F : Fam d L N) : Fam d L N := fun b => sigE r (F b)

/-- `σ_s` on an activity. -/
def sigK (r : ℂ) (K : Act d L N) : Act d L N := fun X => sigE r (K X)

theorem sigF_add (r : ℂ) (F G : Fam d L N) : sigF r (F + G) = sigF r F + sigF r G :=
  funext fun b => map_add _ _ _

theorem sigF_sub (r : ℂ) (F G : Fam d L N) : sigF r (F - G) = sigF r F - sigF r G :=
  funext fun b => map_sub _ _ _

theorem sigK_sub (r : ℂ) (K K' : Act d L N) : sigK r (K - K') = sigK r K - sigK r K' :=
  funext fun X => map_sub _ _ _

theorem sigF_sigF (r r' : ℂ) (F : Fam d L N) : sigF r (sigF r' F) = sigF (r * r') F :=
  funext fun b => Subtype.ext (by simp [sigF, sig_sig])

theorem sigK_sigK (r r' : ℂ) (K : Act d L N) : sigK r (sigK r' K) = sigK (r * r') K :=
  funext fun X => Subtype.ext (by simp [sigK, sig_sig])

theorem sigF_one (F : Fam d L N) : sigF 1 F = F :=
  funext fun b => Subtype.ext (by simp [sigF, sig_one_apply])

theorem sigK_one (K : Act d L N) : sigK 1 K = K :=
  funext fun X => Subtype.ext (by simp [sigK, sig_one_apply])

theorem AE_sigE (T : AffAut d L N) (r : ℂ) (F : EvR (Lam d L N)) :
    AE T (sigE r F) = sigE r (AE T F) :=
  Subtype.ext (by simp only [AE, coe_mapE, coe_sigE]; exact map_sig_comm _ r _)

theorem Jsym_sig (r : ℂ) (F : Alg d L N) : Jsym (sig r F) = sig r (Jsym F) := by
  rw [Jsym]; exact map_sig_comm _ r _

theorem sig_mem_JS {F : Alg d L N} (hF : F ∈ JS d L N) (r : ℂ) : sig r F ∈ JS d L N := by
  rw [mem_JS] at hF ⊢; rw [Jsym_sig, hF]

theorem sigF_mem {j : ℕ} {F : Fam d L N} (hF : F ∈ BSub (L := L) (N := N) j) (r : ℂ) :
    sigF r F ∈ BSub (L := L) (N := N) j := by
  refine ⟨⟨fun b => ?_, fun b => ?_⟩, famCovG_sig hF.2.1 r, fun T hT hP b hb => ?_,
    fun b => ?_, fun b hb => ?_⟩
  · simp only [sigF, coe_sigE]; exact sig_mem_NX (hF.1.loc b) r
  · simp only [sigF, coe_sigE]; exact isSym_sig (hF.1.sym b) r
  · simp only [sigF]; rw [AE_sigE, hF.2.2.1 T hT hP b hb]
  · simp only [sigF, coe_sigE]; exact sig_mem_JS (hF.2.2.2.1 b) r
  · simp only [sigF, hF.2.2.2.2 b hb, map_zero]

theorem sigK_mem {j : ℕ} {K : Act d L N} (hK : K ∈ ASub (L := L) (N := N) j) (r : ℂ) :
    sigK r K ∈ ASub (L := L) (N := N) j := by
  refine ⟨⟨fun X hX => ?_, fun X hX => ?_⟩, fun t ht X => ?_, fun T hT hP X => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · simp only [sigK, coe_sigE]; exact sig_mem_NX (hK.1.loc X hX) r
  · simp only [sigK, coe_sigE]; exact isSym_sig (hK.1.sym X hX) r
  · simp only [sigK, coe_sigE]; rw [hK.2.1 t ht X, autAlg_sig]
  · simp only [sigK]; rw [AE_sigE, hK.2.2.1 T hT hP X]
  · simp only [sigK, coe_sigE]; exact sig_mem_JS (hK.2.2.2.1 X hX) r
  · simp only [sigK, hK.2.2.2.2 X hX, map_zero]

theorem Tj_sig_eq {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℝ} (hs : 0 < s) (F : Alg d L N) :
    Tj d (L : ℝ) j ℓ (sig (s : ℂ) F) = Tj d (L : ℝ) j (s * ℓ) F :=
  tNorm_sig_eq (by positivity) hℓ hs F

theorem Fnorm_sigF {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℝ} (hs : 0 < s) (F : Fam d L N) :
    Fnorm j ℓ (sigF (s : ℂ) F) = Fnorm j (s * ℓ) F := by
  unfold Fnorm; simp only [sigF, coe_sigE, Tj_sig_eq hℓ hs]

theorem Knorm_sigK {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) {s : ℝ} (hs : 0 < s) (K : Act d L N) :
    Knorm j ℓ A (sigK (s : ℂ) K) = Knorm j (s * ℓ) A K := by
  unfold Knorm; simp only [sigK, coe_sigE, Tj_sig_eq hℓ hs]

end

end Step2
