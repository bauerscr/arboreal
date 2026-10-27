import Flow.FlowCoup
import Flow.Spaces
import Flow.StableCont

/-!
# The renormalisation group step on a single torus, in rescaled coordinates

Ingredients for the dynamical system of Section `sec:flow` (`e:flowblock`), on a fixed torus
`Λ_N` and a fixed scale `j` with `j + 1 < N`:

* `restr j K`: the activity `K` restricted to connected polymers (the normalised form of an
  element of `𝒦_j`, as in `KSp`);
* the rescaled coordinates `v = (ẑ, ŷ, â) = (z, y, L^{2j} a)`, `b̂ = L^{-(d-2)j} b`
  (`Vres`, `vres`);
* `FN`: `(v, b̂, K) ↦ K_{j+1}` (restricted to connected polymers), a map
  `Vsp × ℂ × 𝒦_j(Λ_N) → 𝒦_{j+1}(Λ_N)`;
* `DN`: its linearisation `K ↦ D K_{j+1}|_0 (0, K)`;
* `BN`: the part `B_j` of `e:flowblock`, `(b̂, K) ↦ v_{j+1} - E v` (read off from
  `(u_{j+1}, V_{j+1})`, which are linear in `(V_j, K_j)`).

The hypotheses (the conclusions of `thm:step` and of the covariance and `Loc` estimates, for the
covariances `C_{j+1}` of Section `sec:frd`) are collected in the structure `Hyp`.
The mass parameter `m ∈ ℝ` enters through `C_{j+1}` with `m² = max m 0`.
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step Metric Filter Topology Coup

variable {d L : ℕ} [NeZero L]

/-! ### Restriction to connected polymers -/

open Classical in
/-- `K` restricted to connected `j`-polymers. -/
def restr (j : ℕ) {N : ℕ} (K : Act d L N) : Act d L N := fun X => if IsConn j X then K X else 0

theorem restr_of_conn {j N : ℕ} (K : Act d L N) {X : Finset (Lam d L N)} (hX : IsConn j X) :
    restr j K X = K X := by simp [restr, hX]

theorem restr_of_not_conn {j N : ℕ} (K : Act d L N) {X : Finset (Lam d L N)}
    (hX : ¬ IsConn j X) : restr j K X = 0 := by simp [restr, hX]

theorem restr_mem {j N : ℕ} (hj : j ≤ N) {K : Act d L N} (hK : InK j K) :
    restr j K ∈ KSub j N := by
  refine ⟨⟨fun X hX => ?_, fun X hX => ?_, fun X hX => ?_, fun T hT hTb X hX => ?_⟩,
    fun X hX => restr_of_not_conn K hX⟩
  · rw [restr_of_conn K hX]; exact hK.loc X hX
  · rw [restr_of_conn K hX]; exact hK.sym X hX
  · rw [restr_of_conn K hX]; exact hK.jinv X hX
  · rw [restr_of_conn K hX, hK.aut T hT hTb X hX, restr_of_conn]
    exact (hTb.isConn_img hT hj).2 hX

theorem Knorm_congr {j N : ℕ} {ℓ A : ℝ} {K K' : Act d L N} (h : ∀ X, IsConn j X → K X = K' X) :
    Knorm j ℓ A K = Knorm j ℓ A K' := by
  unfold Knorm
  refine iSup_congr fun X => iSup_congr fun hX => ?_
  rw [h X (mem_connSets.1 hX)]

theorem Knorm_restr {j N : ℕ} {ℓ A : ℝ} (K : Act d L N) : Knorm j ℓ A (restr j K) = Knorm j ℓ A K :=
  Knorm_congr fun _ hX => restr_of_conn K hX

theorem restr_add {j N : ℕ} (K K' : Act d L N) : restr j (K + K') = restr j K + restr j K' := by
  funext X; by_cases hX : IsConn j X <;> simp [restr, hX]

theorem restr_smul {j N : ℕ} (c : ℂ) (K : Act d L N) : restr j (c • K) = c • restr j K := by
  funext X; by_cases hX : IsConn j X <;> simp [restr, hX]

/-! ### The hypotheses -/

/-- The covariance `C_{j+1}` on `Λ_N`, with `m² = max m 0`. -/
abbrev Cm (d L N : ℕ) [NeZero L] (m : ℝ) (j : ℕ) : Matrix (Lam d L N) (Lam d L N) ℝ :=
  Cfrd d L N (max m 0) j

/-- The hypotheses used for the construction of the dynamical system of Section `sec:flow`:
the conclusions of Theorem `thm:step` (in the form of `Step.step_deriv`), of the covariance
estimates (`cov_bounds`) and of the estimates for `Loc` (`WQ_bounds`), for the covariances
`C_{j+1}` of Section `sec:frd` with `j + 1 < N`. -/
structure Hyp (d L : ℕ) [NeZero L] (A ℓ₀ ε C₁ δK Kc Cw : ℝ) : Prop where
  hd : 3 ≤ d
  hL : 2 ^ (d + 3) + 8 * d < L
  hA : 1 ≤ A
  hℓ₀ : 0 < ℓ₀
  hε : 0 < ε
  hC₁ : 0 ≤ C₁
  hδK : 0 ≤ δK
  hKc : 0 ≤ Kc
  hCw : 0 ≤ Cw
  good : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq →
    GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Cfrd d L N msq j)
  zero : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq →
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (Knext j (Cfrd d L N msq j) 0 (0 : Act d L N)) = 0
  lip : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq →
    ∀ (V₁ V₂ : Vcoup) (K₁ K₂ : Act d L N), InK j K₁ → InK j K₂ →
      xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2) →
      xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2) →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
          (fun U => Knext j (Cfrd d L N msq j) V₁ K₁ U - Knext j (Cfrd d L N msq j) V₂ K₂ U) ≤
        ENNReal.ofReal C₁ * xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂)
  rem : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq →
    ∀ (V₁ V₂ : Vcoup) (K₁ K₂ : Act d L N), InK j K₁ → InK j K₂ →
      xnorm j (ellj d L ℓ₀ j) A V₁ K₁ ≤ ENNReal.ofReal (ε / 2) →
      xnorm j (ellj d L ℓ₀ j) A V₂ K₂ ≤ ENNReal.ofReal (ε / 2) →
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U => Knext j (Cfrd d L N msq j) V₁ K₁ U -
          Knext j (Cfrd d L N msq j) V₂ K₂ U -
            DKnext j (Cfrd d L N msq j) 0 0 (V₁ - V₂) (K₁ - K₂) U) ≤
        ENNReal.ofReal C₁ *
          max (xnorm j (ellj d L ℓ₀ j) A V₁ K₁) (xnorm j (ellj d L ℓ₀ j) A V₂ K₂) *
          xnorm j (ellj d L ℓ₀ j) A (V₁ - V₂) (K₁ - K₂)
  dK : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq → ∀ (V' : Vcoup) (K' : Act d L N), InK j K' →
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j (Cfrd d L N msq j) 0 0 V' K') ≤
      ENNReal.ofReal δK * Knorm j (ellj d L ℓ₀ j) A K'
  dV : ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq → ∀ V' : Vcoup,
    Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (DKnext j (Cfrd d L N msq j) 0 0 V' (0 : Act d L N)) = 0
  cov : ∀ (N j : ℕ), j + 1 ≤ N → ∀ msq : ℝ, 0 ≤ msq →
    |Cfrd d L N msq j 0 0| ≤ Kc * (L : ℝ) ^ (-(((d : ℝ) - 2) * j)) ∧
    ∀ e : Dir d, |Cfrd d L N msq j 0 (dirVec e) - Cfrd d L N msq j 0 0| ≤
      Kc * (L : ℝ) ^ (-((d : ℝ) * j))
  wq : ∀ (N j : ℕ), j + 1 < N → ∀ K : Act d L N, InK j K → ∀ i₀ : Fin d,
    ‖(WQ i₀ j K).z‖ ≤ Cw / ℓ₀ ^ 2 * (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
    ‖(WQ i₀ j K).y‖ ≤ Cw / ℓ₀ ^ 2 * (Knorm j (ellj d L ℓ₀ j) A K).toReal ∧
    (L : ℝ) ^ (2 * j) * ‖(WQ i₀ j K).a‖ ≤ Cw / ℓ₀ ^ 2 * (Knorm j (ellj d L ℓ₀ j) A K).toReal

variable {ℓ₀ A ε C₁ δK Kc Cw : ℝ}

namespace Hyp

variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

theorem hd1 : 1 ≤ d := by have := H.hd; omega
theorem hL8 : 2 ^ (d + 3) ≤ L := by have := H.hL; omega
theorem hL16 : 16 ≤ L := by
  have h1 := H.hL
  have h2 : 2 ^ 4 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by have := H.hd; omega)
  omega
theorem hL1 : (1 : ℝ) ≤ L := by have := H.hL16; exact_mod_cast (by omega : 1 ≤ L)
theorem hL0 : (0 : ℝ) < L := by linarith [H.hL1]
theorem goodm {N j : ℕ} (hj : j + 1 < N) (m : ℝ) :
    GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Cm d L N m j) := H.good N j hj _ (le_max_right m 0)

end Hyp

/-! ### Rescaled coordinates -/

/-- The rescaled coordinates `v = (ẑ, ŷ, â)`. -/
abbrev Vsp := ℂ × ℂ × ℂ

variable (d L) in
/-- The coupling constants `(z, y, a, b) = (ẑ, ŷ, L^{-2j} â, L^{(d-2)j} b̂)` of rescaled
coordinates `(v, b̂)` at scale `j`. -/
def VresL (j : ℕ) : (Vsp × ℂ) →ₗ[ℂ] Vcoup where
  toFun p := ⟨p.1.1, p.1.2.1, p.1.2.2 / (L : ℂ) ^ (2 * j), (L : ℂ) ^ ((d - 2) * j) * p.2⟩
  map_add' p q := Vcoup.ext' (by simp) (by simp) (by simp [add_div]) (by simp [mul_add])
  map_smul' c p := Vcoup.ext' (by simp) (by simp) (by simp [mul_div_assoc])
    (by simp; ring)

@[simp] theorem VresL_z (j : ℕ) (p : Vsp × ℂ) : (VresL d L j p).z = p.1.1 := rfl
@[simp] theorem VresL_y (j : ℕ) (p : Vsp × ℂ) : (VresL d L j p).y = p.1.2.1 := rfl
@[simp] theorem VresL_a (j : ℕ) (p : Vsp × ℂ) :
    (VresL d L j p).a = p.1.2.2 / (L : ℂ) ^ (2 * j) := rfl
@[simp] theorem VresL_b (j : ℕ) (p : Vsp × ℂ) :
    (VresL d L j p).b = (L : ℂ) ^ ((d - 2) * j) * p.2 := rfl

theorem norm_Lpow (n : ℕ) : ‖(L : ℂ) ^ n‖ = (L : ℝ) ^ n := by
  rw [norm_pow, Complex.norm_natCast]

/-- The constant `c_X = 4 c_V + 1` in `‖(V, K)‖_j ≤ c_X ‖(v, b̂, K)‖`. -/
def cX (d : ℕ) (ℓ₀ : ℝ) : ℝ := 4 * cV d ℓ₀ + 1

theorem cX_pos (d : ℕ) (ℓ₀ : ℝ) : 0 < cX d ℓ₀ := by
  have := cV_nonneg d ℓ₀; unfold cX; linarith

theorem Vnorm_VresL_le (hd : 2 ≤ d) {j N : ℕ} (hj : j ≤ N) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (p : Vsp × ℂ) :
    Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) (VresL d L j p) ≤
      ENNReal.ofReal (4 * cV d ℓ₀ * ‖p‖) := by
  refine (Vnorm_le_coef hd hj hℓ₀ _).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [VresL_z, VresL_y, VresL_a, VresL_b, norm_mul, norm_div, norm_Lpow]
  have ha : (L : ℝ) ^ (2 * j) * (‖p.1.2.2‖ / (L : ℝ) ^ (2 * j)) = ‖p.1.2.2‖ := by
    field_simp
  have hb : (L : ℝ) ^ ((d - 2) * j) * ‖p.2‖ / (L : ℝ) ^ ((d - 2) * j) = ‖p.2‖ := by
    field_simp
  rw [ha, hb]
  have h1 : ‖p.1.1‖ ≤ ‖p‖ := (norm_fst_le _).trans (norm_fst_le _)
  have h2 : ‖p.1.2.1‖ ≤ ‖p‖ := ((norm_fst_le _).trans (norm_snd_le _)).trans (norm_fst_le _)
  have h3 : ‖p.1.2.2‖ ≤ ‖p‖ := ((norm_snd_le _).trans (norm_snd_le _)).trans (norm_fst_le _)
  have h4 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le _
  have := cV_nonneg d ℓ₀
  nlinarith

/-! ### The map `(v, b̂, K) ↦ K_{j+1}` on a torus -/

instance instFactEllj {ℓ₀ : ℝ} [h : Fact (0 < ℓ₀)] (j : ℕ) : Fact (0 < ellj d (L : ℝ) ℓ₀ j) :=
  ⟨ellj_pos (d := d) (L := L) (Nat.cast_pos.2 (NeZero.pos L)) h.out j⟩

variable [Fact (0 < ℓ₀)] [Fact (0 < A)]

/-- The torus space `𝒦_j(Λ_N)` with the norm `‖·‖_j`. -/
abbrev KS (d L : ℕ) [NeZero L] (j N : ℕ) (ℓ₀ A : ℝ) := KSp d L j N (ellj d (L : ℝ) ℓ₀ j) A

/-- The points `(v, b̂, K)` of the torus version of the dynamical system. -/
abbrev XS (d L : ℕ) [NeZero L] (j N : ℕ) (ℓ₀ A : ℝ) := Vsp × ℂ × KS d L j N ℓ₀ A

theorem coeffKSp_apply' {j N : ℕ} {ℓ A : ℝ} (X : Finset (Lam d L N)) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) (K : KSp d L j N ℓ A) :
    KFam.coeffKSp X z K = coeff (K.toAct X : Alg d L N) z := rfl

theorem KSp.norm_eq {j N : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)] (K : KSp d L j N ℓ A) :
    ENNReal.ofReal ‖K‖ = Knorm j ℓ A K.toAct :=
  ENNReal.ofReal_toReal (Knorm_ne_top Fact.out _)

theorem KSp.norm_sub_eq {j N : ℕ} {ℓ A : ℝ} [Fact (0 < ℓ)] [Fact (0 < A)]
    (K K' : KSp d L j N ℓ A) :
    ‖K - K'‖ = (Knorm j ℓ A (fun U => K.toAct U - K'.toAct U)).toReal := by
  rw [KSp.norm_def, _root_.map_sub]; rfl

theorem VresL_sub {N : ℕ} (j : ℕ) (x x' : XS d L j N ℓ₀ A) :
    VresL d L j (x.1, x.2.1) - VresL d L j (x'.1, x'.2.1) =
      VresL d L j ((x - x').1, (x - x').2.1) := by
  rw [← _root_.map_sub]; rfl

theorem toAct_sub' {j N : ℕ} {ℓ A : ℝ} (K K' : KSp d L j N ℓ A) :
    K.toAct - K'.toAct = (K - K').toAct := (_root_.map_sub _ _ _).symm

theorem xnorm_XS_le (hd : 2 ≤ d) {j N : ℕ} (hj : j ≤ N) (x : XS d L j N ℓ₀ A) :
    xnorm j (ellj d L ℓ₀ j) A (VresL d L j (x.1, x.2.1)) x.2.2.toAct ≤
      ENNReal.ofReal (cX d ℓ₀ * ‖x‖) := by
  unfold xnorm
  have h1 := Vnorm_VresL_le (L := L) (N := N) hd hj (Fact.out : 0 < ℓ₀) (x.1, x.2.1)
  have hp : ‖((x.1, x.2.1) : Vsp × ℂ)‖ ≤ ‖x‖ := by
    rw [Prod.norm_mk, Prod.norm_def x, Prod.norm_def x.2]
    exact max_le_max le_rfl (le_max_left _ _)
  have hK : ‖x.2.2‖ ≤ ‖x‖ := (norm_snd_le _).trans (norm_snd_le _)
  rw [← KSp.norm_eq]
  have := cV_nonneg d ℓ₀
  calc Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) (VresL d L j (x.1, x.2.1)) +
        ENNReal.ofReal ‖x.2.2‖ ≤ ENNReal.ofReal (4 * cV d ℓ₀ * ‖x‖) + ENNReal.ofReal ‖x‖ := by
        gcongr
        exact h1.trans (ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg ((x.1, x.2.1) : Vsp × ℂ)]))
    _ = ENNReal.ofReal (cX d ℓ₀ * ‖x‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
        congr 1; unfold cX; ring

/-- A family in `KSp` all of whose coefficients are continuous is continuous. -/
theorem KSp.continuous_of_coeff {P : Type*} [TopologicalSpace P] {j N : ℕ} {ℓ A : ℝ}
    [Fact (0 < ℓ)] [Fact (0 < A)] {g : P → KSp d L j N ℓ A}
    (hc : ∀ (X : Finset (Lam d L N)) (n : ℕ) (z : Fin n → Sf (Lam d L N)),
      Continuous (fun m => coeff ((g m).toAct X : Alg d L N) z)) : Continuous g := by
  obtain ⟨S, hS⟩ := LinearMap.exists_leftInverse_of_injective (KSp.coeffs (d := d) (L := L)
    (j := j) (N := N) (ℓ := ℓ) (A := A)) (LinearMap.ker_eq_bot.2 KSp.coeffs_injective)
  have hT : Continuous (fun m => KSp.coeffs (g m)) := continuous_pi fun q => hc q.1 q.2.1 q.2.2
  have e : g = fun m => S (KSp.coeffs (g m)) := funext fun m => (LinearMap.congr_fun hS (g m)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap S).continuous.comp hT

variable (ℓ₀ A) in
open Classical in
/-- **`K_{j+1}` as a function of the rescaled coordinates** on the torus `Λ_N` (restricted to
connected polymers). -/
def FN (m : ℝ) (j N : ℕ) (x : XS d L j N ℓ₀ A) : KS d L (j + 1) N ℓ₀ A :=
  if h : restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct) ∈
      KSub (j + 1) N then KSp.mk _ h else 0

variable (ℓ₀ A) in
/-- The linearisation `K ↦ D K_{j+1}|_0 (0, K)` (as the derivative of `t ↦ K_{j+1}(0, t K)`). -/
def DN (m : ℝ) (j N : ℕ) (K : KS d L j N ℓ₀ A) : KS d L (j + 1) N ℓ₀ A :=
  deriv (fun t : ℂ => FN ℓ₀ A m j N (0, 0, t • K)) 0

section
variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

theorem FN_toAct {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (x : XS d L j N ℓ₀ A) :
    (FN ℓ₀ A m j N x).toAct =
      restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct) := by
  rw [FN, dif_pos (restr_mem hj.le (InK_Knext H.hd1 H.hL8 hj (H.goodm hj m) _ x.2.2.inK))]
  rfl

open Classical in
theorem coeff_FN {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (x : XS d L j N ℓ₀ A)
    (X : Finset (Lam d L N)) {n : ℕ} (z : Fin n → Sf (Lam d L N)) :
    coeff ((FN ℓ₀ A m j N x).toAct X : Alg d L N) z = if IsConn (j + 1) X then
      coeff (Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct X : Alg d L N) z
      else 0 := by
  rw [FN_toAct H hj]
  by_cases hX : IsConn (j + 1) X
  · rw [restr_of_conn _ hX, if_pos hX]
  · rw [restr_of_not_conn _ hX, if_neg hX]; simp [coeff_zero]

theorem FN_line_differentiable {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (K : KS d L j N ℓ₀ A) :
    Differentiable ℂ (fun t : ℂ => FN ℓ₀ A m j N (0, 0, t • K)) := by
  have hC := H.goodm hj m
  intro t
  refine ((KSp.differentiableOn_of_coeff (U := Set.univ) fun X n z => ?_) t
    (Set.mem_univ t)).differentiableAt Filter.univ_mem
  simp only [coeff_FN H hj]
  split_ifs
  · have h := Knext_line_hol H.hd1 H.hL8 (by omega) hC.covInv hC.symm' 0 0 (InK.zero j) K.inK X
    have e : (fun t : ℂ => coeff (Knext j (Cm d L N m j) (VresL d L j (0, 0))
        (t • K).toAct X : Alg d L N) z) = fun t : ℂ =>
          coeff (Knext j (Cm d L N m j) (0 + t • 0) (0 + t • K.toAct) X : Alg d L N) z := by
      funext t; simp [Prod.mk_zero_zero, _root_.map_zero]
    rw [e]
    exact (h n z).differentiableOn
  · exact differentiableOn_const _

theorem hasDerivAt_FN_line {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (K : KS d L j N ℓ₀ A) :
    HasDerivAt (fun t : ℂ => FN ℓ₀ A m j N (0, 0, t • K)) (DN ℓ₀ A m j N K) 0 :=
  (FN_line_differentiable H hj m K 0).hasDerivAt

theorem DN_toAct {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (K : KS d L j N ℓ₀ A) :
    (DN ℓ₀ A m j N K).toAct = restr (j + 1) (DKnext j (Cm d L N m j) 0 0 0 K.toAct) := by
  have hC := H.goodm hj m
  funext X
  refine Subtype.ext (ext_coeff fun n z => ?_)
  have h1 := ((KFam.coeffKSp X z).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℂ)
    (hasDerivAt_FN_line H hj m K)).deriv
  simp only [LinearMap.coe_toContinuousLinearMap', Function.comp_def, coeffKSp_apply'] at h1
  rw [← h1]
  simp only [coeff_FN H hj]
  by_cases hX : IsConn (j + 1) X
  · simp only [if_pos hX, restr_of_conn _ hX]
    rw [coeff_DKnext H.hd1 H.hL8 (by omega) hC.covInv hC.symm' 0 0 (InK.zero j) K.inK X z]
    congr 1
    funext t
    simp [Prod.mk_zero_zero, _root_.map_zero]
  · simp only [if_neg hX, restr_of_not_conn _ hX, deriv_const]
    simp [coeff_zero]

theorem FN_zero {j N : ℕ} (hj : j + 1 < N) (m : ℝ) : FN (d := d) (L := L) ℓ₀ A m j N 0 = 0 := by
  refine norm_eq_zero.1 ?_
  rw [KSp.norm_def, FN_toAct H hj, Knorm_restr]
  simp only [Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero, _root_.map_zero]
  rw [H.zero N j hj _ (le_max_right m 0), ENNReal.toReal_zero]

/-- The radius `r = ε / (2 c_X)` on which the estimates of `thm:step` apply. -/
def rad (d : ℕ) (ℓ₀ ε : ℝ) : ℝ := ε / (2 * cX d ℓ₀)

theorem rad_pos : 0 < rad d ℓ₀ ε := by
  have := cX_pos d ℓ₀; have := H.hε; unfold rad; positivity

theorem xnorm_small {j N : ℕ} (hj : j ≤ N) {x : XS d L j N ℓ₀ A} (hx : ‖x‖ ≤ rad d ℓ₀ ε) :
    xnorm j (ellj d L ℓ₀ j) A (VresL d L j (x.1, x.2.1)) x.2.2.toAct ≤
      ENNReal.ofReal (ε / 2) := by
  refine (xnorm_XS_le (by have := H.hd; omega) hj x).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := cX_pos d ℓ₀
  calc cX d ℓ₀ * ‖x‖ ≤ cX d ℓ₀ * rad d ℓ₀ ε := mul_le_mul_of_nonneg_left hx h.le
    _ = ε / 2 := by unfold rad; field_simp

/-- **Lipschitz bound** for `FN` on the ball of radius `r`. -/
theorem FN_lip {j N : ℕ} (hj : j + 1 < N) (m : ℝ) {x x' : XS d L j N ℓ₀ A}
    (hx : ‖x‖ ≤ rad d ℓ₀ ε) (hx' : ‖x'‖ ≤ rad d ℓ₀ ε) :
    ‖FN ℓ₀ A m j N x - FN ℓ₀ A m j N x'‖ ≤ C₁ * cX d ℓ₀ * ‖x - x'‖ := by
  rw [KSp.norm_sub_eq,
    FN_toAct H hj, FN_toAct H hj]
  have e : Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U =>
      restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct) U -
      restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x'.1, x'.2.1)) x'.2.2.toAct) U) =
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U =>
        Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct U -
        Knext j (Cm d L N m j) (VresL d L j (x'.1, x'.2.1)) x'.2.2.toAct U) :=
    Knorm_congr fun X hX => by simp only [restr_of_conn _ hX]
  rw [e]
  have h := H.lip N j hj _ (le_max_right m 0) _ _ _ _ x.2.2.inK x'.2.2.inK
    (xnorm_small H (by omega) hx) (xnorm_small H (by omega) hx')
  rw [VresL_sub, toAct_sub'] at h
  refine ENNReal.toReal_le_of_le_ofReal (by have := cX_pos d ℓ₀; have := H.hC₁; positivity)
    (h.trans ?_)
  rw [mul_assoc, ENNReal.ofReal_mul H.hC₁]
  gcongr
  exact xnorm_XS_le (by have := H.hd; omega) (by omega) (x - x')

theorem DKnext_split {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (V' : Vcoup) {K' : Act d L N}
    (hK' : InK j K') {X : Finset (Lam d L N)} (hX : IsConn (j + 1) X) :
    DKnext j (Cm d L N m j) 0 0 V' K' X = DKnext j (Cm d L N m j) 0 0 0 K' X := by
  have hC := H.goodm hj m
  have hlin := DKnext_lin H.hd1 H.hL8 (by omega) hC.covInv hC.symm' 0 V' 0 (InK.zero j)
    (InK.zero j) hK' 1 1
  simp only [one_smul, add_zero, zero_add] at hlin
  rw [hlin, Pi.add_apply]
  have h0 := H.dV N j hj _ (le_max_right m 0) V'
  have h1 := wnorm_le_Knorm (j := j + 1) (ℓ := ellj d L ℓ₀ (j + 1)) (A := A)
    (K := DKnext j (Cm d L N m j) 0 0 V' 0) hX
  rw [h0, nonpos_iff_eq_zero, wnorm, mul_eq_zero, ENNReal.ofReal_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (not_le.2 (pow_pos (by linarith [H.hA]) _))
  · have hz : DKnext j (Cm d L N m j) 0 0 V' 0 X = 0 := Subtype.ext
      ((tNorm_eq_zero_iff (by have := H.hL0; positivity) (ellj_pos (Nat.cast_pos.2 (NeZero.pos L)) H.hℓ₀ _)).1 h1)
    rw [hz, zero_add]

/-- **The remainder bound** `‖g(x) - g(x')‖ ≤ γ max(‖x‖, ‖x'‖) ‖x - x'‖` for `FN - DN`. -/
theorem FN_rem {j N : ℕ} (hj : j + 1 < N) (m : ℝ) {x x' : XS d L j N ℓ₀ A}
    (hx : ‖x‖ ≤ rad d ℓ₀ ε) (hx' : ‖x'‖ ≤ rad d ℓ₀ ε) :
    ‖FN ℓ₀ A m j N x - FN ℓ₀ A m j N x' - DN ℓ₀ A m j N (x.2.2 - x'.2.2)‖ ≤
      C₁ * cX d ℓ₀ ^ 2 * max ‖x‖ ‖x'‖ * ‖x - x'‖ := by
  rw [KSp.norm_def (ℓ := ellj d L ℓ₀ (j + 1)) (A := A), _root_.map_sub, _root_.map_sub, FN_toAct H hj,
    FN_toAct H hj, DN_toAct H hj]
  have e : Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A
      (restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct) -
        restr (j + 1) (Knext j (Cm d L N m j) (VresL d L j (x'.1, x'.2.1)) x'.2.2.toAct) -
        restr (j + 1) (DKnext j (Cm d L N m j) 0 0 0 (x.2.2 - x'.2.2).toAct)) =
      Knorm (j + 1) (ellj d L ℓ₀ (j + 1)) A (fun U =>
        Knext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct U -
        Knext j (Cm d L N m j) (VresL d L j (x'.1, x'.2.1)) x'.2.2.toAct U -
        DKnext j (Cm d L N m j) 0 0 (VresL d L j (x.1, x.2.1) - VresL d L j (x'.1, x'.2.1))
          (x.2.2.toAct - x'.2.2.toAct) U) := by
    refine Knorm_congr fun X hX => ?_
    simp only [Pi.sub_apply, restr_of_conn _ hX]
    rw [DKnext_split H hj m _ (x.2.2.inK.sub x'.2.2.inK) hX,
      toAct_sub' (ℓ := ellj d L ℓ₀ j) (A := A)]
  rw [e]
  have h := H.rem N j hj _ (le_max_right m 0) _ _ _ _ x.2.2.inK x'.2.2.inK
    (xnorm_small H (by omega) hx) (xnorm_small H (by omega) hx')
  refine ENNReal.toReal_le_of_le_ofReal (by have := cX_pos d ℓ₀; have := H.hC₁; positivity)
    (h.trans ?_)
  rw [VresL_sub, toAct_sub']
  have h1 := xnorm_XS_le (by have := H.hd; omega) (by omega : j ≤ N) x
  have h2 := xnorm_XS_le (by have := H.hd; omega) (by omega : j ≤ N) x'
  have h3 := xnorm_XS_le (by have := H.hd; omega) (by omega : j ≤ N) (x - x')
  have hc := (cX_pos d ℓ₀).le
  calc ENNReal.ofReal C₁ * max (xnorm j (ellj d L ℓ₀ j) A (VresL d L j (x.1, x.2.1)) x.2.2.toAct)
        (xnorm j (ellj d L ℓ₀ j) A (VresL d L j (x'.1, x'.2.1)) x'.2.2.toAct) *
        xnorm j (ellj d L ℓ₀ j) A (VresL d L j ((x - x').1, (x - x').2.1)) (x - x').2.2.toAct
      ≤ ENNReal.ofReal C₁ * max (ENNReal.ofReal (cX d ℓ₀ * ‖x‖))
          (ENNReal.ofReal (cX d ℓ₀ * ‖x'‖)) * ENNReal.ofReal (cX d ℓ₀ * ‖x - x'‖) := by
        gcongr
    _ = ENNReal.ofReal (C₁ * cX d ℓ₀ ^ 2 * max ‖x‖ ‖x'‖ * ‖x - x'‖) := by
        rw [← ENNReal.ofReal_max, ← ENNReal.ofReal_mul H.hC₁,
          ← ENNReal.ofReal_mul (mul_nonneg H.hC₁ (le_max_of_le_left (mul_nonneg hc (norm_nonneg _)))),
          ← mul_max_of_nonneg _ _ hc]
        congr 1; ring

/-- **Holomorphy of `FN`**: holomorphic curves are mapped to holomorphic curves. -/
theorem FN_differentiableOn {j N : ℕ} (hj : j + 1 < N) (m : ℝ) {U : Set ℂ}
    {c : ℂ → XS d L j N ℓ₀ A} (hc : DifferentiableOn ℂ c U) :
    DifferentiableOn ℂ (fun t => FN ℓ₀ A m j N (c t)) U := by
  refine KSp.differentiableOn_of_coeff fun X n z => ?_
  simp only [coeff_FN H hj]
  split_ifs
  · have hC := H.goodm hj m
    have hW : HolV (fun e : XS d L j N ℓ₀ A => VresL d L j (e.1, e.2.1)) :=
      ⟨by simp only [VresL_z]; fun_prop, by simp only [VresL_y]; fun_prop,
        by simp only [VresL_a]; fun_prop, by simp only [VresL_b]; fun_prop⟩
    have hK : HolK (fun e : XS d L j N ℓ₀ A => e.2.2.toAct) := fun X n z => by
      show Differentiable ℂ fun e : XS d L j N ℓ₀ A =>
        (KFam.coeffKSp X z).toContinuousLinearMap e.2.2
      fun_prop
    exact (Knext_hol H.hd1 H.hL8 (by omega) hC.covInv hC.symm' hW hK (fun e => e.2.2.inK) X n
      z).comp_differentiableOn hc
  · exact differentiableOn_const _

/-- Continuity of `FN` in the mass parameter, for fixed `x`. -/
theorem FN_continuous_m {j N : ℕ} (hj : j + 1 < N) (x : XS d L j N ℓ₀ A) :
    Continuous (fun m : ℝ => FN ℓ₀ A m j N x) := by
  refine KSp.continuous_of_coeff fun X n z => ?_
  simp only [coeff_FN H hj]
  split_ifs
  · exact (Knext_continuousOn_msq H.hd H.hL8 hj _ x.2.2.inK X z).comp_continuous
      (continuous_id.max continuous_const) (fun m => le_max_right m 0)
  · exact continuous_const

/-- Joint continuity of `FN` in the mass parameter and `x` (on the ball of radius `r`). -/
theorem FN_continuous {P : Type*} [TopologicalSpace P] {j N : ℕ} (hj : j + 1 < N)
    {μ : P → ℝ} (hμ : Continuous μ) {x : P → XS d L j N ℓ₀ A} (hx : Continuous x)
    (hxr : ∀ p, ‖x p‖ ≤ rad d ℓ₀ ε) :
    Continuous (fun p => FN ℓ₀ A (μ p) j N (x p)) := by
  have h := continuous_apply_of_lipschitz (fun p y => FN ℓ₀ A (μ p) j N y)
    (closedBall 0 (rad d ℓ₀ ε)) (C₁ * cX d ℓ₀)
    (fun p y hy y' hy' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact FN_lip H hj _ (mem_closedBall_zero_iff.1 hy) (mem_closedBall_zero_iff.1 hy'))
    (fun y _ => (FN_continuous_m H hj y).comp hμ) hx
    (fun p => mem_closedBall_zero_iff.2 (hxr p))
  exact h

theorem DN_add_smul {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (a b : ℂ) (K K' : KS d L j N ℓ₀ A) :
    DN ℓ₀ A m j N (a • K + b • K') = a • DN ℓ₀ A m j N K + b • DN ℓ₀ A m j N K' := by
  have hC := H.goodm hj m
  refine KSp.toAct_injective ?_
  rw [_root_.map_add, _root_.map_smul, _root_.map_smul, DN_toAct H hj, DN_toAct H hj,
    DN_toAct H hj, _root_.map_add, _root_.map_smul, _root_.map_smul, ← restr_smul, ← restr_smul,
    ← restr_add]
  congr 1
  have := DKnext_lin H.hd1 H.hL8 (by omega) hC.covInv hC.symm' 0 0 0 (InK.zero j) K.inK K'.inK a b
  simpa using this

variable (ℓ₀ A) in
/-- `DN` as a linear map. -/
def DNL {j N : ℕ} (hj : j + 1 < N) (m : ℝ) : KS d L j N ℓ₀ A →ₗ[ℂ] KS d L (j + 1) N ℓ₀ A where
  toFun := DN ℓ₀ A m j N
  map_add' K K' := by simpa using DN_add_smul H hj m 1 1 K K'
  map_smul' c K := by simpa using DN_add_smul H hj m c 0 K 0

theorem DN_norm_le {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (K : KS d L j N ℓ₀ A) :
    ‖DN ℓ₀ A m j N K‖ ≤ δK * ‖K‖ := by
  rw [KSp.norm_def, DN_toAct H hj, Knorm_restr, KSp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal (by have := H.hδK; positivity)
    ((H.dK N j hj _ (le_max_right m 0) 0 K.toAct K.inK).trans (le_of_eq ?_))
  rw [ENNReal.ofReal_mul H.hδK, ENNReal.ofReal_toReal (Knorm_ne_top Fact.out _)]

theorem norm_XS_K {j N : ℕ} (K : KS d L j N ℓ₀ A) : ‖((0, 0, K) : XS d L j N ℓ₀ A)‖ = ‖K‖ := by
  simp [Prod.norm_def]

/-- Continuity of `DN` in the mass parameter, as a uniform limit of difference quotients. -/
theorem DN_continuous_m {j N : ℕ} (hj : j + 1 < N) (K : KS d L j N ℓ₀ A) :
    Continuous (fun m : ℝ => DN ℓ₀ A m j N K) := by
  have hr := rad_pos H
  set s : ℝ := rad d ℓ₀ ε / (‖K‖ + 1) with hs
  have hs0 : 0 < s := by positivity
  have hsK : s * ‖K‖ ≤ rad d ℓ₀ ε := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg K]
  set t : ℕ → ℂ := fun n => ((s / (n + 1) : ℝ) : ℂ) with ht
  have htn : ∀ n, ‖t n‖ = s / (n + 1) := fun n => by
    rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have htpos : ∀ n, t n ≠ 0 := fun n => by
    rw [← norm_ne_zero_iff, htn]; positivity
  have htr : ∀ n, ‖t n‖ * ‖K‖ ≤ rad d ℓ₀ ε := fun n => by
    rw [htn]
    refine le_trans ?_ hsK
    gcongr
    calc s / (n + 1) ≤ s / 1 := by gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      _ = s := div_one s
  set c := C₁ * cX d ℓ₀ ^ 2 * ‖K‖ ^ 2
  have hc : 0 ≤ c := by have := H.hC₁; positivity
  have key : ∀ n (m : ℝ), dist ((t n)⁻¹ • FN ℓ₀ A m j N (0, 0, t n • K)) (DN ℓ₀ A m j N K) ≤
      c * (s / (n + 1)) := by
    intro n m
    have hx : ‖((0, 0, t n • K) : XS d L j N ℓ₀ A)‖ ≤ rad d ℓ₀ ε := by
      rw [norm_XS_K H, norm_smul]; exact htr n
    have h := FN_rem H hj m (x' := (0 : XS d L j N ℓ₀ A)) hx (by rw [norm_zero]; exact hr.le)
    simp only [Prod.snd_zero, sub_zero, FN_zero H hj, norm_zero, max_eq_left (norm_nonneg _),
      norm_XS_K H] at h
    rw [show DN ℓ₀ A m j N (t n • K) = t n • DN ℓ₀ A m j N K by
        simpa using DN_add_smul H hj m (t n) 0 K 0] at h
    rw [dist_eq_norm]
    have e : (t n)⁻¹ • FN ℓ₀ A m j N (0, 0, t n • K) - DN ℓ₀ A m j N K =
        (t n)⁻¹ • (FN ℓ₀ A m j N (0, 0, t n • K) - t n • DN ℓ₀ A m j N K) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (htpos n), one_smul]
    rw [e, norm_smul, norm_inv, htn]
    rw [norm_smul, htn] at h
    have hsn : 0 < s / (n + 1) := by positivity
    rw [inv_mul_le_iff₀ hsn]
    calc ‖FN ℓ₀ A m j N (0, 0, t n • K) - t n • DN ℓ₀ A m j N K‖ ≤
        C₁ * cX d ℓ₀ ^ 2 * (s / (n + 1) * ‖K‖) * (s / (n + 1) * ‖K‖) := h
      _ = s / (n + 1) * (c * (s / (n + 1))) := by simp only [c]; ring
  have hu : Tendsto (fun n : ℕ => c * (s / (n + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (c * s)
    simpa [mul_div_assoc, div_eq_mul_inv, mul_assoc] using this
  refine (tendstoUniformlyOn_univ.1 (tendstoUniformlyOn_of_dist_le hu
    (fun n m _ => key n m))).continuous (Frequently.of_forall fun n => ?_)
  exact (FN_continuous_m H hj _).const_smul _

/-! ### Compatibility -/

theorem sixteen_pow_le {j N : ℕ} (hj : j + 3 ≤ N) : 16 * L ^ (j + 1) ≤ L ^ N := by
  have h16 := H.hL16
  calc 16 * L ^ (j + 1) ≤ L ^ 2 * L ^ (j + 1) := Nat.mul_le_mul_right _ (by nlinarith)
    _ = L ^ (j + 3) := by ring
    _ ≤ L ^ N := Nat.pow_le_pow_right (by omega) hj

theorem restr_compat {j N M D : ℕ} (hjN : j + 3 ≤ N) (hNM : N ≤ M) {K : Act d L N}
    {K' : Act d L M} (hc : Compat (j + 1) D K K') :
    Compat (j + 1) D (restr (j + 1) K) (restr (j + 1) K') := by
  intro X hX hcen hdiam
  have hX16 : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N := fun x hx => by
    have := hcen x hx; omega
  have hXc := (isConn_image_iff (N := N) (M := M) hNM (by omega : j + 1 ≤ N)
    (sixteen_pow_le H hjN) hX16).2 hX
  rw [restr_of_conn _ hX, restr_of_conn _ hXc]
  exact hc X hX hcen hdiam

/-- The next activities of compatible activities are compatible. -/
theorem FN_compat {j N M : ℕ} (hjN : j + 3 ≤ N) (hNM : N ≤ M) (m : ℝ) (v : Vsp) (bh : ℂ)
    (K : KS d L j N ℓ₀ A) (K' : KS d L j M ℓ₀ A)
    (hc : Compat j (Dc d L N j) K.toAct K'.toAct) :
    Compat (j + 1) (Dc d L N (j + 1)) (FN ℓ₀ A m j N (v, bh, K)).toAct
      (FN ℓ₀ A m j M (v, bh, K')).toAct := by
  rw [FN_toAct H (by omega), FN_toAct H (by omega)]
  exact restr_compat H hjN hNM (Knext_compat H.hd H.hL8 hNM hjN (le_max_right m 0) _ K.inK K'.inK hc)

theorem DN_compat {j N M : ℕ} (hjN : j + 3 ≤ N) (hNM : N ≤ M) (m : ℝ)
    (K : KS d L j N ℓ₀ A) (K' : KS d L j M ℓ₀ A)
    (hc : Compat j (Dc d L N j) K.toAct K'.toAct) :
    Compat (j + 1) (Dc d L N (j + 1)) (DN ℓ₀ A m j N K).toAct (DN ℓ₀ A m j M K').toAct := by
  set q : ℂ → KS d L (j + 1) N ℓ₀ A × KS d L (j + 1) M ℓ₀ A :=
    fun t => (FN ℓ₀ A m j N (0, 0, t • K), FN ℓ₀ A m j M (0, 0, t • K'))
  have hq : ∀ t, q t ∈ CompatSub (j + 1) (Dc d L N (j + 1)) N M (ellj d L ℓ₀ (j + 1)) A := by
    intro t
    have hc' : ((t • K, t • K') : KS d L j N ℓ₀ A × KS d L j M ℓ₀ A) ∈
        CompatSub j (Dc d L N j) N M (ellj d L ℓ₀ j) A := by
      have := (CompatSub (d := d) (L := L) j (Dc d L N j) N M (ellj d L ℓ₀ j) A).smul_mem t
        (show ((K, K') : KS d L j N ℓ₀ A × KS d L j M ℓ₀ A) ∈ _ from hc)
      simpa using this
    exact FN_compat H hjN hNM m 0 0 (t • K) (t • K') hc'
  have hd := deriv_mem_of_isClosed (isClosed_compatSub _ _ _) hq 0
  have hD : deriv q 0 = (DN ℓ₀ A m j N K, DN ℓ₀ A m j M K') :=
    ((hasDerivAt_FN_line H (by omega) m K).prodMk (hasDerivAt_FN_line H (by omega) m K')).deriv
  rw [hD] at hd
  exact hd

end

/-! ### The coupling constants: `E` and `B_j` -/

variable (L) in
/-- The rescaled coordinates `(z, y, L^{2j} a)` of `V` at scale `j`, as a linear map. -/
def vresL (j : ℕ) : Vcoup →ₗ[ℂ] Vsp where
  toFun V := (V.z, V.y, (L : ℂ) ^ (2 * j) * V.a)
  map_add' V W := by simp [mul_add]
  map_smul' c V := by simp; ring

@[simp] theorem vresL_apply (j : ℕ) (V : Vcoup) :
    vresL L j V = (V.z, V.y, (L : ℂ) ^ (2 * j) * V.a) := rfl

variable (L) in
/-- `E(ẑ, ŷ, â) = (ẑ, ŷ, L² â)`. -/
def Emap : Vsp →ₗ[ℂ] Vsp where
  toFun v := (v.1, v.2.1, (L : ℂ) ^ 2 * v.2.2)
  map_add' v w := by simp [mul_add]
  map_smul' c v := by simp; ring

@[simp] theorem Emap_apply (v : Vsp) : Emap L v = (v.1, v.2.1, (L : ℂ) ^ 2 * v.2.2) := rfl

theorem rpow_neg_nat {x : ℝ} (hx : 0 < x) (n : ℕ) {r : ℝ} (hr : r = n) :
    x ^ (-r) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx.le, hr, Real.rpow_natCast]

@[simp] theorem Vcoup_neg_z (V : Vcoup) : (-V).z = -V.z := rfl
@[simp] theorem Vcoup_neg_y (V : Vcoup) : (-V).y = -V.y := rfl
@[simp] theorem Vcoup_neg_a (V : Vcoup) : (-V).a = -V.a := rfl
@[simp] theorem Vcoup_neg_b (V : Vcoup) : (-V).b = -V.b := rfl

variable (ℓ₀ A) in
/-- The map `(b̂, K) ↦ v_{j+1} - E v` (`B_j` of `e:flowblock`) on the torus `Λ_N`. -/
def BNf (m : ℝ) (j N : ℕ) (p : ℂ × KS d L j N ℓ₀ A) : Vsp :=
  vresL L (j + 1) (uVnext j (Cm d L N m j) (VresL d L j (0, p.1)) p.2.toAct).2

section
variable (H : Hyp d L A ℓ₀ ε C₁ δK Kc Cw)
include H

theorem uVnext_add {j N : ℕ} (hj : j < N) (m : ℝ) (V W : Vcoup) {K K' : Act d L N}
    (hK : InK j K) (hK' : InK j K') :
    uVnext j (Cm d L N m j) (V + W) (K + K') =
      uVnext j (Cm d L N m j) V K + uVnext j (Cm d L N m j) W K' := by
  simpa using uVnext_lin H.hd1 H.hL8 hj (hinv_frd j _ (le_max_right m 0))
    (hsym_frd (d := d) j _ (le_max_right m 0)) V W hK hK' 1 1

theorem BNf_add_smul {j N : ℕ} (hj : j < N) (m : ℝ) (a b : ℂ) (p q : ℂ × KS d L j N ℓ₀ A) :
    BNf ℓ₀ A m j N (a • p + b • q) = a • BNf ℓ₀ A m j N p + b • BNf ℓ₀ A m j N q := by
  have e1 : ((0 : Vsp), (a • p + b • q).1) = a • ((0 : Vsp), p.1) + b • ((0 : Vsp), q.1) := by
    ext <;> simp
  have h := uVnext_lin H.hd1 H.hL8 hj (hinv_frd j _ (le_max_right m 0))
    (hsym_frd (d := d) j _ (le_max_right m 0)) (VresL d L j (0, p.1)) (VresL d L j (0, q.1))
    p.2.inK q.2.inK a b
  unfold BNf
  rw [e1, _root_.map_add, _root_.map_smul, _root_.map_smul, Prod.snd_add, Prod.smul_snd,
    Prod.smul_snd, _root_.map_add, _root_.map_smul, _root_.map_smul]
  erw [h]
  rw [Prod.snd_add, Prod.smul_snd, Prod.smul_snd, _root_.map_add, _root_.map_smul,
    _root_.map_smul]

variable (ℓ₀ A) in
/-- `B_j` on the torus `Λ_N`, as a linear map. -/
def BNL {j N : ℕ} (hj : j < N) (m : ℝ) : (ℂ × KS d L j N ℓ₀ A) →ₗ[ℂ] Vsp where
  toFun := BNf ℓ₀ A m j N
  map_add' p q := by simpa using BNf_add_smul H hj m 1 1 p q
  map_smul' c p := by simpa using BNf_add_smul H hj m c 0 p 0

/-- The explicit form of `V_{j+1}` for `V_j = (0, 0, 0, b)`: the Wick contribution
`W(V_j)` of `eq:tildeflow` and the contribution `-W_Q(K)` of `Loc`. -/
theorem uVnext_bK {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (i₀ : Fin d) (V : Vcoup)
    (K : Act d L N) (hK : InK j K) :
    (uVnext j (Cm d L N m j) V K).2 =
      Vlin 1 1 V (Wf d (Cm d L N m j 0 0 : ℂ) (Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ) V) +
        -WQ i₀ j K := by
  have hC := H.goodm hj m
  have h := uVnext_add H (by omega : j < N) m V 0 (InK.zero j) hK
  rw [add_zero, zero_add] at h
  rw [h, Prod.snd_add, uVnext_V H.hd1 H.hL8 (by omega) hC.covInv hC.symm' (Sum.inl i₀),
    uVnext_K H.hd1 H.hL8 hj hC.covInv hC.symm' hK i₀]

variable (d L) in
/-- The bound `β` on `‖B_j‖`. -/
def βB (ℓ₀ Kc Cw : ℝ) : ℝ := (L : ℝ) ^ 2 * ((2 * d + 1) * Kc + Cw / ℓ₀ ^ 2)

theorem BNf_norm_le {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (p : ℂ × KS d L j N ℓ₀ A) :
    ‖BNf ℓ₀ A m j N p‖ ≤ βB d L ℓ₀ Kc Cw * ‖p‖ := by
  have i₀ : Fin d := ⟨0, by have := H.hd; omega⟩
  have hL0 := H.hL0
  have hL1 := H.hL1
  have hKc := H.hKc
  have hCw := H.hCw
  have hℓ₀ := H.hℓ₀
  obtain ⟨hc0, hc1⟩ := H.cov N j (by omega) (max m 0) (le_max_right m 0)
  obtain ⟨hwz, hwy, hwa⟩ := H.wq N j hj p.2.toAct p.2.inK i₀
  rw [← KSp.norm_def] at hwz hwy hwa
  have hk0 : 0 ≤ ‖p.2‖ := norm_nonneg _
  have hbhp : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have hkp : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hc1' := hc1 (Sum.inl i₀)
  set P := (L : ℝ) ^ ((d - 2) * j) with hP
  set Q := (L : ℝ) ^ j with hQ
  have hP0 : 0 < P := by positivity
  have hQ1 : 1 ≤ Q := one_le_pow₀ hL1
  have hPQ : (L : ℝ) ^ (d * j) = P * Q ^ 2 := by
    rw [mul_comm d j, pow_jd (by have := H.hd; omega) j]
  rw [rpow_neg_nat hL0 ((d - 2) * j)
    (by push_cast [Nat.cast_sub (by have := H.hd; omega : 2 ≤ d)]; ring)] at hc0
  rw [rpow_neg_nat hL0 (d * j) (by push_cast; ring), hPQ] at hc1'
  -- the three components
  have ez : (BNf ℓ₀ A m j N p).1 = (L : ℂ) ^ ((d - 2) * j) * p.1 *
      ((Cm d L N m j 0 0 : ℂ) - (Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ)) -
      (WQ i₀ j p.2.toAct).z := by
    simp [BNf, uVnext_bK H hj m i₀ _ _ p.2.inK, Vlin, Wf]; ring
  have ey : (BNf ℓ₀ A m j N p).2.1 = -((L : ℂ) ^ ((d - 2) * j) * p.1 * (Cm d L N m j 0 0 : ℂ)) -
      (WQ i₀ j p.2.toAct).y := by
    simp [BNf, uVnext_bK H hj m i₀ _ _ p.2.inK, Vlin, Wf]; ring
  have ea : (BNf ℓ₀ A m j N p).2.2 = (L : ℂ) ^ 2 * ((L : ℂ) ^ (2 * j) *
      ((L : ℂ) ^ ((d - 2) * j) * p.1 * (2 * d * ((Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ) -
        (Cm d L N m j 0 0 : ℂ))))) -
      (L : ℂ) ^ 2 * ((L : ℂ) ^ (2 * j) * (WQ i₀ j p.2.toAct).a) := by
    simp [BNf, uVnext_bK H hj m i₀ _ _ p.2.inK, Vlin, Wf]; ring
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
  have hdiff : ‖((Cm d L N m j 0 0 : ℂ) - (Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ))‖ ≤
      Kc * (P * Q ^ 2)⁻¹ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hc1'
  have hdiff' : ‖((Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ) - (Cm d L N m j 0 0 : ℂ))‖ ≤
      Kc * (P * Q ^ 2)⁻¹ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hc1'
  have hc0' : ‖(Cm d L N m j 0 0 : ℂ)‖ ≤ Kc * P⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hc0
  have hnP : ‖(L : ℂ) ^ ((d - 2) * j)‖ = P := by rw [norm_Lpow]
  have hnQ : ‖(L : ℂ) ^ (2 * j)‖ = Q ^ 2 := by rw [norm_Lpow, pow_mul']
  have hn2 : ‖(L : ℂ) ^ 2‖ = (L : ℝ) ^ 2 := norm_Lpow 2
  have hQ2 : (Q ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hQ1)
  have hPP : P * (P * Q ^ 2)⁻¹ = (Q ^ 2)⁻¹ := by field_simp
  have hβ : ∀ a b : ℝ, a ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ →
      b ≤ (L : ℝ) ^ 2 * (Cw / ℓ₀ ^ 2) * ‖p.2‖ → a + b ≤ βB d L ℓ₀ Kc Cw * ‖p‖ := by
    intro a b ha hb
    unfold βB
    have h1 : 0 ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) := by positivity
    have h2 : 0 ≤ (L : ℝ) ^ 2 * (Cw / ℓ₀ ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbhp h1, mul_le_mul_of_nonneg_left hkp h2]
  have hb1 : 0 ≤ ‖p.1‖ := norm_nonneg _
  have hcw : 0 ≤ Cw / ℓ₀ ^ 2 * ‖p.2‖ := by positivity
  have hcw2 : Cw / ℓ₀ ^ 2 * ‖p.2‖ ≤ (L : ℝ) ^ 2 * (Cw / ℓ₀ ^ 2) * ‖p.2‖ := by
    have := mul_le_mul_of_nonneg_right hL2 hcw
    linarith [show (L : ℝ) ^ 2 * (Cw / ℓ₀ ^ 2) * ‖p.2‖ = (L : ℝ) ^ 2 * (Cw / ℓ₀ ^ 2 * ‖p.2‖)
      by ring]
  have hK1 : Kc * ‖p.1‖ ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ := by
    have h1 : 1 ≤ (L : ℝ) ^ 2 * (2 * d + 1) := by
      have := mul_nonneg hd0 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)
      linarith [show (L : ℝ) ^ 2 * (2 * d + 1) = (L : ℝ) ^ 2 + 2 * (d * (L : ℝ) ^ 2) by ring]
    have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hKc hb1)
    linarith [show (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ =
      (L : ℝ) ^ 2 * (2 * d + 1) * (Kc * ‖p.1‖) by ring]
  have hK2 : (L : ℝ) ^ 2 * (2 * d * Kc) * ‖p.1‖ ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ := by
    have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2) hKc) hb1
    linarith [show (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ =
      (L : ℝ) ^ 2 * (2 * d * Kc) * ‖p.1‖ + (L : ℝ) ^ 2 * Kc * ‖p.1‖ by ring]
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le ?_ (max_le ?_ ?_)
  · rw [ez]
    refine (norm_sub_le _ _).trans (hβ _ _ ?_ ?_)
    · rw [norm_mul, norm_mul, hnP]
      calc P * ‖p.1‖ * ‖((Cm d L N m j 0 0 : ℂ) - (Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ))‖
          ≤ P * ‖p.1‖ * (Kc * (P * Q ^ 2)⁻¹) := by gcongr
        _ = Kc * (Q ^ 2)⁻¹ * ‖p.1‖ := by rw [← hPP]; ring
        _ ≤ Kc * 1 * ‖p.1‖ := by gcongr
        _ ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ := by rw [mul_one]; exact hK1
    · exact hwz.trans hcw2
  · rw [ey]
    refine (norm_sub_le _ _).trans (hβ _ _ ?_ ?_)
    · rw [norm_neg, norm_mul, norm_mul, hnP]
      calc P * ‖p.1‖ * ‖(Cm d L N m j 0 0 : ℂ)‖ ≤ P * ‖p.1‖ * (Kc * P⁻¹) := by gcongr
        _ = Kc * ‖p.1‖ := by field_simp
        _ ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ := hK1
    · exact hwy.trans hcw2
  · rw [ea]
    refine (norm_sub_le _ _).trans (hβ _ _ ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hnP, hnQ, hn2,
        RCLike.norm_ofNat, Complex.norm_natCast]
      calc (L : ℝ) ^ 2 * (Q ^ 2 * (P * ‖p.1‖ * (2 * d *
            ‖((Cm d L N m j 0 (dirVec (Sum.inl i₀)) : ℂ) - (Cm d L N m j 0 0 : ℂ))‖)))
          ≤ (L : ℝ) ^ 2 * (Q ^ 2 * (P * ‖p.1‖ * (2 * d * (Kc * (P * Q ^ 2)⁻¹)))) := by gcongr
        _ = (L : ℝ) ^ 2 * (2 * d * Kc) * ‖p.1‖ := by field_simp
        _ ≤ (L : ℝ) ^ 2 * ((2 * d + 1) * Kc) * ‖p.1‖ := hK2
    · rw [norm_mul, norm_mul, hn2, hnQ]
      have hwa' : Q ^ 2 * ‖(WQ i₀ j p.2.toAct).a‖ ≤ Cw / ℓ₀ ^ 2 * ‖p.2‖ := by
        rw [hQ, ← pow_mul, mul_comm j 2]; exact hwa
      calc (L : ℝ) ^ 2 * (Q ^ 2 * ‖(WQ i₀ j p.2.toAct).a‖) ≤
          (L : ℝ) ^ 2 * (Cw / ℓ₀ ^ 2 * ‖p.2‖) :=
            mul_le_mul_of_nonneg_left hwa' (by positivity)
        _ = _ := by ring

theorem BNf_continuous_m {j N : ℕ} (hj : j + 1 < N) (p : ℂ × KS d L j N ℓ₀ A) :
    Continuous (fun m : ℝ => BNf ℓ₀ A m j N p) := by
  obtain ⟨-, hz, hy, ha, -⟩ := uVnext_continuousOn_msq H.hd H.hL8 hj (VresL d L j (0, p.1)) p.2.inK
  have c : ∀ {f : ℝ → ℂ}, ContinuousOn f (Set.Ici 0) → Continuous (fun m => f (max m 0)) :=
    fun h => h.comp_continuous (continuous_id.max continuous_const) (fun m => le_max_right m 0)
  unfold BNf
  simp only [vresL_apply]
  exact (c hz).prodMk ((c hy).prodMk (continuous_const.mul (c ha)))

/-- `B_j` does not depend on the torus (for compatible activities). -/
theorem BNf_compat {j N M : ℕ} (hjN : j + 3 ≤ N) (hNM : N ≤ M) (m : ℝ) (bh : ℂ)
    (K : KS d L j N ℓ₀ A) (K' : KS d L j M ℓ₀ A)
    (hc : Compat j (Dc d L N j) K.toAct K'.toAct) :
    BNf ℓ₀ A m j N (bh, K) = BNf ℓ₀ A m j M (bh, K') := by
  unfold BNf
  rw [uVnext_compat H.hd H.hL8 hNM hjN (le_max_right m 0) _ K.inK K'.inK hc]

/-- **`e:flowblock`, first row**: `v_{j+1} = E v_j + B_j w_j`. -/
theorem uVnext_step {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (x : XS d L j N ℓ₀ A) :
    vresL L (j + 1) (uVnext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct).2 =
      Emap L x.1 + BNf ℓ₀ A m j N (x.2.1, x.2.2) := by
  have hC := H.goodm hj m
  have e1 : VresL d L j (x.1, x.2.1) = VresL d L j (x.1, 0) + VresL d L j (0, x.2.1) := by
    rw [← _root_.map_add]; simp
  have h := uVnext_add H (by omega : j < N) m (VresL d L j (x.1, 0)) (VresL d L j (0, x.2.1))
    (InK.zero j) x.2.2.inK
  rw [zero_add] at h
  have hV0 := uVnext_V H.hd1 H.hL8 (j := j) (by omega) hC.covInv hC.symm' (Sum.inl ⟨0, by
    have := H.hd; omega⟩) (VresL d L j (x.1, 0))
  rw [Wf_b_zero _ _ (by simp)] at hV0
  have hV : Vlin 1 1 (VresL d L j (x.1, 0)) 0 = VresL d L j (x.1, 0) :=
    Vcoup.ext' (by simp [Vlin]) (by simp [Vlin]) (by simp [Vlin]) (by simp [Vlin])
  rw [e1, h, Prod.snd_add, hV0, hV, _root_.map_add]
  congr 1
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  simp only [vresL_apply, VresL_z, VresL_y, VresL_a, Emap_apply]
  congr 2
  field_simp
  ring

theorem uVnext_step_b {j N : ℕ} (hj : j + 1 < N) (m : ℝ) (x : XS d L j N ℓ₀ A) :
    (uVnext j (Cm d L N m j) (VresL d L j (x.1, x.2.1)) x.2.2.toAct).2.b =
      (L : ℂ) ^ ((d - 2) * (j + 1)) * (((L : ℂ) ^ (d - 2))⁻¹ * x.2.1) := by
  rw [uVnext_bK H hj m ⟨0, by have := H.hd; omega⟩ _ _ x.2.2.inK]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  simp only [Vcoup.add_b, Vlin, Wf, Vcoup_neg_b, WQ, VresL_b, neg_zero, add_zero, one_mul, mul_zero]
  rw [mul_add, pow_add, mul_one]
  field_simp

theorem VresL_vresL (j : ℕ) (V : Vcoup) (bh : ℂ) (hb : V.b = (L : ℂ) ^ ((d - 2) * j) * bh) :
    VresL d L j (vresL L j V, bh) = V := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  refine Vcoup.ext' (by simp) (by simp) ?_ (by simp [hb])
  simp only [VresL_a, vresL_apply]
  field_simp

end

end

end Flow
