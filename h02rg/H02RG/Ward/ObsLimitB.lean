import Ward.ObsLimitA

/-!
# Infinite-volume observable couplings, part B: bounds

From `Obs.Vobs_recursion_two` and the bound on `K^obs_j` of `FlowData.obs` (at the pair
`(ctr_N, b)`, `b ≠ ctr_N`), with `θ = L^{-κ}`, `E = C λ̄ |b₀|` and `ρ = L^{-(d-2)}`:

* `StepBd`: `|λ_{k+1} - λ_k| ≤ C_S E θ^k` (both slots) and
  `|γ-step_k - λ_{k+1} C_{k+1}(x,x)| ≤ C_S ℓ_k^2 E θ^k` (`exists_stepBd`);
* along the flow on `Λ_N`: `|λ_k| ≤ Λm := λ̄ + C_S E/(1-θ)` (`la_N_bd`, `lb_N_bd`) and
  `|γ-step_k| ≤ (Λm + C_S E) ℓ₀^2 ρ^k` (`ga_N_bd`, `gb_N_bd`);
* for the `N`-independent sequences of part A: `lA_succ`, `lB_succ` (increments),
  `gA_bd`, `gB_bd`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- `θ = L^{-κ}`. -/
abbrev th (L : ℕ) (κ : ℝ) : ℝ := (L : ℝ) ^ (-κ)

/-- `ρ = L^{-(d-2)}`. -/
abbrev rho (d L : ℕ) : ℝ := (L : ℝ) ^ (-((d : ℝ) - 2))

theorem th_nonneg (L : ℕ) (κ : ℝ) : 0 ≤ th L κ := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem th_lt_one (hL : 2 ≤ L) (hκ : 0 < κ) : th L κ < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)

theorem rho_nonneg (d L : ℕ) : 0 ≤ rho d L := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem rho_lt_one (hd : 3 ≤ d) (hL : 2 ≤ L) : rho d L < 1 := by
  have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < L)) (by linarith)

theorem rho_le_one (hd : 2 ≤ d) (L : ℕ) [NeZero L] : rho d L ≤ 1 := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast NeZero.one_le) (by linarith)

theorem norm_lbar (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) : ‖(lbar : ℂ)‖ = lbar := by
  rw [Complex.norm_real, Real.norm_of_nonneg H.fd.lbar_pos.le]

theorem three_le_L (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) : 3 ≤ L := by
  have : 2 ^ 2 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := H.fd.hL8; omega

variable (d L) in
/-- The flow of part A on `Λ_N` at the pair `(a, b)`. -/
abbrev FO (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (N : ℕ) (a b : Lam d L N) (j : ℕ) :
    Coup .two × (Finset (Lam d L N) → OE .two (Lam d L N)) :=
  flowO d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) a b j

variable (d L) in
/-- The step data `(u + V)^obs_{j+1}` of `FO`. -/
abbrev NA (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (N : ℕ) (a b : Lam d L N) (j : ℕ) :
    Coup .two :=
  nextAt d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) a b j

variable (d L) in
/-- **One-step bounds** along the flow at `(ctr_N, b)`, `b ≠ ctr_N`, with constant `Cs`. -/
def StepBd (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ Cs : ℝ) : Prop :=
  ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ (N : ℕ) (b : Lam d L N), b ≠ ctr d L N →
    ∀ k < N,
    ‖laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 -
        laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 -
        lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖gaOf .two (NA d L V₀c lbar msq b₀ N (ctr d L N) b k) -
        laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
          (Flow.covAt d L N msq k (ctr d L N) (ctr d L N) : ℂ)‖ ≤
      Cs * ellj d L ℓ₀ k ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k) ∧
    ‖gbOf .two (NA d L V₀c lbar msq b₀ N (ctr d L N) b k) -
        lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 *
          (Flow.covAt d L N msq k b b : ℂ)‖ ≤
      Cs * ellj d L ℓ₀ k ^ 2 * (C * lbar * ‖b₀‖ * th L κ ^ k)

/-- The one-step bounds hold with a constant `Cs` depending only on `d`. -/
theorem exists_stepBd (d : ℕ) (hd : 1 ≤ d) : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (L : ℕ) [NeZero L]
    (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), ObsLimHyp d L A ℓ₀ V₀c lbar C κ →
    StepBd d L A ℓ₀ V₀c lbar C κ Cs := by
  obtain ⟨Cs, hCs, hrec⟩ := Vobs_recursion_two d
  refine ⟨Cs, hCs, ?_⟩
  intro L _ A ℓ₀ V₀c lbar C κ H msq hmsq b₀ hb₀ N b hb k hk
  have hθ : (L : ℝ) ^ (-(κ * k)) = th L κ ^ k := rpow_neg_mul_nat (Nat.cast_nonneg _) κ k
  have hK := (H.fd.obs .two N msq (lbar : ℂ) b₀ b hmsq (by rw [norm_lbar H]; exact hb₀)
    (le_of_eq (norm_lbar H)) hb k hk.le).2
  rw [norm_lbar H, hθ] at hK
  have he : 0 ≤ C * lbar * ‖b₀‖ * th L κ ^ k := by
    have := H.fd.C_nonneg; have := H.fd.lbar_pos; have := th_nonneg L κ; positivity
  obtain ⟨r1, r2, r3, r4, -⟩ := hrec L N k ℓ₀ H.fd.hℓ₀ (Flow.covAt d L N msq k)
    (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1 (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).2
    (ctr d L N) b A H.fd.hA1 _ he hK
    (fun hj Y hY => abSmall_flowO (V₀c msq b₀) (lbar : ℂ) (ctr d L N) b hd H.fd.hL8
      (H.fd.good N msq hmsq) hk hj hY)
  have e1 : (FO d L V₀c lbar msq b₀ N (ctr d L N) b (k + 1)).1 =
      Coup.toV .two (nextObs (Flow.covAt d L N msq k) k
        (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1 (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).2
        (ctr d L N) b) := rfl
  rw [e1, laOf_toV, lbOf_toV]
  exact ⟨r1, r2, r3, r4⟩

/-! ### Points -/

theorem ctr_ne_zero (hd : 1 ≤ d) (hL : 3 ≤ L) {N : ℕ} (hN : 2 ≤ N) :
    (0 : Lam d L N) ≠ ctr d L N := by
  intro h
  have i0 : Fin d := ⟨0, by omega⟩
  have h1 := congrArg (fun x : Lam d L N => (co x i0).val) h
  have h0 : (co (0 : Lam d L N) i0).val = 0 := ZMod.val_zero
  rw [h0, ctr_val (by omega)] at h1
  have : L ≤ L ^ (N - 1) := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem redZ_ctr (hL : 3 ≤ L) (N : ℕ) (i : Fin d) :
    redZ N (ctr d L N) i = (((L ^ (N - 1) - 1) / 2 : ℕ) : ℤ) := by
  simp only [redZ]
  rw [ctr_val (by omega), Nat.mod_eq_of_lt]
  have : 0 < L ^ (N - 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  omega

/-- A point `z ∈ [0, L^{N-2})^d` is not the centre of `Λ_N`. -/
theorem prj_ne_ctr (hd : 1 ≤ d) (hL : 3 ≤ L) {N : ℕ} (hN : 2 ≤ N) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) (hz : ∀ i, z i < ((L ^ (N - 2) : ℕ) : ℤ)) :
    (prj z : Lam d L N) ≠ ctr d L N := by
  intro h
  have hle : L ^ (N - 2) ≤ L ^ (N - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hz' : ∀ i, z i < ((L ^ (N - 1) : ℕ) : ℤ) := fun i =>
    (hz i).trans_le (by exact_mod_cast hle)
  have h1 := redZ_prj_of (N := N) (L := L) hz0 hz'
  rw [h] at h1
  have i0 : Fin d := ⟨0, by omega⟩
  have h2 := congrFun h1 i0
  rw [redZ_ctr hL] at h2
  have h3 := hz i0
  rw [← h2] at h3
  have h4 : L ^ (N - 1) = L * L ^ (N - 2) := by
    rw [← pow_succ']; congr 1; omega
  have h5 : 3 * L ^ (N - 2) ≤ L * L ^ (N - 2) := Nat.mul_le_mul_right _ hL
  have h6 : (L ^ (N - 1) - 1) / 2 < L ^ (N - 2) := by exact_mod_cast h3
  have h7 : 0 < L ^ (N - 2) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  omega

/-! ### Bounds along the flow on `Λ_N` -/

/-- A sequence with `f 0 = a` and increments `‖f (k+1) - f k‖ ≤ C_S E θ^k` (`k < n`) satisfies
`‖f n‖ ≤ ‖a‖ + C_S E/(1-θ)`. -/
theorem geom_bd (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) {Cs : ℝ} (hCs : 0 ≤ Cs) (f : ℕ → ℂ)
    {E : ℝ} (hE : 0 ≤ E) {a : ℂ} (hf0 : f 0 = a) {n : ℕ}
    (h : ∀ k < n, ‖f (k + 1) - f k‖ ≤ Cs * (E * th L κ ^ k)) :
    ‖f n‖ ≤ ‖a‖ + Cs * E / (1 - th L κ) := by
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have h1 := norm_sub_le_geom_tail f (mul_nonneg hCs hE) (th_nonneg L κ) hθ1 (Nat.zero_le n)
    (fun k _ hk => (h k hk).trans (le_of_eq (by ring)))
  rw [pow_zero, mul_one] at h1
  have h0 : ‖f 0‖ = ‖a‖ := by rw [hf0]
  calc ‖f n‖ = ‖f 0 - (f 0 - f n)‖ := by congr 1; abel
    _ ≤ ‖f 0‖ + ‖f 0 - f n‖ := norm_sub_le _ _
    _ ≤ ‖a‖ + Cs * E / (1 - th L κ) := by linarith

/-- `Λm = λ̄ + C_S E/(1-θ)`. -/
abbrev Lm (lbar C κ Cs : ℝ) (b₀ : ℂ) (L : ℕ) : ℝ :=
  lbar + Cs * (C * lbar * ‖b₀‖) / (1 - th L κ)

/-- The size of the torus used for the increments of the `b` slot at `z`. -/
def MBs (z : Zd d) (j : ℕ) : ℕ := j + 4 + supNormZ z


variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
include H hd hCs hS

theorem E_nonneg (b₀ : ℂ) : 0 ≤ C * lbar * ‖b₀‖ := by
  have := H.fd.C_nonneg; have := H.fd.lbar_pos; positivity

omit hd hCs hS in
theorem la_zero (msq : ℝ) (b₀ : ℂ) (N : ℕ) (a b : Lam d L N) :
    laOf .two (FO d L V₀c lbar msq b₀ N a b 0).1 = lbar := rfl

omit hd hCs hS in
theorem lb_zero (msq : ℝ) (b₀ : ℂ) (N : ℕ) (a b : Lam d L N) :
    lbOf .two (FO d L V₀c lbar msq b₀ N a b 0).1 = lbar := rfl

theorem la_N_bd {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k ≤ N) :
    ‖laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤ Lm lbar C κ Cs b₀ L :=
  (geom_bd H hCs (fun k => laOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1)
    (E_nonneg H hd hCs hS b₀) (la_zero H _ _ _ _ _)
    fun i hi => (hS msq hmsq b₀ hb₀ N b hb i (by omega)).1).trans_eq
    (by rw [norm_lbar H])

theorem lb_N_bd {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k ≤ N) :
    ‖lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1‖ ≤ Lm lbar C κ Cs b₀ L :=
  (geom_bd H hCs (fun k => lbOf .two (FO d L V₀c lbar msq b₀ N (ctr d L N) b k).1)
    (E_nonneg H hd hCs hS b₀) (lb_zero H _ _ _ _ _)
    fun i hi => (hS msq hmsq b₀ hb₀ N b hb i (by omega)).2.1).trans_eq
    (by rw [norm_lbar H])

theorem Lm_nonneg (b₀ : ℂ) : 0 ≤ Lm lbar C κ Cs b₀ L := by
  have hθ1 := th_lt_one (by have := three_le_L H; omega) H.fd.κ_pos (L := L)
  have := E_nonneg H hd hCs hS b₀
  have := H.fd.lbar_pos
  have := H.fd.C_nonneg
  have : 0 < 1 - th L κ := by linarith
  unfold Lm; positivity

theorem gstep_bd {k : ℕ} {x l c : ℂ} {B e : ℝ} (hx : ‖x - l * c‖ ≤ Cs * ellj d L ℓ₀ k ^ 2 * (e * th L κ ^ k))
    (hl : ‖l‖ ≤ B) (hc : ‖c‖ ≤ ellj d L ℓ₀ (k + 1) ^ 2) (hB : 0 ≤ B) (he : 0 ≤ e) (hd2 : 2 ≤ d) :
    ‖x‖ ≤ (B + Cs * e) * ℓ₀ ^ 2 * rho d L ^ k := by
  have hL : 3 ≤ L := three_le_L H
  have hθ1 := th_lt_one (by omega) H.fd.κ_pos (L := L)
  have hθk : th L κ ^ k ≤ 1 := pow_le_one₀ (th_nonneg L κ) hθ1.le
  have hs : ellj d L ℓ₀ (k + 1) ^ 2 ≤ ellj d L ℓ₀ k ^ 2 := by
    rw [ellj_sq, ellj_sq, pow_succ]
    have h1 := rho_le_one hd2 L
    have h2 : 0 ≤ rho d L ^ k := pow_nonneg (rho_nonneg d L) k
    have h3 : 0 ≤ ℓ₀ ^ 2 := sq_nonneg _
    calc ℓ₀ ^ 2 * (rho d L ^ k * rho d L) ≤ ℓ₀ ^ 2 * (rho d L ^ k * 1) := by gcongr
      _ = ℓ₀ ^ 2 * rho d L ^ k := by ring
  have hlc : ‖l * c‖ ≤ B * ellj d L ℓ₀ k ^ 2 := by
    rw [norm_mul]
    exact mul_le_mul hl (hc.trans hs) (norm_nonneg _) hB
  have hq : Cs * ellj d L ℓ₀ k ^ 2 * (e * th L κ ^ k) ≤ Cs * e * ellj d L ℓ₀ k ^ 2 := by
    have : e * th L κ ^ k ≤ e := by
      calc e * th L κ ^ k ≤ e * 1 := mul_le_mul_of_nonneg_left hθk he
        _ = e := mul_one e
    have h0 : 0 ≤ Cs * ellj d L ℓ₀ k ^ 2 := mul_nonneg hCs (sq_nonneg _)
    calc Cs * ellj d L ℓ₀ k ^ 2 * (e * th L κ ^ k) ≤ Cs * ellj d L ℓ₀ k ^ 2 * e :=
          mul_le_mul_of_nonneg_left this h0
      _ = Cs * e * ellj d L ℓ₀ k ^ 2 := by ring
  calc ‖x‖ = ‖(x - l * c) + l * c‖ := by congr 1; abel
    _ ≤ ‖x - l * c‖ + ‖l * c‖ := norm_add_le _ _
    _ ≤ Cs * e * ellj d L ℓ₀ k ^ 2 + B * ellj d L ℓ₀ k ^ 2 := add_le_add (hx.trans hq) hlc
    _ = (B + Cs * e) * ℓ₀ ^ 2 * rho d L ^ k := by rw [ellj_sq]; ring

theorem ga_N_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k < N) :
    ‖gaOf .two (NA d L V₀c lbar msq b₀ N (ctr d L N) b k)‖ ≤
      (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * rho d L ^ k := by
  have hc := abs_cov_le H.fd.hℓ₀ (H.fd.good N msq hmsq k hk) (ctr d L N) (ctr d L N)
  refine gstep_bd H hd hCs hS (hS msq hmsq b₀ hb₀ N b hb k hk).2.2.1
    (la_N_bd H hd hCs hS hmsq hb₀ hb (by omega)) ?_ (Lm_nonneg H hd hCs hS b₀)
    (E_nonneg H hd hCs hS b₀) hd2
  rw [Complex.norm_real, Real.norm_eq_abs]; exact hc

theorem gb_N_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N : ℕ}
    {b : Lam d L N} (hb : b ≠ ctr d L N) {k : ℕ} (hk : k < N) :
    ‖gbOf .two (NA d L V₀c lbar msq b₀ N (ctr d L N) b k)‖ ≤
      (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * rho d L ^ k := by
  have hc := abs_cov_le H.fd.hℓ₀ (H.fd.good N msq hmsq k hk) b b
  refine gstep_bd H hd hCs hS (hS msq hmsq b₀ hb₀ N b hb k hk).2.2.2
    (lb_N_bd H hd hCs hS hmsq hb₀ hb (by omega)) ?_ (Lm_nonneg H hd hCs hS b₀)
    (E_nonneg H hd hCs hS b₀) hd2
  rw [Complex.norm_real, Real.norm_eq_abs]; exact hc

/-! ### The `N`-independent sequences -/

/-- `|λ_{a,j+1} - λ_{a,j}| ≤ C_S E θ^j`. -/
theorem lA_succ {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (j : ℕ) :
    ‖lA d L V₀c lbar msq b₀ (j + 1) - lA d L V₀c lbar msq b₀ j‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ j) := by
  have hne := ctr_ne_zero hd (three_le_L H) (N := j + 3) (by omega)
  rw [← (lA_char H hd hmsq hb₀ (N := j + 3) (j := j + 1) (by omega) 0).1,
    ← (lA_char H hd hmsq hb₀ (N := j + 3) (j := j) (by omega) 0).1]
  exact (hS msq hmsq b₀ hb₀ (j + 3) 0 hne j (by omega)).1

theorem MBs_facts (hL : 3 ≤ L) {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) (j : ℕ) :
    (∀ i, z i < ((L ^ (MBs z j - 1) : ℕ) : ℤ)) ∧ (∀ i, z i < ((L ^ (MBs z j - 2) : ℕ) : ℤ)) :=
  ⟨lt_pow_of_le_supNormZ (by omega) hz0 (by unfold MBs; omega),
    lt_pow_of_le_supNormZ (by omega) hz0 (by unfold MBs; omega)⟩

/-- `|λ_{b,j+1}(z) - λ_{b,j}(z)| ≤ C_S E θ^j` for `z ∈ ℕ^d`. -/
theorem lB_succ {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) (j : ℕ) :
    ‖lB d L V₀c lbar msq b₀ z (j + 1) - lB d L V₀c lbar msq b₀ z j‖ ≤
      Cs * (C * lbar * ‖b₀‖ * th L κ ^ j) := by
  obtain ⟨h1, h2⟩ := MBs_facts H hd hCs hS (three_le_L H) hz0 j
  have hne := prj_ne_ctr hd (three_le_L H) (N := MBs z j) (by unfold MBs; omega) hz0 h2
  rw [← (lB_char H hd hmsq hb₀ hz0 (M := MBs z j) (j := j + 1) (by unfold MBs; omega) h1
      (ctr d L _)).1,
    ← (lB_char H hd hmsq hb₀ hz0 (M := MBs z j) (j := j) (by unfold MBs; omega) h1
      (ctr d L _)).1]
  exact (hS msq hmsq b₀ hb₀ (MBs z j) (prj z) hne j (by unfold MBs; omega)).2.1

theorem gA_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (j : ℕ) :
    ‖gA d L V₀c lbar msq b₀ j‖ ≤
      (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * rho d L ^ j := by
  have hne := ctr_ne_zero hd (three_le_L H) (N := j + 3) (by omega)
  rw [← (lA_char H hd hmsq hb₀ (N := j + 3) (j := j) (by omega) 0).2]
  exact ga_N_bd H hd hCs hS hd2 hmsq hb₀ hne (by omega)

theorem gB_bd (hd2 : 2 ≤ d) {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar)
    {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) (j : ℕ) :
    ‖gB d L V₀c lbar msq b₀ z j‖ ≤
      (Lm lbar C κ Cs b₀ L + Cs * (C * lbar * ‖b₀‖)) * ℓ₀ ^ 2 * rho d L ^ j := by
  obtain ⟨h1, h2⟩ := MBs_facts H hd hCs hS (three_le_L H) hz0 j
  have hne := prj_ne_ctr hd (three_le_L H) (N := MBs z j) (by unfold MBs; omega) hz0 h2
  rw [← (lB_char H hd hmsq hb₀ hz0 (M := MBs z j) (j := j) (by unfold MBs; omega) h1
      (ctr d L _)).2]
  exact gb_N_bd H hd hCs hS hd2 hmsq hb₀ hne (by unfold MBs; omega)

end

end Ward
