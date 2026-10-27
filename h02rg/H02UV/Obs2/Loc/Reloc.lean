import Grassmann.Examples
import Loc.EstBasic
import Obs2.Map.ExactStep
import Obs2.Flow.EstMu

/-!
# B3, T3: relocating the localisation point of the Case-(2) observable

Route shift–relocate–restart (Log.md, "B3"). Moving the coupling term `λσ_aψ̄_aψ_a` to the point
`a'` leaves the remainder `λσ(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})`. The gradient weights `h^{|α|}` of the
test functions make this remainder small in `T_j(ℓ)`, with `h = L^j`.

* `reloc_step`: `‖ψ̄_{x+e}ψ_{x+e} − ψ̄_xψ_x‖_{T(ℓ)} ≤ 2ℓ²h⁻¹` for a unit vector `e`, when `p_Φ ≥ 1`.
  The proof writes the difference as `(∇_eψ̄)_xψ_{x+e} + ψ̄_x(∇_eψ)_x` and uses `tNorm_dψ_le`.
* `reloc_vadd`: along a multi-index `α`, `‖pbp(α +ᵥ x) − pbp x‖ ≤ 2|α|ℓ²h⁻¹`.
* `reloc_exists_mi`: every `w` is `∑_eα(e)e` with `|α| ≤ d|w|_∞`.
* **`reloc_pbp`**: `‖ψ̄_aψ_a − ψ̄_{a'}ψ_{a'}‖_{T_j(ℓ)} ≤ 2d|a − a'|_∞ℓ²L^{-j}`, for `1 ≤ d`.
  **`reloc_coupling`** adds a coupling: `‖λ(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})‖ ≤ 2d|λ||a − a'|_∞ℓ²L^{-j}`.
  For the `σ_a` component, `oTo_wA` identifies the observable norm with this `T_j` norm.
* **`reloc_exact`**: exactness does not depend on the Loc point. For two configurations `P` and
  `P'` (for example `a` and `a'`) and the same input `(V, W, K)` satisfying `OLocHyp` for both,
  the two exact steps `stepK_ZVKO` have the same left side `𝔼_Cθ Z_j`. Hence the two outputs
  coincide, `e^{-u^P}Z^P_{j+1} = e^{-u^{P'}}Z^{P'}_{j+1}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Loc FRD Obs Obs.SA Obs.LocObs ENNReal

variable {d L N : ℕ} [NeZero L]

/-! ### One unit step -/

theorem reloc_psi_shift (e : Dir d) (x : Lam d L N) (s : ℤˣ) :
    ψ ((x + dirVec e, s) : Sf (Lam d L N)) = ψ ((x, s) : Sf (Lam d L N)) + dψ e (x, s) := by
  rw [dψ, sh, single_vadd]; abel

/-- **One unit step**: `‖ψ̄_{x+e}ψ_{x+e} − ψ̄_xψ_x‖_{T(ℓ)} ≤ 2ℓ²h⁻¹` (`p_Φ ≥ 1`). -/
theorem reloc_step {p : ℕ} {h ℓ : ℝ} (hp : 1 ≤ p) (hh : 0 < h) (hℓ : 0 < ℓ) (e : Dir d)
    (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (pbp (x + dirVec e) - pbp x) ≤ ENNReal.ofReal (2 * (ℓ ^ 2 * h⁻¹)) := by
  have e1 : pbp (x + dirVec e) - pbp x =
      dψ e (x, -1) * ψ ((x + dirVec e, 1) : Sf (Lam d L N)) +
        ψ ((x, -1) : Sf (Lam d L N)) * dψ e (x, 1) := by
    simp only [pbp, psibar, psi]
    rw [reloc_psi_shift e x (-1), reloc_psi_shift e x 1]
    noncomm_ring
  rw [e1]
  have hb1 : tNorm (Dir d) p h ℓ (dψ e (x, -1) * ψ ((x + dirVec e, 1) : Sf (Lam d L N))) ≤
      ENNReal.ofReal (ℓ ^ 2 * h⁻¹) := by
    refine (tNorm_mul_le hh hℓ _ _).trans ?_
    rw [tNorm_ψ hh hℓ]
    calc tNorm (Dir d) p h ℓ (dψ e (x, -1)) * ENNReal.ofReal ℓ
        ≤ ENNReal.ofReal (ℓ * h⁻¹) * ENNReal.ofReal ℓ := by
          gcongr; exact tNorm_dψ_le hp hh hℓ e _
      _ = ENNReal.ofReal (ℓ ^ 2 * h⁻¹) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hb2 : tNorm (Dir d) p h ℓ (ψ ((x, -1) : Sf (Lam d L N)) * dψ e (x, 1)) ≤
      ENNReal.ofReal (ℓ ^ 2 * h⁻¹) := by
    refine (tNorm_mul_le hh hℓ _ _).trans ?_
    rw [tNorm_ψ hh hℓ]
    calc ENNReal.ofReal ℓ * tNorm (Dir d) p h ℓ (dψ e (x, 1))
        ≤ ENNReal.ofReal ℓ * ENNReal.ofReal (ℓ * h⁻¹) := by
          gcongr; exact tNorm_dψ_le hp hh hℓ e _
      _ = ENNReal.ofReal (ℓ ^ 2 * h⁻¹) := by
          rw [← ENNReal.ofReal_mul hℓ.le]; congr 1; ring
  refine (tNorm_add_le _ _).trans ?_
  have h0 : 0 ≤ ℓ ^ 2 * h⁻¹ := by positivity
  rw [two_mul, ENNReal.ofReal_add h0 h0]
  exact add_le_add hb1 hb2

/-! ### Along a multi-index -/

theorem reloc_mabs_add_single (α : Dir d → ℕ) (e : Dir d) :
    Grassmann.mabs (α + Pi.single e 1) = Grassmann.mabs α + 1 := by
  unfold Grassmann.mabs
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

/-- `‖ψ̄_{α+x}ψ_{α+x} − ψ̄_xψ_x‖_{T(ℓ)} ≤ 2|α|ℓ²h⁻¹`. -/
theorem reloc_vadd {p : ℕ} {h ℓ : ℝ} (hp : 1 ≤ p) (hh : 0 < h) (hℓ : 0 < ℓ) :
    ∀ (n : ℕ) (α : Dir d → ℕ), Grassmann.mabs α = n → ∀ x : Lam d L N,
      tNorm (Dir d) p h ℓ (pbp (α +ᵥ x) - pbp x) ≤
        ENNReal.ofReal (2 * n * (ℓ ^ 2 * h⁻¹)) := by
  intro n
  induction n with
  | zero =>
    intro α hα x
    have h0 : α = 0 := by
      funext e
      have := (Finset.sum_eq_zero_iff.1 (show ∑ e, α e = 0 from hα)) e (mem_univ e)
      simpa using this
    rw [h0, zero_vadd, sub_self]
    simp [tNorm_zero']
  | succ n ih =>
    intro α hα x
    obtain ⟨e, he⟩ : ∃ e, 0 < α e := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      have : Grassmann.mabs α = 0 := Finset.sum_eq_zero fun e _ => by have := hne e; omega
      omega
    set α' : Dir d → ℕ := fun f => α f - (Pi.single e 1 : Dir d → ℕ) f with hα'
    have hsplit : α = α' + Pi.single e 1 := by
      funext f
      by_cases hf : f = e
      · subst hf; simp [α']; omega
      · simp [α', hf]
    have hm' : Grassmann.mabs α' = n := by
      have := reloc_mabs_add_single α' e
      rw [← hsplit] at this; omega
    have hv : α +ᵥ x = α' +ᵥ (x + dirVec e) := by
      rw [hsplit, add_vadd, single_vadd]
    have e2 : pbp (α +ᵥ x) - pbp x =
        (pbp (α' +ᵥ (x + dirVec e)) - pbp (x + dirVec e)) + (pbp (x + dirVec e) - pbp x) := by
      rw [hv]; abel
    rw [e2]
    refine (tNorm_add_le _ _).trans ?_
    have h0 : 0 ≤ ℓ ^ 2 * h⁻¹ := by positivity
    have hn : (0 : ℝ) ≤ 2 * n * (ℓ ^ 2 * h⁻¹) := by positivity
    calc _ ≤ ENNReal.ofReal (2 * n * (ℓ ^ 2 * h⁻¹)) + ENNReal.ofReal (2 * (ℓ ^ 2 * h⁻¹)) :=
          add_le_add (ih α' hm' _) (reloc_step hp hh hℓ e x)
      _ = ENNReal.ofReal (2 * ((n + 1 : ℕ) : ℝ) * (ℓ ^ 2 * h⁻¹)) := by
          rw [← ENNReal.ofReal_add hn (by positivity)]; congr 1; push_cast; ring

/-- **Every `w` is a sum of unit vectors** `∑_eα(e)e` with `|α| ≤ d|w|_∞`. -/
theorem reloc_exists_mi (w : Lam d L N) :
    ∃ α : Dir d → ℕ, (∀ x : Lam d L N, α +ᵥ x = x + w) ∧ Grassmann.mabs α ≤ d * supNorm w := by
  choose r hr hra using fun i => exists_natAbs_eq_zabs ((w : Fin d → ZMod (L ^ N)) i)
  let α : Dir d → ℕ := fun e => match e with
    | Sum.inl i => (r i).toNat
    | Sum.inr i => (-r i).toNat
  refine ⟨α, fun x => ?_, ?_⟩
  · rw [vadd_def, add_comm]
    congr 1
    funext j
    have hs : (∑ e, α e • dirVec e : Torus d (L ^ N)) j =
        ∑ e, α e • ((dirVec e : Torus d (L ^ N)) : Fin d → ZMod (L ^ N)) j :=
      Finset.sum_apply j _ _
    rw [hs, Fintype.sum_sum_type]
    simp only [α, dirVec, Pi.neg_apply, Pi.single_apply, smul_neg, nsmul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq, mem_univ, if_true]
    rw [← hr j]
    have : ((r j).toNat : ℤ) - ((-r j).toNat : ℤ) = r j := by omega
    conv_rhs => rw [← this]
    push_cast; ring
  · unfold Grassmann.mabs
    rw [Fintype.sum_sum_type]
    simp only [α]
    rw [← Finset.sum_add_distrib]
    calc ∑ i, ((r i).toNat + (-r i).toNat) ≤ ∑ _i : Fin d, supNorm w := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : zabs ((w : Fin d → ZMod (L ^ N)) i) ≤ supNorm w :=
            Finset.le_sup (f := fun i => zabs ((w : Fin d → ZMod (L ^ N)) i)) (mem_univ i)
          have h2 := hra i
          omega
      _ = d * supNorm w := by rw [Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The relocation bound**: `‖ψ̄_aψ_a − ψ̄_{a'}ψ_{a'}‖_{T_j(ℓ)} ≤ 2d|a − a'|_∞ℓ²L^{-j}`. -/
theorem reloc_pbp (hd : 1 ≤ d) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (a a' : Lam d L N) :
    Tj d (L : ℝ) j ℓ (pbp a - pbp a') ≤
      ENNReal.ofReal (2 * d * supNorm (a - a') * ℓ ^ 2 / (L : ℝ) ^ j) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  obtain ⟨α, hα, hαn⟩ := reloc_exists_mi (a - a')
  have hp : 1 ≤ pPhi d := by unfold pPhi; omega
  have := reloc_vadd (L := L) (N := N) hp hh hℓ _ α rfl a'
  rw [hα, show a' + (a - a') = a by abel] at this
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : ((Grassmann.mabs α : ℕ) : ℝ) ≤ (d : ℝ) * supNorm (a - a') := by exact_mod_cast hαn
  have hq : 0 ≤ ℓ ^ 2 * ((L : ℝ) ^ j)⁻¹ := by positivity
  calc 2 * ((Grassmann.mabs α : ℕ) : ℝ) * (ℓ ^ 2 * ((L : ℝ) ^ j)⁻¹)
      ≤ 2 * ((d : ℝ) * supNorm (a - a')) * (ℓ ^ 2 * ((L : ℝ) ^ j)⁻¹) := by gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- **The relocated coupling term**: `‖λ(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})‖_{T_j(ℓ)} ≤
2d|λ||a − a'|_∞ℓ²L^{-j}`. -/
theorem reloc_coupling (hd : 1 ≤ d) {j : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (cpl : ℂ) (a a' : Lam d L N) :
    Tj d (L : ℝ) j ℓ (cpl • (pbp a - pbp a')) ≤
      ENNReal.ofReal (‖cpl‖ * (2 * d * supNorm (a - a') * ℓ ^ 2 / (L : ℝ) ^ j)) := by
  refine (tNorm_smul_le _ _).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _)]
  gcongr
  exact reloc_pbp hd hℓ a a'

/-! ### Exactness does not depend on the Loc point -/

/-- **Exactness is independent of the Loc point**: for two point configurations `P`, `P'` (e.g.
`P.a = a`, `P'.a = a'`) and one input `(V, W, K)` with `OLocHyp` for both, the outputs of the two
exact steps coincide (both equal `𝔼_Cθ Z_j`). -/
theorem reloc_exact {c : Obs.Case} (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hjN : j + 1 < N)
    {C : Matrix (Lam d L N) (Lam d L N) ℂ} (hC : CovRange j C) {V W : OFam c d L N}
    {K : OAct c d L N} (P P' : ObsPts d L N) (H : OLocHyp P j V W K) (H' : OLocHyp P' j V W K) :
    expU (-uXB P j C V W K univ) (-uXO P j C V W K univ) *
        gZO (j + 1) (ItO P j C V W K) (KplusO P j C V W K) =
      expU (-uXB P' j C V W K univ) (-uXO P' j C V W K univ) *
        gZO (j + 1) (ItO P' j C V W K) (KplusO P' j C V W K) := by
  rw [← stepK_ZVKO hd hL hjN hC H, ← stepK_ZVKO hd hL hjN hC H']

end

end Obs2
