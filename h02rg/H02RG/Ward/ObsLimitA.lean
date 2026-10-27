import Obs.TranslCons
import PtCorr.ContJoint
import Psi4.Alg

/-!
# Infinite-volume observable couplings, part A: the `N`-independent sequences

Along the canonical family `(Λ_N, ctr_N)` (Case (2), `l₀ = λ̄`), the single-point couplings at
scale `j` do not depend on `N ≥ j + 2` (`Obs.a_ctr_consist`, `Obs.b_consist`):

* `lA … j = λ_{a,j}` and `gA … j = γ_{a,j+1} - γ_{a,j}` (the `u`-part produced by step `j`) at
  the centre, computed on `Λ_{j+2}` at the pair `(ctr, ctr)` (`lA_char`: the same for every
  `N ≥ j + 2` and every partner `x ∈ Λ_N`);
* `lB … z j = λ_{b,j}` and `gB … z j` at a point `z ∈ ℕ^d ⊆ ℤ^d`, computed on
  `Λ_{MB z j}` at `(prj z, prj z)` (`lB_char`: the same on every `Λ_M` with `j + 2 ≤ M` and
  `z ∈ [0, L^{M-1})^d`, for every partner), and `lB_eq`: on `Λ_N` the `b` slot at `b` is
  the one at the reduced point `redZ N b`.

The hypotheses (`ObsLimHyp`) are the common flow `PtCorr.FlowData`, `L` odd, and the torus
independence of the bulk flow from `Flow.thm_flow_real` (not recorded in `FlowData`; it is in
`PtCorr.FlowDataW`, and `ObsLimHyp.ofW` gives `ObsLimHyp` from `FlowDataW`).
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric

variable {d L : ℕ} [NeZero L]

/-- The hypotheses for the infinite-volume limits of the observable couplings. -/
structure ObsLimHyp (d L : ℕ) [NeZero L] (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ) :
    Prop where
  fd : FlowData d L A ℓ₀ V₀c lbar C κ
  odd : Odd L
  consV : ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ N M j : ℕ, j + 2 ≤ N → N ≤ M →
    (Flow.flowN d L N msq (V₀c msq b₀) j).1 = (Flow.flowN d L M msq (V₀c msq b₀) j).1
  consU : ∀ msq : ℝ, 0 ≤ msq → ∀ b₀ : ℂ, ‖b₀‖ ≤ lbar → ∀ N M j : ℕ, j + 3 ≤ N → N ≤ M →
    Flow.uflow d L N msq (V₀c msq b₀) j = Flow.uflow d L M msq (V₀c msq b₀) j

variable {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

/-- `FlowDataW` (the common flow of `PtCorr.setupW`, with the torus-independence clauses
`indepV`, `indepU`) and `L` odd give `ObsLimHyp`. -/
theorem ObsLimHyp.ofW (HW : FlowDataW d L A ℓ₀ V₀c lbar C κ) (hLodd : Odd L) :
    ObsLimHyp d L A ℓ₀ V₀c lbar C κ :=
  ⟨HW.toFlowData, hLodd, HW.indepV, HW.indepU⟩

theorem ObsLimHyp.hbulk (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) {msq : ℝ} (hmsq : 0 ≤ msq)
    {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N M : ℕ} (hNM : N ≤ M) :
    ∀ k, k + 3 ≤ N →
      uVnext k (Flow.covAt d L M msq k) (Flow.flowN d L M msq (V₀c msq b₀) k).1
          (Flow.flowN d L M msq (V₀c msq b₀) k).2 =
        uVnext k (Flow.covAt d L N msq k) (Flow.flowN d L N msq (V₀c msq b₀) k).1
          (Flow.flowN d L N msq (V₀c msq b₀) k).2 :=
  hbulk_of (fun j hj => H.consV msq hmsq b₀ hb₀ N M j hj hNM)
    (fun j hj => H.consU msq hmsq b₀ hb₀ N M j hj hNM)

/-! ### The sequences -/

variable (d L) in
/-- `λ_{a,j}` at the centre (Case (2), `l₀ = λ̄`), computed on `Λ_{j+2}`. -/
def lA (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (j : ℕ) : ℂ :=
  laOf .two (flowO d L .two (j + 2) msq (V₀c msq b₀) (initObs .two (lbar : ℂ))
    (ctr d L (j + 2)) (ctr d L (j + 2)) j).1

variable (d L) in
/-- `γ_{a,j+1} - γ_{a,j}`, the `a` part of `u^obs_{j+1}` at the centre, computed on `Λ_{j+2}`. -/
def gA (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (j : ℕ) : ℂ :=
  gaOf .two (nextAt d L .two (j + 2) msq (V₀c msq b₀) (initObs .two (lbar : ℂ))
    (ctr d L (j + 2)) (ctr d L (j + 2)) j)

/-- A torus size on which `z` (with `0 ≤ z`) is represented faithfully at scale `j`. -/
def MB (z : Zd d) (j : ℕ) : ℕ := j + 2 + supNormZ z

variable (d L) in
/-- `λ_{b,j}` at the point `z ∈ ℕ^d`, computed on `Λ_{MB z j}`. -/
def lB (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (z : Zd d) (j : ℕ) : ℂ :=
  lbOf .two (flowO d L .two (MB z j) msq (V₀c msq b₀) (initObs .two (lbar : ℂ))
    (prj z) (prj z) j).1

variable (d L) in
/-- `γ_{b,j+1} - γ_{b,j}` at the point `z ∈ ℕ^d`, computed on `Λ_{MB z j}`. -/
def gB (V₀c : ℝ → ℂ → Vcoup) (lbar msq : ℝ) (b₀ : ℂ) (z : Zd d) (j : ℕ) : ℂ :=
  gbOf .two (nextAt d L .two (MB z j) msq (V₀c msq b₀) (initObs .two (lbar : ℂ))
    (prj z) (prj z) j)

/-! ### Arithmetic of the points -/

theorem redZ_prj_of {N : ℕ} {z : Zd d} (hz0 : ∀ i, 0 ≤ z i)
    (hzN : ∀ i, z i < ((L ^ (N - 1) : ℕ) : ℤ)) : redZ N (prj z : Lam d L N) = z := by
  funext i
  obtain ⟨n, hn⟩ : ∃ n : ℕ, z i = n := ⟨(z i).toNat, (Int.toNat_of_nonneg (hz0 i)).symm⟩
  have hn' : n < L ^ (N - 1) := by have := hzN i; rw [hn] at this; exact_mod_cast this
  have hle : L ^ (N - 1) ≤ L ^ N :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  show ((((co (prj z : Lam d L N) i).val % L ^ (N - 1) : ℕ) : ℤ)) = z i
  have h1 : co (prj z : Lam d L N) i = ((n : ℕ) : ZMod (L ^ N)) := by
    show ((z i : ℤ) : ZMod (L ^ N)) = _
    rw [hn]; simp
  rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (show n < L ^ N by omega), Nat.mod_eq_of_lt hn', hn]

theorem lt_pow_of_le_supNormZ (hL : 2 ≤ L) {z : Zd d} (hz0 : ∀ i, 0 ≤ z i) {k : ℕ}
    (hk : supNormZ z ≤ k) (i : Fin d) : z i < ((L ^ k : ℕ) : ℤ) := by
  have h1 := natAbs_le_supNormZ z i
  have h2 : supNormZ z < L ^ supNormZ z := Nat.lt_pow_self (by omega)
  have h3 : L ^ supNormZ z ≤ L ^ k := Nat.pow_le_pow_right (by omega) hk
  have h4 : ((z i).natAbs : ℤ) = z i := Int.natAbs_of_nonneg (hz0 i)
  have h5 : (z i).natAbs < L ^ k := by omega
  rw [← h4]; exact_mod_cast h5

theorem redZ_nonneg (N : ℕ) (b : Lam d L N) (i : Fin d) : 0 ≤ redZ N b i :=
  Nat.cast_nonneg _

theorem redZ_lt (N : ℕ) (b : Lam d L N) (i : Fin d) :
    redZ N b i < ((L ^ (N - 1) : ℕ) : ℤ) := by
  have : (co b i).val % L ^ (N - 1) < L ^ (N - 1) := Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
  simp only [redZ]; exact_mod_cast this

/-! ### Characterisations -/

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d)
include H hd

/-- **The `a` slot at the centre is `lA`, `gA`** on every `Λ_N`, `N ≥ j + 2`, for every
partner. -/
theorem lA_char {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N j : ℕ}
    (hj : j + 2 ≤ N) (x : Lam d L N) :
    laOf .two (flowO d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N) x j).1 =
        lA d L V₀c lbar msq b₀ j ∧
      gaOf .two (nextAt d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) (ctr d L N) x j) =
        gA d L V₀c lbar msq b₀ j := by
  obtain ⟨h1, -, h3⟩ := a_ctr_consist hd H.fd.hL8 hj hmsq (V₀c msq b₀) (H.fd.good N msq hmsq)
    (H.hbulk hmsq hb₀ hj) H.odd (c := .two) (Vo₀ := initObs .two (lbar : ℂ))
    (Vo₀' := initObs .two (lbar : ℂ)) rfl (ctr d L (j + 2)) x (j := j) le_rfl
  exact ⟨h1.symm, h3.symm⟩

/-- **The `b` slot at `z ∈ ℕ^d` is `lB`, `gB`** on every `Λ_M` with `j + 2 ≤ M` on which `z`
is reduced, for every partner. -/
theorem lB_char {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {z : Zd d}
    (hz0 : ∀ i, 0 ≤ z i) {M j : ℕ} (hj : j + 2 ≤ M)
    (hzM : ∀ i, z i < ((L ^ (M - 1) : ℕ) : ℤ)) (a' : Lam d L M) :
    lbOf .two (flowO d L .two M msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) a' (prj z) j).1 =
        lB d L V₀c lbar msq b₀ z j ∧
      gbOf .two (nextAt d L .two M msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) a' (prj z) j) =
        gB d L V₀c lbar msq b₀ z j := by
  have hL2 : 2 ≤ L := by
    have : 2 ^ 1 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := H.fd.hL8; omega
  have hMP : M ≤ max M (MB z j) := le_max_left _ _
  have hBP : MB z j ≤ max M (MB z j) := le_max_right _ _
  have hjB : j + 2 ≤ MB z j := by unfold MB; omega
  have hz1 : redZ M (prj z : Lam d L M) = z := redZ_prj_of hz0 hzM
  have hz2 : redZ (MB z j) (prj z : Lam d L (MB z j)) = z :=
    redZ_prj_of hz0 (lt_pow_of_le_supNormZ hL2 hz0 (by unfold MB; omega))
  obtain ⟨e1, -, e3⟩ := b_consist hd H.fd.hL8 hMP hmsq (V₀c msq b₀) (H.fd.good M msq hmsq)
    (H.fd.good _ msq hmsq) (H.hbulk hmsq hb₀ hMP) (c := .two)
    (Vo₀ := initObs .two (lbar : ℂ)) (Vo₀' := initObs .two (lbar : ℂ)) rfl a' (prj z)
    (prj z) hj
  obtain ⟨f1, -, f3⟩ := b_consist hd H.fd.hL8 hBP hmsq (V₀c msq b₀) (H.fd.good _ msq hmsq)
    (H.fd.good _ msq hmsq) (H.hbulk hmsq hb₀ hBP) (c := .two)
    (Vo₀ := initObs .two (lbar : ℂ)) (Vo₀' := initObs .two (lbar : ℂ)) rfl (prj z) (prj z)
    (prj z) hjB
  rw [hz1] at e1 e3
  rw [hz2] at f1 f3
  exact ⟨e1.trans f1.symm, e3.trans f3.symm⟩

/-- **The `b` slot on `Λ_N`** at `b` is `lB`, `gB` at the reduced point `redZ N b`, for every
partner (`j + 2 ≤ N`). -/
theorem lB_eq {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) {N j : ℕ}
    (hj : j + 2 ≤ N) (a b : Lam d L N) :
    lbOf .two (flowO d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) a b j).1 =
        lB d L V₀c lbar msq b₀ (redZ N b) j ∧
      gbOf .two (nextAt d L .two N msq (V₀c msq b₀) (initObs .two (lbar : ℂ)) a b j) =
        gB d L V₀c lbar msq b₀ (redZ N b) j := by
  obtain ⟨e1, -, e3⟩ := b_consist hd H.fd.hL8 (le_refl N) hmsq (V₀c msq b₀)
    (H.fd.good N msq hmsq) (H.fd.good N msq hmsq) (H.hbulk hmsq hb₀ le_rfl) (c := .two)
    (Vo₀ := initObs .two (lbar : ℂ)) (Vo₀' := initObs .two (lbar : ℂ)) rfl a b a hj
  obtain ⟨f1, f3⟩ := lB_char H hd hmsq hb₀ (redZ_nonneg N b) hj (redZ_lt N b) a
  exact ⟨e1.trans f1, e3.trans f3⟩

end

end Ward
