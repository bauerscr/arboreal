module

public import ArborealDecay.Superpoly.Piece

/-!
# The annulus bound for one factor (from `(AN)`)
-/

@[expose] public section

namespace ArborealDecay.Superpoly

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical ArborealDecay.Surgery ArborealDecay.ExpDecay ArborealDecay.Lattice

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The injection of the abstract annulus graph into the ambient type. -/
def jF (φ : V → ℤ × ℤ) (r₀ m k : ℕ) : Bool ⊕ lamF φ r₀ k → Amb V m :=
  Sum.elim (fun b => if b then rho V m (k + 1) else rho V m k) (iotaF φ r₀ m k)

section

variable {φ : V → ℤ × ℤ} (hφ : Function.Injective φ) {r₀ : ℕ} (hr : 0 < r₀) {m k : ℕ}
  (hk : k < m)

include hr hk

theorem jF_injective : Function.Injective (jF (V := V) φ r₀ m k) := by
  have hne : rho V m k ≠ rho V m (k + 1) := fun h => by
    have := rho_injective hk.le (Nat.succ_le_of_lt hk) h
    omega
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simp only [jF, Sum.elim_inl] at h
    cases a <;> cases b <;> simp_all
  · exfalso
    simp only [jF, Sum.elim_inl, Sum.elim_inr, iotaF, rho] at h
    split_ifs at h
  · exfalso
    simp only [jF, Sum.elim_inl, Sum.elim_inr, iotaF, rho] at h
    split_ifs at h
  · simp only [jF, Sum.elim_inr] at h
    exact congrArg Sum.inr (iotaF_injective r₀ m k h)

include hφ

theorem jF_annulusCollapse (z : lamF φ r₀ k) :
    jF φ r₀ m k (annulusCollapse (2 ^ k * r₀) (lamF φ r₀ k) z) =
      piW φ r₀ m (iotaF φ r₀ m k z) := by
  have hmono := lev_strictMono hr
  have hb := lamF_bounds z.2
  have hh : heightT φ r₀ m (iotaF φ r₀ m k z) = supNorm z.1 := by
    show supNorm (φ (psiF φ z.1)) = supNorm z.1
    rw [phi_psiF z.2]
  have hlev : ((2 ^ k * r₀ : ℕ) : ℤ) = lev r₀ k := rfl
  have hlev2 : 2 * ((2 ^ k * r₀ : ℕ) : ℤ) = lev r₀ (k + 1) := by rw [hlev, lev_succ]
  unfold annulusCollapse
  split_ifs with e1 e2
  · rw [piW_of_eq φ hr m hk.le _ (by rw [hh, e1, hlev])]
    simp [jF]
  · rw [piW_of_eq φ hr m (Nat.succ_le_of_lt hk) _ (by rw [hh, e2, hlev2])]
    simp [jF]
  · have hfix : piW φ r₀ m (iotaF φ r₀ m k z) = iotaF φ r₀ m k z := by
      refine piW_of_ne φ r₀ m _ fun j hj hjx => ?_
      rw [hh] at hjx
      rcases le_or_gt j k with hjk | hjk
      · have := hmono.monotone hjk; rw [hlev] at e1; omega
      · have := hmono.monotone (show k + 1 ≤ j by omega); rw [hlev2] at e2; omega
    rw [hfix]; rfl

end

/-- **One annulus factor** (from `(AN)`). -/
theorem piece_bound_of_inputs {B C κ : ℝ}
    (hAN : ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
      (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * (r : ℤ)) →
      ∀ (w : Λ → Λ → ℝ) (hw : ∀ i j, w i j = w j i), (∀ i j, 0 ≤ w i j) →
        (∀ i j, w i j ≠ 0 → IsNN (i : ℤ × ℤ) j) → (∀ i j, w i j ≤ B) →
        connProb (mapW w (annulusCollapse r Λ)) (mapW_symm hw _) (Sum.inl false) (Sum.inl true)
          ≤ C * (r : ℝ) ^ (-κ))
    {φ : V → ℤ × ℤ} (hφ : Function.Injective φ) {r₀ : ℕ} (hr : 2 ≤ r₀) {m k : ℕ} (hk : k < m)
    {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (hβB : ∀ i j, β i j ≤ B) (hdiag : ∀ u, β u u = 0)
    (hLip : ∀ u v, β u v ≠ 0 → |supNorm (φ u) - supNorm (φ v)| ≤ 1)
    (hNN : ∀ u v, β u v ≠ 0 → supNorm (φ u) ≤ lev r₀ m → supNorm (φ v) ≤ lev r₀ m →
      IsNN (φ u) (φ v)) :
    connProb (wiredW φ r₀ m β) (wiredW_symm φ r₀ m hβ) (rho V m k) (rho V m (k + 1)) ≤
      C * ((2 ^ k * r₀ : ℕ) : ℝ) ^ (-κ) := by
  have hr0 : 0 < r₀ := by omega
  have hmono := lev_strictMono hr0
  have hlev : ((2 ^ k * r₀ : ℕ) : ℤ) = lev r₀ k := rfl
  have hlev2 : 2 * ((2 ^ k * r₀ : ℕ) : ℤ) = lev r₀ (k + 1) := by rw [hlev, lev_succ]
  have hr2 : 2 ≤ 2 ^ k * r₀ := le_trans hr (Nat.le_mul_of_pos_left _ (by positivity))
  set Λ := lamF φ r₀ k with hΛ
  set w := wF φ r₀ k β with hw
  have hwsymm : ∀ i j, w i j = w j i := fun i j => hβ _ _
  have hAN' := hAN (2 ^ k * r₀) hr2 Λ
    (fun z hz => by
      have := lamF_bounds hz
      rw [hlev, ← lev_succ]; exact this)
    w hwsymm (fun i j => hβ0 _ _)
    (fun i j hij => by
      have h1 : supNorm (φ (psiF φ i.1)) ≤ lev r₀ m := by
        rw [phi_psiF i.2]; have := (lamF_bounds i.2).2
        exact this.trans (hmono.monotone (Nat.succ_le_of_lt hk))
      have h2 : supNorm (φ (psiF φ j.1)) ≤ lev r₀ m := by
        rw [phi_psiF j.2]; have := (lamF_bounds j.2).2
        exact this.trans (hmono.monotone (Nat.succ_le_of_lt hk))
      have := hNN _ _ hij h1 h2
      rwa [phi_psiF i.2, phi_psiF j.2] at this)
    (fun i j => hβB _ _)
  -- the window
  have hwin : connProb (wiredW φ r₀ m β) (wiredW_symm φ r₀ m hβ) (rho V m k)
      (rho V m (k + 1)) = H02.arborealProb (restrW (KF φ r₀ m k) (wiredW φ r₀ m β))
        (restrW_symm _ (wiredW_symm φ r₀ m hβ))
        (fun F => F.Reachable (rho V m k) (rho V m (k + 1))) :=
    window_restrict (h := heightT φ r₀ m) (t := lev r₀) (ρ := rho V m) hmono
    (fun k hk => heightT_rho φ r₀ m hk) (wiredW_symm φ r₀ m hβ) (wiredW_nonneg φ r₀ m hβ0)
    (wiredW_lip φ r₀ m hdiag hLip)
    (fun k hk u hu hne v => wiredW_junk φ hr0 m β hk u hu hne v) hk
  -- the weights
  have hE : restrW (KF φ r₀ m k) (wiredW φ r₀ m β) =
      mapW (mapW w (annulusCollapse (2 ^ k * r₀) Λ)) (jF φ r₀ m k) := by
    funext u v
    calc restrW (KF φ r₀ m k) (wiredW φ r₀ m β) u v
        = mapW (restrW (AkF φ r₀ m k) (liftW β)) (piW φ r₀ m) u v :=
          (mapW_restrW (liftW β) (liftW_symm hβ) (piW φ r₀ m) (AkF φ r₀ m k) (KF φ r₀ m k)
            (fun u' hu' => piW_mem_KF hφ hr0 hk hu')
            (fun u u' hu h => piW_preimage_KF hφ hr0 hk hu h) u v).symm
      _ = mapW (mapW w (iotaF φ r₀ m k)) (piW φ r₀ m) u v := by
          have : restrW (AkF φ r₀ m k) (liftW β) = mapW w (iotaF φ r₀ m k) := by
            funext a b; exact (mapW_wF_iotaF r₀ m k hdiag a b).symm
          rw [this]
      _ = mapW w (piW φ r₀ m ∘ iotaF φ r₀ m k) u v := mapW_comp _ _ _ _ _
      _ = mapW w (jF φ r₀ m k ∘ annulusCollapse (2 ^ k * r₀) Λ) u v := by
          have : piW φ r₀ m ∘ iotaF φ r₀ m k = jF φ r₀ m k ∘ annulusCollapse (2 ^ k * r₀) Λ := by
            funext z; exact (jF_annulusCollapse hφ hr0 hk z).symm
          rw [this]
      _ = _ := (mapW_comp _ _ _ _ _).symm
  have hjinj := jF_injective (φ := φ) (r₀ := r₀) (m := m) hr0 hk
  have hG := mapW_symm hwsymm (annulusCollapse (2 ^ k * r₀) Λ)
  have hGnn : ∀ a b, 0 ≤ mapW w (annulusCollapse (2 ^ k * r₀) Λ) a b :=
    mapW_nonneg (fun i j => hβ0 _ _) _
  have hemb := arborealProb_reach_embed (jF φ r₀ m k) hjinj
    (mapW_symm hG (jF φ r₀ m k)) hG (mapW_nonneg hGnn _)
    (fun u v huv => by
      rcases huv with h | h
      · exact mapW_not_range_left _ h v
      · exact mapW_not_range_right _ h u)
    (fun a b => mapW_inj_apply hjinj _ (mapW_diag _ _) a b) (Sum.inl true) (Sum.inl false)
  have hj0 : jF φ r₀ m k (Sum.inl false) = rho V m k := by simp [jF]
  have hj1 : jF φ r₀ m k (Sum.inl true) = rho V m (k + 1) := by simp [jF]
  rw [hj0, hj1] at hemb
  have step : connProb (wiredW φ r₀ m β) (wiredW_symm φ r₀ m hβ) (rho V m k) (rho V m (k + 1)) =
      connProb (mapW w (annulusCollapse (2 ^ k * r₀) Λ)) hG (Sum.inl false) (Sum.inl true) := by
    unfold connProb at hwin ⊢
    rw [hwin]
    rw [arborealProb_congr_weights hE _ (mapW_symm hG (jF φ r₀ m k))]
    exact hemb
  rw [step]
  exact hAN'

end

end ArborealDecay.Superpoly
