import PtCorr2.Restart.RestartBulk
import PtCorr2.Restart.RestartPairB
import Obs2.Flow.GamRem

/-!
# T5: the accumulated `a`-constant `u_a` along the restarted history (the `γ`-flow of the datum)

Along `obsHistFrom R P m δ` (Case (2), datum with `V_m(B)_a = α + βψ̄_aψ_a`), with
`γ^F_k = -ε(u^{obs}_{k,a})` (`gamF`):

* **`rpg_gam_succ`** (exact, copy of `gamA_succ` + `gamRem2_split`, `k ≥ m`):
  `γ^F_{k+1} = γ^F_k − ∑_Bε(V_k(B)_a) − β^F_k·c_k + gamWKF_k`, with the **bulk** factor
  `c_k = C_k(a,a) − ε(F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅))` (`rpgC`), the same for the restarted and every
  standard history (`bulkE2_histVF2_eq`): the restarted `γ`-flow is driven by `β^F_k` exactly as
  the reference one by `β_k`.
* `rpg_epsTot_succ`: no constants in `V_k` for `k > m`.
* **`rpg_gam_le`**: `|γ^F_n| ≤ |γ^F_m| + |∑_Bε(V_m(B)_a)| + ∑_{m ≤ k < n}(|β^F_k||c_k| + |gamWKF_k|)`
  (linear in the datum's sizes).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Gam

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (m : ℕ)
  (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))

/-- `γ^F_k = -ε(u^{obs}_{k,a})` along the restarted history. -/
def gamF (k : ℕ) : ℂ := -ε ((obsHistFrom R P m o' k t).u : SA .two (Lam 2 L N)).a

/-- `∑_Bε(V_k(B)_a)` along the restarted history. -/
def epsTotF (k : ℕ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k, ε (histVF2 R P m o' t k b : SA .two (Lam 2 L N)).a

/-- The `K`/`𝒲` part of the `γ`-remainder along the restarted history. -/
def gamWKF (k : ℕ) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) k,
      ε (expLC (histCovO R t k) (Q2O P k (histKF2 R P m o' t k) b : SA .two (Lam 2 L N)).a) +
    ∑ b ∈ blockIdx (L := L) (N := N) k,
      ε (EthO (histCovO R t k) (histWF2 R P m o' t k b) : SA .two (Lam 2 L N)).a

/-- The bulk factor of the `γ`-flow, `c_k = C_k(a,a) − ε(F_{C_k}(ψ̄_aψ_a, V'_k(Λ)_∅))` (for the
standard history from `o₀`). -/
def rpgC (o₀ : ObsSt .two L N) (k : ℕ) : ℂ :=
  histCovO R t k P.a P.a - ε (FC (histCovO R t k) (pbp P.a) (bulkE2 (histCovO R t)
    (histVO2 R P o₀ t) k))

/-- **The exact `γ`-flow of the restarted history.** -/
theorem rpg_gam_succ (h0 : o'.IsObs) (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) {k : ℕ} (hk : m ≤ k) :
    gamF R P m o' t (k + 1) = gamF R P m o' t k - epsTotF R P m o' t k -
      betaTot2 k (histVF2 R P m o' t k) * rpgC R P t o₀ k + gamWKF R P m o' t k := by
  have hform := hformF2 R P m o' t hf0 k hk
  have hu : ((obsHistFrom R P m o' (k + 1) t).u : SA .two (Lam 2 L N)).a =
      ((obsHistFrom R P m o' k t).u : SA .two (Lam 2 L N)).a +
        ∑ b ∈ blockIdx (L := L) (N := N) k, (upO P k (histCovO R t k) (histVF2 R P m o' t k)
          (histWF2 R P m o' t k) (histKF2 R P m o' t k) b : SA .two (Lam 2 L N)).a := by
    rw [obsHistFrom_succ hk]
    show ((obsHistFrom R P m o' k t).u + uObsTot P k (histCovO R t k) (histVF2 R P m o' t k)
      (histWF2 R P m o' t k) (histKF2 R P m o' t k) : SA .two (Lam 2 L N)).a = _
    rw [uObsTot, add_a, AddSubmonoidClass.coe_finsetSum, sum_a]
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) k,
      ε (upO P k (histCovO R t k) (histVF2 R P m o' t k) (histWF2 R P m o' t k)
        (histKF2 R P m o' t k) b : SA .two (Lam 2 L N)).a =
      ε (histVF2 R P m o' t k b : SA .two (Lam 2 L N)).a +
        mass2 (histVF2 R P m o' t k b : SA .two (Lam 2 L N)).a * histCovO R t k P.a P.a -
        (ε (expLC (histCovO R t k) (Q2O P k (histKF2 R P m o' t k) b : SA .two (Lam 2 L N)).a) +
          ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) k b)
            (blockSet (L := L) (N := N) k b)
            (SXO k (histCovO R t k) (histVF2 R P m o' t k) (histWF2 R P m o' t k)
              (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).a)) := by
    intro b _
    rw [upO_a, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_a, map_sub,
      map_sub, eps_expLC_loc2 (hform b)]
    ring
  -- the remainder split
  have hrem : ∑ b ∈ blockIdx (L := L) (N := N) k,
      (ε (expLC (histCovO R t k) (Q2O P k (histKF2 R P m o' t k) b : SA .two (Lam 2 L N)).a) +
        ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) k b)
          (blockSet (L := L) (N := N) k b)
          (SXO k (histCovO R t k) (histVF2 R P m o' t k) (histWF2 R P m o' t k)
            (Step2.Bp (L := L) (N := N) k b) : SA .two (Lam 2 L N)).a)) =
      gamWKF R P m o' t k + betaTot2 k (histVF2 R P m o' t k) *
        ε (FC (histCovO R t k) (pbp P.a)
          (VprLO k (histCovO R t k) (histVF2 R P m o' t k) : SA .two (Lam 2 L N)).e) := by
    unfold gamWKF
    rw [sum_add_distrib, eps_total_LS, eps_SbO_sum, eps_FC_VprLO P k _ _ hform]
    ring
  have hbulk : (VprLO k (histCovO R t k) (histVF2 R P m o' t k) : SA .two (Lam 2 L N)).e =
      bulkE2 (histCovO R t) (histVO2 R P o₀ t) k :=
    bulkE2_histVF2_eq R P m o' t h0 o₀ ho₀ k
  unfold gamF epsTotF rpgC
  rw [hu, map_add, map_sum, sum_congr rfl hb, sum_sub_distrib, sum_add_distrib, ← sum_mul, hrem,
    hbulk]
  unfold betaTot2
  ring

/-- `∑_Bε(V_{k+1}(B)_a) = 0` along the restarted history (`k ≥ m`). -/
theorem rpg_epsTot_succ {k : ℕ} (hk : m ≤ k) : epsTotF R P m o' t (k + 1) = 0 := by
  unfold epsTotF
  refine sum_eq_zero fun c' _ => ?_
  rw [histVF2_succ_a R P m o' t hk, Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum]
  exact sum_eq_zero fun b _ => eps_VpO_a _ _ _ _ _ _ _

/-- **The accumulated `a`-constant of the restarted history.** -/
theorem rpg_gam_le (h0 : o'.IsObs) (hf0 : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) :
    ∀ d : ℕ, ‖gamF R P m o' t (m + d)‖ ≤ ‖gamF R P m o' t m‖ +
      (if d = 0 then 0 else ‖epsTotF R P m o' t m‖) +
      ∑ i ∈ range d, (‖betaTot2 (m + i) (histVF2 R P m o' t (m + i))‖ *
        ‖rpgC R P t o₀ (m + i)‖ + ‖gamWKF R P m o' t (m + i)‖)
  | 0 => by simp
  | d + 1 => by
    have ih := rpg_gam_le h0 hf0 o₀ ho₀ d
    rw [← Nat.add_assoc, rpg_gam_succ R P m o' t h0 hf0 o₀ ho₀ (by omega), sum_range_succ]
    have hE : ‖epsTotF R P m o' t (m + d)‖ ≤ if d = 0 then ‖epsTotF R P m o' t m‖ else 0 := by
      rcases d with _ | d
      · simp
      · rw [← Nat.add_assoc, rpg_epsTot_succ R P m o' t (by omega)]; simp
    have h1 : ‖gamF R P m o' t (m + d) - epsTotF R P m o' t (m + d) -
        betaTot2 (m + d) (histVF2 R P m o' t (m + d)) * rpgC R P t o₀ (m + d) +
        gamWKF R P m o' t (m + d)‖ ≤ ‖gamF R P m o' t (m + d)‖ + ‖epsTotF R P m o' t (m + d)‖ +
        ‖betaTot2 (m + d) (histVF2 R P m o' t (m + d))‖ * ‖rpgC R P t o₀ (m + d)‖ +
        ‖gamWKF R P m o' t (m + d)‖ := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) (le_of_eq (norm_mul _ _)))) le_rfl)
    refine h1.trans ?_
    split_ifs at ih hE with hd
    · subst hd; simp at ih ⊢; linarith
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      linarith

end Gam

end

end PtCorr2
