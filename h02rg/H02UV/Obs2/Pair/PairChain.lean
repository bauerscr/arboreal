import Obs2.Flow.GamRem
import Obs2.Loc.PauliMass
import Obs2.Map.SwapHist

/-!
# The Case-(2) pair chain: the exact one-step identity for the pair constant `q = -ε(u^{obs}_{ab})`

One step of the second-order map with sources (`Obs2/Map/Map`), Case (2), points `a = P.a`,
`b = P.b`, covariance `C`, inputs `V, W, K`. All statements are exact and hold for arbitrary
point configurations.

* **Pauli split** (`eps_expLC_pauli`): `ε(e^{ℒ_C}F) = ε(F) + C(a,a)·m₂(F) + 𝔡_C^a(F)`, with the
  *Pauli defect* `𝔡_C^a(F) = ε(e^{ℒ_C}F) - ε(e^{ℒ_{C(a,a)J}}F)` (`J` all ones;
  `e^{ℒ_{cJ}} = 1 + cDD̄`, `m₂ = ε∘DD̄`). It vanishes when `C` is constant on the support of `F`
  (`expLC_congr_NX`), i.e. it only sees `C(a,a) - C(a,b)`-type differences.
* **The `ab` constant of a step** (`epsAB_uObsTot`): `∑_Bε(u^{obs}_{j+1}(B)_{ab}) =
  ∑_Bε(e^{ℒ_C}V(B)_{ab}) - ∑_Bε(e^{ℒ_C}Q(B)_{ab}) - ∑_Bε(loc^{ab}S(B_+)_{ab})`, and the same for
  `a` (`epsA_uObsTot`) and `b` (`epsB_uObsTot`, via `loc^b = loc^a` at `b` in Case (2)).
* **The double contraction** (`eps_FC_pbp_pbp`): `ε F_C(ψ̄_aψ_a, ψ̄_bψ_b) = -C(a,b)C(b,a)`; hence
  `ε F_C(V'(Λ)_a, V'(Λ)_b) = -β_aβ_bC(a,b)C(b,a)` (`eps_FC_VprLO_ab`) for `V_a`, `V_b` of the
  local forms `α + βψ̄_aψ_a`, `α + βψ̄_bψ_b`.
* **The Pauli-adjusted increment** (`pair_incr_pure`, `pair_step_id`): for the step increments
  `Δq = -∑ε(u_{ab})`, `Δγ_• = -∑ε(u_•)` and any accumulated `A_a, A_b`,
  `Δq + Δγ_aA_b + A_aΔγ_b + Δγ_aΔγ_b
     = -C(a,a)·r̃ + β_aβ_b(C(a,a)C(b,b) - C(a,b)C(b,a)) - 𝔡 + Rem`,
  `r̃ = r + β_aA_b + β_bA_a` (`r = ∑_Bm₂(V(B)_{ab})`, the marginal pair coupling), if
  `C(a,a) = C(b,b)` and `V` has no observable constants. `Rem` collects the activity and
  `𝒲` parts, the `F_C(V'_{ab}, V'_∅)` term and the `γ` remainders `ρ_a, ρ_b`.
  The two leading terms: the coupling `r̃` (zero at coalescence) and the determinant defect,
  which is the Pauli cancellation `(ψ̄_aψ_a)^2 = 0` in the merged picture.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

section Pure

variable {d L N : ℕ} [NeZero L]

/-! ### The Pauli split of `ε ∘ e^{ℒ_C}` -/

/-- `ε(e^{ℒ_{cJ}}F) = ε(F) + c·m₂(F)`. -/
theorem eps_expLC_J (c : ℂ) (F : Alg d L N) :
    ε (expLC (c • Jmat (Lam d L N)) F) = ε F + c * mass2 F := by
  rw [expLC_J, map_add, map_smul, LopC_J, ← mass2_eq_DDbar, smul_eq_mul]

/-- **The Pauli defect** `𝔡_C^a(F) = ε(e^{ℒ_C}F) - ε(e^{ℒ_{C(a,a)J}}F)`. -/
def pauliDef (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) (F : Alg d L N) : ℂ :=
  ε (expLC C F) - ε (expLC (C a a • Jmat (Lam d L N)) F)

/-- **Pauli split**: `ε(e^{ℒ_C}F) = ε(F) + C(a,a)m₂(F) + 𝔡_C^a(F)`. -/
theorem eps_expLC_pauli (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) (F : Alg d L N) :
    ε (expLC C F) = ε F + C a a * mass2 F + pauliDef C a F := by
  rw [pauliDef, eps_expLC_J]; ring


/-! ### The double contraction `ε F_C(ψ̄_aψ_a, ψ̄_bψ_b)` -/

theorem eps_DD_pbp (z x y : Lam d L N) :
    ε (D (x, -1) (D (y, 1) (pbp z : Alg d L N))) = if y = z ∧ x = z then -1 else 0 := by
  have e : (pbp z : Alg d L N) = -(ExteriorAlgebra.ι ℂ (ev ((z, 1) : Sf (Lam d L N))) *
      ExteriorAlgebra.ι ℂ (ev (z, -1))) := by
    show psibar z * psi z = _
    exact ψ_anticomm _ _
  rw [e, map_neg, map_neg, D_pair, D_ι]
  simp [ev, Pi.single_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem eps_DD_pbp' (z x y : Lam d L N) :
    ε (D (y, 1) (D (x, -1) (pbp z : Alg d L N))) = if y = z ∧ x = z then 1 else 0 := by
  have e : (pbp z : Alg d L N) = -(ExteriorAlgebra.ι ℂ (ev ((z, 1) : Sf (Lam d L N))) *
      ExteriorAlgebra.ι ℂ (ev (z, -1))) := by
    show psibar z * psi z = _
    exact ψ_anticomm _ _
  rw [e, map_neg, map_neg, D_pair, D_ι]
  simp [ev, Pi.single_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- **`ε F_C(ψ̄_aψ_a, ψ̄_bψ_b) = -C(a,b)C(b,a)`**. -/
theorem eps_FC_pbp_pbp (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a b : Lam d L N) :
    ε (FC C (pbp a) (pbp b)) = -(C a b * C b a) := by
  rw [eps_FC_pbp]
  simp only [eps_DD_pbp, eps_DD_pbp']
  simp [mul_ite, ite_and, sum_ite_eq']
  ring

/-! ### The constants of one step, componentwise -/

variable (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
  (V W : OFam .two d L N) (K : OAct .two d L N)

/-- The `σ_aσ_b` part of the observable constant of a block: `ε((u+V)_{j+1}(B)_{ab})`. -/
theorem upO_ab_eq (b : Fin d → ℕ) :
    (upO P j C V W K b : SA .two (Lam d L N)).ab =
      algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .two (Lam d L N)).ab) := by
  show (πobs (epsO (uVpO P j C V W K b)) : SA .two (Lam d L N)).ab = _
  rw [ab_πobs]; rfl

/-- The `σ_b` part of the observable constant of a block. -/
theorem upO_b_eq (b : Fin d → ℕ) :
    (upO P j C V W K b : SA .two (Lam d L N)).b =
      algebraMap ℂ (Alg d L N) (ε (uVpO P j C V W K b : SA .two (Lam d L N)).b) := by
  show cmp false (πobs (epsO (uVpO P j C V W K b)) : SA .two (Lam d L N)) = _
  rw [cmp_πobs]; rfl

/-- `(u+V)_{j+1}(B)_{ab} = e^{ℒ_C}V(B)_{ab} - e^{ℒ_C}Q(B)_{ab} - loc^{ab} S(B_+)_{ab}`. -/
theorem uVpO_ab (b : Fin d → ℕ) :
    (uVpO P j C V W K b : SA .two (Lam d L N)).ab =
      expLC C (V b : SA .two (Lam d L N)).ab - expLC C (Q2O P j K b : SA .two (Lam d L N)).ab -
        locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab := by
  have h2 : (uVpO P j C V W K b : SA .two (Lam d L N)).ab =
      (VprO C V b : SA .two (Lam d L N)).ab - (EthO C (Q2O P j K b) : SA .two (Lam d L N)).ab -
        (LSO P j C V W b : SA .two (Lam d L N)).ab := rfl
  rw [h2, VprO, (EthO_comp C _).2.2, (EthO_comp C _).2.2]; rfl

/-- `(u+V)_{j+1}(B)_b = e^{ℒ_C}V(B)_b - e^{ℒ_C}Q(B)_b - loc^b S(B_+)_b` (`loc^b = loc^a` at `b`). -/
theorem uVpO_b (b : Fin d → ℕ) :
    (uVpO P j C V W K b : SA .two (Lam d L N)).b =
      expLC C (V b : SA .two (Lam d L N)).b - expLC C (Q2O P j K b : SA .two (Lam d L N)).b -
        locAp Obs.Case.two P.b (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).b := by
  have h2 : (uVpO P j C V W K b : SA .two (Lam d L N)).b =
      (VprO C V b : SA .two (Lam d L N)).b - (EthO C (Q2O P j K b) : SA .two (Lam d L N)).b -
        (LSO P j C V W b : SA .two (Lam d L N)).b := rfl
  have hE : ∀ F : OE .two (Lam d L N), (EthO C F : SA .two (Lam d L N)).b =
      expLC C (F : SA .two (Lam d L N)).b := fun F => by
    have := (EthO_comp C F).2.1 false
    simpa only [cmp_false] using this
  rw [h2, VprO, hE, hE, ← locBp_two_eq_locAp]; rfl

/-- **`V_{j+1}(B)` has no `σ_aσ_b` constant**: `ε(V_{j+1}(B)_{ab}) = 0`. -/
theorem eps_VpO_ab (b : Fin d → ℕ) : ε (VpO P j C V W K b : SA .two (Lam d L N)).ab = 0 := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).ab = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
      (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
  rw [h1, halg, upO_ab_eq, sub_zero, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, sub_self]

/-- **`ε(V_{j+1}(B)_b) = 0`**. -/
theorem eps_VpO_b (b : Fin d → ℕ) : ε (VpO P j C V W K b : SA .two (Lam d L N)).b = 0 := by
  have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).b = 0 := by
    rw [Subalgebra.coe_algebraMap]; exact algebraMap_b _
  have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).b =
      (uVpO P j C V W K b : SA .two (Lam d L N)).b -
        ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
          SA .two (Lam d L N)).b - (upO P j C V W K b : SA .two (Lam d L N)).b := rfl
  rw [h1, halg, upO_b_eq, sub_zero, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply, sub_self]

/-! ### `loc^{ab}` preserves `ε` and distributes it over the blocks -/

theorem eps_Dt (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    ε (Dt X a b F) = 0 := by
  simp [Dt, dbar, dlt, pbp, psibar, psi, map_mul, eps_ψ]

theorem eps_locABt {X : Finset (Lam d L N)} {a : Lam d L N} (ha : a ∈ X) (b : Lam d L N)
    (F : Alg d L N) : ε (locABt X a b F) = ε F := by
  rw [locABt, map_add, eps_Dt, add_zero, locEven_single_eq' ha subset_rfl]
  simp [eps_pbp]

theorem eps_locABtX {P : ObsPts d L N} {X : Finset (Lam d L N)} (h : (X ∩ P.pts).Nonempty)
    (F : Alg d L N) : ε (locABtX X P.a P.b F) = ε F := by
  unfold locABtX
  split_ifs with ha
  · exact eps_locABt ha _ F
  · obtain ⟨x, hx⟩ := h
    rw [mem_inter] at hx
    have hb : P.b ∈ X := by
      rcases mem_insert.1 hx.2 with rfl | h'
      · exact absurd hx.1 ha
      · rw [mem_singleton] at h'; rw [← h']; exact hx.1
    exact eps_locABt hb _ F

/-- **`∑_{B ∈ 𝓑_j(X)} ε(loc^{ab}_{X,B}F) = ε(F)`** if `X` meets `{a, b}` (and `0` otherwise). -/
theorem eps_sum_blocks_ab (P : ObsPts d L N) {j : ℕ} {X : Finset (Lam d L N)} (hX : IsPolymer j X)
    (F : Alg d L N) :
    ∑ b ∈ blocks j X, ε (locABtXY P X (blockSet j b) F) =
      if (X ∩ P.pts).Nonempty then ε F else 0 := by
  have e : ∀ b ∈ blocks j X, ε (locABtXY P X (blockSet j b) F) =
      ((blockSet (L := L) (N := N) j b ∩ P.pts).card : ℂ) / ((X ∩ P.pts).card : ℂ) *
        ε (locABtX X P.a P.b F) := fun b _ => by
    rw [locABtXY, map_smul, smul_eq_mul]
  rw [sum_congr rfl e, ← sum_mul, ← sum_div]
  have hc : ∑ b ∈ blocks j X, ((blockSet (L := L) (N := N) j b ∩ P.pts).card : ℂ) =
      ((X ∩ P.pts).card : ℂ) := by
    rw [← Nat.cast_sum, ← card_biUnion]
    · rw [← biUnion_inter, biUnion_blocks hX]
    · intro b _ b' _ hbb'
      exact Disjoint.mono inter_subset_left inter_subset_left
        (pairwiseDisjoint_blockSet j (blocks j X) (by assumption) (by assumption) hbb')
  rw [hc]
  split_ifs with h
  · rw [div_self (Nat.cast_ne_zero.2 (card_ne_zero.2 h)), one_mul, eps_locABtX h]
  · rw [not_nonempty_iff_eq_empty.1 h, card_empty, Nat.cast_zero, div_zero, zero_mul]

/-- The `ab` part of `S(B_+)` on the `(j+1)`-blocks not meeting `{a, b}` (not localised). -/
def farAB : ℂ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    if (blockSet (L := L) (N := N) (j + 1) c' ∩ P.pts).Nonempty then 0 else
      ε (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab

/-- **The localisation cancels in `ε` (`ab` part)**:
`∑_B ε(loc^{ab}S(B_+)_{ab}) = ∑_B ε(S(B)_{ab}) - farAB`. -/
theorem eps_total_LS_ab :
    ∑ b ∈ blockIdx (L := L) (N := N) j,
        ε (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam d L N)).ab -
        farAB P j C V W := by
  rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j, farAB, ← sum_sub_distrib]
  refine sum_congr rfl fun c' hc' => ?_
  have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      ε (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) =
        ε (locABtXY P (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
          (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab) := by
    intro b hb
    rw [Bp_eq_of_mem hb]
  rw [sum_congr rfl e, eps_sum_blocks_ab P (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c'))]
  have hS : ε (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        ε (SbO j C V W b : SA .two (Lam d L N)).ab := by
    rw [SXO, AddSubmonoidClass.coe_finsetSum, sum_ab, map_sum]
  split_ifs <;> rw [hS] <;> ring

/-! ### The sharp second-order `ab` part -/

/-- `F_C(X, X)_{ab} = 2F_C(X_{ab}, X_∅) + 2F_C(X_a, X_b)` (Case (2)). -/
theorem FCO_self_ab {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    (X : OE .two Λ) :
    (FCO C X X : SA .two Λ).ab = (2 : ℂ) • FC C (X : SA .two Λ).ab (X : SA .two Λ).e +
      (2 : ℂ) • FC C (X : SA .two Λ).a (X : SA .two Λ).b := by
  have ha : inv' (X : SA .two Λ).a = (X : SA .two Λ).a := by
    have := X.par_a; simpa [Case.s] using this
  rw [FCO_ab]
  simp only [Case.s, one_smul, Case.tau_two]
  rw [FC_comm_even C X.par_e (X : SA .two Λ).ab, FC_comm_even C ha (X : SA .two Λ).b]
  rw [two_smul, two_smul]; abel

/-- **`∑_Bε(S(B)_{ab}) = εF_C(V'(Λ)_{ab}, V'(Λ)_∅) + εF_C(V'(Λ)_a, V'(Λ)_b) + ∑_Bε((𝔼θ𝒲(B))_{ab})`**
(sharp splitting). -/
theorem eps_SbO_sum_ab :
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam d L N)).ab =
      ε (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) +
        ε (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).b) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).ab := by
  rw [← map_sum, ← sum_ab, ← AddSubmonoidClass.coe_finsetSum, SbO_sum, Subalgebra.coe_add,
    Subalgebra.coe_smul, add_ab, smul_ab, FCO_self_ab, AddSubmonoidClass.coe_finsetSum,
    sum_ab, map_add, map_sum, smul_add, smul_smul, smul_smul, map_add, map_smul, map_smul]
  norm_num

/-- `ε(F_C(α + βψ̄_aψ_a, α' + β'ψ̄_bψ_b)) = -ββ'C(a,b)C(b,a)`. -/
theorem eps_FC_loc2_loc2 {a b : Lam d L N} {X Y : Alg d L N} (hX : Loc2Form a X)
    (hY : Loc2Form b Y) : ε (FC C X Y) = -(mass2 X * mass2 Y * (C a b * C b a)) := by
  rw [eps_FC_loc2 C hX]
  obtain ⟨α, β, rfl⟩ := hY
  rw [mass2_loc, FC_add_right, FC_smul_right, FC_smul_right, FC_one_right, smul_zero, zero_add,
    map_smul, smul_eq_mul, eps_FC_pbp_pbp]
  ring

/-! ### The `σ_b` analogues of `eps_total_LS`, `eps_SbO_sum` -/

theorem eps_total_LS_b :
    ∑ b ∈ blockIdx (L := L) (N := N) j,
        ε (locAp Obs.Case.two P.b (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).b) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam d L N)).b := by
  rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j]
  refine sum_congr rfl fun c' hc' => ?_
  have hne : (blockSet (L := L) (N := N) (j + 1) c').Nonempty := mem_blockIdx.1 hc'
  have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      ε (locAp Obs.Case.two P.b (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).b) =
        ε (locAp Obs.Case.two P.b (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
          (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).b) := by
    intro b hb
    rw [Bp_eq_of_mem hb]
  rw [sum_congr rfl e, eps_sum_blocks (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hne,
    SXO, AddSubmonoidClass.coe_finsetSum, sum_b, map_sum]

theorem eps_SbO_sum_b :
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (SbO j C V W b : SA .two (Lam d L N)).b =
      ε (FC C (VprLO j C V : SA .two (Lam d L N)).b (VprLO j C V : SA .two (Lam d L N)).e) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).b := by
  have hF : ∀ X : OE .two (Lam d L N), (FCO C X X : SA .two (Lam d L N)).b =
      (2 : ℂ) • FC C (X : SA .two (Lam d L N)).b (X : SA .two (Lam d L N)).e := fun X => by
    have h := FCO_cmp C false X X
    simp only [cmp_false, Case.tau_two] at h
    rw [h, FC_comm_even C X.par_e, two_smul]
  rw [← map_sum, ← sum_b, ← AddSubmonoidClass.coe_finsetSum, SbO_sum, Subalgebra.coe_add,
    Subalgebra.coe_smul, add_b, smul_b, hF, smul_smul, AddSubmonoidClass.coe_finsetSum,
    sum_b, map_add, map_sum]
  norm_num

/-! ### The step constants in couplings -/

/-- `β_b = ∑_Bm₂(V(B)_b)`. -/
def betaB2 : ℂ := ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (V b : SA .two (Lam d L N)).b

/-- **The marginal pair coupling** `r = ∑_Bm₂(V(B)_{ab})`. -/
def rAB2 : ℂ := ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (V b : SA .two (Lam d L N)).ab

/-- The Pauli defect of `V_{ab}`: `𝔡 = ∑_B 𝔡^a_C(V(B)_{ab})`. -/
def pdefAB2 : ℂ := ∑ b ∈ blockIdx (L := L) (N := N) j, pauliDef C P.a (V b : SA .two (Lam d L N)).ab

/-- The `K`, `𝒲` part of the `ab` constant. -/
def wkAB2 : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab) +
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).ab

/-- The `K`, `𝒲` part of the `σ_a` constant. -/
def wkA2 : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) +
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).a

/-- The `K`, `𝒲` part of the `σ_b` constant. -/
def wkB2 : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).b) +
    ∑ b ∈ blockIdx (L := L) (N := N) j, ε (EthO C (W b) : SA .two (Lam d L N)).b

theorem VprLO_a_form (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    Loc2Form P.a (VprLO j C V : SA .two (Lam d L N)).a ∧
      mass2 (VprLO j C V : SA .two (Lam d L N)).a = betaTot2 j V := by
  have hpr : ∀ b, (VprO C V b : SA .two (Lam d L N)).a = expLC C (V b : SA .two (Lam d L N)).a :=
    fun b => by
      have h0 := (EthO_comp C (V b)).2.1 true
      simp only [cmp_true] at h0
      rw [VprO, h0]
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_a]
  refine ⟨Loc2Form.sum _ fun b _ => by rw [hpr]; exact (hVa b).expLC C, ?_⟩
  rw [mass2_sum, betaTot2]
  refine sum_congr rfl fun b _ => ?_
  obtain ⟨α, β, hb⟩ := hVa b
  rw [hpr, hb, mass2_expLC_loc, mass2_loc]

theorem VprLO_b_form (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b) :
    Loc2Form P.b (VprLO j C V : SA .two (Lam d L N)).b ∧
      mass2 (VprLO j C V : SA .two (Lam d L N)).b = betaB2 j V := by
  have hpr : ∀ b, (VprO C V b : SA .two (Lam d L N)).b = expLC C (V b : SA .two (Lam d L N)).b :=
    fun b => by
      have h0 := (EthO_comp C (V b)).2.1 false
      simp only [cmp_false] at h0
      rw [VprO, h0]
  rw [VprLO, AddSubmonoidClass.coe_finsetSum, sum_b]
  refine ⟨Loc2Form.sum _ fun b _ => by rw [hpr]; exact (hVb b).expLC C, ?_⟩
  rw [mass2_sum, betaB2]
  refine sum_congr rfl fun b _ => ?_
  obtain ⟨α, β, hb⟩ := hVb b
  rw [hpr, hb, mass2_expLC_loc, mass2_loc]

/-- **The `ab` constant of a step**: `ε(u^{obs}_{j+1}(Λ)_{ab}) = ∑_Bε(V(B)_{ab}) + C(a,a)r + 𝔡 -
wkAB - εF_C(V'_{ab}, V'_∅) + farAB + β_aβ_bC(a,b)C(b,a)`. -/
theorem epsAB_uObsTot (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a)
    (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b) :
    ε (uObsTot P j C V W K : SA .two (Lam d L N)).ab =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).ab +
        C P.a P.a * rAB2 j V + pdefAB2 P j C V - wkAB2 P j C W K -
        ε (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) +
        farAB P j C V W + betaTot2 j V * betaB2 j V * (C P.a P.b * C P.b P.a) := by
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε (upO P j C V W K b : SA .two (Lam d L N)).ab =
        (ε (V b : SA .two (Lam d L N)).ab + C P.a P.a * mass2 (V b : SA .two (Lam d L N)).ab +
          pauliDef C P.a (V b : SA .two (Lam d L N)).ab) -
        ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab) -
        ε (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) := by
    intro b _
    rw [upO_ab_eq, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_ab,
      map_sub, map_sub, eps_expLC_pauli]
  rw [uObsTot, AddSubmonoidClass.coe_finsetSum, sum_ab, map_sum, sum_congr rfl hb,
    sum_sub_distrib, sum_sub_distrib, sum_add_distrib, sum_add_distrib, eps_total_LS_ab,
    eps_SbO_sum_ab, eps_FC_loc2_loc2 C (VprLO_a_form P j C V hVa).1 (VprLO_b_form P j C V hVb).1,
    (VprLO_a_form P j C V hVa).2, (VprLO_b_form P j C V hVb).2, ← mul_sum]
  unfold rAB2 pdefAB2 wkAB2
  ring

/-- **The `σ_a` constant of a step**: `ε(u^{obs}_{j+1}(Λ)_a) = ∑_Bε(V(B)_a) + β_aC(a,a) - wkA -
εF_C(V'_a, V'_∅)`. -/
theorem epsA_uObsTot (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    ε (uObsTot P j C V W K : SA .two (Lam d L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).a +
        betaTot2 j V * C P.a P.a - wkA2 P j C W K -
        ε (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e) := by
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε (upO P j C V W K b : SA .two (Lam d L N)).a =
        (ε (V b : SA .two (Lam d L N)).a + mass2 (V b : SA .two (Lam d L N)).a * C P.a P.a) -
        ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) -
        ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a) := by
    intro b _
    rw [upO_a, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_a,
      map_sub, map_sub, eps_expLC_loc2 (hVa b)]
  rw [uObsTot, AddSubmonoidClass.coe_finsetSum, sum_a, map_sum, sum_congr rfl hb,
    sum_sub_distrib, sum_sub_distrib, sum_add_distrib, eps_total_LS, eps_SbO_sum, ← sum_mul]
  unfold wkA2 betaTot2
  ring

/-- **The `σ_b` constant of a step**. -/
theorem epsB_uObsTot (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b) :
    ε (uObsTot P j C V W K : SA .two (Lam d L N)).b =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).b +
        betaB2 j V * C P.b P.b - wkB2 P j C W K -
        ε (FC C (VprLO j C V : SA .two (Lam d L N)).b (VprLO j C V : SA .two (Lam d L N)).e) := by
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε (upO P j C V W K b : SA .two (Lam d L N)).b =
        (ε (V b : SA .two (Lam d L N)).b + mass2 (V b : SA .two (Lam d L N)).b * C P.b P.b) -
        ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).b) -
        ε (locAp Obs.Case.two P.b (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).b) := by
    intro b _
    rw [upO_b_eq, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_b,
      map_sub, map_sub, eps_expLC_loc2 (hVb b)]
  rw [uObsTot, AddSubmonoidClass.coe_finsetSum, sum_b, map_sum, sum_congr rfl hb,
    sum_sub_distrib, sum_sub_distrib, sum_add_distrib, eps_total_LS_b, eps_SbO_sum_b, ← sum_mul]
  unfold wkB2 betaB2
  ring

/-! ### The Pauli-adjusted increment -/

/-- **Pure form of the Pauli-adjusted increment.** With `Δq = -(c_{aa}r + 𝔡 - X + β_aβ_bc_{ab}c_{ba})`,
`Δγ_a = -(β_ac_{aa} - ρ_a)`, `Δγ_b = -(β_bc_{aa} - ρ_b)`:
`Δq + Δγ_aA_b + A_aΔγ_b + Δγ_aΔγ_b = -c_{aa}(r + β_aA_b + β_bA_a)
  + β_aβ_b(c_{aa}^2 - c_{ab}c_{ba}) - 𝔡 + (X + ρ_a(A_b - β_bc_{aa}) + ρ_b(A_a - β_ac_{aa}) + ρ_aρ_b)`. -/
theorem pair_incr_pure (caa cab cba r pd X βa βb ρa ρb Aa Ab : ℂ) :
    -(caa * r + pd - X + βa * βb * (cab * cba)) + (-(βa * caa - ρa)) * Ab +
        Aa * (-(βb * caa - ρb)) + (-(βa * caa - ρa)) * (-(βb * caa - ρb)) =
      -(caa * (r + βa * Ab + βb * Aa)) + βa * βb * (caa * caa - cab * cba) - pd +
        (X + ρa * (Ab - βb * caa) + ρb * (Aa - βa * caa) + ρa * ρb) := by
  ring

/-- The `X` part of a step: `wkAB + εF_C(V'_{ab}, V'_∅) - farAB`. -/
def xAB2 : ℂ :=
  wkAB2 P j C W K +
    ε (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) -
    farAB P j C V W

/-- `ρ_a = wkA + εF_C(V'_a, V'_∅)`. -/
def rhoA2 : ℂ :=
  wkA2 P j C W K + ε (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e)

/-- `ρ_b = wkB + εF_C(V'_b, V'_∅)`. -/
def rhoB2 : ℂ :=
  wkB2 P j C W K + ε (FC C (VprLO j C V : SA .two (Lam d L N)).b (VprLO j C V : SA .two (Lam d L N)).e)

/-- **The Pauli-adjusted increment of one step** (exact). If `V` has no observable constants and
`C(a,a) = C(b,b)`, then for the step increments `Δq = -ε(u_{ab})`, `Δγ_• = -ε(u_•)` of
`u^{obs}_{j+1}(Λ)` and any `A_a`, `A_b`:
`Δq + Δγ_aA_b + A_aΔγ_b + Δγ_aΔγ_b = -C(a,a)(r + β_aA_b + β_bA_a)
  + β_aβ_b(C(a,a)^2 - C(a,b)C(b,a)) - 𝔡 + Rem`,
`Rem = X + ρ_a(A_b - β_bC(a,a)) + ρ_b(A_a - β_aC(a,a)) + ρ_aρ_b`. -/
theorem pair_step_id (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a)
    (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b)
    (h0ab : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).ab = 0)
    (h0a : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).a = 0)
    (h0b : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).b = 0)
    (hC : C P.b P.b = C P.a P.a) (Aa Ab : ℂ) :
    -ε (uObsTot P j C V W K : SA .two (Lam d L N)).ab +
        (-ε (uObsTot P j C V W K : SA .two (Lam d L N)).a) * Ab +
        Aa * (-ε (uObsTot P j C V W K : SA .two (Lam d L N)).b) +
        (-ε (uObsTot P j C V W K : SA .two (Lam d L N)).a) *
          (-ε (uObsTot P j C V W K : SA .two (Lam d L N)).b) =
      -(C P.a P.a * (rAB2 j V + betaTot2 j V * Ab + betaB2 j V * Aa)) +
        betaTot2 j V * betaB2 j V * (C P.a P.a * C P.a P.a - C P.a P.b * C P.b P.a) -
        pdefAB2 P j C V +
        (xAB2 P j C V W K + rhoA2 P j C V W K * (Ab - betaB2 j V * C P.a P.a) +
          rhoB2 P j C V W K * (Aa - betaTot2 j V * C P.a P.a) +
          rhoA2 P j C V W K * rhoB2 P j C V W K) := by
  have e1 : -ε (uObsTot P j C V W K : SA .two (Lam d L N)).ab =
      -(C P.a P.a * rAB2 j V + pdefAB2 P j C V - xAB2 P j C V W K +
        betaTot2 j V * betaB2 j V * (C P.a P.b * C P.b P.a)) := by
    rw [epsAB_uObsTot P j C V W K hVa hVb, h0ab, xAB2]; ring
  have e2 : -ε (uObsTot P j C V W K : SA .two (Lam d L N)).a =
      -(betaTot2 j V * C P.a P.a - rhoA2 P j C V W K) := by
    rw [epsA_uObsTot P j C V W K hVa, h0a, rhoA2]; ring
  have e3 : -ε (uObsTot P j C V W K : SA .two (Lam d L N)).b =
      -(betaB2 j V * C P.a P.a - rhoB2 P j C V W K) := by
    rw [epsB_uObsTot P j C V W K hVb, h0b, rhoB2, hC]; ring
  rw [e1, e2, e3]
  exact pair_incr_pure _ _ _ _ _ _ _ _ _ _ _ _

/-! ### The `m₂` flows of one step: `β_a`, `β_b`, `r` -/

/-- **The `m₂` Pauli defect** `𝔡₂(F) = m₂(e^{ℒ_C}F) - m₂(F)` (`m₂ ∘ e^{ℒ_{cJ}} = m₂`). -/
def pauliDef2 (C : Matrix (Lam d L N) (Lam d L N) ℂ) (F : Alg d L N) : ℂ :=
  mass2 (expLC C F) - mass2 F

theorem isHom_dbar (a b : Lam d L N) : IsHom 1 (dbar a b : Alg d L N) :=
  (isHom_ι _).sub (isHom_ι _)

theorem isHom_dlt (a b : Lam d L N) : IsHom 1 (dlt a b : Alg d L N) :=
  (isHom_ι _).sub (isHom_ι _)

/-- The `δ`-terms of `loc^{ab}` carry no `m₂`. -/
theorem mass2_Dt (X : Finset (Lam d L N)) (a b : Lam d L N) (F : Alg d L N) :
    mass2 (Dt X a b F) = 0 := by
  have h1 : mass2 (dbar a b * psi a : Alg d L N) = 0 := by
    rw [dbar, sub_mul, mass2_sub, mass2_psibar_psi, mass2_psibar_psi, sub_self]
  have h2 : mass2 (psibar a * dlt a b : Alg d L N) = 0 := by
    rw [dlt, mul_sub, mass2_sub, mass2_psibar_psi, mass2_psibar_psi, sub_self]
  have h3 : mass2 (dbar a b * dlt a b : Alg d L N) = 0 := by
    rw [dbar, dlt, sub_mul, mul_sub, mul_sub, mass2_sub, mass2_sub, mass2_sub, mass2_psibar_psi,
      mass2_psibar_psi, mass2_psibar_psi, mass2_psibar_psi]
    ring
  have h4 : mass2 (pbp a * (dbar a b * dlt a b) : Alg d L N) = 0 :=
    mass2_of_isHom ((((isHom_ι _).mul (isHom_ι _))).mul ((isHom_dbar a b).mul (isHom_dlt a b)))
      (by norm_num)
  simp only [Dt, mass2_add, mass2_smul, h1, h2, h3, h4, mul_zero, add_zero]

theorem mass2_locABtX {P : ObsPts d L N} {X : Finset (Lam d L N)} (h : (X ∩ P.pts).Nonempty)
    (F : Alg d L N) : mass2 (locABtX X P.a P.b F) = mass2 F := by
  have key : ∀ {a : Lam d L N} (b : Lam d L N), a ∈ X → mass2 (locABt X a b F) = mass2 F := by
    intro a b ha
    rw [locABt, mass2_add, mass2_Dt, add_zero, locEven_single_eq' ha subset_rfl, mass2_add,
      mass2_smul, mass2_smul, mass2_one, mass2_pbp]
    ring
  unfold locABtX
  split_ifs with ha
  · exact key _ ha
  · obtain ⟨x, hx⟩ := h
    rw [mem_inter] at hx
    have hb : P.b ∈ X := by
      rcases mem_insert.1 hx.2 with rfl | h'
      · exact absurd hx.1 ha
      · rw [mem_singleton] at h'; rw [← h']; exact hx.1
    exact key _ hb

/-- `∑_{B ∈ 𝓑_j(X)} m₂(loc^{ab}_{X,B}F) = m₂(F)` if `X` meets `{a, b}` (and `0` otherwise). -/
theorem mass2_sum_blocks_ab (P : ObsPts d L N) {j : ℕ} {X : Finset (Lam d L N)}
    (hX : IsPolymer j X) (F : Alg d L N) :
    ∑ b ∈ blocks j X, mass2 (locABtXY P X (blockSet j b) F) =
      if (X ∩ P.pts).Nonempty then mass2 F else 0 := by
  rw [← mass2_sum, locABtXY_sum_blocks P hX]
  split_ifs with h
  · rw [locABtXY_self P X h, mass2_locABtX h]
  · rw [locABtXY, not_nonempty_iff_eq_empty.1 h, card_empty, Nat.cast_zero, div_zero, zero_smul,
      mass2_zero]

/-- The `m₂` of the `ab` part of `S(B_+)` on the `(j+1)`-blocks not meeting `{a, b}`. -/
def farABm : ℂ :=
  ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
    if (blockSet (L := L) (N := N) (j + 1) c' ∩ P.pts).Nonempty then 0 else
      mass2 (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab

/-- The `K`, `𝒲` part of the `r` flow. -/
def eAB2 : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab) +
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (W b) : SA .two (Lam d L N)).ab

/-- The `K`, `𝒲` part of the `β_a` flow. -/
def eA2 : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (Q2O P j K b) : SA .two (Lam d L N)).a +
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (W b) : SA .two (Lam d L N)).a

/-- The `K`, `𝒲` part of the `β_b` flow. -/
def eB2 : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (Q2O P j K b) : SA .two (Lam d L N)).b +
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (W b) : SA .two (Lam d L N)).b

/-- The `m₂` Pauli defect of `V_{ab}`, summed. -/
def pdefM2 : ℂ := ∑ b ∈ blockIdx (L := L) (N := N) j, pauliDef2 C (V b : SA .two (Lam d L N)).ab

/-- **The `β_a` flow of one step**: `β_a' = β_a - m₂F_C(V'_a, V'_∅) - eA`. -/
theorem betaA_next (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    betaTot2 (j + 1) (Vnext2O P j C V W K) =
      betaTot2 j V -
        mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e) -
        eA2 P j C W K := by
  have h := total_step_pt P j C V W K mass2L mass2_algebraMap (locMass_two P.a)
  have e1 : betaTot2 (j + 1) (Vnext2O P j C V W K) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, mass2L (VpO P j C V W K b : SA .two (Lam d L N)).a := by
    rw [betaTot2, ← sum_blockIdx_succ j]
    refine sum_congr rfl fun c' _ => ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_a, mass2_sum]; rfl
  have e2 : ∑ b ∈ blockIdx (L := L) (N := N) j, mass2L (VprO C V b : SA .two (Lam d L N)).a =
      betaTot2 j V := by
    rw [betaTot2]
    refine sum_congr rfl fun b _ => ?_
    have h0 := (EthO_comp C (V b)).2.1 true
    simp only [cmp_true] at h0
    show mass2 (VprO C V b : SA .two (Lam d L N)).a = _
    obtain ⟨α, β, hb⟩ := hVa b
    rw [VprO, h0, hb, mass2_expLC_loc, mass2_loc]
  rw [e1, h, e2, eA2]; simp only [mass2L, LinearMap.coe_mk, AddHom.coe_mk]; ring

/-- **The `β_b` flow of one step** (the mirror of `betaA_next`). -/
theorem betaB_next (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b) :
    betaB2 (j + 1) (Vnext2O P j C V W K) =
      betaB2 j V -
        mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).b (VprLO j C V : SA .two (Lam d L N)).e) -
        eB2 P j C W K := by
  set P' : ObsPts d L N := ⟨P.b, P.a, P.Ra⟩
  have hP : P'.a = P.pt false := rfl
  have h := betaA_next P' j C (prjF false V) (prjF false W) (prjF false K) (fun b => hVb b)
  have ka : ∀ X : OE .two (Lam d L N), ((prjO false X : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).a = (X : SA .two (Lam d L N)).b := fun _ => rfl
  have ke : ∀ X : OE .two (Lam d L N), ((prjO false X : OE .two (Lam d L N)) :
      SA .two (Lam d L N)).e = (X : SA .two (Lam d L N)).e := fun _ => rfl
  have e1 : Vnext2O P' j C (prjF false V) (prjF false W) (prjF false K) =
      fun c' => prjO false (Vnext2O P j C V W K c') :=
    funext fun c' => (prj_Vnext2O false hP j C V W K c').symm
  have e2 : VprLO j C (prjF false V) = prjO false (VprLO j C V) := (prj_VprLO false j C V).symm
  have e3 : ∀ b, EthO C (Q2O P' j (prjF false K) b) = prjO false (EthO C (Q2O P j K b)) :=
    fun b => by rw [prjO_EthO, prj_Q2O false hP]
  have e4 : ∀ b, EthO C (prjF false W b) = prjO false (EthO C (W b)) :=
    fun b => by rw [prjO_EthO]; rfl
  simp only [betaTot2, eA2, e1, e2, e3, e4, ka, ke] at h
  simp only [betaB2, eB2]
  rw [h]
  simp only [prjF_apply, ka]

theorem mass2_SbO_sum_ab :
    ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (SbO j C V W b : SA .two (Lam d L N)).ab =
      mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) +
        mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).b) +
        ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (EthO C (W b) : SA .two (Lam d L N)).ab := by
  rw [← mass2_sum, ← sum_ab, ← AddSubmonoidClass.coe_finsetSum, SbO_sum, Subalgebra.coe_add,
    Subalgebra.coe_smul, add_ab, smul_ab, FCO_self_ab, AddSubmonoidClass.coe_finsetSum,
    sum_ab, mass2_add, mass2_sum, smul_add, smul_smul, smul_smul, mass2_add, mass2_smul,
    mass2_smul]
  norm_num

/-- `m₂(F_C(α + βψ̄_aψ_a, α' + β'ψ̄_bψ_b)) = -ββ'(C(a,b) + C(b,a))`. -/
theorem mass2_FC_loc2_loc2 {a b : Lam d L N} {X Y : Alg d L N} (hX : Loc2Form a X)
    (hY : Loc2Form b Y) : mass2 (FC C X Y) = -(mass2 X * mass2 Y * (C a b + C b a)) := by
  obtain ⟨α, β, rfl⟩ := hX
  obtain ⟨α', β', rfl⟩ := hY
  have e : (pbp b : Alg d L N) = -(psi b * psibar b) := by
    show psibar b * psi b = _
    exact ψ_anticomm _ _
  rw [mass2_loc, mass2_loc, FC_add_left, Step2.FC_const_left, zero_add, FC_smul_left,
    FC_add_right, FC_smul_right, FC_smul_right, FC_one_right, smul_zero, zero_add, e,
    ← neg_one_smul ℂ (psi b * psibar b), FC_smul_right, mass2_smul, mass2_smul, mass2_smul,
    mass2_FC_pbp_pair]
  ring

/-- **The `r` flow of one step**:
`r' = r + 𝔡₂ - eAB - m₂F_C(V'_{ab}, V'_∅) + β_aβ_b(C(a,b) + C(b,a)) + farABm`. -/
theorem rAB_next (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a)
    (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b) :
    rAB2 (j + 1) (Vnext2O P j C V W K) =
      rAB2 j V + pdefM2 j C V - eAB2 P j C W K -
        mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) +
        betaTot2 j V * betaB2 j V * (C P.a P.b + C P.b P.a) + farABm P j C V W := by
  have e1 : rAB2 (j + 1) (Vnext2O P j C V W K) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (VpO P j C V W K b : SA .two (Lam d L N)).ab := by
    rw [rAB2, ← sum_blockIdx_succ j]
    refine sum_congr rfl fun c' _ => ?_
    rw [Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_ab, mass2_sum]
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      mass2 (VpO P j C V W K b : SA .two (Lam d L N)).ab =
        (mass2 (V b : SA .two (Lam d L N)).ab + pauliDef2 C (V b : SA .two (Lam d L N)).ab) -
        mass2 (expLC C (Q2O P j K b : SA .two (Lam d L N)).ab) -
        mass2 (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) := by
    intro b _
    have halg : ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
        SA .two (Lam d L N)).ab = 0 := by
      rw [Subalgebra.coe_algebraMap]; exact algebraMap_ab _
    have h1 : (VpO P j C V W K b : SA .two (Lam d L N)).ab =
        (uVpO P j C V W K b : SA .two (Lam d L N)).ab -
          ((algebraMap ℂ (OE .two (Lam d L N)) (upB P j C V W K b) : OE .two (Lam d L N)) :
            SA .two (Lam d L N)).ab - (upO P j C V W K b : SA .two (Lam d L N)).ab := rfl
    rw [h1, halg, upO_ab_eq, sub_zero, mass2_sub, mass2_algebraMap, sub_zero, uVpO_ab, mass2_sub,
      mass2_sub, pauliDef2]
    ring
  have hL : ∑ b ∈ blockIdx (L := L) (N := N) j,
      mass2 (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
          (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) =
      ∑ b ∈ blockIdx (L := L) (N := N) j, mass2 (SbO j C V W b : SA .two (Lam d L N)).ab -
        farABm P j C V W := by
    rw [← sum_blockIdx_succ j, ← sum_blockIdx_succ j, farABm, ← sum_sub_distrib]
    refine sum_congr rfl fun c' hc' => ?_
    have e : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        mass2 (locABtXY P (Step2.Bp (L := L) (N := N) j b) (blockSet (L := L) (N := N) j b)
            (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).ab) =
          mass2 (locABtXY P (blockSet (L := L) (N := N) (j + 1) c') (blockSet j b)
            (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') : SA .two (Lam d L N)).ab) := by
      intro b hb
      rw [Bp_eq_of_mem hb]
    rw [sum_congr rfl e, mass2_sum_blocks_ab P (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c'))]
    have hS : mass2 (SXO j C V W (blockSet (L := L) (N := N) (j + 1) c') :
        SA .two (Lam d L N)).ab = ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
          mass2 (SbO j C V W b : SA .two (Lam d L N)).ab := by
      rw [SXO, AddSubmonoidClass.coe_finsetSum, sum_ab, mass2_sum]
    split_ifs <;> rw [hS] <;> ring
  rw [e1, sum_congr rfl hb, sum_sub_distrib, sum_sub_distrib, sum_add_distrib, hL,
    mass2_SbO_sum_ab, mass2_FC_loc2_loc2 C (VprLO_a_form P j C V hVa).1 (VprLO_b_form P j C V hVb).1,
    (VprLO_a_form P j C V hVa).2, (VprLO_b_form P j C V hVb).2]
  unfold rAB2 pdefM2 eAB2
  ring

/-! ### The flow of the Pauli-adjusted pair coupling `r̃` -/

/-- `m₂(F_C(α + βψ̄_aψ_a, e)) = β·m₂(F_C(ψ̄_aψ_a, e))`. -/
theorem mass2_FC_loc2 {a : Lam d L N} {X : Alg d L N} (hX : Loc2Form a X) (e : Alg d L N) :
    mass2 (FC C X e) = mass2 X * mass2 (FC C (pbp a) e) := by
  obtain ⟨α, β, rfl⟩ := hX
  rw [mass2_loc, FC_add_left, Step2.FC_const_left, zero_add, FC_smul_left, mass2_smul]

/-- **Pure form of the `r̃` flow.** With `β_a' = β_a(1-n_a) - e_a`, `β_b' = β_b(1-n_b) - e_b`,
`r' = r(1-n_a) - d + p - e + β_aβ_b(c_{ab}+c_{ba}) + f`, `A_a' = A_a - β_ac + ρ_a`,
`A_b' = A_b - β_bc + ρ_b`: `r' + β_a'A_b' + β_b'A_a' = (1-n_a)(r + β_aA_b + β_bA_a) + σ`. -/
theorem rtil_flow_pure (r βa βb na nb ea eb c cab cba d p e f ρa ρb Aa Ab : ℂ) :
    (r * (1 - na) - d + p - e + βa * βb * (cab + cba) + f) +
        (βa * (1 - na) - ea) * (Ab - βb * c + ρb) + (βb * (1 - nb) - eb) * (Aa - βa * c + ρa) =
      (1 - na) * (r + βa * Ab + βb * Aa) +
        (βa * βb * (cab + cba - 2 * c) + βa * βb * c * (na + nb) + (na - nb) * βb * Aa - d + p -
          e + f + (βa * (1 - na) - ea) * ρb + (βb * (1 - nb) - eb) * ρa - ea * (Ab - βb * c) -
          eb * (Aa - βa * c)) := by
  ring

/-- The vertex factor `n_a = m₂F_C(ψ̄_aψ_a, V'(Λ)_∅)` of one step. -/
def nA2 : ℂ := mass2 (FC C (pbp P.a) (VprLO j C V : SA .two (Lam d L N)).e)

/-- The vertex factor `n_b = m₂F_C(ψ̄_bψ_b, V'(Λ)_∅)` of one step. -/
def nB2 : ℂ := mass2 (FC C (pbp P.b) (VprLO j C V : SA .two (Lam d L N)).e)

/-- The non-local part of the vertex correction of `V'_{ab}`: `m₂F_C(V'_{ab}, V'_∅) - r n_a`. -/
def dR2 : ℂ :=
  mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e) -
    rAB2 j V * nA2 P j C V

/-- **The source of the `r̃` flow of one step** (all terms are defects or remainders):
`σ = β_aβ_b(C(a,b) + C(b,a) - 2C(a,a)) + β_aβ_bC(a,a)(n_a + n_b) + (n_a - n_b)β_bA_a - d_r + 𝔡₂
  - e_{ab} + f + β_a'ρ_b + β_b'ρ_a - e_a(A_b - β_bC(a,a)) - e_b(A_a - β_aC(a,a))`. -/
def rSrc (Aa Ab : ℂ) : ℂ :=
  betaTot2 j V * betaB2 j V * (C P.a P.b + C P.b P.a - 2 * C P.a P.a) +
    betaTot2 j V * betaB2 j V * C P.a P.a * (nA2 P j C V + nB2 P j C V) +
    (nA2 P j C V - nB2 P j C V) * betaB2 j V * Aa - dR2 P j C V + pdefM2 j C V -
    eAB2 P j C W K + farABm P j C V W +
    (betaTot2 j V * (1 - nA2 P j C V) - eA2 P j C W K) * rhoB2 P j C V W K +
    (betaB2 j V * (1 - nB2 P j C V) - eB2 P j C W K) * rhoA2 P j C V W K -
    eA2 P j C W K * (Ab - betaB2 j V * C P.a P.a) - eB2 P j C W K * (Aa - betaTot2 j V * C P.a P.a)

/-- **The `r̃` flow of one step** (exact): if `V` has no `σ_a`, `σ_b` constants and
`C(a,a) = C(b,b)`, then with `A_•' = A_• - ε(u_•)`:
`r' + β_a'A_b' + β_b'A_a' = (1 - n_a)(r + β_aA_b + β_bA_a) + σ`. -/
theorem rtil_step (hVa : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a)
    (hVb : ∀ b, Loc2Form P.b (V b : SA .two (Lam d L N)).b)
    (h0a : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).a = 0)
    (h0b : ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).b = 0)
    (hC : C P.b P.b = C P.a P.a) (Aa Ab : ℂ) :
    rAB2 (j + 1) (Vnext2O P j C V W K) +
        betaTot2 (j + 1) (Vnext2O P j C V W K) *
          (Ab - ε (uObsTot P j C V W K : SA .two (Lam d L N)).b) +
        betaB2 (j + 1) (Vnext2O P j C V W K) *
          (Aa - ε (uObsTot P j C V W K : SA .two (Lam d L N)).a) =
      (1 - nA2 P j C V) * (rAB2 j V + betaTot2 j V * Ab + betaB2 j V * Aa) +
        rSrc P j C V W K Aa Ab := by
  have ha : mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e)
      = betaTot2 j V * nA2 P j C V := by
    rw [mass2_FC_loc2 C (VprLO_a_form P j C V hVa).1, (VprLO_a_form P j C V hVa).2, nA2]
  have hb : mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).b (VprLO j C V : SA .two (Lam d L N)).e)
      = betaB2 j V * nB2 P j C V := by
    rw [mass2_FC_loc2 C (VprLO_b_form P j C V hVb).1, (VprLO_b_form P j C V hVb).2, nB2]
  have e1 := betaA_next P j C V W K hVa
  have e2 := betaB_next P j C V W K hVb
  have e3 := rAB_next P j C V W K hVa hVb
  have e4 := epsA_uObsTot P j C V W K hVa
  have e5 := epsB_uObsTot P j C V W K hVb
  rw [ha] at e1
  rw [hb] at e2
  rw [h0a] at e4
  rw [h0b, hC] at e5
  have hd : mass2 (FC C (VprLO j C V : SA .two (Lam d L N)).ab (VprLO j C V : SA .two (Lam d L N)).e)
      = rAB2 j V * nA2 P j C V + dR2 P j C V := by rw [dR2]; ring
  rw [hd] at e3
  rw [e1, e2, e3, e4, e5, rSrc]
  unfold rhoA2 rhoB2
  linear_combination rtil_flow_pure (rAB2 j V) (betaTot2 j V) (betaB2 j V) (nA2 P j C V)
    (nB2 P j C V) (eA2 P j C W K) (eB2 P j C W K) (C P.a P.a) (C P.a P.b) (C P.b P.a) (dR2 P j C V)
    (pdefM2 j C V) (eAB2 P j C W K) (farABm P j C V W)
    (wkA2 P j C W K + ε (FC C (VprLO j C V : SA .two (Lam d L N)).a (VprLO j C V : SA .two (Lam d L N)).e))
    (wkB2 P j C W K + ε (FC C (VprLO j C V : SA .two (Lam d L N)).b (VprLO j C V : SA .two (Lam d L N)).e))
    Aa Ab

/-! ### A discrete Gronwall bound for `r̃` relative to the vertex -/

/-- **Relative Gronwall bound.** If `r_{k+1} = (1-n_k)r_k + σ_k`, `β_{k+1} = (1-n_k)β_k - e_k`,
`r_j = 0`, `β_{k+1} ≠ 0`, `‖σ_k‖ ≤ s_k‖β_{k+1}‖`, `‖e_k‖ ≤ ε_k‖β_{k+1}‖` (`s, ε ≥ 0`), then
`‖r_k‖ ≤ (∑_{j≤i<k}s_i)∏_{j≤i<k}(1+ε_i)·‖β_k‖`. -/
theorem rel_gronwall (r β n σ e : ℕ → ℂ) (s ε : ℕ → ℝ) (j m : ℕ) (hr0 : r j = 0)
    (hs0 : ∀ k, 0 ≤ s k) (hε0 : ∀ k, 0 ≤ ε k)
    (hr : ∀ k, j ≤ k → k < m → r (k + 1) = (1 - n k) * r k + σ k)
    (hβ : ∀ k, j ≤ k → k < m → β (k + 1) = (1 - n k) * β k - e k)
    (hβ0 : ∀ k, j ≤ k → k < m → β (k + 1) ≠ 0)
    (hσ : ∀ k, j ≤ k → k < m → ‖σ k‖ ≤ s k * ‖β (k + 1)‖)
    (he : ∀ k, j ≤ k → k < m → ‖e k‖ ≤ ε k * ‖β (k + 1)‖) :
    ∀ k, j ≤ k → k ≤ m → ‖r k‖ ≤ (∑ i ∈ Ico j k, s i) * (∏ i ∈ Ico j k, (1 + ε i)) * ‖β k‖ := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; simp [hr0]
  | succ k hk ih0 =>
    intro hkm
    have hkm' : k < m := by omega
    have ih := ih0 hkm'.le
    set S := ∑ i ∈ Ico j k, s i
    set Pp := ∏ i ∈ Ico j k, (1 + ε i)
    have hS : 0 ≤ S := sum_nonneg fun i _ => hs0 i
    have hP1 : 1 ≤ Pp := by
      have := Finset.prod_le_prod (s := Ico j k) (f := fun _ => (1 : ℝ)) (g := fun i => 1 + ε i)
        (fun _ _ => zero_le_one) (fun i _ => by linarith [hε0 i])
      simpa using this
    have hb := hβ0 k hk hkm'
    have hbn : 0 < ‖β (k + 1)‖ := norm_pos_iff.2 hb
    -- r_{k+1} = (β_{k+1} + e_k)·(r_k/β_k) + σ_k when β_k ≠ 0; handle β_k = 0 separately
    have key : ‖r (k + 1)‖ ≤ (S * Pp * (1 + ε k) + s k) * ‖β (k + 1)‖ := by
      by_cases hbk : β k = 0
      · have hrk : r k = 0 := by
          have := ih; rw [hbk, norm_zero, mul_zero] at this; exact norm_le_zero_iff.1 this
        rw [hr k hk hkm', hrk, mul_zero, zero_add]
        refine (hσ k hk hkm').trans ?_
        have : 0 ≤ S * Pp * (1 + ε k) * ‖β (k + 1)‖ :=
          mul_nonneg (mul_nonneg (mul_nonneg hS (by linarith)) (by linarith [hε0 k])) (norm_nonneg _)
        nlinarith
      · have e1 : (1 - n k) * r k = (β (k + 1) + e k) * (r k / β k) := by
          rw [hβ k hk hkm']; field_simp; ring
        have hq : ‖r k / β k‖ ≤ S * Pp := by
          rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hbk)]; exact ih
        rw [hr k hk hkm', e1]
        calc ‖(β (k + 1) + e k) * (r k / β k) + σ k‖
            ≤ (‖β (k + 1)‖ + ‖e k‖) * ‖r k / β k‖ + ‖σ k‖ := by
              refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
          _ ≤ (‖β (k + 1)‖ + ε k * ‖β (k + 1)‖) * (S * Pp) + s k * ‖β (k + 1)‖ := by
              have h1 : ‖β (k + 1)‖ + ‖e k‖ ≤ ‖β (k + 1)‖ + ε k * ‖β (k + 1)‖ := by
                linarith [he k hk hkm']
              have h2 := mul_le_mul h1 hq (norm_nonneg _)
                (by have := hε0 k; have := norm_nonneg (β (k + 1)); nlinarith)
              linarith [hσ k hk hkm']
          _ = (S * Pp * (1 + ε k) + s k) * ‖β (k + 1)‖ := by ring
    refine key.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [sum_Ico_succ_top hk, prod_Ico_succ_top hk]
    have hsk := hs0 k
    have h1 : s k ≤ s k * (Pp * (1 + ε k)) := by
      have : 1 ≤ Pp * (1 + ε k) := by nlinarith [hε0 k]
      nlinarith
    nlinarith

end Pure

section Hist

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R))

theorem histVO2_b (k : ℕ) (b : Fin 2 → ℕ) :
    (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).b :=
  emb_add_cmp false _ _

theorem histVO2_ab (k : ℕ) (b : Fin 2 → ℕ) :
    (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).ab =
      ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).ab :=
  zero_add _

theorem histVO2_succ_b (k : ℕ) (c' : Fin 2 → ℕ) :
    (histVO2 R P o₀ t (k + 1) c' : SA .two (Lam 2 L N)).b =
      (Vnext2O P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
        (histKO2 R P o₀ t k) c' : SA .two (Lam 2 L N)).b := by
  rw [histVO2_b, obsHist_succ]
  exact piobs_cmp false _

theorem histVO2_succ_ab (k : ℕ) (c' : Fin 2 → ℕ) :
    (histVO2 R P o₀ t (k + 1) c' : SA .two (Lam 2 L N)).ab =
      (Vnext2O P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
        (histKO2 R P o₀ t k) c' : SA .two (Lam 2 L N)).ab := by
  rw [histVO2_ab, obsHist_succ]
  exact piobs_ab _

/-- **`V_k(B)_b = α + βψ̄_bψ_b` at every scale** (the mirror `prj_obsHist` of `obsHist_hform2`). -/
theorem obsHist_hform2_b (h0 : ∀ b, Loc2Form P.b (o₀.V b : SA .two (Lam 2 L N)).b) (k : ℕ)
    (b : Fin 2 → ℕ) : Loc2Form P.b (histVO2 R P o₀ t k b : SA .two (Lam 2 L N)).b := by
  set P' : ObsPts 2 L N := ⟨P.b, P.a, P.Ra⟩
  have hP : P'.a = P.pt false := rfl
  have h0' : ∀ b, Loc2Form P'.a ((prjSt false o₀).V b : SA .two (Lam 2 L N)).a := fun b => h0 b
  have hf := obsHist_hform2 R P' (prjSt false o₀) t h0' k b
  rw [histVO2_a, ← prj_obsHist R false hP o₀ t k] at hf
  rw [histVO2_b]
  exact hf

/-- `u^{obs}_{k+1} = u^{obs}_k + u^{obs}_{k+1}(Λ)` (the constant of step `k`). -/
theorem obsHist_u_succ (k : ℕ) :
    (obsHist R P o₀ (k + 1) t).u = (obsHist R P o₀ k t).u +
      uObsTot P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
        (histKO2 R P o₀ t k) := by
  rw [obsHist_succ]; rfl

/-- `q_k = -ε(u^{obs}_{k,ab})`. -/
def qAB2 (k : ℕ) : ℂ := -ε ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).ab

/-- `γ_{b,k} = -ε(u^{obs}_{k,b})`. -/
def gamB2 (k : ℕ) : ℂ := -ε ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).b

theorem epsAB_hist_succ (k : ℕ) :
    ∑ b ∈ blockIdx (L := L) (N := N) (k + 1),
      ε (histVO2 R P o₀ t (k + 1) b : SA .two (Lam 2 L N)).ab = 0 := by
  refine sum_eq_zero fun c' _ => ?_
  rw [histVO2_succ_ab, Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_ab, map_sum]
  exact sum_eq_zero fun b _ => eps_VpO_ab _ _ _ _ _ _ _

theorem epsB_hist_succ (k : ℕ) :
    ∑ b ∈ blockIdx (L := L) (N := N) (k + 1),
      ε (histVO2 R P o₀ t (k + 1) b : SA .two (Lam 2 L N)).b = 0 := by
  refine sum_eq_zero fun c' _ => ?_
  rw [histVO2_succ_b, Vnext2O, AddSubmonoidClass.coe_finsetSum, sum_b, map_sum]
  exact sum_eq_zero fun b _ => eps_VpO_b _ _ _ _ _ _ _

/-- **The Pauli-adjusted increment along the history** (`k ≥ 1`, `C_k(a,a) = C_k(b,b)`):
`Δq_k + Δγ_{a,k}A_b + A_aΔγ_{b,k} + Δγ_{a,k}Δγ_{b,k} = -C_k(a,a)r̃_k
  + β_aβ_b(C_k(a,a)^2 - C_k(a,b)C_k(b,a)) - 𝔡_k + Rem_k`, `r̃_k = r_k + β_{a,k}A_b + β_{b,k}A_a`. -/
theorem pair_hist_step (h0a : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a)
    (h0b : ∀ b, Loc2Form P.b (o₀.V b : SA .two (Lam 2 L N)).b) {k : ℕ} (hk : 1 ≤ k)
    (hC : histCovO R t k P.b P.b = histCovO R t k P.a P.a) (Aa Ab : ℂ) :
    (qAB2 R P o₀ t (k + 1) - qAB2 R P o₀ t k) + (gamA R P o₀ t (k + 1) - gamA R P o₀ t k) * Ab +
        Aa * (gamB2 R P o₀ t (k + 1) - gamB2 R P o₀ t k) +
        (gamA R P o₀ t (k + 1) - gamA R P o₀ t k) * (gamB2 R P o₀ t (k + 1) - gamB2 R P o₀ t k) =
      -(histCovO R t k P.a P.a * (rAB2 k (histVO2 R P o₀ t k) +
          betaTot2 k (histVO2 R P o₀ t k) * Ab + betaB2 k (histVO2 R P o₀ t k) * Aa)) +
        betaTot2 k (histVO2 R P o₀ t k) * betaB2 k (histVO2 R P o₀ t k) *
          (histCovO R t k P.a P.a * histCovO R t k P.a P.a -
            histCovO R t k P.a P.b * histCovO R t k P.b P.a) -
        pdefAB2 P k (histCovO R t k) (histVO2 R P o₀ t k) +
        (xAB2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) +
          rhoA2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
              (histKO2 R P o₀ t k) *
            (Ab - betaB2 k (histVO2 R P o₀ t k) * histCovO R t k P.a P.a) +
          rhoB2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
              (histKO2 R P o₀ t k) *
            (Aa - betaTot2 k (histVO2 R P o₀ t k) * histCovO R t k P.a P.a) +
          rhoA2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
              (histKO2 R P o₀ t k) *
            rhoB2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
              (histKO2 R P o₀ t k)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hu := obsHist_u_succ R P o₀ t (k' + 1)
  have dq : qAB2 R P o₀ t (k' + 1 + 1) - qAB2 R P o₀ t (k' + 1) =
      -ε (uObsTot P (k' + 1) (histCovO R t (k' + 1)) (histVO2 R P o₀ t (k' + 1))
        (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1)) : SA .two (Lam 2 L N)).ab := by
    unfold qAB2; rw [hu, Subalgebra.coe_add, add_ab, map_add]; ring
  have da : gamA R P o₀ t (k' + 1 + 1) - gamA R P o₀ t (k' + 1) =
      -ε (uObsTot P (k' + 1) (histCovO R t (k' + 1)) (histVO2 R P o₀ t (k' + 1))
        (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1)) : SA .two (Lam 2 L N)).a := by
    unfold gamA; rw [hu, Subalgebra.coe_add, add_a, map_add]; ring
  have db : gamB2 R P o₀ t (k' + 1 + 1) - gamB2 R P o₀ t (k' + 1) =
      -ε (uObsTot P (k' + 1) (histCovO R t (k' + 1)) (histVO2 R P o₀ t (k' + 1))
        (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1)) : SA .two (Lam 2 L N)).b := by
    unfold gamB2; rw [hu, Subalgebra.coe_add, add_b, map_add]; ring
  rw [dq, da, db]
  exact pair_step_id P (k' + 1) _ _ _ _ (obsHist_hform2 R P o₀ t h0a (k' + 1))
    (obsHist_hform2_b R P o₀ t h0b (k' + 1)) (epsAB_hist_succ R P o₀ t k')
    (epsTot2_succ R P o₀ t k') (epsB_hist_succ R P o₀ t k') hC Aa Ab

/-! ### Telescoping above coalescence -/

/-- `D_{j,k} = (q_k - q_j) + (γ_{a,k} - γ_{a,j})(γ_{b,k} - γ_{b,j})`: the Pauli-adjusted
accumulated pair constant from `j` to `k`. -/
def pairD2 (j k : ℕ) : ℂ :=
  (qAB2 R P o₀ t k - qAB2 R P o₀ t j) +
    (gamA R P o₀ t k - gamA R P o₀ t j) * (gamB2 R P o₀ t k - gamB2 R P o₀ t j)

/-- **The Pauli-adjusted pair coupling** `r̃_{j,k} = r_k + β_{a,k}(γ_{b,k} - γ_{b,j}) +
β_{b,k}(γ_{a,k} - γ_{a,j})` (`r̃_{j,j} = r_j`, `= 0` at coalescence). -/
def rTil2 (j k : ℕ) : ℂ :=
  rAB2 k (histVO2 R P o₀ t k) +
    betaTot2 k (histVO2 R P o₀ t k) * (gamB2 R P o₀ t k - gamB2 R P o₀ t j) +
    betaB2 k (histVO2 R P o₀ t k) * (gamA R P o₀ t k - gamA R P o₀ t j)

/-- The determinant defect `β_aβ_b(C(a,a)^2 - C(a,b)C(b,a))` of step `k`. -/
def detDef2 (k : ℕ) : ℂ :=
  betaTot2 k (histVO2 R P o₀ t k) * betaB2 k (histVO2 R P o₀ t k) *
    (histCovO R t k P.a P.a * histCovO R t k P.a P.a -
      histCovO R t k P.a P.b * histCovO R t k P.b P.a)

/-- The Pauli defect of `V_k(B)_{ab}`, summed. -/
def pdef2 (k : ℕ) : ℂ := pdefAB2 P k (histCovO R t k) (histVO2 R P o₀ t k)

/-- The remainder of step `k`: `X + ρ_a(A_b - β_bC(a,a)) + ρ_b(A_a - β_aC(a,a)) + ρ_aρ_b`. -/
def pairRem2 (j k : ℕ) : ℂ :=
  xAB2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) +
    rhoA2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) *
      ((gamB2 R P o₀ t k - gamB2 R P o₀ t j) -
        betaB2 k (histVO2 R P o₀ t k) * histCovO R t k P.a P.a) +
    rhoB2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) *
      ((gamA R P o₀ t k - gamA R P o₀ t j) -
        betaTot2 k (histVO2 R P o₀ t k) * histCovO R t k P.a P.a) +
    rhoA2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k) *
      rhoB2 P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k)

/-- The increment of step `k`: `-C_k(a,a)r̃_{j,k} + detDef_k - 𝔡_k + Rem_{j,k}`. -/
def pairInc2 (j k : ℕ) : ℂ :=
  -(histCovO R t k P.a P.a * rTil2 R P o₀ t j k) + detDef2 R P o₀ t k - pdef2 R P o₀ t k +
    pairRem2 R P o₀ t j k

theorem pairD2_self (j : ℕ) : pairD2 R P o₀ t j j = 0 := by
  unfold pairD2; ring

/-- **One step of `D`** (`k ≥ 1`, `C_k(b,b) = C_k(a,a)`). -/
theorem pairD2_succ (h0a : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a)
    (h0b : ∀ b, Loc2Form P.b (o₀.V b : SA .two (Lam 2 L N)).b) (j : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hC : histCovO R t k P.b P.b = histCovO R t k P.a P.a) :
    pairD2 R P o₀ t j (k + 1) = pairD2 R P o₀ t j k + pairInc2 R P o₀ t j k := by
  have h := pair_hist_step R P o₀ t h0a h0b hk hC (gamA R P o₀ t k - gamA R P o₀ t j)
    (gamB2 R P o₀ t k - gamB2 R P o₀ t j)
  unfold pairInc2 rTil2 detDef2 pdef2 pairRem2
  unfold pairD2
  linear_combination h

/-- **`D_{j,n} = ∑_{j ≤ k < n} inc_k`** (`j ≥ 1`, `C_k(b,b) = C_k(a,a)`). -/
theorem pairD2_eq_sum (h0a : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a)
    (h0b : ∀ b, Loc2Form P.b (o₀.V b : SA .two (Lam 2 L N)).b) {j : ℕ} (hj : 1 ≤ j)
    (hC : ∀ k, histCovO R t k P.b P.b = histCovO R t k P.a P.a) :
    ∀ n, j ≤ n → pairD2 R P o₀ t j n = ∑ k ∈ Ico j n, pairInc2 R P o₀ t j k
  | n, hn => by
    induction n with
    | zero => have : j = 0 := by omega
              omega
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hn with h | h
      · rw [← h, Ico_self, sum_empty, pairD2_self]
      · rw [pairD2_succ R P o₀ t h0a h0b j (by omega) (hC n), ih (by omega),
          sum_Ico_succ_top (by omega)]

/-- The source of the `r̃` flow at step `k` along the history. -/
def rSrc2 (j k : ℕ) : ℂ :=
  rSrc P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k)
    (gamA R P o₀ t k - gamA R P o₀ t j) (gamB2 R P o₀ t k - gamB2 R P o₀ t j)

/-- The vertex factor `n_{a,k}` along the history. -/
def nA2h (k : ℕ) : ℂ := nA2 P k (histCovO R t k) (histVO2 R P o₀ t k)

/-- **The `r̃` flow along the history** (`k ≥ 1`, `C_k(b,b) = C_k(a,a)`):
`r̃_{j,k+1} = (1 - n_{a,k})r̃_{j,k} + σ_{j,k}`. -/
theorem rTil2_succ (h0a : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a)
    (h0b : ∀ b, Loc2Form P.b (o₀.V b : SA .two (Lam 2 L N)).b) (j : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hC : histCovO R t k P.b P.b = histCovO R t k P.a P.a) :
    rTil2 R P o₀ t j (k + 1) = (1 - nA2h R P o₀ t k) * rTil2 R P o₀ t j k + rSrc2 R P o₀ t j k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hu := obsHist_u_succ R P o₀ t (k' + 1)
  have ga : gamA R P o₀ t (k' + 1 + 1) - gamA R P o₀ t j = (gamA R P o₀ t (k' + 1) -
      gamA R P o₀ t j) - ε (uObsTot P (k' + 1) (histCovO R t (k' + 1)) (histVO2 R P o₀ t (k' + 1))
        (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1)) : SA .two (Lam 2 L N)).a := by
    unfold gamA; rw [hu, Subalgebra.coe_add, add_a, map_add]; ring
  have gb : gamB2 R P o₀ t (k' + 1 + 1) - gamB2 R P o₀ t j = (gamB2 R P o₀ t (k' + 1) -
      gamB2 R P o₀ t j) - ε (uObsTot P (k' + 1) (histCovO R t (k' + 1)) (histVO2 R P o₀ t (k' + 1))
        (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1)) : SA .two (Lam 2 L N)).b := by
    unfold gamB2; rw [hu, Subalgebra.coe_add, add_b, map_add]; ring
  have hr : rAB2 (k' + 1 + 1) (histVO2 R P o₀ t (k' + 1 + 1)) =
      rAB2 (k' + 1 + 1) (Vnext2O P (k' + 1) (histCovO R t (k' + 1)) (histVO2 R P o₀ t (k' + 1))
        (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1))) := by
    unfold rAB2; exact sum_congr rfl fun c' _ => by rw [histVO2_succ_ab]
  have hba : betaTot2 (k' + 1 + 1) (histVO2 R P o₀ t (k' + 1 + 1)) =
      betaTot2 (k' + 1 + 1) (Vnext2O P (k' + 1) (histCovO R t (k' + 1))
        (histVO2 R P o₀ t (k' + 1)) (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1))) := by
    unfold betaTot2; exact sum_congr rfl fun c' _ => by rw [histVO2_succ_a]
  have hbb : betaB2 (k' + 1 + 1) (histVO2 R P o₀ t (k' + 1 + 1)) =
      betaB2 (k' + 1 + 1) (Vnext2O P (k' + 1) (histCovO R t (k' + 1))
        (histVO2 R P o₀ t (k' + 1)) (histWO2 R P o₀ t (k' + 1)) (histKO2 R P o₀ t (k' + 1))) := by
    unfold betaB2; exact sum_congr rfl fun c' _ => by rw [histVO2_succ_b]
  unfold rTil2
  rw [ga, gb, hr, hba, hbb]
  exact rtil_step P (k' + 1) _ _ _ _ (obsHist_hform2 R P o₀ t h0a (k' + 1))
    (obsHist_hform2_b R P o₀ t h0b (k' + 1)) (epsTot2_succ R P o₀ t k')
    (epsB_hist_succ R P o₀ t k') hC _ _

theorem obsInit_two_form_b (V : OCoup .two) (b : Fin 2 → ℕ) :
    Loc2Form P.b ((obsInit .two V P).V b : SA .two (Lam 2 L N)).b := by
  have e : ((obsInit .two V P).V b : SA .two (Lam 2 L N)).b =
      ind (P.b ∈ blockSet (L := L) (N := N) 0 b) •
        (algebraMap ℂ (Grassmann.N (Lam 2 L N)) (-OCoup2.gb V) -
          OCoup2.mub V • (psibar P.b * psi P.b)) := rfl
  rw [e]
  refine ⟨ind (P.b ∈ blockSet (L := L) (N := N) 0 b) * (-OCoup2.gb V),
    ind (P.b ∈ blockSet (L := L) (N := N) 0 b) * (-OCoup2.mub V), ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, pbp]
  module

/-- `r̃_{j,j} = 0` when `V_j` has no `ab` part (coalescence, `obsHist_coal_valid`). -/
theorem rTil2_self_zero {j : ℕ} (h : ∀ B, ((obsHist R P o₀ j t).V B : SA .two (Lam 2 L N)).ab = 0) :
    rTil2 R P o₀ t j j = 0 := by
  unfold rTil2 rAB2
  simp only [histVO2_ab, h, sub_self, mul_zero, add_zero]
  exact sum_eq_zero fun _ _ => mass2_zero

/-- The `K`, `𝒲` part `e_{a,k}` of the `β_a` flow along the history. -/
def eA2h (k : ℕ) : ℂ := eA2 P k (histCovO R t k) (histWO2 R P o₀ t k) (histKO2 R P o₀ t k)

/-- **The `β_a` flow along the history**: `β_{a,k+1} = (1 - n_{a,k})β_{a,k} - e_{a,k}`. -/
theorem betaA_hist_succ (h0a : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a) (k : ℕ) :
    betaTot2 (k + 1) (histVO2 R P o₀ t (k + 1)) =
      (1 - nA2h R P o₀ t k) * betaTot2 k (histVO2 R P o₀ t k) - eA2h R P o₀ t k := by
  have hba : betaTot2 (k + 1) (histVO2 R P o₀ t (k + 1)) =
      betaTot2 (k + 1) (Vnext2O P k (histCovO R t k) (histVO2 R P o₀ t k) (histWO2 R P o₀ t k)
        (histKO2 R P o₀ t k)) := by
    unfold betaTot2; exact sum_congr rfl fun c' _ => by rw [histVO2_succ_a]
  have hv := obsHist_hform2 R P o₀ t h0a k
  rw [hba, betaA_next P k _ _ _ _ hv, mass2_FC_loc2 _ (VprLO_a_form P k _ _ hv).1,
    (VprLO_a_form P k _ _ hv).2]
  unfold nA2h nA2 eA2h
  ring

/-- **`r̃` relative to the vertex** (discrete Gronwall along the history): if the sources and the
`K`, `𝒲` parts of the `β_a` flow are relatively small, `‖σ_{j,k}‖ ≤ s_k‖β_{a,k+1}‖`,
`‖e_{a,k}‖ ≤ ε_k‖β_{a,k+1}‖`, then `‖r̃_{j,k}‖ ≤ (∑s)∏(1+ε)‖β_{a,k}‖` for `j ≤ k ≤ m`. -/
theorem rTil2_rel_bound (h0a : ∀ b, Loc2Form P.a (o₀.V b : SA .two (Lam 2 L N)).a)
    (h0b : ∀ b, Loc2Form P.b (o₀.V b : SA .two (Lam 2 L N)).b) {j m : ℕ} (hj : 1 ≤ j)
    (hC : ∀ k, histCovO R t k P.b P.b = histCovO R t k P.a P.a)
    (hcoal : ∀ B, ((obsHist R P o₀ j t).V B : SA .two (Lam 2 L N)).ab = 0) (s ε : ℕ → ℝ)
    (hs0 : ∀ k, 0 ≤ s k) (hε0 : ∀ k, 0 ≤ ε k)
    (hβ0 : ∀ k, j ≤ k → k < m → betaTot2 (k + 1) (histVO2 R P o₀ t (k + 1)) ≠ 0)
    (hσ : ∀ k, j ≤ k → k < m →
      ‖rSrc2 R P o₀ t j k‖ ≤ s k * ‖betaTot2 (k + 1) (histVO2 R P o₀ t (k + 1))‖)
    (he : ∀ k, j ≤ k → k < m →
      ‖eA2h R P o₀ t k‖ ≤ ε k * ‖betaTot2 (k + 1) (histVO2 R P o₀ t (k + 1))‖) :
    ∀ k, j ≤ k → k ≤ m → ‖rTil2 R P o₀ t j k‖ ≤
      (∑ i ∈ Ico j k, s i) * (∏ i ∈ Ico j k, (1 + ε i)) * ‖betaTot2 k (histVO2 R P o₀ t k)‖ :=
  rel_gronwall (fun k => rTil2 R P o₀ t j k) (fun k => betaTot2 k (histVO2 R P o₀ t k))
    (nA2h R P o₀ t) (rSrc2 R P o₀ t j) (eA2h R P o₀ t) s ε j m
    (rTil2_self_zero R P o₀ t hcoal) hs0 hε0
    (fun k hk _ => rTil2_succ R P o₀ t h0a h0b j (by omega) (hC k))
    (fun k _ _ => betaA_hist_succ R P o₀ t h0a k) hβ0 hσ he

end Hist

end

end Obs2
