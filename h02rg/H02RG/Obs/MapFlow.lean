import Obs.MapSupp
import Obs.Norm

/-!
# The `ab` components below the coalescence scale (proof of Lemma `lem:Vobs-bd`)

Along the flow of the observable renormalisation group map started with `r_{a,0} = r_{b,0} = 0`
(Case (1)), resp. `η₀ = r_{a,0} = r_{b,0} = 0` (Case (2)) (the `u` parts `q_a, q_b, γ` are not
inputs of the map), and with
`K₀` in `𝒩^obs_sym` (`InKO … False …`, e.g. `K₀(X) = 1_{X = ∅}`), the `ab` components of
`V_j(B)` and of `K_j(X)`, `X ∈ 𝒮_j`, vanish for `j < j_ab` (`flow_ab`, `flow_ab_coal`).

The mechanism (finite range): if `C_{j+1}(a,b) = 0` and no small set has both `a` and `b` in its
neighbourhood (`Far j a b`, which holds for `j < j_ab` when `L ≥ 2^{d+3}`, `far_of_lt_coal`),
then
* `K_j(X)_{ab} = 0` for small `X` (from `K_j(X) ∈ 𝒩^obs(X^□)`, `ab_eq_zero_of_far`), so
  `Q^obs` has no `ab` part and the new `q_a, q_b, η, r_a, r_b` vanish (`abZero_nextObs`);
* all ingredients lie in `𝒩^obs_sym` and so does `K_{j+1}` (`InKO_KnextO`, `flow_step`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L N : ℕ} [NeZero L]

/-- No small set has both `a` and `b` in its small set neighbourhood. -/
def Far (j : ℕ) (a b : Lam d L N) : Prop :=
  ∀ Y, IsSmall j Y → ¬ (a ∈ nbhd j Y ∧ b ∈ nbhd j Y)

/-- `Far` below the coalescence scale. -/
theorem far_of_lt_coal (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} {a b : Lam d L N} (hj : j < coal L a b) :
    Far j a b := by
  rintro Y hY ⟨ha, hb⟩
  obtain ⟨x, hx, h1⟩ := exists_near_of_mem_nbhd ha
  obtain ⟨y, hy, h2⟩ := exists_near_of_mem_nbhd hb
  have h3 := supNorm_le_of_isSmall hY hx hy
  have e : a - b = (a - x) + ((x - y) + (y - b)) := by abel
  have h4 := supNorm_add_le (a - x) ((x - y) + (y - b))
  have h5 := supNorm_add_le (x - y) (y - b)
  rw [supNorm_sub_comm] at h2
  have h6 : supNorm (a - b) ≤ 3 * (2 ^ d * L ^ j) := by rw [e]; omega
  have h7 := pow_le_of_lt_coal hj
  have h8 : (supNorm (a - b) : ℝ) ≤ 3 * (2 ^ d * (L : ℝ) ^ j) := by exact_mod_cast h6
  have hL' : (2 : ℝ) ^ (d + 3) ≤ L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) j
  have h9 : (L : ℝ) ^ (j + 1) = L * L ^ j := by ring
  have h10 : (2 : ℝ) ^ (d + 3) = 8 * 2 ^ d := by ring
  have h11 : (0 : ℝ) < 2 ^ d := by positivity
  nlinarith

/-- `C_{j+1}(a, b) = 0` below the coalescence scale. -/
theorem C_eq_zero_of_lt_coal {j : ℕ} {ℓ₀ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℝ}
    (hC : GoodCov j ℓ₀ C) (hjN : j + 1 < N) {a b : Lam d L N} (hj : j < coal L a b) :
    C a b = 0 :=
  hC.range hjN a b (pow_le_of_lt_coal hj)

section Step

variable {c : Case} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {Vb : Vcoup} {Vo : Coup c}
  {K : Finset (Lam d L N) → OE c (Lam d L N)} {a b : Lam d L N}

/-- `K_j(X)_{ab} = 0` for small `X` if `K_j ∈ 𝒩^obs` and `Far`. -/
theorem ab_eq_zero_of_far (hK : InKO c False a b j K) (hfar : Far j a b) {Y : Finset (Lam d L N)}
    (hY : IsSmall j Y) : (K Y : SA c (Lam d L N)).ab = 0 := by
  obtain ⟨⟨-, -, -, -, h5, h6⟩, -⟩ := hK Y ⟨hY.1, hY.2.1⟩
  by_cases ha : a ∈ nbhd j Y
  · have hb : b ∉ nbhd j Y := fun hb => hfar Y hY ⟨ha, hb⟩
    exact (h6 (by simpa using hb)).2
  · exact (h5 (by simpa using ha)).2

theorem mass2_zero : mass2 (0 : Alg d L N) = 0 := by simp [mass2]

/-- The `ab` part of `Q^obs` vanishes if `K^{ab} = 0` on small sets. -/
theorem Qcoup_abZero (h : ∀ Y, IsSmall j Y → (K Y : SA c (Lam d L N)).ab = 0) :
    AbZero c (Qcoup c j K a b) := by
  have hs : ∀ x, ∀ Y ∈ smallAt j x, (K Y : SA c (Lam d L N)).ab = 0 := fun _ Y hY =>
    h Y (mem_smallSets.1 (mem_filter.1 hY).1)
  have h1 : ∀ x, ∑ Y ∈ smallAt j x, ε ((K Y : SA c (Lam d L N)).ab) / cardAB a b Y = 0 :=
    fun x => sum_eq_zero fun Y hY => by rw [hs x Y hY, map_zero, zero_div]
  have h2 : ∀ x, ∑ Y ∈ smallAt j x, mass2 ((K Y : SA c (Lam d L N)).ab) / cardAB a b Y = 0 :=
    fun x => sum_eq_zero fun Y hY => by rw [hs x Y hY, mass2_zero, zero_div]
  by_cases hj : j + 1 < N
  · cases c
    · simp only [AbZero, Qcoup, if_pos hj]
      exact ⟨by rw [h1, neg_zero], by rw [h1, neg_zero], h2 a, h2 b⟩
    · simp only [AbZero, Qcoup, if_pos hj]
      exact ⟨by rw [h1, neg_zero], by rw [h1, neg_zero], trivial, h2 a, h2 b⟩
  · rw [Qcoup_of_not hj]
    cases c
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The `V` part has no `ab` couplings: `r_a = r_b = 0`, resp. `η = r_a = r_b = 0`. -/
def AbZeroV : (c : Case) → Coup c → Prop
  | .one, V => Coup1.ra V = 0 ∧ Coup1.rb V = 0
  | .two, V => Coup2.eta V = 0 ∧ Coup2.ra V = 0 ∧ Coup2.rb V = 0

theorem abZero_toV_iff (c : Case) (V : Coup c) : AbZero c (Coup.toV c V) ↔ AbZeroV c V := by
  cases c
  · exact ⟨fun h => h.2.2, fun h => ⟨rfl, rfl, h⟩⟩
  · exact ⟨fun h => h.2.2, fun h => ⟨rfl, rfl, h⟩⟩

theorem abZero_toV (c : Case) {V : Coup c} (h : AbZero c V) : AbZero c (Coup.toV c V) := by
  cases c
  · exact ⟨rfl, rfl, h.2.2⟩
  · exact ⟨rfl, rfl, h.2.2⟩

theorem abZero_toU (c : Case) {V : Coup c} (h : AbZero c V) : AbZero c (Coup.toU c V) := by
  cases c
  · exact ⟨h.1, h.2.1, rfl, rfl⟩
  · exact ⟨h.1, h.2.1, rfl, rfl, rfl⟩

/-- **No new `ab` couplings below the coalescence scale**: if `C(a,b) = 0`, `V_j` has no
`ab` couplings and `K_j^{ab} = 0` on small sets, then `(u + V)^obs_{j+1}` has none
(`q_{x,j+1} = η_{j+1} = r_{x,j+1} = 0`). -/
theorem abZero_nextObs (hCab : C a b = 0) (hVo : AbZeroV c Vo)
    (h : ∀ Y, IsSmall j Y → (K Y : SA c (Lam d L N)).ab = 0) :
    AbZero c (nextObs C j Vo K a b) := by
  have hQ := Qcoup_abZero (a := a) (b := b) h
  cases c
  · obtain ⟨hqa, hqb, hra, hrb⟩ := hQ
    obtain ⟨hVa, hVb⟩ : Coup1.ra Vo = 0 ∧ Coup1.rb Vo = 0 := hVo
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [nextObs, Wcoup, Coup.next, Coup.sub, Coup.toV, Coup1.next, hCab, hqa, hqb, hra, hrb,
        hVa, hVb]
  · obtain ⟨hqa, hqb, he, hra, hrb⟩ := hQ
    obtain ⟨hVe, hVa, hVb⟩ := hVo
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [nextObs, Wcoup, Coup.next, Coup.sub, Coup.toV, Coup2.next, hCab, hqa, hqb, he, hra,
        hrb, hVe, hVa, hVb]

theorem abZeroV_toV (c : Case) {V : Coup c} (h : AbZero c V) : AbZeroV c (Coup.toV c V) := by
  cases c
  · exact h.2.2
  · exact h.2.2

theorem coupLoc_of_abZero {P : Prop} {W : Coup c} (h : AbZero c W) : CoupLoc c P a b j W := by
  refine ⟨Or.inl ?_, Or.inr (Or.inl h)⟩
  cases c
  · rfl
  · exact h.2.2.1

/-- **One step below the coalescence scale**: `(u + V)^obs_{j+1}` has no `ab` couplings and
`K_{j+1} ∈ 𝒩^obs_sym`. -/
theorem flow_step (hd : 1 ≤ d) (hCab : C a b = 0) (hfar : Far j a b)
    (hK : InKO c False a b j K) (hVo : AbZeroV c Vo) :
    AbZero c (nextObs C j Vo K a b) ∧ InKO c False a b (j + 1) (KnextO j C Vb Vo K a b) := by
  have hab := fun Y (hY : IsSmall j Y) => ab_eq_zero_of_far hK hfar hY
  have hn := abZero_nextObs hCab hVo hab
  refine ⟨hn, InKO_KnextO hd ⟨hK, fun _ => hab, coupLoc_of_abZero ((abZero_toV_iff c Vo).2 hVo),
    coupLoc_of_abZero (abZero_toV c hn), coupLoc_of_abZero (abZero_toU c hn)⟩⟩

end Step

/-! ### Along the flow -/

section Flow

variable {c : Case} (a b : Lam d L N)

/-- **The `ab` components vanish below the coalescence scale** along a flow of the observable
map: if `C_{j+1}(a,b) = 0` and `Far j a b` for `j < J`, the flow starts with no `ab` couplings
(`r_{a,0} = r_{b,0} = 0`, resp. `η₀ = r_{a,0} = r_{b,0} = 0`) and `K₀ ∈ 𝒩^obs_sym`, then for `j ≤ J`: `V_j` has no `ab`
couplings (so `(V_j(B))_{ab} = 0`) and `K_j ∈ 𝒩^obs_sym`; hence `K_j(X)_{ab} = 0` for small
`X` whenever `Far j a b`. -/
theorem flow_ab (hd : 1 ≤ d) (Cs : ℕ → Matrix (Lam d L N) (Lam d L N) ℝ) (Vb : ℕ → Vcoup)
    (Vo : ℕ → Coup c) (K : ℕ → Finset (Lam d L N) → OE c (Lam d L N))
    (hVo : ∀ j, Vo (j + 1) = Coup.toV c (nextObs (Cs j) j (Vo j) (K j) a b))
    (hK : ∀ j X, IsConn (j + 1) X → K (j + 1) X = KnextO j (Cs j) (Vb j) (Vo j) (K j) a b X)
    (h0 : AbZeroV c (Vo 0)) (hK0 : InKO c False a b 0 (K 0)) {J : ℕ}
    (hC : ∀ j < J, Cs j a b = 0) (hfar : ∀ j < J, Far j a b) :
    ∀ j ≤ J, AbZeroV c (Vo j) ∧ InKO c False a b j (K j) := by
  intro j hj
  induction j with
  | zero => exact ⟨h0, hK0⟩
  | succ j ih =>
    obtain ⟨hV, hKj⟩ := ih (by omega)
    obtain ⟨hn, hK'⟩ := flow_step (Vb := Vb j) hd (hC j (by omega)) (hfar j (by omega)) hKj hV
    refine ⟨?_, fun X hX => ?_⟩
    · rw [hVo]; exact abZeroV_toV c hn
    · rw [hK j X hX]; exact hK' X hX

end Flow

end

end Obs
