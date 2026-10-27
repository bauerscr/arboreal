import Obs.LocObsContract

/-!
# Proposition `prop:Loc-obs`: localisation with observables

We work with the observable components `F_a, F_b, F_{ab} ∈ 𝒩(Λ)` (the bulk component `F_∅` is
treated by Proposition `prop:Loc`, `Loc.Loc_bound`, `Loc.Loc_contract`), with the operators
`locA c a`, `locB c b`, `locAB a b` of `Obs.LocObsDef` (`c : ObsCase` is Case (1) or (2)).

## Weights (`e:ellsigma`)
`wA c j = ℓ_{a,j} = ℓ_{b,j}` (`ℓ_j^{-1}` in Case (1), `ℓ_j^{-2}` in Case (2)) and
`wAB c jab j = ℓ_{ab,j}` (`ℓ_j^{-2}`, resp. `ℓ_j^{-2} ℓ_{j ∧ j_{ab}}^{-2}`), with `ℓ_j = ellj`.
The weights are functions of the scale `j` only: on the left of the contraction estimate the
weights at scale `j + 1` are `ℓ_{a,j+1} = ℓ_{j+1}^{-1}` etc. (not `(2ℓ_{j+1})^{-1}`), which is the
larger (hence stronger) choice.  `obsNorm c jab k ℓ F_a F_b F_{ab} =
ℓ_{a,k} ‖F_a‖_{T_k(ℓ)} + ℓ_{b,k} ‖F_b‖_{T_k(ℓ)} + ℓ_{ab,k} ‖F_{ab}‖_{T_k(ℓ)}` is the observable part
of `e:Tphi-obs` (evaluated in `T_k(ℓ)`, so that `T_{j+1}(2ℓ_{j+1})` is `obsNorm … (j+1) (2ℓ_{j+1})`).
`j_{ab} = +∞` can be represented by any `jab ≥ N`.

## Results
For `d ≥ 3`, `L ≥ L₀(d) = 2^{d+3} + 8d + 1`, `j < N`, `ℓ₀ > 0`, small `Y ⊆ X`, `F_• ∈ 𝒩(X^□)`:
* (i) `locObs_bound`: `‖Loc_{X,Y} F‖ ≤ C̄ ‖F‖` in `obsNorm` at `(j, ℓ_j)` (componentwise:
  `locA_bound`, `locB_bound`, `locAB_bound`, valid for every `ℓ > 0`);
* (ii) `locObs_contract`: for `U(1)`-invariant components,
  `obsNorm (j+1) (2ℓ_{j+1}) ((1 - Loc_X) F) ≤ C̄ L^{-1} obsNorm j ℓ_j F`, provided `j_{ab} ≤ j` or
  `F_{ab} = 0`, and the observable points of each nonzero component lie in `X`
  (componentwise, unweighted: `locA_contract` etc. with rates `θ L^{-1} = L^{-d_+^a - 1}`, resp.
  `θ^2 L^{-1} = L^{-d_+ - 1}`, `θ = ℓ_{j+1}/ℓ_j = L^{-(d-2)/2}`);
* (iii) `locA_eq_sum`, `locB_eq_sum`, `locAB_eq_sum`: `Loc_X = ∑_i Loc_{X,X_i}`;
* (iv) `locA_image_one`, `locB_image_one`, `locA_image_two`, `locB_image_two`, `locAB_image`,
  `locAB_image_ab`: the image of `Loc_{X,B}` consists of the monomials of `def:cVobs` at the
  points of `B ∩ {a, b}`;
* locality: `locA_mem`, `locB_mem`, `locAB_mem`: `Loc_{X,Y} F ∈ 𝒩(Y ∩ {a,b})`.

## Deviations
* **Rate in (ii).**  We prove `C̄ L^{-1}` for the weighted norms: the relative gain of the first
  monomials not in the image (`ψ̄` with one gradient, resp. `ψ̄ψ` with one gradient, dimension
  `d_+ + 1`, and the monomials of higher degree, which gain at least `L^{-(d-2)} ≤ L^{-1}`).  The
  text's `L^{-d_+}` in `e:Loc-obs-contract` is not dimensionally meaningful for the observable
  components (the weights lose exactly `L^{d_+}`, as the text remarks); the unweighted
  componentwise estimates `‖(1 - loc) F_•‖_{T_{j+1}(2ℓ_{j+1})} ≤ C̄ L^{-d_+ - 1} ‖F_•‖_{T_j(ℓ_j)}`
  are `locA_contract` etc.
* **Observable points in `X`.**  If `a ∉ X` then `loc^a_{X∩{a}} = 0`, and (ii) can only hold for
  `F_a = 0`; this is automatic in the text's setting (`σ_a` occurs in `K(X)` only for `a ∈ X`) and
  is an explicit hypothesis here (`a ∈ X ∨ F_a = 0`, `(a ∈ X ∨ b ∈ X) ∨ F_{ab} = 0`).
* **`U(1)` invariance** of the components is expressed by charges (`HasCharge`): in Case (1)
  `F_a` has charge `1` (one more `ψ̄`), `F_b` charge `-1`, `F_{ab}` charge `0`; in Case (2) all
  charges are `0`.  See also the deviations in `Obs.LocObsDef` (definition via the
  `U(1)`-compatible image, the form of (iv)).
* Equivariance is not formalised.
-/

namespace Obs.LocObs

noncomputable section

open Finset Grassmann FRD Loc

/-! ### Weights -/

/-- `ℓ_{a,j} = ℓ_{b,j}` (`e:ellsigma`). -/
def wA (c : ObsCase) (d : ℕ) (L ℓ₀ : ℝ) (j : ℕ) : ℝ :=
  match c with
  | .one => (ellj d L ℓ₀ j)⁻¹
  | .two => (ellj d L ℓ₀ j)⁻¹ ^ 2

/-- `ℓ_{ab,j}` (`e:ellsigma`). -/
def wAB (c : ObsCase) (d : ℕ) (L ℓ₀ : ℝ) (jab j : ℕ) : ℝ :=
  match c with
  | .one => (ellj d L ℓ₀ j)⁻¹ ^ 2
  | .two => (ellj d L ℓ₀ j)⁻¹ ^ 2 * (ellj d L ℓ₀ (min j jab))⁻¹ ^ 2

variable {d L N : ℕ} [NeZero L]

/-- The observable part of the norm `e:Tphi-obs`, at scale `k` and field parameter `ℓ`. -/
def obsNorm (c : ObsCase) (ℓ₀ : ℝ) (jab k : ℕ) (ℓ : ℝ) (Fa Fb Fab : Alg d L N) : ENNReal :=
  ENNReal.ofReal (wA c d L ℓ₀ k) * Tj d (L : ℝ) k ℓ Fa +
    ENNReal.ofReal (wA c d L ℓ₀ k) * Tj d (L : ℝ) k ℓ Fb +
    ENNReal.ofReal (wAB c d L ℓ₀ jab k) * Tj d (L : ℝ) k ℓ Fab

theorem wA_nonneg (c : ObsCase) {ℓ₀ : ℝ} (hL : (0 : ℝ) < L) (hℓ₀ : 0 < ℓ₀) (j : ℕ) :
    0 ≤ wA c d L ℓ₀ j := by
  have := ellj_pos (d := d) hL hℓ₀ j
  cases c <;> simp only [wA] <;> positivity

theorem wAB_nonneg (c : ObsCase) {ℓ₀ : ℝ} (hL : (0 : ℝ) < L) (hℓ₀ : 0 < ℓ₀) (jab j : ℕ) :
    0 ≤ wAB c d L ℓ₀ jab j := by
  have := ellj_pos (d := d) hL hℓ₀ j
  have := ellj_pos (d := d) hL hℓ₀ (min j jab)
  cases c <;> simp only [wAB] <;> positivity

/-- The exponent of the weight ratio: `ℓ_{a,j+1} = θ^{-k_a} ℓ_{a,j}`. -/
def kA : ObsCase → ℕ
  | .one => 1
  | .two => 2

theorem ellj_succ_inv {ℓ₀ : ℝ} (hL : (0 : ℝ) < L) (j : ℕ) :
    (ellj d L ℓ₀ (j + 1))⁻¹ = (ellj d L ℓ₀ j)⁻¹ * ((L : ℝ) ^ (-((d : ℝ) - 2) / 2))⁻¹ := by
  rw [ellj_succ hL j, mul_inv]

theorem wA_succ (c : ObsCase) {ℓ₀ : ℝ} (hL : (0 : ℝ) < L) (j : ℕ) :
    wA c d L ℓ₀ (j + 1) = wA c d L ℓ₀ j * (((L : ℝ) ^ (-((d : ℝ) - 2) / 2))⁻¹) ^ kA c := by
  cases c <;> simp only [wA, kA, ellj_succ_inv hL j] <;> ring

theorem wAB_succ (c : ObsCase) {ℓ₀ : ℝ} (hL : (0 : ℝ) < L) {jab j : ℕ}
    (hj : jab ≤ j) :
    wAB c d L ℓ₀ jab (j + 1) = wAB c d L ℓ₀ jab j * (((L : ℝ) ^ (-((d : ℝ) - 2) / 2))⁻¹) ^ 2 := by
  have h1 : min (j + 1) jab = jab := min_eq_right (by omega)
  have h2 : min j jab = jab := min_eq_right hj
  cases c <;> simp only [wAB, h1, h2, ellj_succ_inv hL j] <;> ring

/-! ### (iii) additivity -/

theorem locA_eq_sum (c : ObsCase) (a : Lam d L N) {ι : Type*} (s : Finset ι)
    (Q : ι → Finset (Lam d L N)) (hQ : (s : Set ι).PairwiseDisjoint Q) (F : Alg d L N) :
    locA c a (s.biUnion Q) (s.biUnion Q) F = ∑ i ∈ s, locA c a (s.biUnion Q) (Q i) F := by
  cases c
  · exact locOdd_eq_sum s Q hQ _ _ F
  · exact locEven_eq_sum s Q hQ _ F

theorem locB_eq_sum (c : ObsCase) (b : Lam d L N) {ι : Type*} (s : Finset ι)
    (Q : ι → Finset (Lam d L N)) (hQ : (s : Set ι).PairwiseDisjoint Q) (F : Alg d L N) :
    locB c b (s.biUnion Q) (s.biUnion Q) F = ∑ i ∈ s, locB c b (s.biUnion Q) (Q i) F := by
  cases c
  · exact locOdd_eq_sum s Q hQ _ _ F
  · exact locEven_eq_sum s Q hQ _ F

theorem locAB_eq_sum (a b : Lam d L N) {ι : Type*} (s : Finset ι)
    (Q : ι → Finset (Lam d L N)) (hQ : (s : Set ι).PairwiseDisjoint Q) (F : Alg d L N) :
    locAB a b (s.biUnion Q) (s.biUnion Q) F = ∑ i ∈ s, locAB a b (s.biUnion Q) (Q i) F :=
  locEven_eq_sum s Q hQ _ F

/-! ### (iv) the image, and locality -/

/-- (iv), `ab` component: a combination of `1` and `ψ̄_z ψ_z` for `z ∈ B ∩ {a, b}`. -/
theorem locAB_image (a b : Lam d L N) (X B : Finset (Lam d L N)) (F : Alg d L N) :
    ∃ u r : ℂ, locAB a b X B F = (u * (B ∩ {a, b}).card) • (1 : Alg d L N) +
      r • ∑ z ∈ B ∩ {a, b}, pbp z :=
  locEven_image _ X B F

theorem locA_mem (c : ObsCase) (a : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locA c a X Y F ∈ NX ((Y ∩ {a} : Finset (Lam d L N)) : Set (Lam d L N)) := by
  cases c
  · exact locOdd_mem _ _ _ _ F
  · exact locEven_mem _ _ _ F

theorem locB_mem (c : ObsCase) (b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locB c b X Y F ∈ NX ((Y ∩ {b} : Finset (Lam d L N)) : Set (Lam d L N)) := by
  cases c
  · exact locOdd_mem _ _ _ _ F
  · exact locEven_mem _ _ _ F

theorem locAB_mem (a b : Lam d L N) (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    locAB a b X Y F ∈ NX ((Y ∩ {a, b} : Finset (Lam d L N)) : Set (Lam d L N)) :=
  locEven_mem _ _ _ F

/-! ### (i) boundedness -/

/-- `prop:Loc-obs` (i), componentwise. -/
theorem locObs_bound_comp (d : ℕ) : ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ X Y : Finset (Lam d L N), IsSmall j X →
    Y ⊆ X → ∀ (c : ObsCase) (a b : Lam d L N), ∀ F ∈ NX (nbhd j X : Set (Lam d L N)),
    ∀ ℓ : ℝ, 0 < ℓ →
      Tj d (L : ℝ) j ℓ (locA c a X Y F) ≤ ENNReal.ofReal Cbar * Tj d (L : ℝ) j ℓ F ∧
      Tj d (L : ℝ) j ℓ (locB c b X Y F) ≤ ENNReal.ofReal Cbar * Tj d (L : ℝ) j ℓ F ∧
      Tj d (L : ℝ) j ℓ (locAB a b X Y F) ≤ ENNReal.ofReal Cbar * Tj d (L : ℝ) j ℓ F := by
  obtain ⟨C1, hC1, h1⟩ := exists_odd_bound d
  obtain ⟨C2, hC2, h2⟩ := exists_even_bound d
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  intro L _ hL N j hj X Y hX hYX c a b F hF ℓ hℓ
  have m1 : ENNReal.ofReal C1 ≤ ENNReal.ofReal (max C1 C2) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have m2 : ENNReal.ofReal C2 ≤ ENNReal.ofReal (max C1 C2) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have ho : ∀ s P, Tj d (L : ℝ) j ℓ (locOdd s P X Y F) ≤
      ENNReal.ofReal (max C1 C2) * Tj d (L : ℝ) j ℓ F := fun s P =>
    (h1 L hL N j hj X Y hX hYX F hF s P ℓ hℓ).trans (by gcongr)
  have he : ∀ P, Tj d (L : ℝ) j ℓ (locEven P X Y F) ≤
      ENNReal.ofReal (max C1 C2) * Tj d (L : ℝ) j ℓ F := fun P =>
    (h2 L hL N j hj X Y hX hYX F hF P ℓ hℓ).trans (by gcongr)
  cases c
  · exact ⟨ho _ _, ho _ _, he _⟩
  · exact ⟨he _, he _, he _⟩

/-- Proposition `prop:Loc-obs` (i): `‖Loc^obs_{X,Y} F‖_{T_j(ℓ_j)} ≤ C̄ ‖F‖_{T_j(ℓ_j)}`. -/
theorem locObs_bound (d : ℕ) : ∃ Cbar : ℝ, ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ jab : ℕ, ∀ X Y : Finset (Lam d L N),
    IsSmall j X → Y ⊆ X → ∀ (c : ObsCase) (a b : Lam d L N),
    ∀ Fa ∈ NX (nbhd j X : Set (Lam d L N)), ∀ Fb ∈ NX (nbhd j X : Set (Lam d L N)),
    ∀ Fab ∈ NX (nbhd j X : Set (Lam d L N)),
      obsNorm c ℓ₀ jab j (ellj d L ℓ₀ j) (locA c a X Y Fa) (locB c b X Y Fb)
          (locAB a b X Y Fab) ≤
        ENNReal.ofReal Cbar * obsNorm c ℓ₀ jab j (ellj d L ℓ₀ j) Fa Fb Fab := by
  obtain ⟨C, _, hC⟩ := locObs_bound_comp d
  refine ⟨C, 2 ^ (d + 3) + 8 * d + 1, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ jab X Y hX hYX c a b Fa hFa Fb hFb Fab hFab
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ := ellj_pos (d := d) hL0 hℓ₀ j
  have ha := (hC L (by omega) N j hj X Y hX hYX c a b Fa hFa _ hℓ).1
  have hb := (hC L (by omega) N j hj X Y hX hYX c a b Fb hFb _ hℓ).2.1
  have hab := (hC L (by omega) N j hj X Y hX hYX c a b Fab hFab _ hℓ).2.2
  unfold obsNorm
  rw [mul_add, mul_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · calc _ ≤ ENNReal.ofReal (wA c d L ℓ₀ j) * (ENNReal.ofReal C * Tj d (L : ℝ) j _ Fa) := by
          gcongr
      _ = _ := by ring
  · calc _ ≤ ENNReal.ofReal (wA c d L ℓ₀ j) * (ENNReal.ofReal C * Tj d (L : ℝ) j _ Fb) := by
          gcongr
      _ = _ := by ring
  · calc _ ≤ ENNReal.ofReal (wAB c d L ℓ₀ jab j) * (ENNReal.ofReal C * Tj d (L : ℝ) j _ Fab) := by
          gcongr
      _ = _ := by ring

/-! ### (ii) contraction -/

/-- (ii) for `F_a`, unweighted: `‖(1 - loc^a_X) F_a‖_{T_{j+1}(2ℓ_{j+1})} ≤ C̄ θ^{k_a} L^{-1}
‖F_a‖_{T_j(ℓ_j)}`, `θ = L^{-(d-2)/2}` (`k_a = 1` in Case (1), `2` in Case (2)). -/
theorem locA_contract (d : ℕ) (hd : 3 ≤ d) : ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (c : ObsCase) (a : Lam d L N), a ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (chargeA c) F →
      Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (F - locA c a X X F) ≤
        ENNReal.ofReal (Cbar * ((L : ℝ) ^ (-((d : ℝ) - 2) / 2)) ^ kA c / L) *
          Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨C1, hC1, h1⟩ := exists_odd_contract d hd
  obtain ⟨C2, hC2, h2⟩ := exists_even_contract d hd
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X hX c a ha F hF hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hθ : 0 ≤ (L : ℝ) ^ (-((d : ℝ) - 2) / 2) := Real.rpow_nonneg hL0.le _
  have hne : (X ∩ {a}).Nonempty := ⟨a, by simp [ha]⟩
  cases c
  · refine (h1 L hL N j hj ℓ₀ hℓ₀ X hX (-1) {a} hne F hF (by simpa [chargeA] using hFc)).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    simp only [kA, pow_one]
    gcongr
    exact le_max_left _ _
  · refine (h2 L hL N j hj ℓ₀ hℓ₀ X hX {a} hne F hF hFc).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    simp only [kA]
    gcongr
    exact le_max_right _ _

theorem locB_contract (d : ℕ) (hd : 3 ≤ d) : ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ (c : ObsCase) (b : Lam d L N), b ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge (chargeB c) F →
      Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (F - locB c b X X F) ≤
        ENNReal.ofReal (Cbar * ((L : ℝ) ^ (-((d : ℝ) - 2) / 2)) ^ kA c / L) *
          Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨C1, hC1, h1⟩ := exists_odd_contract d hd
  obtain ⟨C2, hC2, h2⟩ := exists_even_contract d hd
  refine ⟨max C1 C2, le_max_of_le_left hC1, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X hX c b hb F hF hFc
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hθ : 0 ≤ (L : ℝ) ^ (-((d : ℝ) - 2) / 2) := Real.rpow_nonneg hL0.le _
  have hne : (X ∩ {b}).Nonempty := ⟨b, by simp [hb]⟩
  cases c
  · refine (h1 L hL N j hj ℓ₀ hℓ₀ X hX 1 {b} hne F hF (by simpa [chargeB] using hFc)).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    simp only [kA, pow_one]
    gcongr
    exact le_max_left _ _
  · refine (h2 L hL N j hj ℓ₀ hℓ₀ X hX {b} hne F hF hFc).trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    simp only [kA]
    gcongr
    exact le_max_right _ _

/-- (ii) for `F_{ab}`, unweighted: `‖(1 - loc^{ab}_X) F_{ab}‖_{T_{j+1}(2ℓ_{j+1})} ≤
C̄ θ^2 L^{-1} ‖F_{ab}‖_{T_j(ℓ_j)}`. -/
theorem locAB_contract (d : ℕ) (hd : 3 ≤ d) : ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ (L : ℕ) [NeZero L],
    2 ^ (d + 3) + 8 * d < L → ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ →
    ∀ X : Finset (Lam d L N), IsSmall j X → ∀ a b : Lam d L N, a ∈ X ∨ b ∈ X →
    ∀ F ∈ NX (nbhd j X : Set (Lam d L N)), HasCharge 0 F →
      Tj d (L : ℝ) (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (F - locAB a b X X F) ≤
        ENNReal.ofReal (Cbar * ((L : ℝ) ^ (-((d : ℝ) - 2) / 2)) ^ 2 / L) *
          Tj d (L : ℝ) j (ellj d L ℓ₀ j) F := by
  obtain ⟨C2, hC2, h2⟩ := exists_even_contract d hd
  refine ⟨C2, hC2, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ X hX a b hab F hF hFc
  have hne : (X ∩ {a, b}).Nonempty := by
    rcases hab with h | h
    · exact ⟨a, by simp [h]⟩
    · exact ⟨b, by simp [h]⟩
  exact h2 L hL N j hj ℓ₀ hℓ₀ X hX {a, b} hne F hF hFc

theorem locOdd_zero (s : ℤˣ) (P X Y : Finset (Lam d L N)) : locOdd s P X Y 0 = 0 := by
  simpa using locOdd_smul s P X Y 0 0

theorem locEven_zero (P X Y : Finset (Lam d L N)) : locEven P X Y 0 = 0 := by
  simpa using locEven_smul P X Y 0 0

theorem locA_zero (c : ObsCase) (a : Lam d L N) (X Y : Finset (Lam d L N)) :
    locA c a X Y 0 = 0 := by
  cases c
  · exact locOdd_zero _ _ _ _
  · exact locEven_zero _ _ _

theorem locB_zero (c : ObsCase) (b : Lam d L N) (X Y : Finset (Lam d L N)) :
    locB c b X Y 0 = 0 := by
  cases c
  · exact locOdd_zero _ _ _ _
  · exact locEven_zero _ _ _

/-- One weighted component: from `‖G‖' ≤ C θ^k/L ‖F‖` and `w' = w θ^{-k}` to
`w' ‖G‖' ≤ C/L w ‖F‖`. -/
theorem weighted_step {A B : ENNReal} {C w w' θ L : ℝ} {k : ℕ} (hθ : 0 < θ) (hw : 0 ≤ w)
    (hw' : w' = w * θ⁻¹ ^ k) (hC : 0 ≤ C) (hL : 0 < L)
    (h : A ≤ ENNReal.ofReal (C * θ ^ k / L) * B) :
    ENNReal.ofReal w' * A ≤ ENNReal.ofReal (C / L) * (ENNReal.ofReal w * B) := by
  calc ENNReal.ofReal w' * A ≤ ENNReal.ofReal w' * (ENNReal.ofReal (C * θ ^ k / L) * B) := by
        gcongr
    _ = ENNReal.ofReal (w' * (C * θ ^ k / L)) * B := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by rw [hw']; positivity)]
    _ = ENNReal.ofReal (C / L * w) * B := by
        congr 2
        rw [hw', inv_pow]
        field_simp
    _ = ENNReal.ofReal (C / L) * (ENNReal.ofReal w * B) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem weighted_zero {A C : ℝ} {w' : ℝ} {B : ENNReal} {k : ℕ} {ℓ : ℝ} (G : Alg d L N)
    (hG : G = 0) :
    ENNReal.ofReal w' * Tj d (L : ℝ) k ℓ G ≤ ENNReal.ofReal A * (ENNReal.ofReal C * B) := by
  subst hG
  rw [show Tj d (L : ℝ) k ℓ (0 : Alg d L N) = 0 by
    refine le_antisymm ?_ bot_le
    simpa using tNorm_smul_le (E := Dir d) (p := pPhi d) (h := (L : ℝ) ^ k) (ℓ := ℓ) (0 : ℂ)
      (0 : Alg d L N)]
  simp

/-- Proposition `prop:Loc-obs` (ii): for `U(1)`-invariant components, with the observable points
of each nonzero component in `X`, and `j_{ab} ≤ j` or `F_{ab} = 0`,
`‖(1 - Loc^obs_X) F‖_{T_{j+1}(2ℓ_{j+1})} ≤ C̄ L^{-1} ‖F‖_{T_j(ℓ_j)}` (weighted norms). -/
theorem locObs_contract (d : ℕ) (hd : 3 ≤ d) : ∃ Cbar : ℝ, ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L],
    L₀ ≤ L → ∀ N j : ℕ, j < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ jab : ℕ, ∀ X : Finset (Lam d L N),
    IsSmall j X → ∀ (c : ObsCase) (a b : Lam d L N),
    ∀ Fa ∈ NX (nbhd j X : Set (Lam d L N)), ∀ Fb ∈ NX (nbhd j X : Set (Lam d L N)),
    ∀ Fab ∈ NX (nbhd j X : Set (Lam d L N)),
    HasCharge (chargeA c) Fa → HasCharge (chargeB c) Fb → HasCharge 0 Fab →
    (a ∈ X ∨ Fa = 0) → (b ∈ X ∨ Fb = 0) → ((a ∈ X ∨ b ∈ X) ∧ jab ≤ j ∨ Fab = 0) →
      obsNorm c ℓ₀ jab (j + 1) (2 * ellj d L ℓ₀ (j + 1)) (Fa - locA c a X X Fa)
          (Fb - locB c b X X Fb) (Fab - locAB a b X X Fab) ≤
        ENNReal.ofReal (Cbar / L) * obsNorm c ℓ₀ jab j (ellj d L ℓ₀ j) Fa Fb Fab := by
  obtain ⟨Ca, hCa, hA⟩ := locA_contract d hd
  obtain ⟨Cb, hCb, hB⟩ := locB_contract d hd
  obtain ⟨Cab, hCab, hAB⟩ := locAB_contract d hd
  refine ⟨max (max Ca Cb) Cab, 2 ^ (d + 3) + 8 * d + 1, ?_⟩
  intro L _ hL N j hj ℓ₀ hℓ₀ jab X hX c a b Fa hFa Fb hFb Fab hFab hca hcb hcab ha hb hab
  have hL' : 2 ^ (d + 3) + 8 * d < L := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hθ : 0 < (L : ℝ) ^ (-((d : ℝ) - 2) / 2) := Real.rpow_pos_of_pos hL0 _
  set C := max (max Ca Cb) Cab
  have hC0 : 0 ≤ C := le_max_of_le_right hCab
  have hwA := wA_nonneg (d := d) c hL0 hℓ₀ j
  have hwAB := wAB_nonneg (d := d) c hL0 hℓ₀ jab j
  unfold obsNorm
  rw [mul_add, mul_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · rcases ha with ha | ha
    · refine weighted_step hθ hwA (wA_succ c hL0 j) hC0 hL0 ?_
      refine (hA L hL' N j hj ℓ₀ hℓ₀ X hX c a ha Fa hFa hca).trans ?_
      gcongr
      exact le_max_of_le_left (le_max_left _ _)
    · exact weighted_zero _ (by rw [ha, locA_zero, sub_zero])
  · rcases hb with hb | hb
    · refine weighted_step hθ hwA (wA_succ c hL0 j) hC0 hL0 ?_
      refine (hB L hL' N j hj ℓ₀ hℓ₀ X hX c b hb Fb hFb hcb).trans ?_
      gcongr
      exact le_max_of_le_left (le_max_right _ _)
    · exact weighted_zero _ (by rw [hb, locB_zero, sub_zero])
  · rcases hab with ⟨hab, hjab⟩ | hab
    · refine weighted_step hθ hwAB (wAB_succ c hL0 hjab) hC0 hL0 ?_
      refine (hAB L hL' N j hj ℓ₀ hℓ₀ X hX a b hab Fab hFab hcab).trans ?_
      gcongr
      exact le_max_right _ _
    · exact weighted_zero _ (by rw [hab, locAB, locEven_zero, sub_zero])

end

end Obs.LocObs
