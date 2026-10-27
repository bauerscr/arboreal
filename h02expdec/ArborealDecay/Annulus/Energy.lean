module

public import ArborealDecay.Annulus.CondId

/-!
# Energies under vertex identification, and the second-moment bound on `Γ`

* `edgeSum_mapW_le`: `∑_{e ∈ E(mapW β f)} (w_e + 3)(∇_e φ')² ≤ ∑_{e ∈ E(β)} (β_e + 3)(∇_e φ)²`
  when `φ' ∘ f = φ`;
* `grad_mapW`: gradient bounds pass to `mapW β f`;
* `edgeSum_restrict_le`, `sum_coe_le`: restriction to a `Finset` of vertices;
* `sum_le_of_injective`: counting through an injection;
* `moment_bound_of_inputs` (supplement `thm:annulus`, step `ann-param`, via `cor:sabot`(i)):
  on `Γ = G/(a=b)`, `E^ρ e^{2 t_y} ≤ exp(-2γ + 6γ² E₀)` for a test function `φ` on `G` with
  `φ_a = φ_b = 0`, `φ_y = 1`, `γ |∇φ| ≤ 1/18` and energy `≤ E₀`.  (H1), (H2) come from (A).
-/

open Matrix Real MeasureTheory

set_option linter.unusedSectionVars false

@[expose] public section

namespace ArborealDecay.Annulus

open ArborealDecay.TLaw ArborealDecay.Surgery ArborealDecay.Wiring ArborealDecay.CondComb

section Generic

variable {Λ Λ' : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

theorem mapW_add_ind (β : Λ → Λ → ℝ) (f : Λ → Λ') (p q : Λ') :
    mapW (fun u v => β u v + 3 * (if 0 < β u v then (1 : ℝ) else 0)) f p q =
      mapW β f p q + 3 * mapW (fun u v => if 0 < β u v then (1 : ℝ) else 0) f p q := by
  unfold mapW
  split_ifs
  · ring
  · simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem edgeSum_mapW_le {β : Λ → Λ → ℝ} (hβ0 : ∀ i j, 0 ≤ β i j) (f : Λ → Λ')
    (φ' : Λ' → ℝ) (φ : Λ → ℝ) (hφ : ∀ u, φ' (f u) = φ u) :
    edgeSum (mapW β f) (fun p q => (mapW β f p q + 3) * (φ' p - φ' q) ^ 2) ≤
      edgeSum β (fun u v => (β u v + 3) * (φ u - φ v) ^ 2) := by
  set β₃ : Λ → Λ → ℝ := fun u v => β u v + 3 * (if 0 < β u v then (1 : ℝ) else 0)
  have hpt : ∀ p q, (if 0 < mapW β f p q then (mapW β f p q + 3) * (φ' p - φ' q) ^ 2 else 0) ≤
      mapW β₃ f p q * (φ' p - φ' q) ^ 2 := by
    intro p q
    rw [mapW_add_ind]
    have hM0 := mapW_nonneg hβ0 f p q
    have hind := ind_le_mapW_ind (β := β) f p q
    have hsq := sq_nonneg (φ' p - φ' q)
    split_ifs at hind ⊢ with h
    · nlinarith
    · have : 0 ≤ mapW (fun u v => if 0 < β u v then (1 : ℝ) else 0) f p q := hind
      positivity
  have hsum := sum_mapW_mul β₃ f (fun p q => (φ' p - φ' q) ^ 2) (fun p => by simp)
  unfold edgeSum
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ p, ∑ q, (if 0 < mapW β f p q then (mapW β f p q + 3) * (φ' p - φ' q) ^ 2 else 0)
      ≤ ∑ p, ∑ q, mapW β₃ f p q * (φ' p - φ' q) ^ 2 :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hpt p q
    _ = ∑ u, ∑ v, β₃ u v * (φ' (f u) - φ' (f v)) ^ 2 := hsum
    _ = ∑ u, ∑ v, (if 0 < β u v then (β u v + 3) * (φ u - φ v) ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        simp only [β₃, hφ]
        split_ifs with h
        · ring
        · have : β u v = 0 := le_antisymm (not_lt.1 h) (hβ0 u v)
          rw [this]; ring

theorem grad_mapW {β : Λ → Λ → ℝ} (f : Λ → Λ') (φ' : Λ' → ℝ) (φ : Λ → ℝ)
    (hφ : ∀ u, φ' (f u) = φ u) {G₀ : ℝ} (hg : ∀ u v, 0 < β u v → |φ u - φ v| ≤ G₀) :
    ∀ p q, 0 < mapW β f p q → |φ' p - φ' q| ≤ G₀ := by
  intro p q h
  obtain ⟨_, u, v, rfl, rfl, huv⟩ := exists_of_mapW_pos h
  rw [hφ, hφ]; exact hg u v huv

/-- Counting through an injection. -/
theorem sum_le_of_injective {α γ : Type*} [Fintype α] [DecidableEq γ] (e : α → γ)
    (he : Function.Injective e) (s : Finset γ) (T : α → ℝ) (g : γ → ℝ)
    (hg : ∀ x ∈ s, 0 ≤ g x) (hT : ∀ q, T q ≠ 0 → e q ∈ s ∧ T q ≤ g (e q)) :
    ∑ q, T q ≤ ∑ x ∈ s, g x := by
  classical
  rw [← Finset.sum_filter_ne_zero]
  calc ∑ q ∈ Finset.univ.filter (fun q => T q ≠ 0), T q
      ≤ ∑ q ∈ Finset.univ.filter (fun q => T q ≠ 0), g (e q) :=
        Finset.sum_le_sum fun q hq => (hT q (Finset.mem_filter.1 hq).2).2
    _ = ∑ x ∈ (Finset.univ.filter (fun q => T q ≠ 0)).image e, g x :=
        (Finset.sum_image fun x _ y _ h => he h).symm
    _ ≤ ∑ x ∈ s, g x := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x hx _ => hg x hx
        intro x hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
        exact (hT q (Finset.mem_filter.1 hq).2).1

end Generic

section Restrict

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem sum_coe_le (C : Finset X) (F : X → X → ℝ) (hF : ∀ x y, 0 ≤ F x y) :
    ∑ x : C, ∑ y : C, F x y ≤ ∑ x, ∑ y, F x y := by
  have e : ∑ x : C, ∑ y : C, F x y = ∑ x ∈ C, ∑ y ∈ C, F x y := by
    rw [← Finset.sum_coe_sort C]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Finset.sum_coe_sort C (F x)
  rw [e]
  calc ∑ x ∈ C, ∑ y ∈ C, F x y ≤ ∑ x ∈ C, ∑ y, F x y :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_univ_sum_of_nonneg fun y => hF x y
    _ ≤ ∑ x, ∑ y, F x y := Finset.sum_le_univ_sum_of_nonneg fun x =>
        Finset.sum_nonneg fun y _ => hF x y

theorem edgeSum_restrict_le (C : Finset X) (G g : X → X → ℝ) (hg : ∀ x y, 0 ≤ g x y) :
    edgeSum (fun x y : C => G x y) (fun x y => g x y) ≤ edgeSum G g := by
  unfold edgeSum
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact sum_coe_le C (fun x y => if 0 < G x y then g x y else 0) fun x y => by
    split_ifs
    · exact hg x y
    · rfl

end Restrict

section Moment

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {a b : V}

/-- A test function on `G`, transported to `Γ = G/(a=b)` (value `0` at `ρ`). -/
def liftGam (φ : V → ℝ) : GamV V a b → ℝ
  | none => 0
  | some x => φ x.1

theorem liftGam_col {φ : V → ℝ} (hφa : φ a = 0) (hφb : φ b = 0) (u : V) :
    liftGam φ (colAB a b u) = φ u := by
  by_cases hu : u ∈ ({a, b} : Finset V)
  · rw [colAB, collapse_of_mem hu]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hφa.symm
    · exact hφb.symm
  · rw [colAB, collapse_of_notMem hu]; rfl

/-- **Second moment at `y`** (supplement `thm:annulus`, via `cor:sabot`(i) with (H1), (H2) from
(A)): `E^ρ_Γ e^{2 t_y} ≤ exp(-2γ + 6γ² E₀)`. -/
theorem moment_bound_of_inputs
    (hA : ∀ (V : Type u) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    {β : V → V → ℝ} (hβ : IsWGraph β) (hconn : (supportGraph (gammaW β a b)).Connected)
    (φ : V → ℝ) (hφa : φ a = 0) (hφb : φ b = 0) (y : Conductance.Interior a b) (hφy : φ y.1 = 1)
    {G₀ E₀ γ : ℝ} (hγ : 0 < γ) (hgrad : ∀ u v, 0 < β u v → |φ u - φ v| ≤ G₀)
    (hγG : γ * G₀ ≤ 1 / 18)
    (hE : edgeSum β (fun u v => (β u v + 3) * (φ u - φ v) ^ 2) ≤ E₀) :
    expect (gammaW β a b) none (3 / 2) (fun τ => exp (2 * TLaw.ext none τ (eI a b y).1)) ≤
      exp (-2 * γ + 6 * γ ^ 2 * E₀) := by
  have hΓ := isWGraph_gammaW hβ a b
  have hφ' : ∀ u, liftGam φ (colAB a b u) = φ u := liftGam_col hφa hφb
  have hgrad' : ∀ p q, 0 < gammaW β a b p q →
      γ * |liftGam (a := a) (b := b) φ p - liftGam φ q| ≤ 1 / 18 := by
    intro p q h
    have := grad_mapW (β := β) (colAB a b) (liftGam φ) φ hφ' hgrad p q h
    exact (mul_le_mul_of_nonneg_left this hγ.le).trans hγG
  have hy : (eI a b y).1 ≠ none := (eI a b y).2
  have hvy : liftGam (a := a) (b := b) φ (eI a b y).1 = 1 := hφy
  have h := sabot_two_thirds hΓ hconn hy hγ (liftGam φ) rfl hvy hgrad'
    (H1_of_inputs hA hΓ hconn none) (B_of_inputs hA hΓ hconn none (eI a b y).1)
  refine h.2.trans (exp_le_exp.2 ?_)
  have hE' := (edgeSum_mapW_le hβ.nonneg (colAB a b) (liftGam φ) φ hφ').trans hE
  have : edgeSum (gammaW β a b)
      (fun i k => (gammaW β a b i k + 3) * (liftGam φ i - liftGam φ k) ^ 2) ≤ E₀ := hE'
  nlinarith [sq_nonneg γ]

end Moment

end ArborealDecay.Annulus
