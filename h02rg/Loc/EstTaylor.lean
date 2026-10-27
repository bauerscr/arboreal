import Loc.EstPath

/-!
# The discrete Taylor polynomial of degree two

For a function `Φ` of `m` points of `ℤ^d` (i.e. of `m d` integer coordinates `w k i`), `taylor2 Φ`
is the Newton interpolation polynomial of degree `2` at `0` (built from forward differences
`D_{k,i}` in the positive coordinate directions).  It is a polynomial of degree `≤ 2` in the
coordinates, and the remainder `Φ - taylor2 Φ` satisfies the usual bounds: if all derivatives of
order `q` of `Φ` are bounded by `K ε^q`, then at points in the box of radius `r` the derivatives of
order `q ≤ 2` of the remainder are bounded by `K (m d (r + 2))^{3 - q} ε^3`, and those of order
`q ≥ 3` by `K ε^q`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d m : ℕ}

/-- The forward difference in the positive direction `e_i` at the point `k`. -/
def Dp (k : Fin m) (i : Fin d) (Φ : (Fin m → Zd d) → ℂ) : (Fin m → Zd d) → ℂ :=
  ediff (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) k (Sum.inl i) Φ

/-- The discrete Taylor (Newton) polynomial of degree `2` at `0`. -/
def taylor2 (Φ : (Fin m → Zd d) → ℂ) (w : Fin m → Zd d) : ℂ :=
  Φ 0 + ∑ k, ∑ i, Dp k i Φ 0 * (w k i : ℂ)
    + (1 / 2) * ∑ k, ∑ i, ∑ k', ∑ i', Dp k' i' (Dp k i Φ) 0 * (w k i : ℂ) * (w k' i' : ℂ)
    - (1 / 2) * ∑ k, ∑ i, Dp k i (Dp k i Φ) 0 * (w k i : ℂ)

/-! ### Differences along vectors -/

/-- `Δ_v f (w) = f (w + v) - f w`. -/
def Dv (v : Fin m → Zd d) (f : (Fin m → Zd d) → ℂ) : (Fin m → Zd d) → ℂ :=
  fun w => f (w + v) - f w

/-- The unit vector `e_{k,i}`. -/
def ee (k : Fin m) (i : Fin d) : Fin m → Zd d := Pi.single k (Pi.single i 1)

theorem ediff_eq_Dv (k : Fin m) (e : Dir d) (f : (Fin m → Zd d) → ℂ) :
    ediff (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) k e f = Dv (Pi.single k (dirZ e)) f := by
  funext w
  simp only [ediff, Dv]
  congr 1
  congr 1
  funext k'
  by_cases hk : k' = k
  · subst hk; simp [single_vaddZ]
  · simp [hk]

theorem Dp_eq_Dv (k : Fin m) (i : Fin d) (f : (Fin m → Zd d) → ℂ) :
    Dp k i f = Dv (ee k i) f := by
  rw [Dp, ediff_eq_Dv]; rfl

theorem Dv_sub (v : Fin m → Zd d) (f g : (Fin m → Zd d) → ℂ) :
    Dv v (fun w => f w - g w) = fun w => Dv v f w - Dv v g w := by
  funext w; simp only [Dv]; ring

theorem Dv_comm (u v : Fin m → Zd d) (f : (Fin m → Zd d) → ℂ) :
    Dv u (Dv v f) = Dv v (Dv u f) := by
  funext w; simp only [Dv]; rw [add_right_comm]; ring

theorem Dv_neg (v : Fin m → Zd d) (f : (Fin m → Zd d) → ℂ) (t : Fin m → Zd d) :
    Dv (-v) f t = -(Dv v f (t + -v)) := by
  simp only [Dv, neg_add_cancel_right]; rw [← sub_eq_add_neg]; ring

theorem supNormZ_single_dirZ_le (k k' : Fin m) (e : Dir d) :
    supNormZ ((Pi.single k (dirZ e) : Fin m → Zd d) k') ≤ 1 := by
  by_cases hk : k' = k
  · subst hk; simpa using supNormZ_dirZ e
  · simp [hk, supNormZ]

/-- A difference in a direction `±e_{k,i}` is `±` a positive difference at a nearby point. -/
theorem Dv_dir (k : Fin m) (e : Dir d) (f : (Fin m → Zd d) → ℂ) (t : Fin m → Zd d) :
    ∃ (i : Fin d) (σ : ℂ) (c : Fin m → Zd d), ‖σ‖ = 1 ∧
      (∀ k', supNormZ (c k') ≤ 1) ∧ Dv (Pi.single k (dirZ e)) f t = σ * Dv (ee k i) f (t + c) := by
  rcases e with i | i
  · refine ⟨i, 1, 0, by simp, fun k' => by simp [supNormZ], ?_⟩
    simp only [one_mul, add_zero]; rfl
  · refine ⟨i, -1, Pi.single k (dirZ (Sum.inr i)), by simp,
      fun k' => supNormZ_single_dirZ_le k k' _, ?_⟩
    have h : (Pi.single k (dirZ (Sum.inr i)) : Fin m → Zd d) = -ee k i := by
      simp [dirZ, ee, Pi.single_neg]
    rw [h, Dv_neg]; ring

/-! ### `taylor2` is quadratic -/

/-- A linear form in the coordinates. -/
def linF (a : Fin m → Fin d → ℂ) (w : Fin m → Zd d) : ℂ := ∑ k, ∑ i, a k i * (w k i : ℂ)

/-- A quadratic form in the coordinates. -/
def quadF (B : Fin m → Fin d → Fin m → Fin d → ℂ) (w : Fin m → Zd d) : ℂ :=
  ∑ k, ∑ i, ∑ k', ∑ i', B k i k' i' * (w k i : ℂ) * (w k' i' : ℂ)

/-- The associated (symmetrised) bilinear form. -/
def bilF (B : Fin m → Fin d → Fin m → Fin d → ℂ) (w u : Fin m → Zd d) : ℂ :=
  ∑ k, ∑ i, ∑ k', ∑ i', B k i k' i' * ((w k i : ℂ) * (u k' i' : ℂ) + (u k i : ℂ) * (w k' i' : ℂ))

theorem linF_add (a : Fin m → Fin d → ℂ) (w u : Fin m → Zd d) :
    linF a (w + u) = linF a w + linF a u := by
  simp only [linF, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add]; ring

theorem quadF_add (B : Fin m → Fin d → Fin m → Fin d → ℂ) (w u : Fin m → Zd d) :
    quadF B (w + u) = quadF B w + quadF B u + bilF B w u := by
  simp only [quadF, bilF, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun k' _ =>
    sum_congr rfl fun i' _ => ?_
  simp only [Pi.add_apply, Int.cast_add]; ring

theorem bilF_add (B : Fin m → Fin d → Fin m → Fin d → ℂ) (w u v : Fin m → Zd d) :
    bilF B (w + u) v = bilF B w v + bilF B u v := by
  simp only [bilF, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun k' _ =>
    sum_congr rfl fun i' _ => ?_
  simp only [Pi.add_apply, Int.cast_add]; ring

theorem taylor2_eq (Φ : (Fin m → Zd d) → ℂ) (w : Fin m → Zd d) :
    taylor2 Φ w = Φ 0 + linF (fun k i => Dp k i Φ 0) w
      + (1 / 2) * quadF (fun k i k' i' => Dp k' i' (Dp k i Φ) 0) w
      - (1 / 2) * linF (fun k i => Dp k i (Dp k i Φ) 0) w := rfl

/-- The second differences of `taylor2 Φ` do not depend on the point. -/
theorem taylor2_second (Φ : (Fin m → Zd d) → ℂ) (w u v : Fin m → Zd d) :
    taylor2 Φ (w + u + v) - taylor2 Φ (w + u) - taylor2 Φ (w + v) + taylor2 Φ w =
      (1 / 2) * bilF (fun k i k' i' => Dp k' i' (Dp k i Φ) 0) u v := by
  simp only [taylor2_eq]
  set a : Fin m → Fin d → ℂ := fun k i => Dp k i Φ 0
  set b : Fin m → Fin d → ℂ := fun k i => Dp k i (Dp k i Φ) 0
  set B : Fin m → Fin d → Fin m → Fin d → ℂ := fun k i k' i' => Dp k' i' (Dp k i Φ) 0
  rw [linF_add a (w + u) v, linF_add a w u, linF_add a w v, linF_add b (w + u) v,
    linF_add b w u, linF_add b w v, quadF_add B (w + u) v, quadF_add B w u, quadF_add B w v,
    bilF_add]
  ring

theorem Dv_Dv_Dv_taylor2 (Φ : (Fin m → Zd d) → ℂ) (x y z : Fin m → Zd d) :
    Dv x (Dv y (Dv z (taylor2 Φ))) = 0 := by
  have key : ∀ p, Dv y (Dv z (taylor2 Φ)) p =
      (1 / 2) * bilF (fun k i k' i' => Dp k' i' (Dp k i Φ) 0) z y := by
    intro p
    have := taylor2_second Φ p z y
    simp only [Dv]
    rw [add_right_comm p y z]
    linear_combination this
  funext w
  change Dv y (Dv z (taylor2 Φ)) (w + x) - Dv y (Dv z (taylor2 Φ)) w = 0
  rw [key, key, sub_self]

/-! ### The Taylor conditions at `0` -/

theorem ee_apply (k k' : Fin m) (i i' : Fin d) :
    ((ee k i k' i' : ℤ) : ℂ) = if k' = k ∧ i' = i then 1 else 0 := by
  by_cases hk : k' = k
  · subst hk
    by_cases hi : i' = i
    · subst hi; simp [ee]
    · simp [ee, hi]
  · simp [ee, hk]

theorem linF_ee (a : Fin m → Fin d → ℂ) (k : Fin m) (i : Fin d) : linF a (ee k i) = a k i := by
  simp [linF, ee_apply, ite_and]

theorem sum4_ee (B : Fin m → Fin d → Fin m → Fin d → ℂ) (k k' : Fin m) (i i' : Fin d) :
    ∑ k₁, ∑ i₁, ∑ k₂, ∑ i₂, B k₁ i₁ k₂ i₂ * ((ee k i k₁ i₁ : ℤ) : ℂ) * ((ee k' i' k₂ i₂ : ℤ) : ℂ)
      = B k i k' i' := by
  simp [ee_apply, ite_and]

theorem quadF_ee (B : Fin m → Fin d → Fin m → Fin d → ℂ) (k : Fin m) (i : Fin d) :
    quadF B (ee k i) = B k i k i := sum4_ee B k k i i

theorem bilF_ee (B : Fin m → Fin d → Fin m → Fin d → ℂ) (k k' : Fin m) (i i' : Fin d) :
    bilF B (ee k i) (ee k' i') = B k i k' i' + B k' i' k i := by
  rw [← sum4_ee B k k' i i', ← sum4_ee B k' k i' i]
  simp only [bilF, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun k' _ =>
    sum_congr rfl fun i' _ => ?_
  ring

theorem taylor2_zero (Φ : (Fin m → Zd d) → ℂ) : taylor2 Φ 0 = Φ 0 := by
  simp [taylor2_eq, linF, quadF]

theorem rem_zero (Φ : (Fin m → Zd d) → ℂ) : (fun w => Φ w - taylor2 Φ w) 0 = 0 := by
  simp [taylor2_zero]

theorem rem_D1_zero (Φ : (Fin m → Zd d) → ℂ) (k : Fin m) (i : Fin d) :
    Dv (ee k i) (fun w => Φ w - taylor2 Φ w) 0 = 0 := by
  have h1 : Dp k i Φ 0 = Φ (0 + ee k i) - Φ 0 := by rw [Dp_eq_Dv]; rfl
  simp only [Dv, zero_add, taylor2_eq, linF_ee, quadF_ee] at h1 ⊢
  simp only [linF, quadF] at *
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, sum_const_zero, add_zero] at *
  linear_combination -h1

theorem rem_D2_zero (Φ : (Fin m → Zd d) → ℂ) (k k' : Fin m) (i i' : Fin d) :
    Dv (ee k' i') (Dv (ee k i) (fun w => Φ w - taylor2 Φ w)) 0 = 0 := by
  have h := taylor2_second Φ 0 (ee k' i') (ee k i)
  rw [bilF_ee] at h
  have h1 : Dp k' i' (Dp k i Φ) 0 = Dv (ee k' i') (Dv (ee k i) Φ) 0 := by
    rw [Dp_eq_Dv, Dp_eq_Dv]
  have h2 : Dp k i (Dp k' i' Φ) 0 = Dv (ee k i) (Dv (ee k' i') Φ) 0 := by
    rw [Dp_eq_Dv, Dp_eq_Dv]
  simp only [Dv] at h h1 h2 ⊢
  simp only [zero_add] at h h1 h2 ⊢
  rw [add_comm (ee k i) (ee k' i')] at h2
  linear_combination -h - (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

/-! ### Third differences -/

theorem rem_D3 (Φ : (Fin m → Zd d) → ℂ) (x y z : Fin m → Zd d) :
    Dv x (Dv y (Dv z (fun w => Φ w - taylor2 Φ w))) = Dv x (Dv y (Dv z Φ)) := by
  rw [Dv_sub, Dv_sub, Dv_sub, Dv_Dv_Dv_taylor2]
  funext w; simp

theorem hs0Z : ∀ y : Zd d, (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) 0 y = y :=
  fun y => zero_vadd _ y

theorem hsaZ : ∀ (b b' : Dir d → ℕ) (y : Zd d),
    (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) (b + b') y =
      (fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) b ((fun (b : Dir d → ℕ) (u : Zd d) => b +ᵥ u) b' y) :=
  fun b b' y => add_vadd b b' y

theorem nabla_three (γ : Fin m → Dir d → ℕ) (k₁ k₂ k₃ : Fin m) (e₁ e₂ e₃ : Dir d)
    (f : (Fin m → Zd d) → ℂ) :
    nabla (fun b u => b +ᵥ u) (γ + Pi.single k₁ (Pi.single e₁ 1) + Pi.single k₂ (Pi.single e₂ 1)
      + Pi.single k₃ (Pi.single e₃ 1)) f =
    nabla (fun b u => b +ᵥ u) γ (Dv (Pi.single k₁ (dirZ e₁)) (Dv (Pi.single k₂ (dirZ e₂))
      (Dv (Pi.single k₃ (dirZ e₃)) f))) := by
  rw [nabla_succ _ hsaZ, nabla_succ _ hsaZ, nabla_succ _ hsaZ, ediff_eq_Dv, ediff_eq_Dv,
    ediff_eq_Dv]

theorem mabs_le_ord (γ : Fin m → Dir d → ℕ) (k : Fin m) : mabs (γ k) ≤ ord γ :=
  Finset.single_le_sum (f := fun k => mabs (γ k)) (fun _ _ => Nat.zero_le _) (mem_univ k)

theorem ord_three (γ : Fin m → Dir d → ℕ) (k₁ k₂ k₃ : Fin m) (e₁ e₂ e₃ : Dir d) :
    ord (γ + Pi.single k₁ (Pi.single e₁ 1) + Pi.single k₂ (Pi.single e₂ 1)
      + Pi.single k₃ (Pi.single e₃ 1)) = ord γ + 3 := by
  rw [ord_add, ord_add, ord_add, ord_single, ord_single, ord_single]

/-- Decomposition of a multi-index of order `≥ 3`. -/
theorem exists_three {γ : Fin m → Dir d → ℕ} (h : 3 ≤ ord γ) :
    ∃ (γ' : Fin m → Dir d → ℕ) (k₁ k₂ k₃ : Fin m) (e₁ e₂ e₃ : Dir d),
      γ = γ' + Pi.single k₁ (Pi.single e₁ 1) + Pi.single k₂ (Pi.single e₂ 1)
        + Pi.single k₃ (Pi.single e₃ 1) := by
  have hne : ∀ α : Fin m → Dir d → ℕ, 1 ≤ ord α → α ≠ 0 := by
    rintro α hα rfl; rw [ord_zero] at hα; omega
  obtain ⟨γ₁, k₃, e₃, rfl⟩ := exists_eq_add_single (hne γ (by omega))
  rw [ord_add, ord_single] at h
  obtain ⟨γ₂, k₂, e₂, rfl⟩ := exists_eq_add_single (hne γ₁ (by omega))
  rw [ord_add, ord_single] at h
  obtain ⟨γ₃, k₁, e₁, rfl⟩ := exists_eq_add_single (hne γ₂ (by omega))
  exact ⟨γ₃, k₁, k₂, k₃, e₁, e₂, e₃, rfl⟩

/-- Derivatives of order `≥ 3` of the remainder are those of `Φ`. -/
theorem nabla_rem_high (Φ : (Fin m → Zd d) → ℂ) {γ : Fin m → Dir d → ℕ} (h : 3 ≤ ord γ) :
    nabla (fun b u => b +ᵥ u) γ (fun w => Φ w - taylor2 Φ w) =
      nabla (fun b u => b +ᵥ u) γ Φ := by
  obtain ⟨γ', k₁, k₂, k₃, e₁, e₂, e₃, rfl⟩ := exists_three h
  rw [nabla_three, nabla_three, rem_D3]

/-- Positive third differences of `Φ` are bounded. -/
theorem D3_bound {Φ : (Fin m → Zd d) → ℂ} {K ε : ℝ} {P : ℕ} (hP : 3 ≤ P)
    (hΦ : ∀ (w : Fin m → Zd d) (γ : Fin m → Dir d → ℕ), (∀ k, mabs (γ k) ≤ P) →
      ‖nabla (fun b u => b +ᵥ u) γ Φ w‖ ≤ K * ε ^ ord γ)
    (k₁ k₂ k₃ : Fin m) (i₁ i₂ i₃ : Fin d) (t : Fin m → Zd d) :
    ‖Dv (ee k₁ i₁) (Dv (ee k₂ i₂) (Dv (ee k₃ i₃) Φ)) t‖ ≤ K * ε ^ 3 := by
  have h := hΦ t (0 + Pi.single k₁ (Pi.single (Sum.inl i₁) 1) + Pi.single k₂ (Pi.single (Sum.inl i₂) 1)
      + Pi.single k₃ (Pi.single (Sum.inl i₃) 1)) (fun k => by
    refine (mabs_le_ord _ k).trans ?_
    rw [ord_three, ord_zero]; omega)
  rw [nabla_three, nabla_zero _ hs0Z, ord_three, ord_zero, zero_add] at h
  exact h

/-! ### The path argument -/

theorem box_step {g : (Fin m → Zd d) → ℂ} {M : ℝ} (hM0 : 0 ≤ M) {ρ : ℕ} (h0 : g 0 = 0)
    (hM : ∀ t : Fin m → Zd d, (∀ k, supNormZ (t k) ≤ ρ) → ∀ k i, ‖Dv (ee k i) g t‖ ≤ M)
    (t : Fin m → Zd d) (ht : ∀ k, supNormZ (t k) ≤ ρ) :
    ‖g t‖ ≤ ((m * d * ρ : ℕ) : ℝ) * M := by
  have h := path_bound_multi g (M := M) (r := ρ) (fun t ht k i => hM t ht k i) t ht
  rw [h0, sub_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hM0)
  calc ∑ k, norm1 (t k) ≤ ∑ _k : Fin m, (d * ρ : ℝ) :=
        sum_le_sum fun k _ => (norm1_le (t k)).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast ht k) (Nat.cast_nonneg _))
    _ = ((m * d * ρ : ℕ) : ℝ) := by simp; ring

/-! ### The remainder estimate -/

theorem taylor2_bound {Φ : (Fin m → Zd d) → ℂ} {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) {P : ℕ}
    (hP : 3 ≤ P)
    (hΦ : ∀ (w : Fin m → Zd d) (γ : Fin m → Dir d → ℕ), (∀ k, mabs (γ k) ≤ P) →
      ‖nabla (fun b u => b +ᵥ u) γ Φ w‖ ≤ K * ε ^ ord γ)
    {r : ℕ} {w : Fin m → Zd d} (hw : ∀ k, supNormZ (w k) ≤ r) (γ : Fin m → Dir d → ℕ)
    (hγ : ∀ k, mabs (γ k) ≤ P) :
    ‖nabla (fun b u => b +ᵥ u) γ (fun w => Φ w - taylor2 Φ w) w‖ ≤
      K * ((m * d * (r + 2) : ℕ) : ℝ) ^ (3 - min (ord γ) 3) * ε ^ (max (ord γ) 3) := by
  set R : (Fin m → Zd d) → ℂ := fun w => Φ w - taylor2 Φ w with hR
  set S : ℝ := ((m * d * (r + 2) : ℕ) : ℝ) with hS
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  set C : ℝ := K * ε ^ 3 with hC
  have hC0 : 0 ≤ C := mul_nonneg hK (pow_nonneg hε 3)
  have B3 : ∀ t k₁ i₁ k₂ i₂ k₃ i₃, ‖Dv (ee k₁ i₁) (Dv (ee k₂ i₂) (Dv (ee k₃ i₃) R)) t‖ ≤ C := by
    intro t k₁ i₁ k₂ i₂ k₃ i₃
    rw [hR, rem_D3]; exact D3_bound hP hΦ _ _ _ _ _ _ t
  have B2 : ∀ t : Fin m → Zd d, (∀ k, supNormZ (t k) ≤ r + 2) → ∀ k i k' i',
      ‖Dv (ee k' i') (Dv (ee k i) R) t‖ ≤ S * C := fun t ht k i k' i' =>
    box_step hC0 (rem_D2_zero Φ k k' i i') (fun t _ k'' i'' => B3 t k'' i'' k' i' k i) t ht
  have B1 : ∀ t : Fin m → Zd d, (∀ k, supNormZ (t k) ≤ r + 2) → ∀ k i,
      ‖Dv (ee k i) R t‖ ≤ S * (S * C) := fun t ht k i =>
    box_step (mul_nonneg hS0 hC0) (rem_D1_zero Φ k i) (fun t ht k' i' => B2 t ht k i k' i') t ht
  have B0 : ∀ t : Fin m → Zd d, (∀ k, supNormZ (t k) ≤ r + 2) →
      ‖R t‖ ≤ S * (S * (S * C)) := fun t ht =>
    box_step (mul_nonneg hS0 (mul_nonneg hS0 hC0)) (rem_zero Φ) (fun t ht k i => B1 t ht k i) t ht
  have hbox : ∀ (c c' : Fin m → Zd d), (∀ k, supNormZ (c k) ≤ 1) → (∀ k, supNormZ (c' k) ≤ 1) →
      ∀ k, supNormZ ((w + c + c') k) ≤ r + 2 := by
    intro c c' hc hc' k
    have h1 := supNormZ_add_le ((w + c) k) (c' k)
    have h2 := supNormZ_add_le (w k) (c k)
    simp only [Pi.add_apply] at h1 h2 ⊢
    have := hw k; have := hc k; have := hc' k
    omega
  have hbox0 : ∀ k, supNormZ (w k) ≤ r + 2 := by
    intro k; simpa using hbox 0 0 (fun _ => by simp [supNormZ]) (fun _ => by simp [supNormZ]) k
  have hbox1 : ∀ c : Fin m → Zd d, (∀ k, supNormZ (c k) ≤ 1) →
      ∀ k, supNormZ ((w + c) k) ≤ r + 2 := by
    intro c hc k; simpa using hbox c 0 hc (fun _ => by simp [supNormZ]) k
  rcases Nat.lt_or_ge (ord γ) 3 with hq | hq
  · interval_cases hq' : ord γ
    · -- order `0`
      rw [ord_eq_zero hq', nabla_zero _ hs0Z]
      calc ‖R w‖ ≤ S * (S * (S * C)) := B0 w hbox0
        _ = _ := by simp only [hC]; norm_num; ring
    · -- order `1`
      obtain ⟨k, e, rfl⟩ := eq_single_of_ord_eq_one hq'
      rw [nabla_single _ hs0Z hsaZ, ediff_eq_Dv]
      obtain ⟨i, σ, c, hσ, hc, heq⟩ := Dv_dir k e R w
      rw [heq, norm_mul, hσ, one_mul]
      calc ‖Dv (ee k i) R (w + c)‖ ≤ S * (S * C) := B1 _ (hbox1 c hc) k i
        _ = _ := by simp only [hC]; norm_num; ring
    · -- order `2`
      have hne : γ ≠ 0 := by rintro rfl; rw [ord_zero] at hq'; omega
      obtain ⟨γ', k, e, rfl⟩ := exists_eq_add_single hne
      rw [ord_add, ord_single] at hq'
      obtain ⟨k', e', rfl⟩ := eq_single_of_ord_eq_one (show ord γ' = 1 by omega)
      rw [nabla_succ _ hsaZ, nabla_single _ hs0Z hsaZ, ediff_eq_Dv, ediff_eq_Dv]
      obtain ⟨i', σ, c, hσ, hc, heq⟩ := Dv_dir k' e' (Dv (Pi.single k (dirZ e)) R) w
      rw [heq, Dv_comm]
      obtain ⟨i, τ, c', hτ, hc', heq'⟩ := Dv_dir k e (Dv (ee k' i') R) (w + c)
      rw [heq', norm_mul, norm_mul, hσ, hτ, one_mul, one_mul]
      calc ‖Dv (ee k i) (Dv (ee k' i') R) (w + c + c')‖ ≤ S * C :=
            B2 _ (hbox c c' hc hc') k' i' k i
        _ = _ := by simp only [hC]; norm_num; ring
  · -- order `≥ 3`
    rw [hR, nabla_rem_high Φ hq, min_eq_right hq, max_eq_left hq, Nat.sub_self, pow_zero,
      mul_one]
    exact hΦ w γ hγ

end

end Loc
