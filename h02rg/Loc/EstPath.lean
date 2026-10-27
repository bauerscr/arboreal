import Loc.EstDefs

/-!
# Path estimates on `ℤ^d`

If the elementary differences `f(t + e_i) - f(t)` of a function on `ℤ^d` are bounded by `M` in a
box, then `‖f(u) - f(0)‖ ≤ ‖u‖_1 M` (walking from `0` to `u` along the coordinate axes).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d : ℕ}

/-- `‖u‖_1 = ∑_i |u_i|`. -/
def norm1 (u : Zd d) : ℝ := ∑ i, ((u i).natAbs : ℝ)

theorem norm1_nonneg (u : Zd d) : 0 ≤ norm1 u := sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem norm1_le (u : Zd d) : norm1 u ≤ d * supNormZ u := by
  unfold norm1
  calc ∑ i, ((u i).natAbs : ℝ) ≤ ∑ _i : Fin d, (supNormZ u : ℝ) :=
        sum_le_sum fun i _ => by exact_mod_cast natAbs_le_supNormZ u i
    _ = d * supNormZ u := by simp

/-- One coordinate: `‖f(t + a e_i) - f(t)‖ ≤ |a| M` if the steps on the segment are bounded. -/
theorem path_bound_one (f : Zd d → ℂ) {M : ℝ} (i : Fin d) (t : Zd d) (a : ℤ)
    (hM : ∀ c : ℤ, min 0 a ≤ c → c ≤ max 0 a →
      ‖f (t + c • Pi.single i 1 + Pi.single i 1) - f (t + c • Pi.single i 1)‖ ≤ M) :
    ‖f (t + a • Pi.single i 1) - f t‖ ≤ (a.natAbs : ℝ) * M := by
  -- induction on `a ≥ 0` and `a ≤ 0`
  have hpos : ∀ k : ℕ, (∀ c : ℤ, 0 ≤ c → c ≤ k →
      ‖f (t + c • Pi.single i 1 + Pi.single i 1) - f (t + c • Pi.single i 1)‖ ≤ M) →
      ‖f (t + (k : ℤ) • Pi.single i 1) - f t‖ ≤ (k : ℝ) * M := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro h
      have h1 := ih fun c hc hck => h c hc (by omega)
      have h2 := h k (by omega) (by omega)
      have e : t + ((k + 1 : ℕ) : ℤ) • (Pi.single i 1 : Zd d) =
          t + (k : ℤ) • Pi.single i 1 + Pi.single i 1 := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      rw [e]
      calc ‖f (t + (k : ℤ) • Pi.single i 1 + Pi.single i 1) - f t‖
          ≤ ‖f (t + (k : ℤ) • Pi.single i 1 + Pi.single i 1) - f (t + (k : ℤ) • Pi.single i 1)‖
            + ‖f (t + (k : ℤ) • Pi.single i 1) - f t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ M + k * M := add_le_add h2 h1
        _ = ((k + 1 : ℕ) : ℝ) * M := by push_cast; ring
  have hneg : ∀ k : ℕ, (∀ c : ℤ, -(k : ℤ) ≤ c → c ≤ 0 →
      ‖f (t + c • Pi.single i 1 + Pi.single i 1) - f (t + c • Pi.single i 1)‖ ≤ M) →
      ‖f (t + (-(k : ℤ)) • Pi.single i 1) - f t‖ ≤ (k : ℝ) * M := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro h
      have h1 := ih fun c hc hck => h c (by omega) hck
      have h2 := h (-((k : ℤ) + 1)) (by push_cast; omega) (by omega)
      have e : t + (-((k + 1 : ℕ) : ℤ)) • (Pi.single i 1 : Zd d) + Pi.single i 1 =
          t + (-(k : ℤ)) • Pi.single i 1 := by
        push_cast
        module
      push_cast at h2
      rw [show (-(↑k + 1 : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, e] at h2
      calc ‖f (t + (-((k + 1 : ℕ) : ℤ)) • Pi.single i 1) - f t‖
          ≤ ‖f (t + (-(k : ℤ)) • Pi.single i 1) - f (t + (-((k + 1 : ℕ) : ℤ)) • Pi.single i 1)‖
            + ‖f (t + (-(k : ℤ)) • Pi.single i 1) - f t‖ := by
            rw [norm_sub_rev (f (t + (-(k : ℤ)) • Pi.single i 1))]
            exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ M + k * M := add_le_add h2 h1
        _ = ((k + 1 : ℕ) : ℝ) * M := by push_cast; ring
  rcases le_total 0 a with ha | ha
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [Int.natAbs_natCast]
    exact hpos k fun c hc hck => hM c (by omega) (by omega)
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat ha
    subst hk
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    exact hneg k fun c hc hck => hM c (by omega) (by omega)

/-- The path estimate in a box around `0`. -/
theorem path_bound_box (f : Zd d → ℂ) {M : ℝ} {r : ℕ}
    (hM : ∀ t : Zd d, supNormZ t ≤ r → ∀ i, ‖f (t + Pi.single i 1) - f t‖ ≤ M) (u : Zd d)
    (hu : supNormZ u ≤ r) : ‖f u - f 0‖ ≤ norm1 u * M := by
  -- walk through the points `w_j = (u_0, …, u_{j-1}, 0, …, 0)`
  let w : ℕ → Zd d := fun j i => if (i : ℕ) < j then u i else 0
  have hw0 : w 0 = 0 := by funext i; simp [w]
  have hwd : w d = u := by funext i; simp [w, i.2]
  have hstep : ∀ j : ℕ, (hj : j < d) →
      ‖f (w (j + 1)) - f (w j)‖ ≤ ((u ⟨j, hj⟩).natAbs : ℝ) * M := by
    intro j hj
    have e : w (j + 1) = w j + u ⟨j, hj⟩ • Pi.single ⟨j, hj⟩ 1 := by
      funext i
      simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases hij : (i : ℕ) = j
      · have : i = ⟨j, hj⟩ := Fin.ext hij
        subst this; simp
      · have hne : i ≠ ⟨j, hj⟩ := fun h => hij (by rw [h])
        simp only [hne, if_false, mul_zero, add_zero]
        by_cases hlt : (i : ℕ) < j
        · simp [hlt, show (i : ℕ) < j + 1 by omega]
        · simp [hlt, show ¬ (i : ℕ) < j + 1 by omega]
    rw [e]
    refine path_bound_one f ⟨j, hj⟩ (w j) (u ⟨j, hj⟩) fun c hc1 hc2 => hM _ ?_ _
    rw [supNormZ_le_iff]
    intro i
    simp only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    have hui := (supNormZ_le_iff u r).1 hu i
    by_cases hij : i = ⟨j, hj⟩
    · subst hij
      simp only [lt_self_iff_false, if_false, if_true, mul_one, zero_add]
      have := (supNormZ_le_iff u r).1 hu ⟨j, hj⟩
      omega
    · simp only [hij, if_false, mul_zero, add_zero]
      split_ifs <;> omega
  have key : ∀ j ≤ d, ‖f (w j) - f (w 0)‖ ≤
      (∑ i ∈ univ.filter (fun i : Fin d => (i : ℕ) < j), ((u i).natAbs : ℝ)) * M := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j (by omega)
      have hs : univ.filter (fun i : Fin d => (i : ℕ) < j + 1) =
          insert ⟨j, by omega⟩ (univ.filter (fun i : Fin d => (i : ℕ) < j)) := by
        ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
      rw [hs, sum_insert (by simp)]
      calc ‖f (w (j + 1)) - f (w 0)‖ ≤ ‖f (w (j + 1)) - f (w j)‖ + ‖f (w j) - f (w 0)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by rw [add_mul]; exact add_le_add h2 h1
  have := key d le_rfl
  rw [hw0, hwd] at this
  have hf : univ.filter (fun i : Fin d => (i : ℕ) < d) = univ := by
    ext i; simp
  rwa [hf] at this

/-- The global path estimate: `‖f(u) - f(v)‖ ≤ ‖u - v‖_1 M`. -/
theorem path_bound (f : Zd d → ℂ) {M : ℝ} (hM : ∀ t i, ‖f (t + Pi.single i 1) - f t‖ ≤ M)
    (u v : Zd d) : ‖f u - f v‖ ≤ norm1 (u - v) * M := by
  have := path_bound_box (fun t => f (t + v)) (r := supNormZ (u - v))
    (fun t _ i => by rw [add_right_comm]; exact hM _ i) (u - v) le_rfl
  simpa using this

/-! ### Several points -/

/-- The path estimate for functions of `m` points of `ℤ^d`, in a box around `0`. -/
theorem path_bound_multi {m : ℕ} (f : (Fin m → Zd d) → ℂ) {M : ℝ} {r : ℕ}
    (hM : ∀ t : Fin m → Zd d, (∀ k, supNormZ (t k) ≤ r) → ∀ k i,
      ‖f (t + Pi.single k (Pi.single i 1)) - f t‖ ≤ M)
    (w : Fin m → Zd d) (hw : ∀ k, supNormZ (w k) ≤ r) :
    ‖f w - f 0‖ ≤ (∑ k, norm1 (w k)) * M := by
  let v : ℕ → Fin m → Zd d := fun j k => if (k : ℕ) < j then w k else 0
  have hv0 : v 0 = 0 := by funext k; simp [v]
  have hvm : v m = w := by funext k; simp [v, k.2]
  have hvbox : ∀ j k, supNormZ (v j k) ≤ r := by
    intro j k; simp only [v]; split_ifs
    · exact hw k
    · simp [supNormZ]
  have hstep : ∀ j : ℕ, (hj : j < m) → ‖f (v (j + 1)) - f (v j)‖ ≤ norm1 (w ⟨j, hj⟩) * M := by
    intro j hj
    set kj : Fin m := ⟨j, hj⟩
    let g : Zd d → ℂ := fun t => f (Function.update (v j) kj t)
    have hg0 : g 0 = f (v j) := by
      simp only [g]; congr 1; funext k
      by_cases hk : k = kj
      · subst hk; simp [v, kj]
      · simp [Function.update_of_ne hk]
    have hg1 : g (w kj) = f (v (j + 1)) := by
      simp only [g]; congr 1; funext k
      by_cases hk : k = kj
      · subst hk; simp [v, kj]
      · rw [Function.update_of_ne hk]
        simp only [v]
        have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
        by_cases hlt : (k : ℕ) < j
        · simp [hlt, show (k : ℕ) < j + 1 by omega]
        · simp [hlt, show ¬ (k : ℕ) < j + 1 by omega]
    have := path_bound_box g (r := r) (fun t ht i => by
      have hu : Function.update (v j) kj t + Pi.single kj (Pi.single i 1) =
          Function.update (v j) kj (t + Pi.single i 1) := by
        funext k
        by_cases hk : k = kj
        · subst hk; simp
        · simp [hk]
      have := hM (Function.update (v j) kj t) (fun k => by
        by_cases hk : k = kj
        · subst hk; simpa using ht
        · rw [Function.update_of_ne hk]; exact hvbox j k) kj i
      rwa [hu] at this) (w kj) (hw kj)
    rwa [hg0, hg1] at this
  have key : ∀ j ≤ m, ‖f (v j) - f (v 0)‖ ≤
      (∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), norm1 (w k)) * M := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j (by omega)
      have hs : univ.filter (fun k : Fin m => (k : ℕ) < j + 1) =
          insert ⟨j, by omega⟩ (univ.filter (fun k : Fin m => (k : ℕ) < j)) := by
        ext k; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
      rw [hs, sum_insert (by simp)]
      calc ‖f (v (j + 1)) - f (v 0)‖ ≤ ‖f (v (j + 1)) - f (v j)‖ + ‖f (v j) - f (v 0)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by rw [add_mul]; exact add_le_add h2 h1
  have := key m le_rfl
  rw [hv0, hvm] at this
  have hf : univ.filter (fun k : Fin m => (k : ℕ) < m) = univ := by
    ext k; simp
  rwa [hf] at this

end

end Loc
