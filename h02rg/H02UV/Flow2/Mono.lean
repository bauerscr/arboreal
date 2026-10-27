import Flow2.History

/-!
# Strict monotonicity of `b ↦ ǧ_N` (Expected result `thm:flow`(ii), abstract form)

The hypotheses `HHyp` of `prop:C6` do **not** imply that `b ↦ ǧ_N(b)` is increasing: (LG) only
bounds `|δG|` from above, and the history enters through `max_{i<j} dist3(t_i, t'_i)` with a
coefficient `a` that does not decay. Along two trajectories `δǧ_j` can lose a factor `1 - O(a)`
per step, while the history term compares `δǧ_j` with the *largest* earlier difference, which over
`N ≫ 1/a` steps is not controlled.

Here are sufficient additional hypotheses (`MonoHyp`):

* the *difference form* of (LG): `|δG_j - δg_j| ≤ a |δg_j| + a |δμ_j| + A ‖δx_j‖ + a M`;
* *fading memory* in (LG), (Lm), (LT): the history condition is
  `w^{j-1-i} dist3(t_i, t'_i) ≤ M` for `i < j` (with a fixed `0 < w ≤ 1`) instead of
  `dist3(t_i, t'_i) ≤ M`;

and numerical conditions on the cone constants (`MonoCoef`, satisfiable for small `a`:
`monoCoef_of_small`). Under these, `ǧ_N` is strictly increasing on `(0, b_max]`
(`gN_strictMonoOn`).

The proof compares two admissible trajectories `t, t'` with `b < b'`.
1. *The `μ`-cone* `|δg_k| ≤ p |δμ_k|`, `‖δx_k‖ ≤ q |δμ_k|`, `H_k ≤ r |δμ_k|` (`H_k` the fading
   history maximum `hmax`) is forward invariant and `|δμ|` does not decrease in it
   (`mu_cone_step`). Since `δμ_N = 0`, the cone holds at no `k ≤ N` (`not_mu_cone`).
2. *The `ǧ`-cone* `δǧ_k > 0`, `‖δx_k‖ ≤ q₂ δǧ_k`, `H_k ≤ r₂ δǧ_k` is then forward invariant:
   outside the `μ`-cone `|δμ_k| ≤ p₂ δǧ_k`, and the difference form of (LG) gives
   `δǧ_{k+1} ≥ (1 - c) δǧ_k` (`g_cone_step`).
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable (F : HData X) (Λ β δ κ cg cm cT : ℝ)

/-- **The additional hypotheses for monotonicity**: the difference form of (LG) and fading memory
in (LG), (Lm), (LT), with memory factor `w ∈ (0, 1]`. -/
structure MonoHyp (N : ℕ) (A a ε w : ℝ) : Prop where
  hw0 : 0 < w
  hw1 : w ≤ 1
  LGd : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    |F.G j t - F.G j t' - ((t j).1 - (t' j).1)| ≤ a * |(t j).1 - (t' j).1| +
      a * |(t j).2.1 - (t' j).2.1| + A * ‖(t j).2.2 - (t' j).2.2‖ + a * M
  Lm : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
      A * ‖(t j).2.2 - (t' j).2.2‖ + a * M
  LT : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    ‖F.T j t - F.T j t'‖ ≤ κ * ‖(t j).2.2 - (t' j).2.2‖ +
      a * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + a * M

/-- The loss factor `c = a + a p₂ + A q₂ + a r₂` of the `ǧ`-cone. -/
def cLoss (A a p₂ q₂ r₂ : ℝ) : ℝ := a + a * p₂ + A * q₂ + a * r₂

/-- **The numerical conditions** on the cone constants: `(p, q, r)` for the `μ`-cone,
`(p₂, q₂, r₂)` for the `ǧ`-cone. -/
structure MonoCoef (A a w p q r p₂ q₂ r₂ : ℝ) : Prop where
  hκ0 : 0 ≤ κ
  hA : 0 ≤ A
  ha : 0 ≤ a
  hp : 0 < p
  hq : 0 ≤ q
  hr : 1 + p + q ≤ r
  eg : (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2)
  ex : κ * q + a * (p + 1) + a * r ≤ q
  em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r)
  hΛ : 1 ≤ Λ
  hp₂ : 1 ≤ p₂ * p
  hq₂ : q₂ ≤ p₂ * q
  hr₂ : r₂ ≤ p₂ * r
  hq₂0 : 0 ≤ q₂
  hr₂0 : 0 ≤ r₂
  hc : cLoss A a p₂ q₂ r₂ < 1
  hx : κ * q₂ + a * (1 + p₂) + a * r₂ ≤ q₂ * (1 - cLoss A a p₂ q₂ r₂)
  hrr : 1 + p₂ + q₂ ≤ r₂ * (1 - cLoss A a p₂ q₂ r₂)
  hw : w ≤ 1 - cLoss A a p₂ q₂ r₂

/-! ### The fading history maximum -/

/-- `H_k = max_{i<k} w^{k-1-i} dist3(u_i, v_i)` (recursively). -/
def hmax (w : ℝ) (u v : Seq X) : ℕ → ℝ
  | 0 => 0
  | k + 1 => max (dist3 (u k) (v k)) (w * hmax w u v k)

variable {F Λ β δ κ cg cm cT}

lemma dist3_nonneg {j : ℕ} (s s' : ℝ × ℝ × X j) : 0 ≤ dist3 s s' := by
  unfold dist3; positivity

lemma hmax_nonneg {w : ℝ} (_hw : 0 ≤ w) (u v : Seq X) : ∀ k, 0 ≤ hmax w u v k
  | 0 => le_rfl
  | _ + 1 => le_max_of_le_left (dist3_nonneg _ _)

lemma hmax_bound {w : ℝ} (hw : 0 ≤ w) (u v : Seq X) :
    ∀ k, ∀ i < k, w ^ (k - 1 - i) * dist3 (u i) (v i) ≤ hmax w u v k
  | 0, i, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    rcases (show i = k ∨ i < k by omega) with rfl | hik
    · simp only [hmax, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      exact le_max_left _ _
    · have h := hmax_bound hw u v k i hik
      have e : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [e, pow_succ, mul_comm (w ^ (k - 1 - i)) w, mul_assoc]
      exact (mul_le_mul_of_nonneg_left h hw).trans (le_max_right _ _)

lemma hmax_succ_le {w : ℝ} (u v : Seq X) (k : ℕ) {B : ℝ}
    (h1 : dist3 (u k) (v k) ≤ B) (h2 : w * hmax w u v k ≤ B) : hmax w u v (k + 1) ≤ B :=
  max_le h1 h2

/-! ### The cones -/

section Cones

variable {N : ℕ} {A a ε w : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w)
include H HM

/-- One step of the `μ`-cone. -/
lemma mu_cone_step {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 1 + p + q ≤ r)
    (eg : (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) + a * r ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r))
    {k : ℕ} (hk : k < N) {u v : Seq X} (hu : InDh Λ β δ κ cg cm cT ε k u)
    (hv : InDh Λ β δ κ cg cm cT ε k v)
    (hg : |(u k).1 - (v k).1| ≤ p * |(u k).2.1 - (v k).2.1|)
    (hx : ‖(u k).2.2 - (v k).2.2‖ ≤ q * |(u k).2.1 - (v k).2.1|)
    (hh : hmax w u v k ≤ r * |(u k).2.1 - (v k).2.1|) :
    (1 + Λ) / 2 * |(u k).2.1 - (v k).2.1| ≤
        |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      |F.G k u - F.G k v| ≤ p * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      ‖F.T k u - F.T k v‖ ≤ q * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      dist3 (u k) (v k) ≤ r * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      w * hmax w u v k ≤ r * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| := by
  set D := |(u k).2.1 - (v k).2.1|
  have hD : 0 ≤ D := abs_nonneg _
  have hw0 := HM.hw0.le
  have hM : 0 ≤ hmax w u v k := hmax_nonneg hw0 u v k
  have hb := hmax_bound hw0 u v k
  have LGd := HM.LGd k hk u v hu hv _ hM hb
  have Lm := HM.Lm k hk u v hu hv _ hM hb
  have LT := HM.LT k hk u v hu hv _ hM hb
  have hΛ := H.hΛ; have hA := H.hA; have ha := H.ha; have hκ0 := H.hκ0
  set D' := |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)|
  have h1 : Λ * D ≤ D' + |F.m k u - F.m k v| := by
    have := abs_sub (Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)) (F.m k u - F.m k v)
    rw [show Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v) - (F.m k u - F.m k v)
      = Λ * ((u k).2.1 - (v k).2.1) by ring, abs_mul, abs_of_pos (by linarith : 0 < Λ)] at this
    exact this
  have hG : |F.G k u - F.G k v| ≤ |(u k).1 - (v k).1| + (a * |(u k).1 - (v k).1| +
      a * D + A * ‖(u k).2.2 - (v k).2.2‖ + a * hmax w u v k) := by
    have := abs_add_le (F.G k u - F.G k v - ((u k).1 - (v k).1)) ((u k).1 - (v k).1)
    rw [sub_add_cancel] at this
    linarith
  have a1 : A * |(u k).1 - (v k).1| ≤ A * (p * D) := mul_le_mul_of_nonneg_left hg hA
  have a2 : A * ‖(u k).2.2 - (v k).2.2‖ ≤ A * (q * D) := mul_le_mul_of_nonneg_left hx hA
  have a4 : κ * ‖(u k).2.2 - (v k).2.2‖ ≤ κ * (q * D) := mul_le_mul_of_nonneg_left hx hκ0
  have a5 : a * |(u k).1 - (v k).1| ≤ a * (p * D) := mul_le_mul_of_nonneg_left hg ha
  have a6 : a * hmax w u v k ≤ a * (r * D) := mul_le_mul_of_nonneg_left hh ha
  have b1 := mul_le_mul_of_nonneg_right em hD
  have b2 := mul_le_mul_of_nonneg_right eg hD
  have b3 := mul_le_mul_of_nonneg_right ex hD
  have hD' : (1 + Λ) / 2 * D ≤ D' := by linarith only [h1, Lm, a1, a2, a6, b1]
  have hDD : D ≤ D' := by
    have := mul_nonneg (sub_nonneg.2 hΛ.le) hD
    linarith only [hD', this]
  have b4 := mul_le_mul_of_nonneg_left hD' hp
  have b5 := mul_le_mul_of_nonneg_left hDD hq
  have hr0 : 0 ≤ r := by linarith
  have b6 := mul_le_mul_of_nonneg_left hDD hr0
  refine ⟨hD', ?_, ?_, ?_, ?_⟩
  · linarith only [hG, hg, a2, a5, a6, b2, b4]
  · linarith only [LT, a4, a5, a6, b3, b5]
  · unfold dist3
    have := mul_le_mul_of_nonneg_right hr hD
    linarith only [hg, hx, this, b6]
  · have c1 := mul_le_mul_of_nonneg_left hh hw0
    have c2 : 0 ≤ (1 - w) * (r * D) := mul_nonneg (by linarith [HM.hw1]) (mul_nonneg hr0 hD)
    linarith only [c1, c2, b6]

end Cones

/-! ### Two admissible trajectories -/

section Two

variable {N : ℕ} {A a ε w : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A a ε)
  (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w)
include H HM

/-- **No `μ`-cone along two distinct admissible trajectories.** -/
lemma not_mu_cone {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 1 + p + q ≤ r)
    (eg : (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) + a * r ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r))
    {b b' μ μ' : ℝ} (hb : b ≠ b') (h : Admissible F Λ κ cm cT N ε b μ)
    (h' : Admissible F Λ κ cm cT N ε b' μ') {k : ℕ} (hk : k ≤ N)
    (hg : |(traj F Λ b' μ' k).1 - (traj F Λ b μ k).1| ≤
      p * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|)
    (hx : ‖(traj F Λ b' μ' k).2.2 - (traj F Λ b μ k).2.2‖ ≤
      q * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|)
    (hh : hmax w (traj F Λ b' μ') (traj F Λ b μ) k ≤
      r * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|) : False := by
  set u := traj F Λ b' μ'
  set v := traj F Λ b μ
  have hΛ := H.hΛ
  -- forward invariance
  have key : ∀ n, k + n ≤ N →
      |(u (k + n)).1 - (v (k + n)).1| ≤ p * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      ‖(u (k + n)).2.2 - (v (k + n)).2.2‖ ≤ q * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      hmax w u v (k + n) ≤ r * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      |(u k).2.1 - (v k).2.1| ≤ |(u (k + n)).2.1 - (v (k + n)).2.1| := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hg, hx, hh, le_rfl⟩
    | succ n ih =>
      intro hkn
      have hlt : k + n < N := by omega
      obtain ⟨ig, ix, ih', iμ⟩ := ih (by omega)
      obtain ⟨s1, s2, s3, s4, s5⟩ := mu_cone_step H HM hp hq hr eg ex em hlt
        (admissible_InDh H h' (k + n) hlt.le) (admissible_InDh H h (k + n) hlt.le) ig ix ih'
      have e0 := traj_succ H b' μ' hlt
      have e1 := traj_succ H b μ hlt
      have hmu : |(u (k + n)).2.1 - (v (k + n)).2.1| ≤
          |Λ * (u (k + n)).2.1 + F.m (k + n) u - (Λ * (v (k + n)).2.1 + F.m (k + n) v)| := by
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (1 + Λ) / 2 by linarith)
          (abs_nonneg ((u (k + n)).2.1 - (v (k + n)).2.1))
        linarith
      rw [← add_assoc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [u, v] at e0 e1 ⊢; rw [e0, e1]; exact s2
      · simp only [u, v] at e0 e1 ⊢; rw [e0, e1]; exact s3
      · refine hmax_succ_le u v (k + n) ?_ ?_
        · simp only [u, v] at e0 e1 s4 ⊢; rw [e0, e1]; exact s4
        · simp only [u, v] at e0 e1 s5 ⊢; rw [e0, e1]; exact s5
      · refine iμ.trans (hmu.trans (le_of_eq ?_))
        simp only [u, v] at e0 e1 ⊢; rw [e0, e1]
  obtain ⟨-, -, -, hμ⟩ := key (N - k) (by omega)
  rw [show k + (N - k) = N by omega, h'.2, h.2, sub_self, abs_zero] at hμ
  have hm0 : |(u k).2.1 - (v k).2.1| = 0 := le_antisymm hμ (abs_nonneg _)
  rw [hm0, mul_zero] at hg hh
  have hw0 := HM.hw0
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have : |(u 0).1 - (v 0).1| = 0 := le_antisymm hg (abs_nonneg _)
    simp only [u, v, traj_zero, abs_eq_zero, sub_eq_zero] at this
    exact hb this.symm
  · have h0 := hmax_bound hw0.le u v k 0 hk0
    have hd : dist3 (u 0) (v 0) ≤ 0 := by
      have hpos : 0 < w ^ (k - 1 - 0) := pow_pos hw0 _
      have := h0.trans hh
      by_contra hc
      push Not at hc
      have := mul_pos hpos hc
      linarith
    have : |(u 0).1 - (v 0).1| = 0 := by
      unfold dist3 at hd
      have := abs_nonneg ((u 0).2.1 - (v 0).2.1)
      have := norm_nonneg ((u 0).2.2 - (v 0).2.2)
      exact le_antisymm (by linarith) (abs_nonneg _)
    simp only [u, v, traj_zero, abs_eq_zero, sub_eq_zero] at this
    exact hb this.symm

/-- One step of the `ǧ`-cone. -/
lemma g_cone_step {p₂ q₂ r₂ : ℝ} (hc : cLoss A a p₂ q₂ r₂ < 1)
    (hx2 : κ * q₂ + a * (1 + p₂) + a * r₂ ≤ q₂ * (1 - cLoss A a p₂ q₂ r₂))
    (hrr : 1 + p₂ + q₂ ≤ r₂ * (1 - cLoss A a p₂ q₂ r₂))
    (hw : w ≤ 1 - cLoss A a p₂ q₂ r₂) (hr₂0 : 0 ≤ r₂)
    {k : ℕ} (hk : k < N) {u v : Seq X} (hu : InDh Λ β δ κ cg cm cT ε k u)
    (hv : InDh Λ β δ κ cg cm cT ε k v)
    (he : 0 < (u k).1 - (v k).1)
    (hm : |(u k).2.1 - (v k).2.1| ≤ p₂ * ((u k).1 - (v k).1))
    (hx : ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1))
    (hh : hmax w u v k ≤ r₂ * ((u k).1 - (v k).1)) :
    (1 - cLoss A a p₂ q₂ r₂) * ((u k).1 - (v k).1) ≤ F.G k u - F.G k v ∧
      ‖F.T k u - F.T k v‖ ≤ q₂ * (F.G k u - F.G k v) ∧
      dist3 (u k) (v k) ≤ r₂ * (F.G k u - F.G k v) ∧
      w * hmax w u v k ≤ r₂ * (F.G k u - F.G k v) := by
  set e := (u k).1 - (v k).1
  set c := cLoss A a p₂ q₂ r₂ with hcd
  have hw0 := HM.hw0.le
  have hM : 0 ≤ hmax w u v k := hmax_nonneg hw0 u v k
  have hb := hmax_bound hw0 u v k
  have LGd := HM.LGd k hk u v hu hv _ hM hb
  have LT := HM.LT k hk u v hu hv _ hM hb
  have hA := H.hA; have ha := H.ha; have hκ0 := H.hκ0
  have he' : |e| = e := abs_of_pos he
  rw [he'] at LGd LT
  have a1 : a * |(u k).2.1 - (v k).2.1| ≤ a * (p₂ * e) := mul_le_mul_of_nonneg_left hm ha
  have a2 : A * ‖(u k).2.2 - (v k).2.2‖ ≤ A * (q₂ * e) := mul_le_mul_of_nonneg_left hx hA
  have a3 : a * hmax w u v k ≤ a * (r₂ * e) := mul_le_mul_of_nonneg_left hh ha
  have a4 : κ * ‖(u k).2.2 - (v k).2.2‖ ≤ κ * (q₂ * e) := mul_le_mul_of_nonneg_left hx hκ0
  have ec : c * e = a * e + a * (p₂ * e) + A * (q₂ * e) + a * (r₂ * e) := by
    rw [hcd]; unfold cLoss; ring
  have hlow : (1 - c) * e ≤ F.G k u - F.G k v := by
    have := (abs_le.1 LGd).1
    linarith only [this, a1, a2, a3, ec]
  have hc0 : 0 < 1 - c := by linarith
  have hT : ‖F.T k u - F.T k v‖ ≤ q₂ * (1 - c) * e := by
    have b1 := mul_le_mul_of_nonneg_right hx2 he.le
    linarith only [LT, a1, a3, a4, b1]
  have hq₂0 : 0 ≤ q₂ := by
    have : 0 ≤ κ * q₂ + a * (1 + p₂) + a * r₂ := by
      have := mul_nonneg ha (show 0 ≤ 1 + p₂ by
        by_contra hn; push Not at hn
        have := abs_nonneg ((u k).2.1 - (v k).2.1)
        have := mul_neg_of_neg_of_pos (show p₂ < 0 by linarith) he
        linarith)
      have := mul_nonneg hκ0 (show 0 ≤ q₂ by
        by_contra hn; push Not at hn
        have := norm_nonneg ((u k).2.2 - (v k).2.2)
        have := mul_neg_of_neg_of_pos hn he
        linarith)
      have := mul_nonneg ha hr₂0
      linarith
    exact nonneg_of_mul_nonneg_left (this.trans hx2) hc0
  refine ⟨hlow, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hlow hq₂0
    linarith only [hT, this]
  · have hd : dist3 (u k) (v k) ≤ (1 + p₂ + q₂) * e := by
      unfold dist3
      rw [he']
      linarith only [hm, hx]
    have b1 := mul_le_mul_of_nonneg_right hrr he.le
    have b2 := mul_le_mul_of_nonneg_left hlow hr₂0
    linarith only [hd, b1, b2]
  · have b1 := mul_le_mul_of_nonneg_left hh hw0
    have b2 : w * (r₂ * e) ≤ (1 - c) * (r₂ * e) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    have b3 := mul_le_mul_of_nonneg_left hlow hr₂0
    linarith only [b1, b2, b3]

/-- **Monotonicity along two admissible trajectories.** -/
theorem traj_strict_mono {p q r p₂ q₂ r₂ : ℝ} (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂)
    {b b' μ μ' : ℝ} (hbb : b < b') (h : Admissible F Λ κ cm cT N ε b μ)
    (h' : Admissible F Λ κ cm cT N ε b' μ') :
    (traj F Λ b μ N).1 < (traj F Λ b' μ' N).1 := by
  set u := traj F Λ b' μ'
  set v := traj F Λ b μ
  have hp := hC.hp
  have hq := hC.hq
  have hp₂0 : 0 ≤ p₂ := by
    by_contra hn; push Not at hn
    have := mul_neg_of_neg_of_pos hn hp
    linarith [hC.hp₂]
  -- outside the `μ`-cone
  have hout : ∀ k ≤ N, 0 < (u k).1 - (v k).1 → ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1) →
      hmax w u v k ≤ r₂ * ((u k).1 - (v k).1) →
      |(u k).2.1 - (v k).2.1| ≤ p₂ * ((u k).1 - (v k).1) := by
    intro k hk he hx hh
    by_contra hn
    push Not at hn
    set e := (u k).1 - (v k).1
    set m := |(u k).2.1 - (v k).2.1|
    refine not_mu_cone H HM hp.le hq hC.hr hC.eg hC.ex hC.em hbb.ne h h' hk ?_ ?_ ?_
    · show |e| ≤ p * m
      rw [abs_of_pos he]
      have h1 := mul_le_mul_of_nonneg_right hC.hp₂ he.le
      have h2 : p₂ * e * p < m * p := mul_lt_mul_of_pos_right hn hp
      linarith only [h1, h2]
    · show ‖(u k).2.2 - (v k).2.2‖ ≤ q * m
      refine hx.trans ?_
      have h1 : q₂ * e ≤ p₂ * q * e := mul_le_mul_of_nonneg_right hC.hq₂ he.le
      have h2 : p₂ * e * q ≤ m * q := mul_le_mul_of_nonneg_right hn.le hq
      linarith only [h1, h2]
    · show hmax w u v k ≤ r * m
      refine hh.trans ?_
      have hr0 : 0 ≤ r := by linarith [hC.hr]
      have h1 : r₂ * e ≤ p₂ * r * e := mul_le_mul_of_nonneg_right hC.hr₂ he.le
      have h2 : p₂ * e * r ≤ m * r := mul_le_mul_of_nonneg_right hn.le hr0
      linarith only [h1, h2]
  -- the `ǧ`-cone
  have key : ∀ k ≤ N, 0 < (u k).1 - (v k).1 ∧
      ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1) ∧
      hmax w u v k ≤ r₂ * ((u k).1 - (v k).1) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [u, v, traj_zero, sub_self, norm_zero, hmax]
      refine ⟨by linarith, ?_, ?_⟩
      · exact mul_nonneg hC.hq₂0 (by linarith)
      · exact mul_nonneg hC.hr₂0 (by linarith)
    | succ k ih =>
      intro hk
      have hlt : k < N := by omega
      obtain ⟨ie, ix, ih'⟩ := ih (by omega)
      have im := hout k hlt.le ie ix ih'
      obtain ⟨s1, s2, s3, s4⟩ := g_cone_step H HM hC.hc hC.hx hC.hrr hC.hw hC.hr₂0 hlt
        (admissible_InDh H h' k hlt.le) (admissible_InDh H h k hlt.le) ie im ix ih'
      have e0 := traj_succ H b' μ' hlt
      have e1 := traj_succ H b μ hlt
      have hc0 : 0 < 1 - cLoss A a p₂ q₂ r₂ := by linarith [hC.hc]
      refine ⟨?_, ?_, ?_⟩
      · simp only [u, v] at e0 e1 s1 ⊢; rw [e0, e1]
        exact lt_of_lt_of_le (mul_pos hc0 ie) s1
      · simp only [u, v] at e0 e1 s2 ⊢; rw [e0, e1]; exact s2
      · refine hmax_succ_le u v k ?_ ?_
        · simp only [u, v] at e0 e1 s3 ⊢; rw [e0, e1]; exact s3
        · simp only [u, v] at e0 e1 s4 ⊢; rw [e0, e1]; exact s4
  have := (key N le_rfl).1
  linarith

end Two

/-! ### Strict monotonicity of `ǧ_N` -/

/-- **Strict monotonicity on any set of admissible initial data** (generic in the `b`-range):
if `μ^c(b)` is admissible for every `b ∈ I`, then `b ↦ ǧ_N(b, μ^c(b))` is strictly increasing
on `I`. -/
theorem strictMonoOn_of_admissible {N : ℕ} {A a ε w p q r p₂ q₂ r₂ : ℝ}
    (H : HHyp F Λ β δ κ cg cm cT N A a ε) (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w)
    (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂) {I : Set ℝ} {μc : ℝ → ℝ}
    (hadm : ∀ b ∈ I, Admissible F Λ κ cm cT N ε b (μc b)) :
    StrictMonoOn (fun b => (traj F Λ b (μc b) N).1) I :=
  fun _ hb _ hb' hbb => traj_strict_mono H HM hC hbb (hadm _ hb) (hadm _ hb')

/-- **Expected result `thm:flow`(ii) (abstract form)**: under the additional hypotheses
`MonoHyp` and the numerical conditions `MonoCoef`, `b ↦ ǧ_N(b)` is strictly increasing on
`(0, b_max]`. -/
theorem gN_strictMonoOn {N : ℕ} {A a ε w p q r p₂ q₂ r₂ : ℝ}
    (H : HHyp F Λ β δ κ cg cm cT N A a ε) (HM : MonoHyp F Λ β δ κ cg cm cT N A a ε w)
    (hC : MonoCoef Λ κ A a w p q r p₂ q₂ r₂) (he : ε ≤ eps0u Λ β δ κ cg cm) (hε : 0 < ε) :
    StrictMonoOn (gN F Λ κ cm cT N ε) (Ioc 0 (bmax β δ cg N ε)) := by
  intro b hb b' hb' hbb
  exact traj_strict_mono H HM hC hbb (muc_spec H he hε hb) (muc_spec H he hε hb')

/-! ### The numerical conditions are satisfiable for small `a` -/

lemma mul_le_of_le_div' {a X Y : ℝ} (hX : 0 < X) (h : a ≤ Y / X) : a * X ≤ Y :=
  (le_div_iff₀ hX).1 h

/-- **`MonoCoef` holds for small `a`**: given `Λ > 1`, `0 ≤ κ < 1`, `A ≥ 0` and the memory
factor `0 < w < 1`, there is `a₁ > 0` such that for `0 ≤ a ≤ a₁` the conditions hold with
`p = (Λ-1)/(8(A+1))`, `q = 4a(p+1)/(1-κ)`, `r = 1+p+q`, `p₂ = 4/p`, `q₂ = 2a(3+2p₂)/(1-κ)`,
`r₂ = 2+p₂`. -/
theorem monoCoef_of_small {Λ κ A w : ℝ} (hΛ : 1 < Λ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hA : 0 ≤ A)
    (hw1 : w < 1) :
    ∃ a₁ > 0, ∀ a, 0 ≤ a → a ≤ a₁ → ∃ p q r p₂ q₂ r₂ : ℝ, MonoCoef Λ κ A a w p q r p₂ q₂ r₂ := by
  obtain ⟨s, hsd⟩ : ∃ s, s = 1 - κ := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsd]; linarith
  obtain ⟨p, hpd⟩ : ∃ p, p = (Λ - 1) / (8 * (A + 1)) := ⟨_, rfl⟩
  have hp : 0 < p := by rw [hpd]; have := sub_pos.2 hΛ; positivity
  have hAp : A * p ≤ (Λ - 1) / 8 := by
    rw [hpd, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := sub_pos.2 hΛ
    nlinarith
  obtain ⟨P, hPd⟩ : ∃ P, P = p + 1 := ⟨_, rfl⟩
  have hP : 0 < P := by rw [hPd]; linarith
  obtain ⟨p₂, hp₂d⟩ : ∃ p₂, p₂ = 4 / p := ⟨_, rfl⟩
  have hp₂ : 0 < p₂ := by rw [hp₂d]; positivity
  have hp₂p : p₂ * p = 4 := by rw [hp₂d]; field_simp
  obtain ⟨K, hKd⟩ : ∃ K, K = 3 + 2 * p₂ := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKd]; linarith
  obtain ⟨B, hBd⟩ : ∃ B, B = 1 + 2 * A / s := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hBd]; positivity
  -- the bounds `a X_i ≤ Y_i`
  obtain ⟨X3, hX3⟩ : ∃ X, X = P * (2 + 4 * (A + 1) / s) := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ X, X = (2 + p) + 4 * P * (A + 1) / s := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ X, X = 2 * K / s + K * B * (2 + p₂) := ⟨_, rfl⟩
  have hX3p : 0 < X3 := by rw [hX3]; positivity
  have hX4p : 0 < X4 := by rw [hX4]; positivity
  have hX7p : 0 < X7 := by rw [hX7]; positivity
  have hKB : 0 < K * B := mul_pos hK hB
  have hY3 : 0 < p * (Λ - 1) / 2 := by have := sub_pos.2 hΛ; positivity
  have hY4 : 0 < 3 / 8 * (Λ - 1) := by have := sub_pos.2 hΛ; positivity
  refine ⟨min (min (s / 2) 1) (min (p * (Λ - 1) / 2 / X3) (min (3 / 8 * (Λ - 1) / X4)
    (min (s / 2 / (K * B)) (min ((1 - w) / (K * B)) (1 / X7))))), ?_, ?_⟩
  · have : 0 < 1 - w := by linarith
    refine lt_min (lt_min (by positivity) one_pos) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))))
  intro a ha ha₁
  have h1 : a ≤ s / 2 := ha₁.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : a ≤ 1 := ha₁.trans ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : a * X3 ≤ p * (Λ - 1) / 2 :=
    mul_le_of_le_div' hX3p (ha₁.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h4 : a * X4 ≤ 3 / 8 * (Λ - 1) := mul_le_of_le_div' hX4p
    (ha₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have h5 : a * (K * B) ≤ s / 2 := mul_le_of_le_div' hKB (ha₁.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have h6 : a * (K * B) ≤ 1 - w := mul_le_of_le_div' hKB (ha₁.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))))
  have h7 : a * X7 ≤ 1 := mul_le_of_le_div' hX7p (ha₁.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))))
  -- the cone constants
  obtain ⟨q, hqd⟩ : ∃ q, q = 4 * a * P / s := ⟨_, rfl⟩
  obtain ⟨q₂, hq₂d⟩ : ∃ q₂, q₂ = 2 * a * K / s := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqd]; positivity
  have hq₂0 : 0 ≤ q₂ := by rw [hq₂d]; positivity
  have hqs : q * s = 4 * a * P := by rw [hqd]; field_simp
  have hq₂s : q₂ * s = 2 * a * K := by rw [hq₂d]; field_simp
  have hcl : cLoss A a p₂ q₂ (2 + p₂) = a * (K * B) := by
    unfold cLoss; rw [hq₂d, hKd, hBd]; field_simp; ring
  have hκq : κ * q = q - q * s := by rw [hsd]; ring
  have hκq₂ : κ * q₂ = q₂ - q₂ * s := by rw [hsd]; ring
  have hqA : a * X3 = 2 * a * P + q * (A + 1) := by rw [hX3, hqd]; field_simp
  have hqA4 : a * X4 = a * (2 + p) + q * (A + 1) := by rw [hX4, hqd]; field_simp
  have hqa : q * (A + a) ≤ q * (A + 1) := mul_le_mul_of_nonneg_left (by linarith) hq0
  have hqP : q ≤ 2 * P := by
    have : q * s ≤ 2 * P * s := by
      rw [hqs]; have := mul_le_mul_of_nonneg_right h1 hP.le; nlinarith
    exact le_of_mul_le_mul_right this hs
  have haq : a * q ≤ a * (2 * P) := mul_le_mul_of_nonneg_left hqP ha
  refine ⟨p, q, 1 + p + q, p₂, q₂, 2 + p₂, ⟨hκ0, hA, ha, hp, hq0, le_rfl, ?_, ?_, ?_, hΛ.le,
    by rw [hp₂p]; norm_num, ?_, ?_, hq₂0, by linarith, ?_, ?_, ?_, ?_⟩⟩
  · -- eg
    have e : (1 + a) * p + a + A * q + a * (1 + p + q) = p + (2 * a * P + q * (A + a)) := by
      rw [hPd]; ring
    rw [e]
    have e2 : p * ((1 + Λ) / 2) = p + p * (Λ - 1) / 2 := by ring
    rw [e2]
    linarith only [h3, hqA, hqa]
  · -- ex
    rw [hκq]
    have e : a * (p + 1) + a * (1 + p + q) = 2 * a * P + a * q := by rw [hPd]; ring
    linarith only [e, haq, hqs]
  · -- em
    have e : A * p + a + A * q + a * (1 + p + q) = A * p + (a * (2 + p) + q * (A + a)) := by ring
    rw [e]
    linarith only [hAp, h4, hqA4, hqa]
  · -- hq₂
    have e : p₂ * q - q₂ = 10 * a / s := by
      rw [hqd, hq₂d, hKd, hPd]; field_simp; rw [hp₂d]; field_simp; ring
    have : 0 ≤ 10 * a / s := by positivity
    linarith
  · -- hr₂
    have e : p₂ * (1 + p + q) = p₂ + p₂ * p + p₂ * q := by ring
    rw [e, hp₂p]
    have := mul_nonneg hp₂.le hq0
    linarith
  · -- hc
    rw [hcl]; linarith
  · -- hx
    rw [hcl, hκq₂]
    have e : a * (1 + p₂) + a * (2 + p₂) = a * K := by rw [hKd]; ring
    have hc2 : q₂ * (a * (K * B)) ≤ q₂ * (s / 2) := mul_le_mul_of_nonneg_left h5 hq₂0
    have e2 : q₂ * (s / 2) = a * K := by linarith only [hq₂s]
    linarith only [e, hc2, e2, hq₂s]
  · -- hrr
    rw [hcl]
    have e : a * X7 = q₂ + a * (K * B) * (2 + p₂) := by rw [hX7, hq₂d]; field_simp
    linarith only [h7, e]
  · -- hw
    rw [hcl]; linarith

end Hist

end Flow2
