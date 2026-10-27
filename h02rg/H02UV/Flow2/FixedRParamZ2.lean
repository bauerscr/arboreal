import Flow2.Mono
import Flow2.Hor2Unique

/-!
# Strict monotonicity of `b ↦ ǧ_N` with a hidden `ζ`-channel

`Flow2/Mono.lean` proves strict monotonicity under `MonoHyp` (difference form of (LG), fading
memory), whose (Lm) has a *small* coefficient `a` of the past. For the RG map without the mass
condition `m² L^{2(N_h+1)} ≤ ϑ`, the past enters `m_j` through the hidden coupling `ζ_j` with a
coefficient of order one (`Flow2/Hor2Unique.lean`). Here:

* `MonoZHyp`: (LGd), (LT) as in `MonoHyp`, (Lmz) `|δm_j| ≤ … + b_ζ ‖δζ_j‖`, and
  (LZ) `‖δζ_{j+1}‖ ≤ A_ζ(|δg_j| + ‖δx_j‖) + a(|δμ_j| + M)`, all with fading memory;
* `MonoZCoef`: the numerical conditions. The `μ`-cone carries `‖δζ_k‖ ≤ s|δμ_k|` (`s` of order
  one, `b_ζ s ≤ (Λ-1)/8`), the `ǧ`-cone `‖δζ_k‖ ≤ z₂ δǧ_k`;
* `mu_cone_step_z`, `not_mu_cone_z`, `g_cone_step_z`, `traj_strict_mono_z`,
  `strictMonoOn_adm_z`: as in `Flow2/Mono.lean`.

The constants are not tied to those of `HHyp` (which may be large); `HHyp` is used only for the
recursion `traj_succ` and the domain.
-/

open Set Filter Topology

noncomputable section

namespace Flow2

namespace Hist

variable {X : ℕ → Type*} [∀ j, NormedAddCommGroup (X j)]
variable {E : Type*} [NormedAddCommGroup E]
variable (F : HData X) (Λ β δ κ cg cm cT : ℝ)

/-- **Monotonicity hypotheses with a hidden coupling `Z`** (fading memory `w`). -/
structure MonoZHyp (N : ℕ) (Z : ℕ → Seq X → E) (A a Aζ bζ ε w : ℝ) : Prop where
  hw0 : 0 < w
  hw1 : w ≤ 1
  hA : 0 ≤ A
  ha : 0 ≤ a
  hAζ : 0 ≤ Aζ
  hbζ : 0 ≤ bζ
  Z0 : ∀ t t' : Seq X, Z 0 t = Z 0 t'
  LGd : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    |F.G j t - F.G j t' - ((t j).1 - (t' j).1)| ≤ a * |(t j).1 - (t' j).1| +
      a * |(t j).2.1 - (t' j).2.1| + A * ‖(t j).2.2 - (t' j).2.2‖ + a * M
  Lmz : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    |F.m j t - F.m j t'| ≤ A * |(t j).1 - (t' j).1| + a * |(t j).2.1 - (t' j).2.1| +
      A * ‖(t j).2.2 - (t' j).2.2‖ + a * M + bζ * ‖Z j t - Z j t'‖
  LT : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    ‖F.T j t - F.T j t'‖ ≤ κ * ‖(t j).2.2 - (t' j).2.2‖ +
      a * (|(t j).1 - (t' j).1| + |(t j).2.1 - (t' j).2.1|) + a * M
  LZ : ∀ j < N, ∀ t t', InDh Λ β δ κ cg cm cT ε j t → InDh Λ β δ κ cg cm cT ε j t' →
    ∀ M, 0 ≤ M → (∀ i < j, w ^ (j - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    ‖Z (j + 1) t - Z (j + 1) t'‖ ≤ Aζ * (|(t j).1 - (t' j).1| + ‖(t j).2.2 - (t' j).2.2‖) +
      a * (|(t j).2.1 - (t' j).2.1| + M)

/-- **The numerical conditions** with a hidden coupling: `(p, q, r, s)` for the `μ`-cone,
`(p₂, q₂, r₂, z₂)` for the `ǧ`-cone. -/
structure MonoZCoef (A a Aζ bζ w p q r s p₂ q₂ r₂ z₂ : ℝ) : Prop where
  hκ0 : 0 ≤ κ
  hp : 0 < p
  hq : 0 ≤ q
  hr : 1 + p + q ≤ r
  hs0 : 0 ≤ s
  eg : (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2)
  ex : κ * q + a * (p + 1) + a * r ≤ q
  em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r + bζ * s)
  esz : Aζ * (p + q) + a * (1 + r) ≤ s
  hΛ : 1 ≤ Λ
  hp₂ : 1 ≤ p₂ * p
  hq₂ : q₂ ≤ p₂ * q
  hr₂ : r₂ ≤ p₂ * r
  hz₂ : z₂ ≤ p₂ * s
  hq₂0 : 0 ≤ q₂
  hr₂0 : 0 ≤ r₂
  hz₂0 : 0 ≤ z₂
  hc : cLoss A a p₂ q₂ r₂ < 1
  hx : κ * q₂ + a * (1 + p₂) + a * r₂ ≤ q₂ * (1 - cLoss A a p₂ q₂ r₂)
  hrr : 1 + p₂ + q₂ ≤ r₂ * (1 - cLoss A a p₂ q₂ r₂)
  hw : w ≤ 1 - cLoss A a p₂ q₂ r₂
  hzz : Aζ * (1 + q₂) + a * (p₂ + r₂) ≤ z₂ * (1 - cLoss A a p₂ q₂ r₂)

variable {F Λ β δ κ cg cm cT}

section Cones

variable {N : ℕ} {Z : ℕ → Seq X → E} {A a Aζ bζ ε w : ℝ}
  (HM : MonoZHyp F Λ β δ κ cg cm cT N Z A a Aζ bζ ε w)
include HM

/-- One step of the `μ`-cone with a hidden coupling. -/
lemma mu_cone_step_z {p q r s : ℝ} (hΛ : 1 ≤ Λ) (hκ0 : 0 ≤ κ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 1 + p + q ≤ r) (hs0 : 0 ≤ s)
    (eg : (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) + a * r ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r + bζ * s))
    (esz : Aζ * (p + q) + a * (1 + r) ≤ s)
    {k : ℕ} (hk : k < N) {u v : Seq X} (hu : InDh Λ β δ κ cg cm cT ε k u)
    (hv : InDh Λ β δ κ cg cm cT ε k v)
    (hg : |(u k).1 - (v k).1| ≤ p * |(u k).2.1 - (v k).2.1|)
    (hx : ‖(u k).2.2 - (v k).2.2‖ ≤ q * |(u k).2.1 - (v k).2.1|)
    (hh : hmax w u v k ≤ r * |(u k).2.1 - (v k).2.1|)
    (hz : ‖Z k u - Z k v‖ ≤ s * |(u k).2.1 - (v k).2.1|) :
    (1 + Λ) / 2 * |(u k).2.1 - (v k).2.1| ≤
        |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      |F.G k u - F.G k v| ≤ p * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      ‖F.T k u - F.T k v‖ ≤ q * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      dist3 (u k) (v k) ≤ r * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      w * hmax w u v k ≤ r * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| ∧
      ‖Z (k + 1) u - Z (k + 1) v‖ ≤
        s * |Λ * (u k).2.1 + F.m k u - (Λ * (v k).2.1 + F.m k v)| := by
  set D := |(u k).2.1 - (v k).2.1|
  have hD : 0 ≤ D := abs_nonneg _
  have hw0 := HM.hw0.le
  have hM : 0 ≤ hmax w u v k := hmax_nonneg hw0 u v k
  have hb := hmax_bound hw0 u v k
  have LGd := HM.LGd k hk u v hu hv _ hM hb
  have Lm := HM.Lmz k hk u v hu hv _ hM hb
  have LT := HM.LT k hk u v hu hv _ hM hb
  have LZ := HM.LZ k hk u v hu hv _ hM hb
  have hA := HM.hA; have ha := HM.ha; have hAζ := HM.hAζ; have hbζ := HM.hbζ
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
  have a7 : bζ * ‖Z k u - Z k v‖ ≤ bζ * (s * D) := mul_le_mul_of_nonneg_left hz hbζ
  have b1 := mul_le_mul_of_nonneg_right em hD
  have b2 := mul_le_mul_of_nonneg_right eg hD
  have b3 := mul_le_mul_of_nonneg_right ex hD
  have hD' : (1 + Λ) / 2 * D ≤ D' := by linarith only [h1, Lm, a1, a2, a6, a7, b1]
  have hDD : D ≤ D' := by
    have := mul_nonneg (sub_nonneg.2 hΛ) hD
    linarith only [hD', this]
  have b4 := mul_le_mul_of_nonneg_left hD' hp
  have b5 := mul_le_mul_of_nonneg_left hDD hq
  have hr0 : 0 ≤ r := by linarith
  have b6 := mul_le_mul_of_nonneg_left hDD hr0
  have b7 := mul_le_mul_of_nonneg_left hDD hs0
  refine ⟨hD', ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hG, hg, a2, a5, a6, b2, b4]
  · linarith only [LT, a4, a5, a6, b3, b5]
  · unfold dist3
    have := mul_le_mul_of_nonneg_right hr hD
    linarith only [hg, hx, this, b6]
  · have c1 := mul_le_mul_of_nonneg_left hh hw0
    have c2 : 0 ≤ (1 - w) * (r * D) := mul_nonneg (by linarith [HM.hw1]) (mul_nonneg hr0 hD)
    linarith only [c1, c2, b6]
  · have c1 : Aζ * (|(u k).1 - (v k).1| + ‖(u k).2.2 - (v k).2.2‖) ≤ Aζ * ((p + q) * D) := by
      refine mul_le_mul_of_nonneg_left ?_ hAζ
      have e : (p + q) * D = p * D + q * D := by ring
      linarith only [hg, hx, e]
    have c2 : a * (D + hmax w u v k) ≤ a * ((1 + r) * D) := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      have e : (1 + r) * D = D + r * D := by ring
      linarith only [hh, e]
    have c3 := mul_le_mul_of_nonneg_right esz hD
    have e : (Aζ * (p + q) + a * (1 + r)) * D = Aζ * ((p + q) * D) + a * ((1 + r) * D) := by
      ring
    linarith only [LZ, c1, c2, c3, e, b7]

/-- One step of the `ǧ`-cone with a hidden coupling. -/
lemma g_cone_step_z {p₂ q₂ r₂ z₂ : ℝ} (hκ0 : 0 ≤ κ) (hc : cLoss A a p₂ q₂ r₂ < 1)
    (hx2 : κ * q₂ + a * (1 + p₂) + a * r₂ ≤ q₂ * (1 - cLoss A a p₂ q₂ r₂))
    (hrr : 1 + p₂ + q₂ ≤ r₂ * (1 - cLoss A a p₂ q₂ r₂))
    (hw : w ≤ 1 - cLoss A a p₂ q₂ r₂) (hq₂0 : 0 ≤ q₂) (hr₂0 : 0 ≤ r₂) (hz₂0 : 0 ≤ z₂)
    (hzz : Aζ * (1 + q₂) + a * (p₂ + r₂) ≤ z₂ * (1 - cLoss A a p₂ q₂ r₂))
    {k : ℕ} (hk : k < N) {u v : Seq X} (hu : InDh Λ β δ κ cg cm cT ε k u)
    (hv : InDh Λ β δ κ cg cm cT ε k v)
    (he : 0 < (u k).1 - (v k).1)
    (hm : |(u k).2.1 - (v k).2.1| ≤ p₂ * ((u k).1 - (v k).1))
    (hx : ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1))
    (hh : hmax w u v k ≤ r₂ * ((u k).1 - (v k).1)) :
    (1 - cLoss A a p₂ q₂ r₂) * ((u k).1 - (v k).1) ≤ F.G k u - F.G k v ∧
      ‖F.T k u - F.T k v‖ ≤ q₂ * (F.G k u - F.G k v) ∧
      dist3 (u k) (v k) ≤ r₂ * (F.G k u - F.G k v) ∧
      w * hmax w u v k ≤ r₂ * (F.G k u - F.G k v) ∧
      ‖Z (k + 1) u - Z (k + 1) v‖ ≤ z₂ * (F.G k u - F.G k v) := by
  set e := (u k).1 - (v k).1
  set c := cLoss A a p₂ q₂ r₂ with hcd
  have hw0 := HM.hw0.le
  have hM : 0 ≤ hmax w u v k := hmax_nonneg hw0 u v k
  have hb := hmax_bound hw0 u v k
  have LGd := HM.LGd k hk u v hu hv _ hM hb
  have LT := HM.LT k hk u v hu hv _ hM hb
  have LZ := HM.LZ k hk u v hu hv _ hM hb
  have hA := HM.hA; have ha := HM.ha; have hAζ := HM.hAζ
  have he' : |e| = e := abs_of_pos he
  rw [he'] at LGd LT LZ
  have a1 : a * |(u k).2.1 - (v k).2.1| ≤ a * (p₂ * e) := mul_le_mul_of_nonneg_left hm ha
  have a2 : A * ‖(u k).2.2 - (v k).2.2‖ ≤ A * (q₂ * e) := mul_le_mul_of_nonneg_left hx hA
  have a3 : a * hmax w u v k ≤ a * (r₂ * e) := mul_le_mul_of_nonneg_left hh ha
  have a4 : κ * ‖(u k).2.2 - (v k).2.2‖ ≤ κ * (q₂ * e) := mul_le_mul_of_nonneg_left hx hκ0
  have ec : c * e = a * e + a * (p₂ * e) + A * (q₂ * e) + a * (r₂ * e) := by
    rw [hcd]; unfold cLoss; ring
  have hlow : (1 - c) * e ≤ F.G k u - F.G k v := by
    have := (abs_le.1 LGd).1
    linarith only [this, a1, a2, a3, ec]
  have hT : ‖F.T k u - F.T k v‖ ≤ q₂ * (1 - c) * e := by
    have b1 := mul_le_mul_of_nonneg_right hx2 he.le
    linarith only [LT, a1, a3, a4, b1]
  refine ⟨hlow, ?_, ?_, ?_, ?_⟩
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
  · have c1 : Aζ * (e + ‖(u k).2.2 - (v k).2.2‖) ≤ Aζ * ((1 + q₂) * e) := by
      refine mul_le_mul_of_nonneg_left ?_ hAζ
      have e1 : (1 + q₂) * e = e + q₂ * e := by ring
      linarith only [hx, e1]
    have c2 : a * (|(u k).2.1 - (v k).2.1| + hmax w u v k) ≤ a * ((p₂ + r₂) * e) := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      have e1 : (p₂ + r₂) * e = p₂ * e + r₂ * e := by ring
      linarith only [hm, hh, e1]
    have c3 := mul_le_mul_of_nonneg_right hzz he.le
    have e1 : (Aζ * (1 + q₂) + a * (p₂ + r₂)) * e = Aζ * ((1 + q₂) * e) + a * ((p₂ + r₂) * e) := by
      ring
    have c4 := mul_le_mul_of_nonneg_left hlow hz₂0
    have e2 : z₂ * (1 - c) * e = z₂ * ((1 - c) * e) := by ring
    linarith only [LZ, c1, c2, c3, e1, c4, e2]

end Cones

section Two

variable {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ bζ ε w : ℝ}
  (H : HHyp F Λ β δ κ cg cm cT N A' a' ε)
  (HM : MonoZHyp F Λ β δ κ cg cm cT N Z A a Aζ bζ ε w)
include H HM

/-- **No `μ`-cone along two distinct admissible trajectories** (hidden coupling). -/
lemma not_mu_cone_z {p q r s : ℝ} (hΛ : 1 ≤ Λ) (hκ0 : 0 ≤ κ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 1 + p + q ≤ r) (hs0 : 0 ≤ s)
    (eg : (1 + a) * p + a + A * q + a * r ≤ p * ((1 + Λ) / 2))
    (ex : κ * q + a * (p + 1) + a * r ≤ q)
    (em : (1 + Λ) / 2 ≤ Λ - (A * p + a + A * q + a * r + bζ * s))
    (esz : Aζ * (p + q) + a * (1 + r) ≤ s)
    {b b' μ μ' : ℝ} (hb : b ≠ b') (h : Admissible F Λ κ cm cT N ε b μ)
    (h' : Admissible F Λ κ cm cT N ε b' μ') {k : ℕ} (hk : k ≤ N)
    (hg : |(traj F Λ b' μ' k).1 - (traj F Λ b μ k).1| ≤
      p * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|)
    (hx : ‖(traj F Λ b' μ' k).2.2 - (traj F Λ b μ k).2.2‖ ≤
      q * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|)
    (hh : hmax w (traj F Λ b' μ') (traj F Λ b μ) k ≤
      r * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|)
    (hz : ‖Z k (traj F Λ b' μ') - Z k (traj F Λ b μ)‖ ≤
      s * |(traj F Λ b' μ' k).2.1 - (traj F Λ b μ k).2.1|) : False := by
  set u := traj F Λ b' μ'
  set v := traj F Λ b μ
  have key : ∀ n, k + n ≤ N →
      |(u (k + n)).1 - (v (k + n)).1| ≤ p * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      ‖(u (k + n)).2.2 - (v (k + n)).2.2‖ ≤ q * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      hmax w u v (k + n) ≤ r * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      ‖Z (k + n) u - Z (k + n) v‖ ≤ s * |(u (k + n)).2.1 - (v (k + n)).2.1| ∧
      |(u k).2.1 - (v k).2.1| ≤ |(u (k + n)).2.1 - (v (k + n)).2.1| := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hg, hx, hh, hz, le_rfl⟩
    | succ n ih =>
      intro hkn
      have hlt : k + n < N := by omega
      obtain ⟨ig, ix, ih', iz, iμ⟩ := ih (by omega)
      obtain ⟨s1, s2, s3, s4, s5, s6⟩ := mu_cone_step_z HM hΛ hκ0 hp hq hr hs0 eg ex em esz hlt
        (admissible_InDh H h' (k + n) hlt.le) (admissible_InDh H h (k + n) hlt.le) ig ix ih' iz
      have e0 := traj_succ H b' μ' hlt
      have e1 := traj_succ H b μ hlt
      have hmu : |(u (k + n)).2.1 - (v (k + n)).2.1| ≤
          |Λ * (u (k + n)).2.1 + F.m (k + n) u - (Λ * (v (k + n)).2.1 + F.m (k + n) v)| := by
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (1 + Λ) / 2 by linarith)
          (abs_nonneg ((u (k + n)).2.1 - (v (k + n)).2.1))
        linarith
      rw [← add_assoc]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [u, v] at e0 e1 ⊢; rw [e0, e1]; exact s2
      · simp only [u, v] at e0 e1 ⊢; rw [e0, e1]; exact s3
      · refine hmax_succ_le u v (k + n) ?_ ?_
        · simp only [u, v] at e0 e1 s4 ⊢; rw [e0, e1]; exact s4
        · simp only [u, v] at e0 e1 s5 ⊢; rw [e0, e1]; exact s5
      · simp only [u, v] at e0 e1 s6 ⊢; rw [e0, e1]; exact s6
      · refine iμ.trans (hmu.trans (le_of_eq ?_))
        simp only [u, v] at e0 e1 ⊢; rw [e0, e1]
  obtain ⟨-, -, -, -, hμ⟩ := key (N - k) (by omega)
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

/-- **Monotonicity along two admissible trajectories** (hidden coupling). -/
theorem traj_strict_mono_z {p q r s p₂ q₂ r₂ z₂ : ℝ}
    (hC : MonoZCoef Λ κ A a Aζ bζ w p q r s p₂ q₂ r₂ z₂)
    {b b' μ μ' : ℝ} (hbb : b < b') (h : Admissible F Λ κ cm cT N ε b μ)
    (h' : Admissible F Λ κ cm cT N ε b' μ') :
    (traj F Λ b μ N).1 < (traj F Λ b' μ' N).1 := by
  set u := traj F Λ b' μ'
  set v := traj F Λ b μ
  have hp := hC.hp
  have hq := hC.hq
  -- outside the `μ`-cone
  have hout : ∀ k ≤ N, 0 < (u k).1 - (v k).1 → ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1) →
      hmax w u v k ≤ r₂ * ((u k).1 - (v k).1) → ‖Z k u - Z k v‖ ≤ z₂ * ((u k).1 - (v k).1) →
      |(u k).2.1 - (v k).2.1| ≤ p₂ * ((u k).1 - (v k).1) := by
    intro k hk he hx hh hz
    by_contra hn
    push Not at hn
    set e := (u k).1 - (v k).1
    set m := |(u k).2.1 - (v k).2.1|
    refine not_mu_cone_z H HM hC.hΛ hC.hκ0 hp.le hq hC.hr hC.hs0 hC.eg hC.ex hC.em hC.esz hbb.ne
      h h' hk ?_ ?_ ?_ ?_
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
    · show ‖Z k u - Z k v‖ ≤ s * m
      refine hz.trans ?_
      have h1 : z₂ * e ≤ p₂ * s * e := mul_le_mul_of_nonneg_right hC.hz₂ he.le
      have h2 : p₂ * e * s ≤ m * s := mul_le_mul_of_nonneg_right hn.le hC.hs0
      linarith only [h1, h2]
  -- the `ǧ`-cone
  have key : ∀ k ≤ N, 0 < (u k).1 - (v k).1 ∧
      ‖(u k).2.2 - (v k).2.2‖ ≤ q₂ * ((u k).1 - (v k).1) ∧
      hmax w u v k ≤ r₂ * ((u k).1 - (v k).1) ∧
      ‖Z k u - Z k v‖ ≤ z₂ * ((u k).1 - (v k).1) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [u, v, traj_zero, sub_self, norm_zero, hmax]
      refine ⟨by linarith, ?_, ?_, ?_⟩
      · exact mul_nonneg hC.hq₂0 (by linarith)
      · exact mul_nonneg hC.hr₂0 (by linarith)
      · rw [HM.Z0 (traj F Λ b' μ') (traj F Λ b μ), sub_self, norm_zero]
        exact mul_nonneg hC.hz₂0 (by linarith)
    | succ k ih =>
      intro hk
      have hlt : k < N := by omega
      obtain ⟨ie, ix, ih', iz⟩ := ih (by omega)
      have im := hout k hlt.le ie ix ih' iz
      obtain ⟨s1, s2, s3, s4, s5⟩ := g_cone_step_z HM hC.hκ0 hC.hc hC.hx hC.hrr hC.hw hC.hq₂0
        hC.hr₂0 hC.hz₂0 hC.hzz hlt (admissible_InDh H h' k hlt.le) (admissible_InDh H h k hlt.le)
        ie im ix ih'
      have e0 := traj_succ H b' μ' hlt
      have e1 := traj_succ H b μ hlt
      have hc0 : 0 < 1 - cLoss A a p₂ q₂ r₂ := by linarith [hC.hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [u, v] at e0 e1 s1 ⊢; rw [e0, e1]
        exact lt_of_lt_of_le (mul_pos hc0 ie) s1
      · simp only [u, v] at e0 e1 s2 ⊢; rw [e0, e1]; exact s2
      · refine hmax_succ_le u v k ?_ ?_
        · simp only [u, v] at e0 e1 s3 ⊢; rw [e0, e1]; exact s3
        · simp only [u, v] at e0 e1 s4 ⊢; rw [e0, e1]; exact s4
      · simp only [u, v] at e0 e1 s5 ⊢; rw [e0, e1]; exact s5
  have := (key N le_rfl).1
  linarith

end Two

/-- **Strict monotonicity of `ǧ_N`** on the `b` with an admissible trajectory (hidden
coupling). -/
theorem strictMonoOn_adm_z {N : ℕ} {A' a' : ℝ} {Z : ℕ → Seq X → E} {A a Aζ bζ ε w : ℝ}
    {p q r s p₂ q₂ r₂ z₂ : ℝ} (H : HHyp F Λ β δ κ cg cm cT N A' a' ε)
    (HM : MonoZHyp F Λ β δ κ cg cm cT N Z A a Aζ bζ ε w)
    (hC : MonoZCoef Λ κ A a Aζ bζ w p q r s p₂ q₂ r₂ z₂) :
    StrictMonoOn (gN F Λ κ cm cT N ε) {b | ∃ μ, Admissible F Λ κ cm cT N ε b μ} := by
  have hspec : ∀ b, (∃ μ, Admissible F Λ κ cm cT N ε b μ) →
      Admissible F Λ κ cm cT N ε b (muc F Λ κ cm cT N ε b) := fun b hb => by
    unfold muc; rw [dif_pos hb]; exact hb.choose_spec
  intro b hb b' hb' hbb
  exact traj_strict_mono_z H HM hC hbb (hspec b hb) (hspec b' hb')

end Hist

end Flow2
