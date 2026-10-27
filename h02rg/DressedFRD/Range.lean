import DressedFRD.Construction

/-!
# Finite range (`thm:main`(iii))

The range bound `2 r̄(w) ≥ 2 rng(O_w)` holds letter by letter (`two_rng_letV_le`). Hence words
of scale `s < N` have range `< L^s/2`, the tails satisfy `rng R_{j,r} < L^r/2` for `r < N`
(`tailRange`), and `rng Γ^int_{j+1} < L^{j+1}/2` for `j + 1 < N` (`two_rng_Gint_lt`).
-/

namespace DressedFRD

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

theorem two_zabs_le (z : ZMod n) : 2 * zabs z ≤ n := by
  unfold zabs
  have := ZMod.val_lt z
  omega

theorem two_supNorm_le (x : Torus d n) : 2 * supNorm x ≤ n := by
  have : supNorm x ≤ n / 2 := Finset.sup_le fun i _ => by
    have := two_zabs_le ((x : Fin d → ZMod n) i); omega
  omega

/-- Every symbol has range `≤ n/2`. -/
theorem two_rng_le (w : Sym d n) : 2 * rng w ≤ n := by
  have : rng w ≤ n / 2 := Finset.sup_le fun x _ => by have := two_supNorm_le x; omega
  omega

theorem rng_smul_neg_le (c : ℂ) (w : Sym d n) : rng (-(c • w)) ≤ rng w :=
  (rng_neg _).trans (rng_smul_le c w)

theorem rng_Asym_mul_le (msq : ℝ) (w : Sym d n) : rng (Asym msq * w) ≤ rng w + 1 := by
  have := rng_mul_le (Asym msq : Sym d n) w
  have := rng_Asym_le (d := d) (n := n) msq
  omega

namespace Data

variable {D : Data d n}

/-- The range invariant of the tails at time `j`. -/
def TailRange (D : Data d n) (j : ℕ) : Prop :=
  ∀ r, j < r → r < D.N → 2 * rng (D.tails j r) < D.L ^ r

/-- The letters satisfy `2 rng ≤ rbV`. -/
theorem two_rng_letV_le (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j < D.N) (R : ℕ → Sym d n)
    (hR : ∀ r, j < r → r < D.N → 2 * rng (R r) < D.L ^ r) (κ : Fin 3) {ℓ : Option ℕ}
    (hℓ : ℓ ∈ alph j D.N) : 2 * rng (D.letV j R κ ℓ) ≤ D.rbV j κ ℓ := by
  have hCle := two_rng_Cle h hL hj
  have hE := two_rng_Ehat h hL hj
  have hE' := two_rng_one_sub_Ehat h hL hj
  -- tail letters: `2 rng R ≤ L^r - 1` for `r < N`, and `2 rng ≤ L^N` always
  have hRr : ∀ r, some r ∈ alph j D.N → 2 * rng (R r) + 1 ≤ D.L ^ r + 1 ∧
      2 * (rng (R r) + 1) ≤ D.L ^ r + 2 := by
    intro r hr
    rw [some_mem_alph] at hr
    by_cases hrN : r < D.N
    · have := hR r hr.1 hrN; omega
    · have hrN' : r = D.N := by omega
      have h' : 2 * rng (R r) ≤ D.L ^ D.N := (two_rng_le (R r)).trans hn.le
      rw [← hrN'] at h'
      omega
  rcases ℓ with _ | r
  · fin_cases κ <;> simp [letV, rbV] <;> omega
  · obtain ⟨h1, h2⟩ := hRr r hℓ
    have hs := rng_smul_neg_le (D.Z j) (R r)
    have hs2 := rng_smul_le (D.Z j) (Asym D.msq * R r)
    have hs3 := rng_smul_neg_le (D.Z j) (Asym D.msq * R r)
    have hA := rng_Asym_mul_le D.msq (R r)
    fin_cases κ <;> simp [letV, rbV] <;> omega

/-- `2 rng O_w ≤ 2 r̄(w)`. -/
theorem two_rng_wordVal_le (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j < D.N) (R : ℕ → Sym d n)
    (hR : ∀ r, j < r → r < D.N → 2 * rng (R r) < D.L ^ r) {k : ℕ}
    {w : Fin (k + 2) → Option ℕ} (hw : w ∈ words j D.N k) :
    2 * rng (wordVal (D.letV j R) w) ≤ rbar (D.rbV j) w := by
  unfold wordVal rbar
  refine (Nat.mul_le_mul_left 2 (rng_prod_le _ _)).trans ?_
  rw [mul_sum]
  exact sum_le_sum fun i _ =>
    two_rng_letV_le h hL hn hj R hR _ (Fintype.mem_piFinset.1 hw i)

theorem two_rng_wLen_lt (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j < D.N) (R : ℕ → Sym d n)
    (hR : ∀ r, j < r → r < D.N → 2 * rng (R r) < D.L ^ r) {s : ℕ} (hs : s < D.N) (k : ℕ) :
    2 * rng (D.wLen j R s k) < D.L ^ s := by
  have hpos : 0 < D.L ^ s := pow_pos (by omega) _
  have key : rng (D.wLen j R s k) ≤ (D.L ^ s - 1) / 2 := by
    refine rng_sum_le _ _ fun w hw => ?_
    rw [mem_filter] at hw
    have h1 := two_rng_wordVal_le h hL hn hj R hR hw.1
    have h2 := lt_pow_scale (L := D.L) (j := j) (N := D.N) (R := rbar (D.rbV j) w)
      (by rw [hw.2]; exact hs)
    rw [hw.2] at h2
    omega
  omega

theorem two_rng_wLow_lt (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j < D.N) (R : ℕ → Sym d n)
    (hR : ∀ r, j < r → r < D.N → 2 * rng (R r) < D.L ^ r) {s : ℕ} (hs : s < D.N) :
    2 * rng (D.wLow j R s) < D.L ^ s := by
  have hpos : 0 < D.L ^ s := pow_pos (by omega) _
  have key : rng (D.wLow j R s) ≤ (D.L ^ s - 1) / 2 := by
    refine rng_sum_le _ _ fun k _ => ?_
    have := two_rng_wLen_lt h hL hn hj R hR hs k
    have := rng_smul_le (D.zp j ^ (k + 1)) (D.wLen j R s k)
    omega
  omega

/-- The range invariant propagates: `rng R_{j+1,r} < L^r/2` for `r < N`. -/
theorem tailRange_succ (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j < D.N) (hR : D.TailRange j) : D.TailRange (j + 1) := by
  intro r hr hrN
  simp only [tails]
  by_cases hc : j + 2 ≤ r ∧ r ≤ D.N
  · rw [if_pos hc]
    have h1 := hR r (by omega) hrN
    have h2 := two_rng_wLow_lt h hL hn hj (D.tails j) hR hrN
    have hw : D.wSc j (D.tails j) r = D.wLow j (D.tails j) r := by simp [wSc, hrN]
    rw [hw]
    have h3 := rng_smul_le (D.Z (j + 1))⁻¹ (D.Z j • D.tails j r + D.wLow j (D.tails j) r)
    have h4 := rng_add_le (D.Z j • D.tails j r) (D.wLow j (D.tails j) r)
    have h5 := rng_smul_le (D.Z j) (D.tails j r)
    have : 2 * max (rng (D.Z j • D.tails j r)) (rng (D.wLow j (D.tails j) r)) < D.L ^ r := by
      rcases le_total (rng (D.Z j • D.tails j r)) (rng (D.wLow j (D.tails j) r)) with h6 | h6
      · rw [max_eq_right h6]; exact h2
      · rw [max_eq_left h6]; omega
    omega
  · rw [if_neg hc, show (0 : Sym d n) = fun _ => (0 : ℂ) from rfl, rng_const]
    exact pow_pos (by omega) _

theorem tailRange_zero (hL : 1 ≤ D.L) : D.TailRange 0 := by
  intro r _ _
  simp only [tails, show (0 : Sym d n) = fun _ => (0 : ℂ) from rfl, rng_const]
  exact pow_pos (by omega) _

theorem tailRange (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N) :
    ∀ j, j ≤ D.N → D.TailRange j
  | 0, _ => tailRange_zero hL
  | j + 1, hj => tailRange_succ h hL hn (by omega) (tailRange h hL hn j (by omega))

/-- `thm:main`(iii): `rng Γ^int_{j+1} < L^{j+1}/2` for `j + 1 < N`. -/
theorem two_rng_Gint_lt (h : StdHyp D.L D.N D.msq D.C) (hL : 1 ≤ D.L) (hn : n = D.L ^ D.N)
    {j : ℕ} (hj : j + 1 < D.N) : 2 * rng (D.Gint j) < D.L ^ (j + 1) := by
  have hR := tailRange h hL hn j (by omega)
  simp only [Gint, if_pos hj]
  have hw : D.wSc j (D.tails j) (j + 1) = D.wLow j (D.tails j) (j + 1) := by simp [wSc, hj]
  rw [hw]
  have h1 := h.range (j + 1) (by omega) hj
  have h2 := hR (j + 1) (by omega) hj
  have h3 := two_rng_wLow_lt h hL hn (by omega) (D.tails j) hR hj
  have h4 := rng_smul_le (D.Z (j + 1))⁻¹
    (ofR (D.C (j + 1)) + D.Z j • D.tails j (j + 1) + D.wLow j (D.tails j) (j + 1))
  have h5 := rng_add_le (ofR (D.C (j + 1)) + D.Z j • D.tails j (j + 1))
    (D.wLow j (D.tails j) (j + 1))
  have h6 := rng_add_le (ofR (D.C (j + 1))) (D.Z j • D.tails j (j + 1))
  have h7 := rng_smul_le (D.Z j) (D.tails j (j + 1))
  have hm : ∀ a b c : ℕ, 2 * a < D.L ^ (j + 1) → 2 * b < D.L ^ (j + 1) →
      2 * c < D.L ^ (j + 1) → 2 * max (max a b) c < D.L ^ (j + 1) := by
    intro a b c ha hb hc
    rcases le_total a b with h | h <;> rcases le_total (max a b) c with h' | h' <;>
      simp only [max_eq_left, max_eq_right, h, h'] <;> omega
  have := hm _ _ _ h1 (lt_of_le_of_lt (Nat.mul_le_mul_left 2 h7) h2) h3
  omega

end Data

end

end DressedFRD
