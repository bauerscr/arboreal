import Spin2.Final.ObsBeta1

set_option autoImplicit false

/-!
# The summed observable renormalisation condition: definitions and the key estimate

The reference-point-free version of the observable renormalisation condition of `ObsBeta1`: with
the connection density
`obsDens L N β = (∑_{x ∈ Λ_N} P_β[0 ↔ x])/L^{2N} = E_β|T_0|/|Λ_N|`
(`T_0` the tree of the origin; `P_β[0 ↔ 0] = 1`),
`obsBetaSum L N β = β · obsDens L N β^{3/2}`.

**Key estimate** (`os_dens_close`): along a trajectory `β_j` (`β_0 = β_ε = 1/b`) that is monotone
(`β_{N−2} ≤ β_j`) with the summed per-step bound `β_j ≤ β_{N−2} + C₁(1 + (N−2−j))`, the multiscale
formula `|P(x) − ϑ_{k_x}²| ≤ Kϑ_{k_x}²/β_{k_x}` (`k_x = min(j(|x|/L^N), N−2)`) gives
`|obsDens(1/b) − ϑ_{N−2}²| ≤ (4C₁ + 2K)ϑ_{N−2}²/β_{N−2}`.
Lower bound: `ϑ_k² ≥ ϑ_{N−2}²`. Upper bound: `ϑ_k²/ϑ_{N−2}² ≤ β_k/β_{N−2} ≤ 1 + C₁(1+i)/β_{N−2}`,
`i = N−2−k`, and `#{x : k_x ≤ N−2−i} ≤ #{x : |x|_∞ < L^{N−1−i}} ≤ 4L^{2(N−1−i)}`
(`os_supNorm_lt`, `os_card_ball`), so `∑_x (1 + i_x) ≤ 2L^{2N}` (`os_geom`); `x = 0` has
`P = 1 = ϑ_0²` and is treated as `k = 0`.

* `obsDens`, `obsBetaSum`, `obsFS` (`f^Σ_N(x) = P_{β_N}[0 ↔ x_N]/obsDens`).
* `Pconn_zero_eq_one`, `obsDens_pos`, `obsDens_le_one`, `obsDens_continuousOn`.
* `os_supNorm_lt`, `os_card_ball`, `os_geom`, **`os_dens_close`**.
* `os_rpow_close`, `os_obsBetaSum_close` (`|obsBetaSum(1/b) − β_{N−2}| ≤ 3C`).
* `os_dens_of_obsBetaSum` (`obsBetaSum = t` gives `obsDens = (tb)^{2/3}`), `obsFS_eq_clF`,
  `obsFS_avg` (the lattice average of `f^Σ_N` is `1`).
-/

namespace Spin2

open Step Step2 PtCorr2 Cont Loc Grassmann Step2.D2

noncomputable section

open Finset Flow2 Flow2.Hist Set Filter Topology

variable {L : ℕ} [NeZero L]

/-! ### Definitions -/

variable (L) in
/-- **The connection density** `obsDens L N β = (∑_{x ∈ Λ_N} P_β[0 ↔ x])/L^{2N} = E_β|T_0|/|Λ_N|`. -/
def obsDens (N : ℕ) (β : ℝ) : ℝ := (∑ x : Lam 2 L N, Pconn L N β x) / (L : ℝ) ^ (2 * N)

variable (L) in
/-- **The summed observable coupling** `t_Σ(β, N) = β · obsDens L N β^{3/2}`. -/
def obsBetaSum (N : ℕ) (β : ℝ) : ℝ := β * obsDens L N β ^ (3 / 2 : ℝ)

variable (L) in
/-- **The normalised two-point function** `f^Σ_N(x) = P_{β_N}[0 ↔ x_N]/obsDens L N β_N` on `𝕋²`. -/
def obsFS (βs : ℕ → ℝ) (N : ℕ) (x : UnitAddTorus (Fin 2)) : ℝ :=
  Pconn L N (βs N) (latPtN L N x) / obsDens L N (βs N)

/-! ### Elementary properties -/

/-- `P_β[0 ↔ 0] = 1`. -/
theorem Pconn_zero_eq_one {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) : Pconn L N β 0 = 1 := by
  unfold Pconn
  have e : (fun F : SimpleGraph (Lam 2 L N) => F.Reachable 0 0) = fun _ => True :=
    funext fun F => propext ⟨fun _ => trivial, fun _ => SimpleGraph.Reachable.refl 0⟩
  rw [e]
  exact H02.arborealProb_true _ (Ward.nnW_nonneg hβ)

theorem os_card (N : ℕ) : (Fintype.card (Lam 2 L N) : ℝ) = (L : ℝ) ^ (2 * N) := by
  rw [show Fintype.card (Lam 2 L N) = (L ^ N) ^ 2 from FRD.card_torus]; push_cast; ring

theorem os_LN_pos (N : ℕ) : (0 : ℝ) < (L : ℝ) ^ (2 * N) :=
  pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L))) _

/-- `obsDens ≥ 1/L^{2N} > 0` (the term `x = 0`). -/
theorem obsDens_pos {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) : 0 < obsDens L N β := by
  unfold obsDens
  refine div_pos ?_ (os_LN_pos N)
  calc (0 : ℝ) < Pconn L N β 0 := by rw [Pconn_zero_eq_one hβ]; exact one_pos
    _ ≤ ∑ x, Pconn L N β x := single_le_sum (fun x _ => (Pconn_mem hβ x).1) (mem_univ 0)

theorem obsDens_le_one {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) : obsDens L N β ≤ 1 := by
  unfold obsDens
  rw [div_le_one (os_LN_pos N)]
  calc ∑ x, Pconn L N β x ≤ ∑ _x : Lam 2 L N, (1 : ℝ) := sum_le_sum fun x _ => (Pconn_mem hβ x).2
    _ = (L : ℝ) ^ (2 * N) := by rw [sum_const, card_univ, nsmul_eq_mul, mul_one, os_card]

/-- **Continuity** of `β ↦ obsDens L N β` on `β ≥ 0`. -/
theorem obsDens_continuousOn (N : ℕ) : ContinuousOn (fun β => obsDens L N β) (Set.Ici 0) := by
  unfold obsDens
  exact (continuousOn_finsetSum _ fun x _ => Pconn_continuousOn x).div_const _

/-! ### Counting -/

/-- From `jp = j(|x|/L^N)`: `|x|_∞ < L^{jp+1}`. -/
theorem os_supNorm_lt (hL : 2 ≤ L) {N : ℕ} {x : Lam 2 L N} (hx : x ≠ 0) {jp : ℕ}
    (hj : (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N)) : supNorm x < L ^ (jp + 1) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have he : 1 ≤ eucl x := cs_one_le_eucl hx
  have hLN : (0 : ℝ) < (L : ℝ) ^ N := by positivity
  have h1 : (N : ℝ) + Real.logb L (eucl x / (L : ℝ) ^ N) < (jp : ℝ) + 1 := by
    have := Int.lt_floor_add_one ((N : ℝ) + Real.logb L (eucl x / (L : ℝ) ^ N))
    have e : ⌊(N : ℝ) + Real.logb L (eucl x / (L : ℝ) ^ N)⌋ = (jp : ℤ) := hj.symm
    rw [e] at this
    exact_mod_cast this
  have h2 : Real.logb L (eucl x) < (jp : ℝ) + 1 := by
    rw [Real.logb_div (by linarith) hLN.ne', Real.logb_pow, Real.logb_self_eq_one hL1] at h1
    linarith
  have h3 : eucl x < (L : ℝ) ^ (jp + 1) := by
    have := (Real.logb_lt_iff_lt_rpow hL1 (by linarith)).1 h2
    have e : ((jp : ℝ) + 1) = ((jp + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast] at this
    exact this
  have h4 : (supNorm x : ℝ) < (L : ℝ) ^ (jp + 1) := lt_of_le_of_lt (supNorm_le_eucl x) h3
  exact_mod_cast h4

/-- `#{x ∈ Λ_N : |x|_∞ ≤ L^{m+1} − 1} ≤ 4L^{2(m+1)}`. -/
theorem os_card_ball (N m : ℕ) :
    ((univ.filter fun x : Lam 2 L N => supNorm x ≤ L ^ (m + 1) - 1).card : ℝ) ≤
      4 * (L : ℝ) ^ (2 * (m + 1)) := by
  have h := FRD.card_supNorm_le (d := 2) (n := L ^ N) (L ^ (m + 1) - 1)
  have hL1 : 1 ≤ L ^ (m + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have h2 : (2 * (L ^ (m + 1) - 1) + 1) ^ 2 ≤ 4 * L ^ (2 * (m + 1)) := by
    have e : 2 * (L ^ (m + 1) - 1) + 1 = 2 * L ^ (m + 1) - 1 := by omega
    rw [e]
    calc (2 * L ^ (m + 1) - 1) ^ 2 ≤ (2 * L ^ (m + 1)) ^ 2 :=
          Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      _ = 4 * L ^ (2 * (m + 1)) := by rw [mul_pow, mul_comm 2 (m + 1), pow_mul]; ring
  exact_mod_cast h.trans h2

omit [NeZero L] in
/-- `∑_{m<n} L^{2(m+1)} ≤ (4/3)L^{2n}` for `L ≥ 2`. -/
theorem os_geom (hL : (2 : ℝ) ≤ L) (n : ℕ) :
    ∑ m ∈ range n, (L : ℝ) ^ (2 * (m + 1)) ≤ 4 / 3 * (L : ℝ) ^ (2 * n) := by
  induction n with
  | zero => simp; norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have e : (L : ℝ) ^ (2 * (n + 1)) = (L : ℝ) ^ (2 * n) * (L : ℝ) ^ 2 := by
      rw [← pow_add]; ring_nf
    have hp : 0 ≤ (L : ℝ) ^ (2 * n) := by positivity
    rw [e]; nlinarith

omit [NeZero L] in
theorem os_supNorm_zero (N : ℕ) : supNorm (0 : Lam 2 L N) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold supNorm
  refine Finset.sup_le fun i _ => ?_
  have e : ((0 : Lam 2 L N) : Fin 2 → ZMod (L ^ N)) i = 0 := rfl
  rw [e]
  simp [zabs]

/-! ### The key estimate -/

set_option maxHeartbeats 1000000 in
/-- **The connection density is `ϑ_{N−2}²(1 + O(1/β_{N−2}))`.** For a trajectory `β_j`
(`β_0 = 1/b`, `β_j > 0`), monotone (`β_{N−2} ≤ β_j`) with the summed per-step bound
`β_j ≤ β_{N−2} + C₁(1 + (N−2−j))`, `β_{N−2} ≥ 4K`, and the multiscale formula
`|P_{1/b}[0 ↔ x] − ϑ_k²| ≤ Kϑ_k²/β_k`, `k = min(j(|x|/L^N), N−2)`, `ϑ_k² = (β_k/β_0)^{2/3}`:
`|obsDens L N (1/b) − ϑ_{N−2}²| ≤ (4C₁ + 2K)ϑ_{N−2}²/β_{N−2}`. -/
theorem os_dens_close (hL : 2 ≤ L) {N : ℕ} (hN : 2 ≤ N) {b K C₁ : ℝ} {β : ℕ → ℝ}
    (hb : 0 < b) (hK : 0 ≤ K) (hC₁ : 0 ≤ C₁) (hβ0 : β 0 = 1 / b)
    (hpos : ∀ j ≤ N - 2, 0 < β j)
    (hmono : ∀ j ≤ N - 2, β (N - 2) ≤ β j)
    (hrec : ∀ j ≤ N - 2, β j ≤ β (N - 2) + C₁ * (1 + ((N - 2 - j : ℕ) : ℝ)))
    (hβN : 4 * K ≤ β (N - 2))
    (hP : ∀ x : Lam 2 L N, x ≠ 0 → ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      |Pconn L N (1 / b) x - (β (min jp (N - 2)) / (1 / b)) ^ (2 / 3 : ℝ)| ≤
        K * (β (min jp (N - 2)) / (1 / b)) ^ (2 / 3 : ℝ) / β (min jp (N - 2))) :
    |obsDens L N (1 / b) - (β (N - 2) / (1 / b)) ^ (2 / 3 : ℝ)| ≤
      (4 * C₁ + 2 * K) * (β (N - 2) / (1 / b)) ^ (2 / 3 : ℝ) / β (N - 2) := by
  classical
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  set Nh := N - 2 with hNh
  have hβN0 : 0 < β Nh := hpos Nh le_rfl
  set θ : ℕ → ℝ := fun k => (β k / (1 / b)) ^ (2 / 3 : ℝ) with hθd
  have hθk : ∀ k, (β k / (1 / b)) ^ (2 / 3 : ℝ) = θ k := fun k => rfl
  have hθ : ∀ k, θ k = (β k * b) ^ (2 / 3 : ℝ) := fun k => by
    simp only [hθd]; rw [div_div_eq_mul_div, div_one]
  have hθpos : ∀ k ≤ Nh, 0 < θ k := fun k hk => by
    rw [hθ]; exact Real.rpow_pos_of_pos (mul_pos (hpos k hk) hb) _
  have hθ0 : θ 0 = 1 := by
    rw [hθ, hβ0, one_div_mul_cancel hb.ne', Real.one_rpow]
  have hθmono : ∀ k ≤ Nh, θ Nh ≤ θ k := fun k hk => by
    rw [hθ, hθ]
    exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right (hmono k hk) hb.le)
      (by norm_num)
  have hθrat : ∀ k ≤ Nh, θ k ≤ θ Nh * (1 + C₁ * (1 + ((Nh - k : ℕ) : ℝ)) / β Nh) := by
    intro k hk
    have h1 : θ k = θ Nh * (β k / β Nh) ^ (2 / 3 : ℝ) := by
      rw [hθ, hθ, ← Real.mul_rpow (mul_pos hβN0 hb).le (div_pos (hpos k hk) hβN0).le]
      congr 1; field_simp
    have h2 : (β k / β Nh) ^ (2 / 3 : ℝ) ≤ β k / β Nh := by
      have : 1 ≤ β k / β Nh := by rw [le_div_iff₀ hβN0]; linarith [hmono k hk]
      calc (β k / β Nh) ^ (2 / 3 : ℝ) ≤ (β k / β Nh) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le this (by norm_num)
        _ = β k / β Nh := Real.rpow_one _
    have h3 : β k / β Nh ≤ 1 + C₁ * (1 + ((Nh - k : ℕ) : ℝ)) / β Nh := by
      rw [div_le_iff₀ hβN0, add_mul, one_mul, div_mul_cancel₀ _ hβN0.ne']
      exact hrec k hk
    rw [h1]
    exact mul_le_mul_of_nonneg_left (h2.trans h3) (hθpos Nh le_rfl).le
  have hθ1 : θ Nh ≤ 1 := by rw [← hθ0]; exact hθmono 0 (Nat.zero_le _)
  set D := (2 * C₁ + K) * θ Nh / β Nh with hDd
  have hD0 : 0 ≤ D := by have := hθpos Nh le_rfl; positivity
  have hc : K / β Nh ≤ 1 / 4 := by rw [div_le_iff₀ hβN0]; linarith
  have hc0 : 0 ≤ K / β Nh := by positivity
  -- the pointwise upper bound
  have key : ∀ (x : Lam 2 L N) (k : ℕ), k ≤ Nh → Pconn L N (1 / b) x ≤ θ k * (1 + K / β Nh) →
      Pconn L N (1 / b) x - θ Nh ≤ D * (1 + ((Nh - k : ℕ) : ℝ)) := by
    intro x k hk hPk
    have hr := hθrat k hk
    set i : ℝ := ((Nh - k : ℕ) : ℝ) with hid
    have hi : 0 ≤ i := Nat.cast_nonneg _
    set a := C₁ * (1 + i) / β Nh with had
    have ha0 : 0 ≤ a := by rw [had]; positivity
    have hθN := (hθpos Nh le_rfl).le
    have hac : a * (K / β Nh) ≤ a / 4 := by
      calc a * (K / β Nh) ≤ a * (1 / 4) := mul_le_mul_of_nonneg_left hc ha0
        _ = a / 4 := by ring
    have hKi : K ≤ K * (1 + i) := by nlinarith
    calc Pconn L N (1 / b) x - θ Nh ≤ θ k * (1 + K / β Nh) - θ Nh := by linarith
      _ ≤ θ Nh * (1 + a) * (1 + K / β Nh) - θ Nh := by
          have := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ 1 + K / β Nh)
          linarith
      _ = θ Nh * (a + K / β Nh + a * (K / β Nh)) := by ring
      _ ≤ θ Nh * (2 * a + K / β Nh) := by
          refine mul_le_mul_of_nonneg_left ?_ hθN; linarith
      _ = θ Nh * (2 * C₁ * (1 + i) + K) / β Nh := by rw [had]; field_simp
      _ ≤ θ Nh * ((2 * C₁ + K) * (1 + i)) / β Nh := by
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hθN) hβN0.le
          nlinarith
      _ = D * (1 + i) := by rw [hDd]; ring
  have hup : ∀ x : Lam 2 L N, ∃ k ≤ Nh,
      Pconn L N (1 / b) x - θ Nh ≤ D * (1 + ((Nh - k : ℕ) : ℝ)) ∧
      (k < Nh → supNorm x < L ^ (k + 1)) := by
    intro x
    by_cases hx : x = 0
    · refine ⟨0, Nat.zero_le _, ?_, fun _ => ?_⟩
      · refine key x 0 (Nat.zero_le _) ?_
        rw [hx, Pconn_zero_eq_one (by positivity), hθ0]
        linarith
      · rw [hx, os_supNorm_zero]
        exact Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
    · obtain ⟨jp, hj, hPx⟩ := hP x hx
      rw [hθk] at hPx
      set k := min jp Nh with hkd
      have hk : k ≤ Nh := min_le_right _ _
      refine ⟨k, hk, key x k hk ?_, fun hkN => ?_⟩
      · have h1 := (abs_le.1 hPx).2
        have h2 : K * θ k / β k ≤ K * θ k / β Nh :=
          div_le_div_of_nonneg_left (by have := hθpos k hk; positivity) hβN0 (hmono k hk)
        have e : θ k * (1 + K / β Nh) = θ k + K * θ k / β Nh := by ring
        rw [e]; linarith
      · have hjk : k = jp := min_eq_left (by omega)
        rw [hjk]; exact os_supNorm_lt hL hx hj
  choose! kx hkx using hup
  -- the sum of `P − ϑ²`
  have hsum1 : ∑ x : Lam 2 L N, (Pconn L N (1 / b) x - θ Nh) ≤
      D * ∑ x : Lam 2 L N, (1 + ((Nh - kx x : ℕ) : ℝ)) := by
    rw [mul_sum]; exact sum_le_sum fun x _ => (hkx x).2.1
  have hcount : ∀ x : Lam 2 L N, ((Nh - kx x : ℕ) : ℝ) ≤
      ∑ m ∈ range Nh, if supNorm x ≤ L ^ (m + 1) - 1 then (1 : ℝ) else 0 := by
    intro x
    obtain ⟨hk, -, hs⟩ := hkx x
    rw [sum_boole]
    rcases eq_or_lt_of_le hk with h | h
    · rw [h, Nat.sub_self]; simp
    · have hs' := hs h
      have hsub : Finset.Ico (kx x) Nh ⊆ (range Nh).filter fun m => supNorm x ≤ L ^ (m + 1) - 1 := by
        intro m hm
        rw [Finset.mem_Ico] at hm
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hm.2, ?_⟩
        have : L ^ (kx x + 1) ≤ L ^ (m + 1) :=
          Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
        omega
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      exact_mod_cast this
  have hsum2 : ∑ x : Lam 2 L N, ∑ m ∈ range Nh,
      (if supNorm x ≤ L ^ (m + 1) - 1 then (1 : ℝ) else 0) ≤ (L : ℝ) ^ (2 * N) := by
    rw [sum_comm]
    calc ∑ m ∈ range Nh, ∑ x : Lam 2 L N, (if supNorm x ≤ L ^ (m + 1) - 1 then (1 : ℝ) else 0)
        = ∑ m ∈ range Nh,
            ((univ.filter fun x : Lam 2 L N => supNorm x ≤ L ^ (m + 1) - 1).card : ℝ) := by
          refine sum_congr rfl fun m _ => ?_; rw [sum_boole]
      _ ≤ ∑ m ∈ range Nh, 4 * (L : ℝ) ^ (2 * (m + 1)) := sum_le_sum fun m _ => os_card_ball N m
      _ = 4 * ∑ m ∈ range Nh, (L : ℝ) ^ (2 * (m + 1)) := by rw [mul_sum]
      _ ≤ 4 * (4 / 3 * (L : ℝ) ^ (2 * Nh)) := by
          exact mul_le_mul_of_nonneg_left (os_geom hL2 Nh) (by norm_num)
      _ ≤ (L : ℝ) ^ (2 * N) := by
          have e : (L : ℝ) ^ (2 * N) = (L : ℝ) ^ (2 * Nh) * (L : ℝ) ^ 4 := by
            rw [← pow_add]; congr 1; omega
          have h16 : (16 : ℝ) ≤ (L : ℝ) ^ 4 := by
            calc (16 : ℝ) = 2 ^ 4 := by norm_num
              _ ≤ (L : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hL2 4
          have hp : 0 ≤ (L : ℝ) ^ (2 * Nh) := by positivity
          rw [e]; nlinarith
  have hsum3 : ∑ x : Lam 2 L N, (1 + ((Nh - kx x : ℕ) : ℝ)) ≤ 2 * (L : ℝ) ^ (2 * N) := by
    rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, os_card]
    have := (sum_le_sum fun x (_ : x ∈ Finset.univ) => hcount x).trans hsum2
    linarith
  -- the lower bound
  have hlow : ∀ x : Lam 2 L N, θ Nh - K * θ Nh / β Nh ≤ Pconn L N (1 / b) x := by
    intro x
    have hc0' : 0 ≤ K * θ Nh / β Nh := by have := hθpos Nh le_rfl; positivity
    by_cases hx : x = 0
    · rw [hx, Pconn_zero_eq_one (by positivity)]; linarith
    · obtain ⟨jp, -, hPx⟩ := hP x hx
      rw [hθk] at hPx
      set k := min jp Nh with hkd
      have hk : k ≤ Nh := min_le_right _ _
      have hβk := hpos k hk
      have h1 := (abs_le.1 hPx).1
      have h2 : K / β k ≤ K / β Nh := div_le_div_of_nonneg_left hK hβN0 (hmono k hk)
      have h4 : θ Nh * (1 - K / β Nh) ≤ θ k * (1 - K / β k) :=
        mul_le_mul (hθmono k hk) (by linarith) (by linarith) (hθpos k hk).le
      have e1 : θ k - K * θ k / β k = θ k * (1 - K / β k) := by ring
      have e2 : θ Nh - K * θ Nh / β Nh = θ Nh * (1 - K / β Nh) := by ring
      linarith [h1, h4, e1, e2]
  -- assembly
  have hcard := os_card (L := L) N
  have hLN := os_LN_pos (L := L) N
  have hdiff : obsDens L N (1 / b) - θ Nh =
      (∑ x : Lam 2 L N, (Pconn L N (1 / b) x - θ Nh)) / (L : ℝ) ^ (2 * N) := by
    rw [eq_div_iff hLN.ne', sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]
    unfold obsDens
    field_simp
  have hlowsum : -(K * θ Nh / β Nh) ≤ obsDens L N (1 / b) - θ Nh := by
    rw [hdiff, le_div_iff₀ hLN]
    have := sum_le_sum fun (x : Lam 2 L N) (_ : x ∈ Finset.univ) =>
      (show -(K * θ Nh / β Nh) ≤ Pconn L N (1 / b) x - θ Nh by linarith [hlow x])
    rw [sum_const, card_univ, nsmul_eq_mul, hcard] at this
    linarith
  have hupsum : obsDens L N (1 / b) - θ Nh ≤ 2 * D := by
    rw [hdiff, div_le_iff₀ hLN]
    calc ∑ x : Lam 2 L N, (Pconn L N (1 / b) x - θ Nh)
        ≤ D * ∑ x : Lam 2 L N, (1 + ((Nh - kx x : ℕ) : ℝ)) := hsum1
      _ ≤ D * (2 * (L : ℝ) ^ (2 * N)) := mul_le_mul_of_nonneg_left hsum3 hD0
      _ = 2 * D * (L : ℝ) ^ (2 * N) := by ring
  rw [hθk, abs_le]
  have hθN := (hθpos Nh le_rfl).le
  have e : (4 * C₁ + 2 * K) * θ Nh / β Nh = 2 * D := by rw [hDd]; ring
  rw [e]
  constructor
  · have : K * θ Nh / β Nh ≤ 2 * D := by
      rw [hDd, ← e]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hθN) hβN0.le
    linarith
  · exact hupsum

/-! ### `obsBetaSum` and the running coupling at scale `N − 2` -/

/-- From `|P − (βt b)^{2/3}| ≤ K(βt b)^{2/3}/βt` and `βt ≥ 4K`: `|(1/b)P^{3/2} − βt| ≤ 3K`. -/
theorem os_rpow_close {b βt K P : ℝ} (hb : 0 < b) (hK : 0 ≤ K) (hβ : 4 * K ≤ βt)
    (hβ0 : 0 < βt)
    (hP : |P - (βt * b) ^ (2 / 3 : ℝ)| ≤ K * (βt * b) ^ (2 / 3 : ℝ) / βt) :
    |1 / b * P ^ (3 / 2 : ℝ) - βt| ≤ 3 * K := by
  set θ := (βt * b) ^ (2 / 3 : ℝ) with hθd
  have hθ : 0 < θ := by positivity
  set e := (P - θ) / θ with hed
  have hPe : P = θ * (1 + e) := by rw [hed]; field_simp; ring
  have he : |e| ≤ K / βt := by
    rw [hed, abs_div, abs_of_pos hθ, div_le_iff₀ hθ]
    calc |P - θ| ≤ K * θ / βt := hP
      _ = K / βt * θ := by ring
  have hKβ : K / βt ≤ 1 / 4 := by rw [div_le_div_iff₀ hβ0 (by norm_num)]; linarith
  have he4 : |e| ≤ 1 / 4 := he.trans hKβ
  have h1e : 0 ≤ 1 + e := by linarith [(abs_le.1 he4).1]
  have hθ32 : θ ^ (3 / 2 : ℝ) = βt * b := by
    rw [hθd, ← Real.rpow_mul (by positivity)]; norm_num
  have hP32 : P ^ (3 / 2 : ℝ) = βt * b * (1 + e) ^ (3 / 2 : ℝ) := by
    rw [hPe, Real.mul_rpow hθ.le h1e, hθ32]
  have hob : 1 / b * P ^ (3 / 2 : ℝ) = βt * (1 + e) ^ (3 / 2 : ℝ) := by
    rw [hP32]; field_simp
  rw [hob]
  have := ob_rpow32 he4
  calc |βt * (1 + e) ^ (3 / 2 : ℝ) - βt| = βt * |(1 + e) ^ (3 / 2 : ℝ) - 1| := by
        rw [show βt * (1 + e) ^ (3 / 2 : ℝ) - βt = βt * ((1 + e) ^ (3 / 2 : ℝ) - 1) by ring,
          abs_mul, abs_of_pos hβ0]
    _ ≤ βt * (9 / 4 * |e|) := mul_le_mul_of_nonneg_left this hβ0.le
    _ ≤ βt * (9 / 4 * (K / βt)) := by gcongr
    _ = 9 / 4 * K := by field_simp
    _ ≤ 3 * K := by linarith

/-- **`obsBetaSum ≈ βt`**: from `|obsDens L N (1/b) − (βt b)^{2/3}| ≤ K(βt b)^{2/3}/βt` and
`βt ≥ 4K`: `|obsBetaSum L N (1/b) − βt| ≤ 3K`. -/
theorem os_obsBetaSum_close {N : ℕ} {b βt K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) (hβ : 4 * K ≤ βt)
    (hβ0 : 0 < βt)
    (hP : |obsDens L N (1 / b) - (βt / (1 / b)) ^ (2 / 3 : ℝ)| ≤
      K * (βt / (1 / b)) ^ (2 / 3 : ℝ) / βt) :
    |obsBetaSum L N (1 / b) - βt| ≤ 3 * K := by
  have hθe : βt / (1 / b) = βt * b := by field_simp
  rw [hθe] at hP
  exact os_rpow_close hb hK hβ hβ0 hP

/-- `obsBetaSum L N (1/b) = t` gives `obsDens L N (1/b) = (tb)^{2/3} = thetaEpsSq t b`. -/
theorem os_dens_of_obsBetaSum {N : ℕ} {b t : ℝ} (hb : 0 < b)
    (h : obsBetaSum L N (1 / b) = t) : obsDens L N (1 / b) = thetaEpsSq t b := by
  unfold obsBetaSum at h
  have hP0 : 0 ≤ obsDens L N (1 / b) := (obsDens_pos (by positivity)).le
  have h' : obsDens L N (1 / b) ^ (3 / 2 : ℝ) = t * b := by
    calc obsDens L N (1 / b) ^ (3 / 2 : ℝ)
        = b * (1 / b * obsDens L N (1 / b) ^ (3 / 2 : ℝ)) := by field_simp
      _ = b * t := by rw [h]
      _ = t * b := mul_comm _ _
  unfold thetaEpsSq
  rw [← h', ← Real.rpow_mul hP0]; norm_num

/-- **`f^Σ_N = clF L t b N`** when `obsBetaSum L N (1/b_N) = t`. -/
theorem obsFS_eq_clF {t : ℝ} {b : ℕ → ℝ} {N : ℕ} (hb : 0 < b N)
    (h : obsBetaSum L N (1 / b N) = t) : obsFS L (fun N => 1 / b N) N = clF L t b N := by
  funext x
  unfold obsFS clF
  beta_reduce
  rw [os_dens_of_obsBetaSum hb h]

/-- **The lattice average of `f^Σ_N` is `1`**: `(1/L^{2N}) ∑_{x ∈ Λ_N} P_β[0 ↔ x]/obsDens = 1`. -/
theorem obsFS_avg {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) :
    (∑ x : Lam 2 L N, Pconn L N β x / obsDens L N β) / (L : ℝ) ^ (2 * N) = 1 := by
  have hD := obsDens_pos (L := L) (N := N) hβ
  have hLN := os_LN_pos (L := L) N
  rw [← sum_div, div_div, div_eq_one_iff_eq (by positivity)]
  unfold obsDens
  field_simp

end

end Spin2
