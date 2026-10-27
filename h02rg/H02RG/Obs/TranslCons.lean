import Obs.Transl
import Obs.FlowObs

/-!
# `N`-independence of the single-point observable couplings

Combining torus independence (`Obs.flowO_consist`), translation covariance
(`Obs.flowO_transl`) and the independence of the partner point (`Obs.flowO_a_indep`,
`Obs.flowO_b_indep`):

* **the `a` slot at the centre** (`la_ctr_consist`, `nextObs_a_ctr_consist`): for
  `j + 2 ≤ N ≤ M`, `λ_{a,j}` of the flow on `Λ_N` at `(ctr_N, any partner)` equals `λ_{a,j}`
  of the flow on `Λ_M` at `(ctr_M, any partner)`; the same for the step data
  `λ_{a,j+1}, γ_{a,j+1}` of `nextObs`.  (Proof: change the partner to `ctr_N` itself, embed into
  `Λ_M` by `flowO_consist`, translate `emb ctr_N` to `ctr_M` by `t = ctr_M - emb ctr_N`, which
  is divisible by `L^{N-1}` for odd `L`.)
* **the `b` slot at any point** (`lb_consist`, `nextObs_b_consist`): for `j + 2 ≤ N ≤ M` and
  `b ∈ Λ_N`, `λ_{b,j}` at `(any partner, b)` on `Λ_N` equals `λ_{b,j}` at
  `(any partner, prj (redZ N b))` on `Λ_M`, where `redZ N b ∈ [0, L^{N-1})^d` is the reduction
  of the coordinates of `b` modulo `L^{N-1}`; the same for `λ_{b,j+1}, γ_{b,j+1}` of `nextObs`.
  (Proof: change the partner to `b`, translate `b` to its reduction by a multiple of `L^{N-1}`,
  embed.)  The reduction is stable: `redZ M (prj (redZ N b)) = redZ N b` (`redZ_prj`).

The bulk hypothesis `hbulk` is that of `flowO_consist` (provided by `Flow.thm_flow`, see
`Obs.hbulk_of`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs Gen FRD

variable {d L : ℕ} [NeZero L] {c : Case}

/-! ### Arithmetic -/

section Arith

theorem pow_facts_ctr (hL : 8 ≤ L) {N : ℕ} :
    8 * ((L ^ (N - 1) - 1) / 2) ≤ L ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h : L ^ N = L * L ^ (N - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : 8 * L ^ (N - 1) ≤ L * L ^ (N - 1) := Nat.mul_le_mul_right _ hL
    have h2 : 8 * ((L ^ (N - 1) - 1) / 2) ≤ 8 * L ^ (N - 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem pow_pred_mul (hL : 8 ≤ L) {N : ℕ} (hN : 1 ≤ N) : 8 * L ^ (N - 1) ≤ L ^ N := by
  have h : L ^ N = L * L ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h]; exact Nat.mul_le_mul_right _ hL

theorem supNorm_ctr_le (hL : 8 ≤ L) (N : ℕ) : 8 * supNorm (ctr d L N) ≤ L ^ N := by
  have h : supNorm (ctr d L N) ≤ (L ^ (N - 1) - 1) / 2 := by
    refine Finset.sup_le fun i _ => ?_
    have := ctr_val (d := d) (N := N) (by omega : 2 ≤ L) i
    exact (min_le_left _ _).trans (le_of_eq this)
  have := pow_facts_ctr (N := N) hL
  omega

/-- For odd `L` and `1 ≤ N ≤ M`: `L^{N-1} ∣ (L^{M-1} - 1)/2 - (L^{N-1} - 1)/2`. -/
theorem dvd_ctr_sub (hLodd : Odd L) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    L ^ (N - 1) ∣ (L ^ (M - 1) - 1) / 2 - (L ^ (N - 1) - 1) / 2 := by
  obtain ⟨r, hr⟩ : Odd (L ^ (N - 1)) := hLodd.pow
  obtain ⟨q, hq⟩ : Odd (L ^ (M - N)) := hLodd.pow
  have hM : L ^ (M - 1) = L ^ (N - 1) * L ^ (M - N) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨q, ?_⟩
  rw [hM, hr, hq]
  have e0 : (2 * r + 1) * (2 * q + 1) = 2 * (2 * r * q + r + q) + 1 := by ring
  have e1 : (2 * r + 1) * (2 * q + 1) - 1 = 2 * (2 * r * q + r + q) := by omega
  have e2 : (2 * r + 1) * q = 2 * r * q + q := by ring
  rw [e1, show 2 * r + 1 - 1 = 2 * r by omega, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num), e2]
  omega

/-- The translation `ctr_M - emb ctr_N` is divisible by `L^{N-1}`. -/
theorem dvd_ctr_transl (hLodd : Odd L) (hL : 8 ≤ L) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M)
    (i : Fin d) :
    L ^ (N - 1) ∣ (co (ctr d L M - Flow.emb N M (ctr d L N)) i).val := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, c₀ = (L ^ (N - 1) - 1) / 2 := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℕ, c₁ = (L ^ (M - 1) - 1) / 2 := ⟨_, rfl⟩
  have hr : rep (ctr d L N) = fun _ => ((c₀ : ℕ) : ℤ) := by
    refine (eq_rep ?_ ?_).symm
    · show ((fun i => (((c₀ : ℕ) : ℤ) : ZMod (L ^ N))) : Fin d → ZMod (L ^ N)) =
        fun _ => (((L ^ (N - 1) - 1) / 2 : ℕ) : ZMod (L ^ N))
      funext i
      show (((c₀ : ℕ) : ℤ) : ZMod (L ^ N)) = (((L ^ (N - 1) - 1) / 2 : ℕ) : ZMod (L ^ N))
      rw [hc₀, Int.cast_natCast]
    · have h1 : supNormZ (fun _ : Fin d => ((c₀ : ℕ) : ℤ)) ≤ c₀ :=
        Finset.sup_le fun i _ => by simp
      have h2 := pow_facts_ctr (N := N) hL
      have h3 : 0 < L ^ N := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
      omega
  have he : co (Flow.emb N M (ctr d L N)) i = ((c₀ : ℕ) : ZMod (L ^ M)) := by
    show ((rep (ctr d L N) i : ℤ) : ZMod (L ^ M)) = _
    rw [hr]; simp
  have hm : co (ctr d L M) i = ((c₁ : ℕ) : ZMod (L ^ M)) := by rw [hc₁]; rfl
  have hle : c₀ ≤ c₁ := by
    have : L ^ (N - 1) ≤ L ^ (M - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have e : co (ctr d L M - Flow.emb N M (ctr d L N)) i = ((c₁ - c₀ : ℕ) : ZMod (L ^ M)) := by
    show co (ctr d L M) i - co (Flow.emb N M (ctr d L N)) i = _
    rw [hm, he, Nat.cast_sub hle]
  rw [e]
  exact dvd_val_natCast (pow_dvd_pow L (by omega)) (by rw [hc₀, hc₁]; exact dvd_ctr_sub hLodd hN hNM)

/-- The reduction of the coordinates of `b ∈ Λ_N` modulo `L^{N-1}`, a point of
`[0, L^{N-1})^d ⊆ ℤ^d`. -/
def redZ (N : ℕ) (b : Lam d L N) : Zd d := fun i => (((co b i).val % L ^ (N - 1) : ℕ) : ℤ)

/-- The reduced point of `Λ_N`. -/
def redPt (N : ℕ) (b : Lam d L N) : Lam d L N := prj (redZ N b)

theorem supNormZ_redZ (N : ℕ) (b : Lam d L N) : supNormZ (redZ N b) + 1 ≤ L ^ (N - 1) := by
  have h0 : 0 < L ^ (N - 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have : supNormZ (redZ N b) ≤ L ^ (N - 1) - 1 := Finset.sup_le fun i _ => by
    have := Nat.mod_lt (co b i).val h0
    simp only [redZ, Int.natAbs_natCast]
    omega
  omega

theorem supNorm_prj_redZ (hL : 8 ≤ L) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (b : Lam d L N) :
    8 * supNorm (prj (redZ N b) : Lam d L M) ≤ L ^ M := by
  have h1 := supNorm_prj_le (n := L ^ M) (redZ N b)
  have h2 := supNormZ_redZ N b
  have h3 := pow_pred_mul hL hN
  have h4 : L ^ N ≤ L ^ M := Nat.pow_le_pow_right (by omega) hNM
  omega

theorem natCast_mod_sub (m P n : ℕ) [NeZero m] :
    ((n % P : ℕ) : ZMod m) - ((n : ℕ) : ZMod m) = -((P * (n / P) : ℕ) : ZMod m) := by
  have h : ((n : ℕ) : ZMod m) = ((n % P : ℕ) : ZMod m) + ((P * (n / P) : ℕ) : ZMod m) := by
    rw [← Nat.cast_add, Nat.mod_add_div]
  rw [h]; ring

/-- The translation `redPt N b - b` is divisible by `L^{N-1}`. -/
theorem dvd_red_transl {N : ℕ} (hN : 1 ≤ N) (b : Lam d L N) (i : Fin d) :
    L ^ (N - 1) ∣ (co (redPt N b - b) i).val := by
  have hk : L ^ (N - 1) ∣ L ^ N := pow_dvd_pow L (by omega)
  have hx : co (redPt N b - b) i =
      (((co b i).val % L ^ (N - 1) : ℕ) : ZMod (L ^ N)) - (((co b i).val : ℕ) : ZMod (L ^ N)) := by
    rw [ZMod.natCast_zmod_val]
    show ((((co b i).val % L ^ (N - 1) : ℕ) : ℤ) : ZMod (L ^ N)) - co b i = _
    rw [Int.cast_natCast]
  rw [hx, natCast_mod_sub]
  exact dvd_val_neg hk (dvd_val_natCast hk (Nat.dvd_mul_right _ _))

theorem redPt_eq_add (N : ℕ) (b : Lam d L N) : b + (redPt N b - b) = redPt N b := by abel

theorem emb_redPt (hL : 8 ≤ L) {N M : ℕ} (hN : 1 ≤ N) (b : Lam d L N) :
    Flow.emb N M (redPt N b) = prj (redZ N b) := by
  have hr : rep (redPt N b) = redZ N b := by
    refine (eq_rep rfl ?_).symm
    have h2 := supNormZ_redZ N b
    have h3 := pow_pred_mul hL hN
    omega
  rw [Flow.emb, hr]

end Arith

/-! ### The consistency statements -/

section Consist

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {N M : ℕ} (hNM : N ≤ M) {msq ℓ₀ : ℝ}
  (hmsq : 0 ≤ msq) (V₀ : Vcoup)
  (hgoodN : ∀ j < N, GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Flow.covAt d L N msq j))
  (hgoodM : ∀ j < M, GoodCov (d := d) (L := L) (N := M) j ℓ₀ (Flow.covAt d L M msq j))
  (hbulk : ∀ k, k + 3 ≤ N →
    uVnext k (Flow.covAt d L M msq k) (Flow.flowN d L M msq V₀ k).1 (Flow.flowN d L M msq V₀ k).2 =
      uVnext k (Flow.covAt d L N msq k) (Flow.flowN d L N msq V₀ k).1
        (Flow.flowN d L N msq V₀ k).2)

theorem eight_le (hL : 2 ^ (d + 3) ≤ L) : 8 ≤ L := by
  have : 2 ^ 3 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

include hd hL hNM hmsq hgoodM hbulk

/-- Step 1 of the `a` slot: `(Λ_N, ctr_N, ctr_N) ≅ (Λ_M, ctr_M, ctr_M)` for `j + 2 ≤ N`. -/
theorem flowO_ctr_consist (hLodd : Odd L) (Vo₀ : Coup c) {j : ℕ} (hj : j + 2 ≤ N) :
    (flowO d L c N msq V₀ Vo₀ (ctr d L N) (ctr d L N) j).1 =
        (flowO d L c M msq V₀ Vo₀ (ctr d L M) (ctr d L M) j).1 ∧
      nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ (ctr d L N) (ctr d L N) j).1
          (flowO d L c N msq V₀ Vo₀ (ctr d L N) (ctr d L N) j).2 (ctr d L N) (ctr d L N) =
        nextObs (Flow.covAt d L M msq j) j (flowO d L c M msq V₀ Vo₀ (ctr d L M) (ctr d L M) j).1
          (flowO d L c M msq V₀ Vo₀ (ctr d L M) (ctr d L M) j).2 (ctr d L M) (ctr d L M) := by
  have h8 := eight_le hL
  have hc := supNorm_ctr_le (d := d) h8 N
  have ht : ∀ i, L ^ (N - 1) ∣ (co (ctr d L M - Flow.emb N M (ctr d L N)) i).val := fun i =>
    dvd_ctr_transl hLodd h8 (by omega) hNM i
  have het : Flow.emb N M (ctr d L N) + (ctr d L M - Flow.emb N M (ctr d L N)) = ctr d L M := by
    abel
  have h1 := (flowO_consist hd hL hNM hmsq V₀ Vo₀ hc hc hbulk j hj).1
  have h2 := nextObs_flowO_consist hd hL hNM hmsq V₀ Vo₀ hc hc hbulk hj
  have h3 := (flowO_transl V₀ Vo₀ hd hL hgoodM (k := N - 1) (by omega) _ ht
    (Flow.emb N M (ctr d L N)) (Flow.emb N M (ctr d L N)) j (by omega)).1
  have h4 := nextObs_flowO_transl V₀ Vo₀ hd hL hgoodM (k := N - 1) (by omega) _ ht
    (Flow.emb N M (ctr d L N)) (Flow.emb N M (ctr d L N)) (j := j) (by omega)
  rw [het] at h3 h4
  exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

/-- **`N`-independence of the `a` slot at the centre**: for `j + 2 ≤ N ≤ M` and any partners
`x ∈ Λ_N`, `y ∈ Λ_M` (and initial couplings with the same `λ_a`), `λ_{a,j}` and the step data
`λ_{a,j+1}`, `γ_{a,j+1}` agree. -/
theorem a_ctr_consist (hLodd : Odd L) {Vo₀ Vo₀' : Coup c} (hla : laOf c Vo₀ = laOf c Vo₀')
    (x : Lam d L N) (y : Lam d L M) {j : ℕ} (hj : j + 2 ≤ N) :
    laOf c (flowO d L c N msq V₀ Vo₀ (ctr d L N) x j).1 =
        laOf c (flowO d L c M msq V₀ Vo₀' (ctr d L M) y j).1 ∧
      laOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ (ctr d L N) x j).1
          (flowO d L c N msq V₀ Vo₀ (ctr d L N) x j).2 (ctr d L N) x) =
        laOf c (nextObs (Flow.covAt d L M msq j) j (flowO d L c M msq V₀ Vo₀' (ctr d L M) y j).1
          (flowO d L c M msq V₀ Vo₀' (ctr d L M) y j).2 (ctr d L M) y) ∧
      gaOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ (ctr d L N) x j).1
          (flowO d L c N msq V₀ Vo₀ (ctr d L N) x j).2 (ctr d L N) x) =
        gaOf c (nextObs (Flow.covAt d L M msq j) j (flowO d L c M msq V₀ Vo₀' (ctr d L M) y j).1
          (flowO d L c M msq V₀ Vo₀' (ctr d L M) y j).2 (ctr d L M) y) := by
  obtain ⟨e1, e2⟩ := flowO_ctr_consist hd hL hNM hmsq V₀ hgoodM hbulk hLodd Vo₀' hj
  have a1 := (flowO_a_indep msq V₀ hla (ctr d L N) x (ctr d L N) j).1
  have a2 := nextObs_flowO_a_indep msq V₀ hla (ctr d L N) x (ctr d L N) j
  have b1 := (flowO_a_indep msq V₀ (rfl : laOf c Vo₀' = _) (ctr d L M) (ctr d L M) y j).1
  have b2 := nextObs_flowO_a_indep msq V₀ (rfl : laOf c Vo₀' = _) (ctr d L M) (ctr d L M) y j
  refine ⟨a1.trans ((congrArg (laOf c) e1).trans b1), a2.1.trans ((congrArg (laOf c) e2).trans b2.1),
    a2.2.trans ((congrArg (gaOf c) e2).trans b2.2)⟩

include hgoodN in
/-- **`N`-independence of the `b` slot**: for `j + 2 ≤ N ≤ M`, `b ∈ Λ_N` and any partners
`a ∈ Λ_N`, `a' ∈ Λ_M` (and initial couplings with the same `λ_b`), `λ_{b,j}` and the step
data `λ_{b,j+1}`, `γ_{b,j+1}` at `b` on `Λ_N` agree with those at the reduced point
`prj (redZ N b)` on `Λ_M`. -/
theorem b_consist {Vo₀ Vo₀' : Coup c} (hlb : lbOf c Vo₀ = lbOf c Vo₀') (a b : Lam d L N)
    (a' : Lam d L M) {j : ℕ} (hj : j + 2 ≤ N) :
    lbOf c (flowO d L c N msq V₀ Vo₀ a b j).1 =
        lbOf c (flowO d L c M msq V₀ Vo₀' a' (prj (redZ N b)) j).1 ∧
      lbOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
          (flowO d L c N msq V₀ Vo₀ a b j).2 a b) =
        lbOf c (nextObs (Flow.covAt d L M msq j) j
          (flowO d L c M msq V₀ Vo₀' a' (prj (redZ N b)) j).1
          (flowO d L c M msq V₀ Vo₀' a' (prj (redZ N b)) j).2 a' (prj (redZ N b))) ∧
      gbOf c (nextObs (Flow.covAt d L N msq j) j (flowO d L c N msq V₀ Vo₀ a b j).1
          (flowO d L c N msq V₀ Vo₀ a b j).2 a b) =
        gbOf c (nextObs (Flow.covAt d L M msq j) j
          (flowO d L c M msq V₀ Vo₀' a' (prj (redZ N b)) j).1
          (flowO d L c M msq V₀ Vo₀' a' (prj (redZ N b)) j).2 a' (prj (redZ N b))) := by
  have h8 := eight_le hL
  have hN : 1 ≤ N := by omega
  have ht : ∀ i, L ^ (N - 1) ∣ (co (redPt N b - b) i).val := fun i => dvd_red_transl hN b i
  have hbt : b + (redPt N b - b) = redPt N b := redPt_eq_add N b
  have hr : 8 * supNorm (redPt N b) ≤ L ^ N := supNorm_prj_redZ (d := d) h8 hN le_rfl b
  -- partner change on `Λ_N`
  have a1 := (flowO_b_indep msq V₀ hlb a b b j).1
  have a2 := nextObs_flowO_b_indep msq V₀ hlb a b b j
  -- translation on `Λ_N`
  have t1 := (flowO_transl V₀ Vo₀' hd hL hgoodN (k := N - 1) (by omega) _ ht b b j (by omega)).1
  have t2 := nextObs_flowO_transl V₀ Vo₀' hd hL hgoodN (k := N - 1) (by omega) _ ht b b
    (j := j) (by omega)
  rw [hbt] at t1 t2
  -- embedding
  have c1 := (flowO_consist hd hL hNM hmsq V₀ Vo₀' hr hr hbulk j hj).1
  have c2 := nextObs_flowO_consist hd hL hNM hmsq V₀ Vo₀' hr hr hbulk hj
  rw [emb_redPt h8 hN] at c1 c2
  -- partner change on `Λ_M`
  have b1 := (flowO_b_indep msq V₀ (rfl : lbOf c Vo₀' = _) (prj (redZ N b)) a' (prj (redZ N b))
    j).1
  have b2 := nextObs_flowO_b_indep msq V₀ (rfl : lbOf c Vo₀' = _) (prj (redZ N b)) a'
    (prj (redZ N b)) j
  refine ⟨a1.trans ((congrArg (lbOf c) (t1.symm.trans c1)).trans b1),
    a2.1.trans ((congrArg (lbOf c) (t2.symm.trans c2)).trans b2.1),
    a2.2.trans ((congrArg (gbOf c) (t2.symm.trans c2)).trans b2.2)⟩

end Consist

end

end Obs
