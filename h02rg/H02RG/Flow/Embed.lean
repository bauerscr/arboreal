import Step.Structure
import Step.FRDCov

/-!
# The identification of `Λ_N` with a neighbourhood of the origin in `Λ_M`

For `N ≤ M` the map `emb x = prj(rep x)` identifies `Λ_N` with the points of `Λ_M` whose centred
representatives are those of `Λ_N`.  It is injective with left inverse `emb M N`
(`emb_emb`), preserves `|x|_∞` (`supNorm_emb`), does not decrease distances
(`supNorm_sub_le_emb`), preserves differences of points that are not too far from the origin
(`emb_sub`, `supNorm_emb_sub`), and preserves `j`-blocks near the origin (`blk_emb_iff`).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L]

/-- The identification `Λ_N → Λ_M`, `x ↦ rep(x) mod L^M`. -/
def emb (N M : ℕ) (x : Lam d L N) : Lam d L M := prj (rep x)

/-- The identification on the generators of the Grassmann algebra. -/
def embV (N M : ℕ) : V (Lam d L N) →ₗ[ℂ] V (Lam d L M) where
  toFun v b := ∑ a : Sf (Lam d L N), if (emb N M a.1, a.2) = b then v a else 0
  map_add' v w := by ext b; simp [← sum_add_distrib, ite_add_zero]
  map_smul' c v := by ext b; simp [mul_sum]

/-- The induced algebra map `𝒩(Λ_N) → 𝒩(Λ_M)`, `ψ_x ↦ ψ_{emb x}`. -/
def embA (N M : ℕ) : Alg d L N →ₐ[ℂ] Alg d L M := ExteriorAlgebra.map (embV N M)

/-- The induced map on even elements. -/
def embE (N M : ℕ) : EvR (Lam d L N) →ₐ[ℂ] EvR (Lam d L M) := mapE (embV N M)

/-- The sup-norm diameter of a finite set. -/
def diam {n : ℕ} [NeZero n] (X : Finset (Torus d n)) : ℕ := X.sup fun x => X.sup fun y => supNorm (x - y)

/-- `K` on `Λ_N` and `K'` on `Λ_M` agree on connected `j`-polymers of diameter `≤ D` in the
central region `|x|_∞ ≤ L^N/4`. -/
def Compat {N M : ℕ} (j D : ℕ) (K : Act d L N) (K' : Act d L M) : Prop :=
  ∀ X : Finset (Lam d L N), IsConn j X → (∀ x ∈ X, 4 * supNorm x ≤ L ^ N) → diam X ≤ D →
    embE N M (K X) = K' (X.image (emb N M))

/-! ### Centred representatives -/

section Rep

variable {n : ℕ} [NeZero n]

theorem rep_bound (x : Torus d n) (i : Fin d) : -(n : ℤ) < 2 * rep x i ∧ 2 * rep x i ≤ n := by
  unfold rep
  have := ZMod.val_lt ((x : Fin d → ZMod n) i)
  split_ifs with h <;> omega

theorem val_intCast_of {k : ℕ} [NeZero k] {w : ℤ} (h1 : -(k : ℤ) ≤ w) (h2 : w < k) :
    (((w : ZMod k).val : ℕ) : ℤ) = if 0 ≤ w then w else w + k := by
  rw [ZMod.val_intCast]
  split_ifs with hw
  · exact Int.emod_eq_of_lt hw h2
  · rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by omega)

theorem rep_prj {w : Zd d} (hw : ∀ i, -(n : ℤ) < 2 * w i ∧ 2 * w i ≤ n) :
    rep (prj w : Torus d n) = w := by
  funext i
  have hi := hw i
  have hv := val_intCast_of (k := n) (w := w i) (by omega) (by omega)
  show (if ((w i : ℤ) : ZMod n).val ≤ n - ((w i : ℤ) : ZMod n).val then
    ((((w i : ℤ) : ZMod n).val : ℕ) : ℤ) else ((((w i : ℤ) : ZMod n).val : ℕ) : ℤ) - n) = w i
  split_ifs with h <;> split_ifs at hv with hw0 <;> omega

theorem val_eq_rep (x : Torus d n) (i : Fin d) :
    ((((x : Fin d → ZMod n) i).val : ℕ) : ℤ) = if 0 ≤ rep x i then rep x i else rep x i + n := by
  have e := congrFun (congrArg (fun y : Torus d n => (y : Fin d → ZMod n)) (prj_rep x)) i
  have hb := rep_bound x i
  have := val_intCast_of (k := n) (w := rep x i) (by omega) (by omega)
  rw [← this]
  exact congrArg (fun z : ZMod n => ((z.val : ℕ) : ℤ)) e.symm

theorem natAbs_rep_le (x : Torus d n) (i : Fin d) : (rep x i).natAbs ≤ supNorm x := by
  rw [← supNormZ_rep_eq]; exact natAbs_le_supNormZ _ i

theorem eq_of_prj_eq {z w : Zd d} (h : (prj z : Torus d n) = prj w)
    (hs : supNormZ z + supNormZ w < n) : z = w := by
  funext i
  have h1 : ((z i : ℤ) : ZMod n) = ((w i : ℤ) : ZMod n) :=
    congrFun (congrArg (fun y : Torus d n => (y : Fin d → ZMod n)) h) i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
  obtain ⟨c, hc⟩ := h1
  have ha := natAbs_le_supNormZ z i
  have hb := natAbs_le_supNormZ w i
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · have : (n : ℤ) * c ≤ -n := by nlinarith
    omega
  · subst hc0; omega
  · have : (n : ℤ) ≤ n * c := by nlinarith
    omega

theorem supNormZ_sub_rep_le (x y : Torus d n) :
    supNormZ (rep x - rep y) ≤ supNorm x + supNorm y := by
  rw [supNormZ_le_iff]
  intro i
  have h1 := natAbs_rep_le x i
  have h2 := natAbs_rep_le y i
  simp only [Pi.sub_apply]
  omega

theorem supNormZ_add_rep_le (x y : Torus d n) :
    supNormZ (rep x + rep y) ≤ supNorm x + supNorm y := by
  rw [supNormZ_le_iff]
  intro i
  have h1 := natAbs_rep_le x i
  have h2 := natAbs_rep_le y i
  simp only [Pi.add_apply]
  omega

/-- Differences of points not too far from the origin have the expected representatives. -/
theorem rep_sub_of {x y : Torus d n} (h : supNorm x + supNorm y + supNorm (x - y) < n) :
    rep (x - y) = rep x - rep y := by
  refine (eq_of_prj_eq (n := n) ?_ ?_).symm
  · rw [prj_sub, prj_rep, prj_rep, prj_rep]
  · have := supNormZ_sub_rep_le x y
    rw [supNormZ_rep_eq]; omega

theorem rep_add_of {x y : Torus d n} (h : supNorm x + supNorm y + supNorm (x + y) < n) :
    rep (x + y) = rep x + rep y := by
  refine (eq_of_prj_eq (n := n) ?_ ?_).symm
  · rw [prj_add, prj_rep, prj_rep, prj_rep]
  · have := supNormZ_add_rep_le x y
    rw [supNormZ_rep_eq]; omega

end Rep

/-! ### Basic properties of `emb` -/

section Emb

variable {N M : ℕ}

theorem pow_le_pow_NM (hNM : N ≤ M) : L ^ N ≤ L ^ M :=
  Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hNM

theorem pow_dvd_NM (hNM : N ≤ M) : L ^ N ∣ L ^ M := pow_dvd_pow L hNM

theorem rep_emb (hNM : N ≤ M) (x : Lam d L N) : rep (emb (d := d) (L := L) N M x) = rep x := by
  refine rep_prj fun i => ?_
  have := rep_bound x i
  have h := pow_le_pow_NM (L := L) hNM
  have h' : ((L ^ N : ℕ) : ℤ) ≤ ((L ^ M : ℕ) : ℤ) := by exact_mod_cast h
  omega

theorem emb_emb (hNM : N ≤ M) (x : Lam d L N) :
    emb (d := d) (L := L) M N (emb N M x) = x := by
  rw [emb, rep_emb hNM]; exact prj_rep x

theorem emb_injective' (hNM : N ≤ M) : Function.Injective (emb (d := d) (L := L) N M) :=
  fun x y h => by rw [← emb_emb hNM x, h, emb_emb hNM y]

theorem supNorm_emb (hNM : N ≤ M) (x : Lam d L N) :
    supNorm (emb (d := d) (L := L) N M x) = supNorm x := by
  rw [← supNormZ_rep_eq, rep_emb hNM, supNormZ_rep_eq]

theorem rep_emb' (y : Lam d L M) (hy : 2 * supNorm y < L ^ N) :
    rep (emb (d := d) (L := L) M N y) = rep y := by
  refine rep_prj fun i => ?_
  have := natAbs_rep_le y i
  omega

/-- Points of `Λ_M` near the origin are in the image of `emb`. -/
theorem emb_emb' (y : Lam d L M) (hy : 2 * supNorm y < L ^ N) :
    emb (d := d) (L := L) N M (emb M N y) = y := by
  rw [emb, rep_emb' y hy]; exact prj_rep y

theorem supNorm_emb' (y : Lam d L M) (hy : 2 * supNorm y < L ^ N) :
    supNorm (emb (d := d) (L := L) M N y) = supNorm y := by
  rw [← supNormZ_rep_eq, rep_emb' y hy, supNormZ_rep_eq]

theorem emb_sub {x y : Lam d L N} (h : supNorm x + supNorm y + supNorm (x - y) < L ^ N) :
    emb (d := d) (L := L) N M (x - y) = emb N M x - emb N M y := by
  rw [emb, rep_sub_of h, prj_sub]; rfl

theorem emb_add {x y : Lam d L N} (h : supNorm x + supNorm y + supNorm (x + y) < L ^ N) :
    emb (d := d) (L := L) N M (x + y) = emb N M x + emb N M y := by
  rw [emb, rep_add_of h, prj_add]; rfl

theorem supNorm_emb_sub (hNM : N ≤ M) {x y : Lam d L N}
    (h : supNorm x + supNorm y + supNorm (x - y) < L ^ N) :
    supNorm (emb (d := d) (L := L) N M x - emb N M y) = supNorm (x - y) := by
  rw [← emb_sub h, supNorm_emb hNM]

theorem prj_eq_of_prj_eq {n k : ℕ} [NeZero n] [NeZero k] (hnk : n ∣ k) {z w : Zd d}
    (h : (prj z : Torus d k) = prj w) : (prj z : Torus d n) = prj w := by
  funext i
  have h1 : ((z i : ℤ) : ZMod k) = ((w i : ℤ) : ZMod k) :=
    congrFun (congrArg (fun y : Torus d k => (y : Fin d → ZMod k)) h) i
  show ((z i : ℤ) : ZMod n) = ((w i : ℤ) : ZMod n)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 ⊢
  exact (Int.natCast_dvd_natCast.2 hnk).trans h1

/-- `emb` does not decrease distances. -/
theorem supNorm_sub_le_emb (hNM : N ≤ M) (x y : Lam d L N) :
    supNorm (x - y) ≤ supNorm (emb (d := d) (L := L) N M x - emb N M y) := by
  have e1 : (emb N M x - emb N M y : Lam d L M) = prj (rep x - rep y) := by
    rw [prj_sub]; rfl
  have e2 : (x - y : Lam d L N) = prj (rep x - rep y) := by rw [prj_sub, prj_rep, prj_rep]
  set w := rep (prj (rep x - rep y) : Lam d L M)
  have e3 : (prj w : Lam d L M) = prj (rep x - rep y) := prj_rep _
  have e4 : (prj w : Lam d L N) = prj (rep x - rep y) := prj_eq_of_prj_eq (pow_dvd_NM hNM) e3
  rw [e1, e2, ← e4, ← supNormZ_rep_eq (prj (rep x - rep y) : Lam d L M)]
  exact supNorm_prj_le w

theorem val_emb (hNM : N ≤ M) (x : Lam d L N) (i : Fin d) :
    ((((emb (d := d) (L := L) N M x : Fin d → ZMod (L ^ M)) i).val : ℕ) : ℤ) =
      if 0 ≤ rep x i then rep x i else rep x i + (L ^ M : ℕ) := by
  rw [val_eq_rep, rep_emb hNM]

theorem div_lt_div_of_add_le {P a b : ℕ} (hP : 0 < P) (h : a + P ≤ b) : a / P < b / P := by
  have : (a + P) / P ≤ b / P := Nat.div_le_div_right h
  rw [Nat.add_div_right a hP] at this
  omega

theorem div_iff_aux {P n m a b a' b' : ℕ} (hP : 0 < P) (hPn : P ∣ n) (hPm : P ∣ m)
    (hnm : n ≤ m) (h8 : 8 * P ≤ n) {r s : ℤ} (hr : 16 * r.natAbs ≤ 7 * n)
    (hs : 16 * s.natAbs ≤ 7 * n)
    (ha : (a : ℤ) = if 0 ≤ r then r else r + n) (ha' : (a' : ℤ) = if 0 ≤ r then r else r + m)
    (hb : (b : ℤ) = if 0 ≤ s then s else s + n) (hb' : (b' : ℤ) = if 0 ≤ s then s else s + m) :
    a' / P = b' / P ↔ a / P = b / P := by
  obtain ⟨t, ht⟩ : P ∣ m - n := Nat.dvd_sub hPm hPn
  split_ifs at ha ha' hb hb' with h1 h2 h2
  · have e1 : a' = a := by omega
    have e2 : b' = b := by omega
    rw [e1, e2]
  · have c1 : a' + P ≤ b' := by omega
    have c2 : a + P ≤ b := by omega
    have := div_lt_div_of_add_le hP c1
    have := div_lt_div_of_add_le hP c2
    omega
  · have c1 : b' + P ≤ a' := by omega
    have c2 : b + P ≤ a := by omega
    have := div_lt_div_of_add_le hP c1
    have := div_lt_div_of_add_le hP c2
    omega
  · have e1 : a' = a + P * t := by omega
    have e2 : b' = b + P * t := by omega
    rw [e1, e2, Nat.add_mul_div_left _ _ hP, Nat.add_mul_div_left _ _ hP]
    omega

/-- `emb` preserves `j`-blocks of points with `|x|_∞ ≤ 7 L^N/16`. -/
theorem blk_emb_iff (hNM : N ≤ M) {j : ℕ} (hj : j ≤ N) (hP : 8 * L ^ j ≤ L ^ N)
    {x y : Lam d L N} (hx : 16 * supNorm x ≤ 7 * L ^ N) (hy : 16 * supNorm y ≤ 7 * L ^ N) :
    blk j (emb (d := d) (L := L) N M x) = blk j (emb N M y) ↔ blk j x = blk j y := by
  simp only [funext_iff, blk]
  refine forall_congr' fun i => ?_
  have hP0 : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  exact div_iff_aux hP0 (pow_dvd_pow L hj) (pow_dvd_pow L (hj.trans hNM)) (pow_le_pow_NM hNM) hP
    ((Nat.mul_le_mul_left 16 (natAbs_rep_le x i)).trans hx)
    ((Nat.mul_le_mul_left 16 (natAbs_rep_le y i)).trans hy)
    (val_eq_rep x i) (val_emb hNM x i) (val_eq_rep y i) (val_emb hNM y i)

theorem supNorm_le_of_blk_eq {j : ℕ} {x y : Lam d L N} (h : blk j x = blk j y) :
    supNorm y ≤ supNorm x + L ^ j := by
  have h1 := supNorm_lt_of_blk_eq h
  have h2 := supNorm_add_le x (y - x)
  rw [add_sub_cancel] at h2
  rw [supNorm_sub_comm] at h1
  omega

end Emb

end

end Flow
