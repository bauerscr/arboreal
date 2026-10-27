import Step2.D2.D2Bx3
import Step2.Map.DCov

/-!
# Torus symbols as `ℤ²` kernels for the polarised bubble

For a symbol `w` on `Λ = (ℤ/L^N)²` and `R ∈ ℕ`:

* `cKer R w u = kern w (u)` for `|u|_∞ ≤ R`, `0` otherwise;
* `kmat_eq_cTor`: if `rng w ≤ R` then `kmat w x y = cTor (cKer R w) (x - y)`;
* `cKer_even`: invariant symbols (`symSub`) give even kernels;
* `negBub_kmat`: `negBub (kmat w) X 0 = bubX (cKer R w) (cKer R w)`;
* `cKer_eq_kern`: `cKer R w v = kern w (prj v)` for `|v|_∞ ≤ R + 4` (`2(R + 4) < L^N`).
-/

namespace Step2

open Step

noncomputable section

open Finset MeasureTheory Step2.D2 Loc FRD Grassmann

variable {L N : ℕ} [NeZero L]

/-- The `ℤ²` kernel of a torus symbol, truncated at `|u|_∞ ≤ R`. -/
def cKer (R : ℕ) (w : DressedFRD.Sym 2 (L ^ N)) (u : ℤ × ℤ) : ℂ :=
  if nm u ≤ R then DressedFRD.kern w (prj (zd u) : Lam 2 L N) else 0

theorem cKer_range {R : ℕ} (w : DressedFRD.Sym 2 (L ^ N)) {u : ℤ × ℤ} (hu : R < nm u) :
    cKer R w u = 0 := by
  unfold cKer; rw [if_neg (by omega)]

theorem cKer_hfs (R : ℕ) (w : DressedFRD.Sym 2 (L ^ N)) : Function.HasFiniteSupport (cKer R w) :=
  hfs_of_range _ fun _ hu => cKer_range w hu

theorem supNorm_prj_zd {u : ℤ × ℤ} (h : 2 * nm u < L ^ N) :
    supNorm (prj (zd u) : Lam 2 L N) = nm u := by
  rw [← nm_rep, rep_prj_zd u h]

/-- **The torus matrix is the `ℤ²` kernel.** -/
theorem kmat_eq_cTor {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hR : DressedFRD.rng w ≤ R)
    (x y : Lam 2 L N) : DressedFRD.kmat w x y = cTor (cKer R w) (x - y) := by
  unfold DressedFRD.kmat cTor cKer
  set z := x - y
  have hz : (prj (zd (rep z 0, rep z 1)) : Lam 2 L N) = z := by rw [zd_rep, prj_rep]
  split_ifs with h
  · rw [hz]
  · rw [nm_rep] at h
    exact DressedFRD.kern_eq_zero_of_rng_lt (by omega)

theorem kern_neg_of_symMem {w : DressedFRD.Sym 2 (L ^ N)} (hw : w ∈ symSub) (x : Lam 2 L N) :
    DressedFRD.kern w (-x) = DressedFRD.kern w x := by
  have e : FRD.symm (n := L ^ N) 1 (fun _ => -1) x = -x := by
    funext i
    simp only [FRD.symm, co, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul,
      Equiv.Perm.coe_one, id]
    rfl
  rw [← e, kern_symm' hw]

theorem prj_zd_neg (u : ℤ × ℤ) : (prj (zd (-u.1, -u.2)) : Lam 2 L N) = -prj (zd u) := by
  rw [← prj_neg]; congr 1; funext i; fin_cases i <;> rfl

theorem nm_neg' (u : ℤ × ℤ) : nm (-u.1, -u.2) = nm u := by
  unfold nm; simp

/-- **Invariant symbols give even kernels.** -/
theorem cKer_even {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hw : w ∈ symSub) (u : ℤ × ℤ) :
    cKer R w (-u.1, -u.2) = cKer R w u := by
  unfold cKer
  rw [nm_neg', prj_zd_neg, kern_neg_of_symMem hw]

/-- **`negBub` of a torus symbol is `𝔅x` of its kernel.** -/
theorem negBub_kmat {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hw : w ∈ symSub)
    (hR : DressedFRD.rng w ≤ R) (hn : 2 * (R + 4) < L ^ N) {X : Finset (Lam 2 L N)}
    (hne : X.Nonempty) (hX : ∀ x ∈ X, 2 * (supNorm (x - base X) + R + 3) < L ^ N) :
    negBub (DressedFRD.kmat w) X 0 = bubX (cKer R w) (cKer R w) :=
  negBub_eq_bubX (fun _ hu => cKer_range w hu) (cKer_even hw) hn (kmat_eq_cTor hR) hne hX

theorem cKer_add (R : ℕ) (w w' : DressedFRD.Sym 2 (L ^ N)) :
    cKer R (w + w') = cKer R w + cKer R w' := by
  funext u; by_cases h : nm u ≤ R <;> simp [cKer, h, DressedFRD.kern_add]

theorem cKer_sub (R : ℕ) (w w' : DressedFRD.Sym 2 (L ^ N)) :
    cKer R (w - w') = cKer R w - cKer R w' := by
  funext u; by_cases h : nm u ≤ R <;> simp [cKer, h, DressedFRD.kern_sub]

theorem cKer_smul (R : ℕ) (c : ℂ) (w : DressedFRD.Sym 2 (L ^ N)) :
    cKer R (c • w) = c • cKer R w := by
  funext u; by_cases h : nm u ≤ R <;> simp [cKer, h, DressedFRD.kern_smul]

theorem cKer_sum {ι : Type*} (s : Finset ι) (R : ℕ) (w : ι → DressedFRD.Sym 2 (L ^ N)) :
    cKer R (∑ i ∈ s, w i) = ∑ i ∈ s, cKer R (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext u; simp [cKer, DressedFRD.kern]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, cKer_add, ih]

/-- `cKer R w v = kern w (prj v)` for `|v|_∞ ≤ R + 4` if `rng w ≤ R` and `2(R + 4) < L^N`. -/
theorem cKer_eq_kern {R : ℕ} {w : DressedFRD.Sym 2 (L ^ N)} (hR : DressedFRD.rng w ≤ R)
    (hn : 2 * (R + 4) < L ^ N) {v : ℤ × ℤ} (hv : nm v ≤ R + 4) :
    cKer R w v = DressedFRD.kern w (prj (zd v) : Lam 2 L N) := by
  unfold cKer
  split_ifs with h
  · rfl
  · symm
    refine DressedFRD.kern_eq_zero_of_rng_lt ?_
    rw [supNorm_prj_zd (by omega)]; omega

end

end Step2
