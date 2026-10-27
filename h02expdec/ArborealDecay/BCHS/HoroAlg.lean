module

public import ArborealDecay.BCHS.ShiftAlg

/-!
# The horospherical substitution is an algebra homomorphism (R1)

`ArborealDecay.Horo.horoF vtx F p = F(x_super(p), y(p), eᵗψ)` is the iterated nilpotent Taylor shift
`shiftL` of `F` followed by the rescaling `scaleA`.  For smooth (`SSmooth`) superfunctions:

* `horoF_add`, `horoF_smul`, `horoF_mul`, `horoF_const`, `horoF_sum`, `horoF_list_prod`: `horoF`
  is (pointwise) an algebra homomorphism;
* `horoF_scomp`: `horoF (g(S)) = g(horoF S)` for `g` smooth on an open set containing the bodies;
* `horoF_x`, `horoF_y`: the coordinates go to `x_i = sinh t_i − eᵗ(½ s_i² + n_i)` and
  `y_i = e^{t_i} s_i` (BCHS (2.73)).
-/

@[expose] public section

namespace ArborealDecay.BCHS

noncomputable section

open Finset ArborealDecay.Super ArborealDecay.Horo Grassmann
open scoped ContDiff

set_option linter.unusedSectionVars false

/-! ### Iterated shifts -/

section ShiftL

variable {E : Type*} [Fintype E]
variable {O : Type*} [Fintype O] [DecidableEq O]
variable {ι : Type*} {v : ι → E → ℝ} {g : ι → (E → ℝ) → ℝ} {n : ι → Gr O} {K : ℕ}

theorem SSmooth.shiftL (hg : ∀ k, ContDiff ℝ ∞ (g k)) (l : List ι) {F : (E → ℝ) → Gr O}
    (hF : SSmooth F) : SSmooth (ArborealDecay.Horo.shiftL v g n K l F) := by
  induction l with
  | nil => exact hF
  | cons k l ih => exact ih.shiftT (v k) (g k) (n k) K (hg k)

theorem shiftL_add (hg : ∀ k, ContDiff ℝ ∞ (g k)) (l : List ι) {F G : (E → ℝ) → Gr O}
    (hF : SSmooth F) (hG : SSmooth G) :
    ArborealDecay.Horo.shiftL v g n K l (fun x => F x + G x) =
      fun x => ArborealDecay.Horo.shiftL v g n K l F x +
        ArborealDecay.Horo.shiftL v g n K l G x := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    funext x
    simp only [ArborealDecay.Horo.shiftL]
    rw [ih]
    exact shiftT_add (v k) (g k) (n k) K (hF.shiftL hg l) (hG.shiftL hg l) x

theorem shiftL_smul (hg : ∀ k, ContDiff ℝ ∞ (g k)) (l : List ι) (r : ℝ) {F : (E → ℝ) → Gr O}
    (hF : SSmooth F) :
    ArborealDecay.Horo.shiftL v g n K l (fun x => r • F x) =
      fun x => r • ArborealDecay.Horo.shiftL v g n K l F x := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    funext x
    simp only [ArborealDecay.Horo.shiftL]
    rw [ih]
    exact shiftT_smul (v k) (g k) (n k) K r (hF.shiftL hg l) x

theorem shiftL_mul (hg : ∀ k, ContDiff ℝ ∞ (g k)) (hn : ∀ k, n k ^ K = 0)
    (hcomm : ∀ k a, n k * a = a * n k) (l : List ι) {F G : (E → ℝ) → Gr O}
    (hF : SSmooth F) (hG : SSmooth G) :
    ArborealDecay.Horo.shiftL v g n K l (fun x => F x * G x) =
      fun x => ArborealDecay.Horo.shiftL v g n K l F x *
        ArborealDecay.Horo.shiftL v g n K l G x := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    funext x
    simp only [ArborealDecay.Horo.shiftL]
    rw [ih]
    exact shiftT_mul (v k) (g k) (hn k) (hcomm k) (hF.shiftL hg l) (hG.shiftL hg l) x

theorem isEven_shiftL (hg : ∀ k, ContDiff ℝ ∞ (g k)) (hnE : ∀ k, IsEven (n k)) (l : List ι)
    {F : (E → ℝ) → Gr O} (hF : SSmooth F) (hE : ∀ x, IsEven (F x)) (x : E → ℝ) :
    IsEven (ArborealDecay.Horo.shiftL v g n K l F x) := by
  induction l generalizing x with
  | nil => exact hE x
  | cons k l ih => exact isEven_shiftT (v k) (g k) (hF.shiftL hg l) ih (hnE k) x

theorem body_shiftL (hn0 : ∀ k, body (n k) = 0) (hK : 0 < K) (l : List ι) (F : (E → ℝ) → Gr O)
    (x : E → ℝ) : body (ArborealDecay.Horo.shiftL v g n K l F x) = body (F x) := by
  induction l generalizing x with
  | nil => rfl
  | cons k l ih =>
    simp only [ArborealDecay.Horo.shiftL]
    rw [body_shiftT (v k) (g k) _ (hn0 k) hK x, ih]

theorem shiftL_scomp (hg : ∀ k, ContDiff ℝ ∞ (g k)) (hn : ∀ k, n k ^ K = 0)
    (hcomm : ∀ k a, n k * a = a * n k) (hnE : ∀ k, IsEven (n k)) (hn0 : ∀ k, body (n k) = 0)
    {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U) {S : (E → ℝ) → Gr O}
    (hS : SSmooth S) (hE : ∀ y, IsEven (S y)) (hb : ∀ y, body (S y) ∈ U) (l : List ι) :
    ArborealDecay.Horo.shiftL v g n K l (fun x => scomp φ (S x)) =
      fun x => scomp φ (ArborealDecay.Horo.shiftL v g n K l S x) := by
  have hK : ∀ k, 0 < K := fun k => pos_of_pow_eq_zero (hn k) one_ne_zero_gr
  induction l with
  | nil => rfl
  | cons k l ih =>
    funext x
    simp only [ArborealDecay.Horo.shiftL]
    rw [ih]
    exact shiftT_scomp (v k) (g k) (hn k) (hcomm k) (hnE k) (hn0 k) hU hφ (hS.shiftL hg l)
      (isEven_shiftL hg hnE l hS hE) (fun y => by rw [body_shiftL hn0 (hK k)]; exact hb y) x

/-- Shifts along `v` do not change a function invariant along `v`. -/
theorem shiftT_of_invariant (v : E → ℝ) (c : (E → ℝ) → ℝ) {n : Gr O} {K : ℕ} (hK : 0 < K)
    {F : (E → ℝ) → Gr O} (hF : SSmooth F) (hinv : ∀ x (t : ℝ), F (x + t • v) = F x) :
    ArborealDecay.Horo.shiftT v c n K F = F := by
  have h1 : pd v F = fun _ => 0 := funext (pd_eq_zero_of_invariant hF.sdiff hinv)
  have hm : ∀ m, ArborealDecay.Horo.pdn v (m + 1) F = fun _ => 0 := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih => rw [pdn_succ, ih]; funext x; exact pd_const 0 v x
  funext x
  exact shiftT_of_one_le v c F n x hK fun m hm' => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm]; simp

/-- Shift of an affine function: if `∂_v F = a` is constant, `F(x + c n v) = F(x) + c a n`. -/
theorem shiftT_of_pd_const (v : E → ℝ) (c : (E → ℝ) → ℝ) {n : Gr O} {K : ℕ} (hn : n ^ K = 0)
    {F : (E → ℝ) → Gr O} (a : Gr O) (hpd : pd v F = fun _ => a) (x : E → ℝ) :
    ArborealDecay.Horo.shiftT v c n K F x = F x + c x • (a * n) := by
  have hm : ∀ m, ArborealDecay.Horo.pdn v (m + 2) F = fun _ => 0 := by
    intro m
    induction m with
    | zero =>
      rw [pdn_succ, pdn_succ, pdn_zero, hpd]; funext x; exact pd_const a v x
    | succ m ih => rw [pdn_succ, ih]; funext x; exact pd_const 0 v x
  rcases K with _ | _ | K
  · exact absurd (show (1 : Gr O) = 0 by simpa using hn) one_ne_zero_gr
  · rw [pow_one] at hn
    rw [hn, mul_zero, smul_zero, add_zero]
    simp [ArborealDecay.Horo.shiftT]
  · rw [ArborealDecay.Horo.shiftT, sum_range_succ', sum_range_succ',
      sum_eq_zero fun m _ => by rw [hm]; simp]
    have h1 : ArborealDecay.Horo.pdn v 1 F x = a := by rw [pdn_succ, pdn_zero, hpd]
    simp [h1, add_comm]

end ShiftL

/-! ### The horospherical substitution -/

section HoroF

variable {Λ M P : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype M] [DecidableEq M]
  [Fintype P] [DecidableEq P]
variable (vtx : M → Λ)

theorem contDiff_gS (k : Λ) : ContDiff ℝ ∞ (gS k : (Λ ⊕ Λ → ℝ) → ℝ) :=
  (hasTemperateGrowth_gS k).1

theorem body_scaleA {O : Type*} (c : O → ℝ) (x : Gr O) : body (scaleA c x) = body x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι w =>
    change body (scaleA c (ExteriorAlgebra.ι ℝ w)) = body (ExteriorAlgebra.ι ℝ w)
    rw [scaleA_ι, body_ι, body_ι]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem isEven_scaleA {O : Type*} (c : O → ℝ) {x : Gr O} (hx : IsEven x) :
    IsEven (scaleA c x) := by
  unfold IsEven at *; rw [inv'_scaleA, hx]

theorem kord_pos : 0 < Kord M P := Nat.succ_pos _

/-- Abbreviation for the hypotheses of the shift lemmas at the horospherical data. -/
theorem nV_pow (k : Λ) : nV vtx k ^ Kord M P = (0 : SG M P) := nV_pow_Kord vtx k

theorem horoF_def (F : (Λ ⊕ Λ → ℝ) → SG M P) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx F p = scaleA (cS vtx fun i => p (.inl i))
      (ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) Finset.univ.toList F (horo p)) :=
  rfl

theorem horoF_add {F G : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSmooth F) (hG : SSmooth G)
    (p : Λ ⊕ Λ → ℝ) : horoF vtx (fun x => F x + G x) p = horoF vtx F p + horoF vtx G p := by
  rw [horoF_def, shiftL_add contDiff_gS _ hF hG, map_add]; rfl

theorem horoF_smul (r : ℝ) {F : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSmooth F) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun x => r • F x) p = r • horoF vtx F p := by
  rw [horoF_def, shiftL_smul contDiff_gS _ r hF, map_smul]; rfl

theorem horoF_neg {F : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSmooth F) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun x => -F x) p = -horoF vtx F p := by
  have := horoF_smul vtx (-1) hF p
  simpa using this

theorem horoF_sub {F G : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSmooth F) (hG : SSmooth G)
    (p : Λ ⊕ Λ → ℝ) : horoF vtx (fun x => F x - G x) p = horoF vtx F p - horoF vtx G p := by
  have := horoF_add vtx hF hG.neg p
  rw [horoF_neg vtx hG] at this
  simpa [sub_eq_add_neg] using this

theorem horoF_mul {F G : (Λ ⊕ Λ → ℝ) → SG M P} (hF : SSmooth F) (hG : SSmooth G)
    (p : Λ ⊕ Λ → ℝ) : horoF vtx (fun x => F x * G x) p = horoF vtx F p * horoF vtx G p := by
  rw [horoF_def, shiftL_mul contDiff_gS (nV_pow vtx) (nV_comm vtx) _ hF hG, map_mul]; rfl

theorem horoF_const (a : SG M P) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun _ => a) p = scaleA (cS vtx fun i => p (.inl i)) a := by
  rw [horoF_def]
  congr 1
  have : ∀ l : List Λ, ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) l
      (fun _ : Λ ⊕ Λ → ℝ => a) = fun _ => a := by
    intro l
    induction l with
    | nil => rfl
    | cons k l ih =>
      simp only [ArborealDecay.Horo.shiftL]
      rw [ih]
      exact shiftT_of_invariant _ _ kord_pos (SSmooth.const a) fun _ _ => rfl
  rw [this]

theorem horoF_sum {ι : Type*} (s : Finset ι) {F : ι → (Λ ⊕ Λ → ℝ) → SG M P}
    (hF : ∀ i ∈ s, SSmooth (F i)) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun x => ∑ i ∈ s, F i x) p = ∑ i ∈ s, horoF vtx (F i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using horoF_const vtx (0 : SG M P) p
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [horoF_add vtx (hF a (mem_insert_self a s))
      (SSmooth.sum s fun i hi => hF i (mem_insert_of_mem hi)),
      ih fun i hi => hF i (mem_insert_of_mem hi)]

theorem horoF_list_prod {ι : Type*} (l : List ι) {F : ι → (Λ ⊕ Λ → ℝ) → SG M P}
    (hF : ∀ i ∈ l, SSmooth (F i)) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun x => (l.map fun i => F i x).prod) p = (l.map fun i => horoF vtx (F i) p).prod := by
  induction l with
  | nil => simpa using horoF_const vtx (1 : SG M P) p
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [horoF_mul vtx (hF i List.mem_cons_self)
      (SSmooth.list_prod l fun j hj => hF j (List.mem_cons_of_mem _ hj)),
      ih fun j hj => hF j (List.mem_cons_of_mem _ hj)]

theorem horoF_scomp {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U)
    {S : (Λ ⊕ Λ → ℝ) → SG M P} (hS : SSmooth S) (hE : ∀ y, IsEven (S y))
    (hb : ∀ y, body (S y) ∈ U) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun x => scomp φ (S x)) p = scomp φ (horoF vtx S p) := by
  rw [horoF_def, shiftL_scomp contDiff_gS (nV_pow vtx) (nV_comm vtx) (isEven_nV vtx)
    (body_nV vtx) hU hφ hS hE hb]
  exact map_scomp _ (body_scaleA _) φ (isNilpotent_soul
    (isEven_shiftL contDiff_gS (isEven_nV vtx) _ hS hE _))

theorem isEven_horoF {S : (Λ ⊕ Λ → ℝ) → SG M P} (hS : SSmooth S) (hE : ∀ y, IsEven (S y))
    (p : Λ ⊕ Λ → ℝ) : IsEven (horoF vtx S p) :=
  isEven_scaleA _ (isEven_shiftL contDiff_gS (isEven_nV vtx) _ hS hE _)

theorem body_horoF (S : (Λ ⊕ Λ → ℝ) → SG M P) (p : Λ ⊕ Λ → ℝ) :
    body (horoF vtx S p) = body (S (horo p)) := by
  rw [horoF_def, body_scaleA, body_shiftL (body_nV vtx) kord_pos]

/-! ### Coordinates -/

theorem exV_inr (k i : Λ) : (exV k : Λ ⊕ Λ → ℝ) (.inr i) = 0 := by
  simp [exV]

theorem exV_inl_ne {k i : Λ} (h : k ≠ i) : (exV k : Λ ⊕ Λ → ℝ) (.inl i) = 0 := by
  simp [exV, Ne.symm h]

theorem gS_add_exV {i k : Λ} (h : k ≠ i) (q : Λ ⊕ Λ → ℝ) (t : ℝ) :
    gS i (q + t • exV k) = gS i q := by
  simp [gS, exV_inl_ne h, exV_inr]

theorem sSmooth_coord (a : Λ ⊕ Λ) :
    SSmooth (fun q : Λ ⊕ Λ → ℝ => q a • (1 : SG M P)) :=
  SSmooth.smul_const (contDiff_apply ℝ ℝ a) 1

theorem sSmooth_gS_smul (i : Λ) (c : SG M P) :
    SSmooth (fun q : Λ ⊕ Λ → ℝ => gS i q • c) :=
  SSmooth.smul_const (contDiff_gS i) c

theorem pd_coord_inl (i : Λ) :
    pd (exV i) (fun q : Λ ⊕ Λ → ℝ => q (.inl i) • (1 : SG M P)) = fun _ => 1 := by
  funext q
  rw [pd_smul_const (differentiable_apply _) 1]
  rw [show (fun q : Λ ⊕ Λ → ℝ => q (.inl i)) =
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Λ ⊕ Λ => ℝ) (.inl i) from rfl,
    ContinuousLinearMap.fderiv]
  simp [exV]

/-- `shiftL` of the coordinate `x_i`: `x_i + g_i(x) n_i` once `i` has been processed. -/
theorem shiftL_coord_inl (i : Λ) (l : List Λ) (hl : l.Nodup) :
    ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) l
        (fun q : Λ ⊕ Λ → ℝ => q (.inl i) • (1 : SG M P)) =
      if i ∈ l then fun q => q (.inl i) • (1 : SG M P) + gS i q • nV vtx i
      else fun q => q (.inl i) • (1 : SG M P) := by
  induction l with
  | nil => simp [ArborealDecay.Horo.shiftL]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    simp only [ArborealDecay.Horo.shiftL]
    rw [ih hl.2]
    by_cases hki : k = i
    · subst hki
      simp only [hl.1, ite_false, List.mem_cons_self, ite_true]
      funext q
      rw [shiftT_of_pd_const _ _ (nV_pow vtx k) 1 (pd_coord_inl k) q, one_mul]
    · have hinv : ∀ (F : (Λ ⊕ Λ → ℝ) → SG M P), (F = fun q => q (.inl i) • (1 : SG M P) +
          gS i q • nV vtx i) ∨ (F = fun q => q (.inl i) • (1 : SG M P)) →
          ArborealDecay.Horo.shiftT (exV k) (gS k) (nV vtx k) (Kord M P) F = F := by
        rintro F (rfl | rfl)
        · refine shiftT_of_invariant _ _ kord_pos
            ((sSmooth_coord _).add (sSmooth_gS_smul i _)) fun q t => ?_
          rw [gS_add_exV hki]
          simp [exV_inl_ne hki]
        · refine shiftT_of_invariant _ _ kord_pos (sSmooth_coord _) fun q t => ?_
          simp [exV_inl_ne hki]
      have hmem : (i ∈ k :: l) ↔ i ∈ l := by
        simp [List.mem_cons, Ne.symm hki]
      by_cases hil : i ∈ l
      · simp only [hil, ite_true, hmem]; exact hinv _ (Or.inl rfl)
      · simp only [hil, ite_false, hmem]; exact hinv _ (Or.inr rfl)

theorem shiftL_coord_inr (i : Λ) (l : List Λ) :
    ArborealDecay.Horo.shiftL exV gS (nV vtx) (Kord M P) l
        (fun q : Λ ⊕ Λ → ℝ => q (.inr i) • (1 : SG M P)) =
      fun q => q (.inr i) • (1 : SG M P) := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [ArborealDecay.Horo.shiftL]
    rw [ih]
    refine shiftT_of_invariant _ _ kord_pos (sSmooth_coord _) fun q t => ?_
    simp [exV_inr]

/-- `horoF x_i = sinh t_i − e^{t_i}(½ s_i² + n_i)`. -/
theorem horoF_x (i : Λ) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun q => q (.inl i) • (1 : SG M P)) p =
      hx (p (.inl i)) (p (.inr i)) • (1 : SG M P) - Real.exp (p (.inl i)) • nV vtx i := by
  rw [horoF_def, shiftL_coord_inl vtx i _ (Finset.nodup_toList _)]
  simp only [Finset.mem_toList, Finset.mem_univ, ite_true]
  rw [map_add, map_smul, map_smul, map_one, scaleA_nV, gS_horo, smul_smul, horo_inl]
  rw [show -Real.exp (-p (.inl i)) * Real.exp (2 * p (.inl i)) = -Real.exp (p (.inl i)) by
    rw [neg_mul, ← Real.exp_add]; ring_nf]
  rw [neg_smul, ← sub_eq_add_neg]

/-- `horoF y_i = e^{t_i} s_i`. -/
theorem horoF_y (i : Λ) (p : Λ ⊕ Λ → ℝ) :
    horoF vtx (fun q => q (.inr i) • (1 : SG M P)) p = hy (p (.inl i)) (p (.inr i)) • (1 : SG M P) := by
  rw [horoF_def, shiftL_coord_inr vtx i]
  simp only [map_smul, map_one]
  rfl

end HoroF

end

end ArborealDecay.BCHS

end
