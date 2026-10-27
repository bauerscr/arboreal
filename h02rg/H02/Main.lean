import H02.Integral
import H02.Graph

/-!
# Theorem `thm:H02forest`

For any real symmetric edge weights `β` and vertex weights `h`,
`[1]_{β,h} = ∑_{F ∈ 𝓕} ∏_{ij ∈ F} β_{ij} ∏_{T ∈ F} (1 + ∑_{i ∈ T} h_i)`.
-/

namespace H02

noncomputable section

set_option linter.unusedSectionVars false

open Finset Classical

variable {Λ : Type*} [DecidableEq Λ]

local notation "A" => Grassmann Λ

variable [Fintype Λ]

/-- `1 + u_a · u_b` as a function of the unordered pair `ab`. -/
def Xs : Sym2 Λ → C Λ := Sym2.lift ⟨Xc, Xc_comm⟩

@[simp] theorem Xs_mk (a b : Λ) : Xs s(a, b) = Xc a b := rfl

/-- The edge set of `S` as a finset (with a fixed decidability instance). -/
def E (S : SimpleGraph Λ) : Finset (Sym2 Λ) := by classical exact S.edgeFinset

@[simp] theorem mem_E {S : SimpleGraph Λ} {e : Sym2 Λ} : e ∈ E S ↔ e ∈ S.edgeSet := by
  simp [E]

theorem E_eq (S : SimpleGraph Λ) [Fintype S.edgeSet] : E S = S.edgeFinset := by
  ext e; simp

/-- The form `∏_{ab ∈ E} (1 + u_a · u_b) ∏_{i ∈ R} ξ_i η_i`. -/
def mono (E : Finset (Sym2 Λ)) (R : Finset Λ) : C Λ := (∏ e ∈ E, Xs e) * ∏ i ∈ R, pc i i

theorem prod_pc_eq {R : Finset Λ} {v : Λ} (hv : v ∈ R) :
    ∏ i ∈ R, pc i i = pc v v * ∏ i ∈ R.erase v, pc i i :=
  (Finset.mul_prod_erase R (fun i => pc i i) hv).symm

theorem mono_mem_freeSub (S : SimpleGraph Λ) (R : Finset Λ) (v : Λ) (hiso : ∀ w, ¬S.Adj v w)
    (hvR : v ∉ R) : mono (E S) R ∈ freeSub v := by
  refine Subalgebra.mul_mem _ (Subalgebra.prod_mem _ fun e he => ?_)
    (Subalgebra.prod_mem _ fun i hi => pc_mem_freeSub (by rintro rfl; exact hvR hi)
      (by rintro rfl; exact hvR hi))
  induction e using Sym2.ind with
  | h a b =>
    rw [mem_E, SimpleGraph.mem_edgeSet] at he
    exact Xc_mem_freeSub (by rintro rfl; exact hiso b he) (by rintro rfl; exact hiso a he.symm)

theorem T_prod_Xs (S : SimpleGraph Λ) (s : Finset Λ) (hS : ∀ x y, S.Adj x y → x ∈ s) :
    T s (cv (∏ e ∈ E S, Xs e)) = 0 := by
  refine T_prod s _ _ (fun e he => ?_) (fun e he => ?_) <;>
  induction e using Sym2.ind with
  | h a b =>
    rw [mem_E, SimpleGraph.mem_edgeSet] at he
    first
    | exact T_Xc (hS a b he) (hS b a he.symm)
    | exact inv'_Xc a b

/-- The key computation: the Berezin integral over the vertices `l` of
`∏_{ab ∈ S} (1 + u_a · u_b) ∏_{i ∈ R} ξ_i η_i` is `1` if `S` is a forest in which no two
vertices of `R` are connected, and `0` otherwise. -/
theorem berezin_mono (n : ℕ) : ∀ (l : List Λ), l.length = n → l.Nodup →
    ∀ (S : SimpleGraph Λ), (∀ x y, S.Adj x y → x ∈ l) → ∀ R : Finset Λ, (∀ x ∈ R, x ∈ l) →
    berezin l (cv (mono (E S) R)) = if Good S R then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro l hl hnd
  -- first the case of nonempty `R`, by induction on the number of edges
  have key : ∀ k, ∀ S : SimpleGraph Λ, (E S).card = k → (∀ x y, S.Adj x y → x ∈ l) →
      ∀ R : Finset Λ, R.Nonempty → (∀ x ∈ R, x ∈ l) →
      berezin l (cv (mono (E S) R)) = if Good S R then 1 else 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro S hk hS R hRne hR
    obtain ⟨v, hv⟩ := hRne
    by_cases hadj : ∃ w, S.Adj v w
    · obtain ⟨w, hvw⟩ := hadj
      have hne : v ≠ w := hvw.ne
      set S' := S.deleteEdges {s(v, w)} with hS'
      have hmem : s(v, w) ∈ E S := by simpa using hvw
      have hE : E S' = (E S).erase s(v, w) := by
        ext e; simp [hS', SimpleGraph.edgeSet_deleteEdges, and_comm]
      have hmono : mono (E S) R =
          Xc v w * (∏ e ∈ E S', Xs e) * (pc v v * ∏ i ∈ R.erase v, pc i i) := by
        rw [mono, hE, ← Finset.mul_prod_erase _ _ hmem, prod_pc_eq hv, Xs_mk]
      by_cases hw : w ∈ R
      · have hw' : w ∈ R.erase v := Finset.mem_erase.2 ⟨hne.symm, hw⟩
        have : mono (E S) R = 0 := by
          rw [hmono, prod_pc_eq hw']
          linear_combination (∏ e ∈ E S', Xs e) * (∏ i ∈ (R.erase v).erase w, pc i i) *
            (pc v v * pc_sq w + pc w w * pc_mul_Xc v w)
        rw [this, map_zero, map_zero, if_neg (not_good_of_adj hv hw hvw)]
      · have hmono' : mono (E S) R = mono (E S') (insert w R) := by
          rw [hmono, mono, Finset.prod_insert hw, prod_pc_eq hv]
          linear_combination (∏ e ∈ E S', Xs e) * (∏ i ∈ R.erase v, pc i i) *
            pc_mul_Xc v w
        have hcard : (E S').card < k := by
          rw [hE, ← hk]; exact Finset.card_erase_lt_of_mem hmem
        rw [hmono', ihk _ hcard S' rfl
          (fun x y hxy => hS x y (SimpleGraph.deleteEdges_le _ hxy)) _ (Finset.insert_nonempty _ _)
          (fun x hx => ?_), if_congr (good_iff_deleteEdges hv hw hvw).symm rfl rfl]
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hS _ _ hvw.symm
        · exact hR x hx
    · push Not at hadj
      have hvl : v ∈ l := hR v hv
      have hfree := mono_mem_freeSub S (R.erase v) v hadj (Finset.notMem_erase v R)
      have : cv (mono (E S) R) = cv (mono (E S) (R.erase v)) * (ξ v * η v) := by
        rw [← coe_pc, ← map_mul, mono, mono, prod_pc_eq hv]; ring_nf
      rw [this, berezin_eq_cons_erase hvl, intStep_free_mul_ξη hfree]
      have hlen : (l.erase v).length < n := by
        rw [List.length_erase_of_mem hvl, ← hl]
        exact Nat.sub_lt (List.length_pos_of_mem hvl) one_pos
      rw [ihn _ hlen (l.erase v) rfl (hnd.erase v) S (fun x y hxy => ?_) (R.erase v)
        (fun x hx => ?_), if_congr (good_iff_erase hv hadj).symm rfl rfl]
      · have hxv : x ≠ v := by rintro rfl; exact hadj y hxy
        exact (List.mem_erase_of_ne hxv).2 (hS x y hxy)
      · obtain ⟨hxv, hx⟩ := Finset.mem_erase.1 hx
        exact (List.mem_erase_of_ne hxv).2 (hR x hx)
  intro S hS R hR
  by_cases hRe : R.Nonempty
  · exact key _ S rfl hS R hRe hR
  rw [Finset.not_nonempty_iff_eq_empty] at hRe
  subst hRe
  cases l with
  | nil =>
    have hS0 : S = ⊥ := by
      ext x y; simpa using hS x y
    subst hS0
    have : E (⊥ : SimpleGraph Λ) = ∅ := by ext e; simp
    rw [this, if_pos ⟨SimpleGraph.isAcyclic_bot, by simp⟩]
    simp [mono]
  | cons v l' =>
    have hs : ∀ i ∈ (v :: l').toFinset, i ∈ v :: l' := fun i hi => List.mem_toFinset.1 hi
    have hv : v ∈ (v :: l').toFinset := by simp
    rw [show mono (E S) ∅ = ∏ e ∈ E S, Xs e by simp [mono],
      berezin_pin hs hv (T_prod_Xs S _ fun x y hxy => List.mem_toFinset.2 (hS x y hxy))]
    have : ξ v * η v * cv (∏ e ∈ E S, Xs e) = cv (mono (E S) {v}) := by
      rw [← coe_pc, ← map_mul, mono, Finset.prod_singleton, mul_comm]
    rw [this, key _ S rfl hS {v} (Finset.singleton_nonempty v) (by simp),
      if_congr (good_empty_iff S v).symm rfl rfl]

theorem int0_mono (G : SimpleGraph Λ) (R : Finset Λ) :
    int0 (cv (mono (E G) R)) = if Good G R then 1 else 0 := by
  unfold int0
  rw [berezin_mono _ _ rfl (Finset.nodup_toList _) G (by simp) R (by simp)]
  split_ifs <;> simp

/-! ### The exponential of the action -/

theorem exp_eq_one_add {a : C Λ} (h : a * a = 0) : IsNilpotent.exp a = 1 + a := by
  rw [IsNilpotent.exp_eq_sum (k := 2) (by rw [pow_two, h])]
  simp [Finset.sum_range_succ]

theorem isNilpotent_of_mul_self {a : C Λ} (h : a * a = 0) : IsNilpotent a :=
  ⟨2, by rw [pow_two, h]⟩

theorem smul_mul_smul_self {r : ℝ} {a : C Λ} (h : a * a = 0) : (r • a) * (r • a) = 0 := by
  rw [smul_mul_smul_comm, h, smul_zero]

theorem exp_sum {ι : Type*} (s : Finset ι) (f : ι → C Λ) (hf : ∀ i ∈ s, IsNilpotent (f i)) :
    IsNilpotent.exp (∑ i ∈ s, f i) = ∏ i ∈ s, IsNilpotent.exp (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [IsNilpotent.exp_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      IsNilpotent.exp_add_of_commute (Commute.all _ _) (hf a (mem_insert_self a s))
        (isNilpotent_sum fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- `-H_{β,h}`, written as an element of the center. -/
def W (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) : C Λ :=
  ∑ e ∈ E (⊤ : SimpleGraph Λ), Sym2.lift ⟨β, hβ⟩ e • Xs e + ∑ i, h i • pc i i

theorem action_eq (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    action β h = -cv (W β hβ h) := by
  have h1 : action β h = cv ((1 / 4 : ℝ) • ∑ i, ∑ j, β i j •
      ((Xc i i - 1) - (Xc i j - 1) - (Xc j i - 1) + (Xc j j - 1)) + ∑ i, h i • (zc i - 1)) := by
    simp [action, map_sum, coe_Xc, coe_zc]
  rw [h1, ← map_neg]
  congr 1
  have hterm : ∀ i j, β i j • ((Xc i i - 1) - (Xc i j - 1) - (Xc j i - 1) + (Xc j j - 1)) =
      (-2 : ℝ) • (β i j • Xc i j) := by
    intro i j; rw [Xc_self, Xc_self, Xc_comm j i]; module
  have hg : ∀ i j, β i j • Xc i j = β j i • Xc j i := fun i j => by rw [hβ, Xc_comm]
  have hsum := sum_sum_eq_two_nsmul (fun i j => β i j • Xc i j) hg (fun i => by simp [Xc_self])
  have hlift : ∀ e, Sym2.lift ⟨fun i j => β i j • Xc i j, hg⟩ e = Sym2.lift ⟨β, hβ⟩ e • Xs e := by
    intro e; induction e using Sym2.ind with | h a b => rfl
  simp_rw [hlift, ← E_eq] at hsum
  simp_rw [hterm, ← Finset.smul_sum, hsum]
  simp only [W, zc, sub_sub_cancel_left, smul_neg, Finset.sum_neg_distrib]
  module

theorem exp_W (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    IsNilpotent.exp (W β hβ h) = ∑ t ∈ (E (⊤ : SimpleGraph Λ)).powerset, ∑ R ∈ (univ : Finset Λ).powerset,
      ((∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) * ∏ i ∈ R, h i) • mono t R := by
  have hX : ∀ e : Sym2 Λ, Xs e * Xs e = 0 := by
    intro e; induction e using Sym2.ind with | h a b => exact Xc_sq a b
  have hn1 : ∀ e ∈ E (⊤ : SimpleGraph Λ), IsNilpotent (Sym2.lift ⟨β, hβ⟩ e • Xs e) :=
    fun e _ => isNilpotent_of_mul_self (smul_mul_smul_self (hX e))
  have hn2 : ∀ i ∈ (univ : Finset Λ), IsNilpotent (h i • pc i i) :=
    fun i _ => isNilpotent_of_mul_self (smul_mul_smul_self (pc_sq i))
  rw [W, IsNilpotent.exp_add_of_commute (Commute.all _ _) (isNilpotent_sum hn1)
    (isNilpotent_sum hn2), exp_sum _ _ hn1, exp_sum _ _ hn2]
  rw [Finset.prod_congr rfl fun e _ => exp_eq_one_add (smul_mul_smul_self (hX e)),
    Finset.prod_congr rfl fun i _ => exp_eq_one_add (smul_mul_smul_self (pc_sq i)),
    Finset.prod_one_add, Finset.prod_one_add, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.prod_smul, Finset.prod_smul, smul_mul_smul_comm, mono]

theorem Xs_sq (e : Sym2 Λ) : Xs e * Xs e = 0 := by
  induction e using Sym2.ind with | h a b => exact Xc_sq a b

theorem isNilpotent_W (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    IsNilpotent (W β hβ h) :=
  (Commute.all _ _).isNilpotent_add
    (isNilpotent_sum fun e _ => isNilpotent_of_mul_self (smul_mul_smul_self (Xs_sq e)))
    (isNilpotent_sum fun i _ => isNilpotent_of_mul_self (smul_mul_smul_self (pc_sq i)))

theorem int0_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    int0 (∑ i ∈ s, f i) = ∑ i ∈ s, int0 (f i) := by
  simp [int0, map_sum]

theorem int0_cv_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → C Λ) :
    int0 (cv (∑ i ∈ s, c i • f i)) = ∑ i ∈ s, c i * int0 (cv (f i)) := by
  simp [int0, map_sum, map_smul]

theorem sum_E_powerset {M : Type*} [AddCommMonoid M] (f : Finset (Sym2 Λ) → M) :
    ∑ t ∈ (E (⊤ : SimpleGraph Λ)).powerset, f t = ∑ G : SimpleGraph Λ, f (E G) := by
  convert sum_edgeFinset_powerset f using 3

open Classical in
/-- **Theorem `thm:H02forest`.** For any real-valued symmetric edge weights `β` and vertex
weights `h`, the partition function `[1]_{β,h}` of the `ℍ^{0|2}` model equals
`∑_{F ∈ 𝓕} ∏_{ij ∈ F} β_{ij} ∏_{T ∈ F} (1 + ∑_{i ∈ T} h_i)`, where `F` runs over the forests
on the vertex set `Λ` and `T` over the trees (connected components) of `F`.  (Forests using an
edge `ij` with `β_{ij} = 0` contribute zero, so this is the sum over the spanning forests of the
graph induced by the nonzero edge weights.) -/
theorem thm_H02forest (β : Λ → Λ → ℝ) (hβ : ∀ i j, β i j = β j i) (h : Λ → ℝ) :
    expect β h 1 = ∑ F : SimpleGraph Λ with F.IsAcyclic,
      (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        ∏ T : F.ConnectedComponent, (1 + ∑ i with F.connectedComponentMk i = T, h i) := by
  have hW := isNilpotent_W β hβ h
  rw [expect, action_eq β hβ h, neg_neg, one_mul, ← IsNilpotent.map_exp hW, exp_W, map_sum,
    int0_sum]
  simp_rw [int0_cv_sum]
  rw [sum_E_powerset (fun t => ∑ R ∈ (univ : Finset Λ).powerset,
    ((∏ e ∈ t, Sym2.lift ⟨β, hβ⟩ e) * ∏ i ∈ R, h i) * int0 (cv (mono t R))), Finset.sum_filter]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp_rw [← E_eq F, int0_mono, mul_assoc, ← Finset.mul_sum, mul_ite, mul_one, mul_zero,
    sum_good F h, mul_ite, mul_zero]

end

end H02
