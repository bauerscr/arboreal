import Step.Decomp
import Step.Coupling

/-!
# Auxiliary results for Propositions `prop:ZVK` (factorisation, symmetries) and
`prop:consistency`

* Geometry: points of `X^□` are within `2^d L^j` of `X` (`exists_near_of_mem_nbhd`), and
  non-touching `j`-polymers are at sup-distance `> L^j` (`lt_supNorm_of_not_touch`); hence the
  covariance vanishes between `U_1^□` and `U_2^□` for non-touching `(j+1)`-polymers
  (`C_eq_zero_of_nbhd`).
* Algebra: `𝔼_C (F_1 F_2) = 𝔼_C F_1 𝔼_C F_2` for `F_i ∈ 𝒩(X_i ⊔ X_i)` if `C` vanishes between
  the disjoint sets `X_1`, `X_2` (`EC_mul_of_sep`).
* A general membership principle (`MemHyp`, `Knext_mem`): if the subalgebras `S ⊆ 𝒩(Λ)`,
  `S_2 ⊆ 𝒩(Λ ⊔ Λ)` are compatible with `θ`, the inclusion and `𝔼_C`, and contain the building
  blocks `K(Y)`, `Loc_{Y,B} K(Y)`, `V(B)`, `V_{j+1}(B)`, then `K_{j+1}(U) ∈ S`.  This gives
  locality, `U(1)` invariance and `J` invariance of `K_{j+1}`.
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Geometry -/

/-- Points of `X^□` lie within `2^d L^j` of `X`. -/
theorem exists_near_of_mem_nbhd {j : ℕ} {X : Finset (Lam d L N)} {y : Lam d L N}
    (hy : y ∈ nbhd j X) : ∃ x ∈ X, supNorm (y - x) ≤ 2 ^ d * L ^ j := by
  simp only [nbhd, mem_filter, mem_univ, true_and] at hy
  obtain ⟨S, hS, hyS, b, hb, hbS⟩ := hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
  exact ⟨x, hx, supNorm_le_of_isSmall hS hyS (hbS (mem_blockSet_blk j x))⟩

theorem nat_near_aux {n P a b : ℕ} (hP : 0 < P) (hPn : P ∣ n) (ha : a < n)
    (h : (b ≤ a ∧ a ≤ b + P) ∨ b + n ≤ a + P) :
    ∃ a' b', a' < n ∧ b' < n ∧ a' / P = a / P ∧ b' / P = b / P ∧
      (a' = b' ∨ a' = b' + 1 ∨ (b' = 0 ∧ a' = n - 1)) := by
  obtain ⟨k, rfl⟩ := hPn
  have hda := Nat.div_add_mod a P
  have hdb := Nat.div_add_mod b P
  have hma := Nat.mod_lt a hP
  have hmb := Nat.mod_lt b hP
  rcases h with ⟨h1, h2⟩ | h3
  · by_cases hq : a / P = b / P
    · exact ⟨a, a, ha, ha, rfl, hq, Or.inl rfl⟩
    · have hle : b / P ≤ a / P := Nat.div_le_div_right h1
      have hle2 : a / P ≤ b / P + 1 := by
        have : a / P ≤ (b + P) / P := Nat.div_le_div_right h2
        rwa [Nat.add_div_right b hP] at this
      have hq' : a / P = b / P + 1 := by omega
      have e1 : P * (a / P) = P * (b / P) + P := by rw [hq']; ring
      have e2 : (b / P) * P = P * (b / P) := Nat.mul_comm _ _
      have e3 : (b / P + 1) * P = P * (b / P) + P := by ring
      refine ⟨P * (a / P), P * (a / P) - 1, by omega, by omega, ?_, ?_, Or.inr (Or.inl ?_)⟩
      · rw [Nat.mul_div_cancel_left _ hP]
      · refine Nat.div_eq_of_lt_le ?_ ?_
        · rw [e2]; omega
        · rw [e3]; omega
      · omega
  · have hk : k ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have e1 : P * (m + 1) = P * m + P := by ring
    have e2 : m * P = P * m := Nat.mul_comm _ _
    have e3 : (m + 1) * P = P * m + P := by ring
    rw [Nat.succ_eq_add_one] at *
    have hb0 : b / P = 0 := Nat.div_eq_of_lt (by omega)
    have ham : a / P = m := Nat.div_eq_of_lt_le (by rw [e2]; omega) (by rw [e3]; omega)
    refine ⟨P * (m + 1) - 1, 0, by omega, by omega, ?_, by rw [Nat.zero_div, hb0], ?_⟩
    · rw [ham]
      exact Nat.div_eq_of_lt_le (by rw [e2]; omega) (by rw [e3]; omega)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem zabs_natCast_sub_le {n a' b' : ℕ} [NeZero n]
    (h : a' = b' ∨ a' = b' + 1 ∨ (b' = 0 ∧ a' = n - 1)) :
    zabs ((a' : ZMod n) - (b' : ZMod n)) ≤ 1 := by
  rcases h with rfl | rfl | ⟨rfl, rfl⟩
  · rw [sub_self]; simp [zabs]
  · rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_left]; exact zabs_one_le
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
    rw [Nat.cast_sub hn, ZMod.natCast_self, Nat.cast_zero, Nat.cast_one, sub_zero, zero_sub,
      zabs_neg]
    exact zabs_one_le

theorem zmod_near {n P : ℕ} [NeZero n] (hP : 0 < P) (hPn : P ∣ n) (u v : ZMod n)
    (h : zabs (u - v) ≤ P) :
    ∃ u' v' : ZMod n, u'.val / P = u.val / P ∧ v'.val / P = v.val / P ∧ zabs (u' - v') ≤ 1 := by
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  rcases zabs_sub_le h with h1 | h2 | h3 | h4
  · obtain ⟨a', b', ha', hb', e1, e2, e3⟩ := nat_near_aux hP hPn hu (Or.inl h1)
    exact ⟨a', b', by rw [ZMod.val_cast_of_lt ha', e1], by rw [ZMod.val_cast_of_lt hb', e2],
      zabs_natCast_sub_le e3⟩
  · obtain ⟨a', b', ha', hb', e1, e2, e3⟩ := nat_near_aux hP hPn hv (Or.inl h2)
    refine ⟨b', a', by rw [ZMod.val_cast_of_lt hb', e2], by rw [ZMod.val_cast_of_lt ha', e1], ?_⟩
    rw [← neg_sub, zabs_neg]
    exact zabs_natCast_sub_le e3
  · obtain ⟨a', b', ha', hb', e1, e2, e3⟩ := nat_near_aux hP hPn hu (Or.inr h3)
    exact ⟨a', b', by rw [ZMod.val_cast_of_lt ha', e1], by rw [ZMod.val_cast_of_lt hb', e2],
      zabs_natCast_sub_le e3⟩
  · obtain ⟨a', b', ha', hb', e1, e2, e3⟩ := nat_near_aux hP hPn hv (Or.inr h4)
    refine ⟨b', a', by rw [ZMod.val_cast_of_lt hb', e2], by rw [ZMod.val_cast_of_lt ha', e1], ?_⟩
    rw [← neg_sub, zabs_neg]
    exact zabs_natCast_sub_le e3

/-- Non-touching `j`-polymers are at sup-distance `> L^j`. -/
theorem lt_supNorm_of_not_touch {j : ℕ} (hj : j ≤ N) {U₁ U₂ : Finset (Lam d L N)}
    (hU₁ : IsPolymer j U₁) (hU₂ : IsPolymer j U₂) (h : ¬ Touch U₁ U₂) {x y : Lam d L N}
    (hx : x ∈ U₁) (hy : y ∈ U₂) : L ^ j < supNorm (x - y) := by
  by_contra hc
  push Not at hc
  have hP : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hPn : L ^ j ∣ L ^ N := pow_dvd_pow L hj
  have key : ∀ i, ∃ u' v' : ZMod (L ^ N), u'.val / L ^ j = (co x i).val / L ^ j ∧
      v'.val / L ^ j = (co y i).val / L ^ j ∧ zabs (u' - v') ≤ 1 :=
    fun i => zmod_near hP hPn _ _ ((supNorm_le_iff _ _).1 hc i)
  choose u v hu hv huv using key
  refine h ⟨(show Lam d L N from u), hU₁ x _ ?_ hx, (show Lam d L N from v), hU₂ y _ ?_ hy, ?_⟩
  · funext i; exact (hu i).symm
  · funext i; exact (hv i).symm
  · rw [supNorm_le_iff]
    exact huv

/-- For non-touching `(j+1)`-polymers, `U_1^□` and `U_2^□` are at distance `> L^{j+1}/2`. -/
theorem lt_two_mul_supNorm_of_nbhd (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) {x y : Lam d L N} (hx : x ∈ nbhd j U₁) (hy : y ∈ nbhd j U₂) :
    L ^ (j + 1) < 2 * supNorm (x - y) := by
  obtain ⟨x₁, hx₁, h1⟩ := exists_near_of_mem_nbhd hx
  obtain ⟨y₁, hy₁, h2⟩ := exists_near_of_mem_nbhd hy
  have h3 := lt_supNorm_of_not_touch hj hU₁ hU₂ h hx₁ hy₁
  have e : x₁ - y₁ = (x₁ - x) + ((x - y) + (y - y₁)) := by abel
  have h4 := supNorm_add_le (x₁ - x) ((x - y) + (y - y₁))
  have h5 := supNorm_add_le (x - y) (y - y₁)
  rw [supNorm_sub_comm] at h1
  have h6 : 4 * (2 ^ d * L ^ j) ≤ L ^ (j + 1) := by
    calc 4 * (2 ^ d * L ^ j) = 2 ^ (d + 2) * L ^ j := by ring
      _ ≤ L * L ^ j := Nat.mul_le_mul_right _ hL
      _ = L ^ (j + 1) := by ring
  rw [e] at h3
  omega

/-- `2 |x|_∞ ≤ L^N` on the torus. -/
theorem two_mul_supNorm_le (x : Lam d L N) : 2 * supNorm x ≤ L ^ N := by
  unfold supNorm
  have : ∀ i ∈ (univ : Finset (Fin d)), 2 * zabs ((x : Fin d → ZMod (L ^ N)) i) ≤ L ^ N := by
    intro i _
    unfold zabs
    have := ZMod.val_lt ((x : Fin d → ZMod (L ^ N)) i)
    omega
  rcases (univ : Finset (Fin d)).eq_empty_or_nonempty with h | h
  · simp [h]
  · obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ h
      (fun i => zabs ((x : Fin d → ZMod (L ^ N)) i))
    rw [he]; exact this i hi

theorem C_eq_zero_of_nbhd (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N) {ℓ₀ : ℝ}
    {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) {x y : Lam d L N} (hx : x ∈ nbhd j U₁) (hy : y ∈ nbhd j U₂) :
    x ≠ y ∧ C x y = 0 ∧ C y x = 0 := by
  have h1 := lt_two_mul_supNorm_of_nbhd hL hj hU₁ hU₂ h hx hy
  have h2 := lt_two_mul_supNorm_of_nbhd hL hj hU₂ hU₁ (fun t => h (touch_symm t)) hy hx
  have hjN : j + 1 < N := by
    rcases hj.lt_or_eq with hj' | hj'
    · exact hj'
    · exfalso
      have := two_mul_supNorm_le (x - y)
      rw [hj'] at h1
      omega
  refine ⟨?_, hC.range hjN x y ?_, hC.range hjN y x ?_⟩
  · rintro rfl
    rw [sub_self, supNorm_zero] at h1
    omega
  · have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (supNorm (x - y) : ℝ) := by exact_mod_cast h1.le
    push_cast at this
    linarith
  · have : ((L ^ (j + 1) : ℕ) : ℝ) ≤ 2 * (supNorm (y - x) : ℝ) := by exact_mod_cast h2.le
    push_cast at this
    linarith

/-! ### Factorisation of `𝔼_C` on the doubled algebra -/

theorem expL_mul_of_disjoint {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℝ)
    {X₁ X₂ : Set Λ} (hX : Disjoint X₁ X₂) (hC : ∀ x ∈ X₁, ∀ y ∈ X₂, C x y = 0 ∧ C y x = 0)
    {F₁ F₂ : Grassmann.N Λ} (hF₁ : F₁ ∈ NX X₁) (hF₂ : F₂ ∈ NX X₂) :
    expL C (F₁ * F₂) = expL C F₁ * expL C F₂ := by
  set C₁ := restr C X₁
  set C₂ := restr C X₂
  have hsub : ∀ G ∈ NX (X₁ ∪ X₂), expL C G = expL (C₁ + C₂) G := by
    intro G hG
    have hk : ∀ k, (Lop C ^ k) G = (Lop (C₁ + C₂) ^ k) G := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
        exact Lop_eq_add_restr C hX hC (Lop_pow_mem_NX _ hG k)
    rw [expL_apply_eq_sum, expL_apply_eq_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [LinearMap.smul_apply, hk]
  have hsplit : ∀ G, expL (C₁ + C₂) G = expL C₁ (expL C₂ G) := by
    intro G
    unfold expL
    rw [Lop_add, IsNilpotent.exp_add_of_commute (Lop_commute _ _) (Lop_isNilpotent _)
      (Lop_isNilpotent _)]
    rfl
  have hsplit' : ∀ G, expL (C₁ + C₂) G = expL C₂ (expL C₁ G) := by
    intro G
    unfold expL
    rw [Lop_add, add_comm, IsNilpotent.exp_add_of_commute (Lop_commute _ _) (Lop_isNilpotent _)
      (Lop_isNilpotent _)]
    rfl
  have h12 : F₁ * F₂ ∈ NX (X₁ ∪ X₂) :=
    mul_mem (NX_mono Set.subset_union_left hF₁) (NX_mono Set.subset_union_right hF₂)
  rw [hsub _ h12, hsub _ (NX_mono Set.subset_union_left hF₁),
    hsub _ (NX_mono Set.subset_union_right hF₂), hsplit, hsplit, hsplit',
    expL_mul_left C₂ F₁ (Lop_restr_mul_left C hX hF₁),
    expL_eq_self C₂ (Lop_restr_eq_zero C hX hF₁),
    expL_eq_self C₁ (Lop_restr_eq_zero C hX.symm hF₂),
    expL_mul_right C₁ _ (Lop_restr_mul_right C hX (expL_mem_NX C₂ hF₂))]

/-- **Factorisation of `𝔼_C`**: `𝔼_C (F_1 F_2) = 𝔼_C F_1 𝔼_C F_2` for `F_i ∈ 𝒩(X_i ⊔ X_i)`
when `X_1`, `X_2` are disjoint and `C` vanishes between them. -/
theorem EC_mul_of_sep {C : Matrix (Lam d L N) (Lam d L N) ℝ} {X₁ X₂ : Set (Lam d L N)}
    (hX : ∀ x ∈ X₁, ∀ y ∈ X₂, x ≠ y ∧ C x y = 0 ∧ C y x = 0) {F₁ F₂ : Alg2 d L N}
    (hF₁ : F₁ ∈ NX2 X₁) (hF₂ : F₂ ∈ NX2 X₂) : EC C (F₁ * F₂) = EC C F₁ * EC C F₂ := by
  rw [EC_eq, EC_eq, EC_eq, ← map_mul]
  congr 1
  refine expL_mul_of_disjoint _ ?_ ?_ hF₁ hF₂
  · rw [Set.disjoint_left]
    rintro a (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · exact (hX x hx y hy).1 (Sum.inl_injective hxy).symm
    · exact Sum.inr_ne_inl hxy
    · exact Sum.inl_ne_inr hxy
    · exact (hX x hx y hy).1 (Sum.inr_injective hxy).symm
  · rintro a (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) b (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) <;>
      simp [liftζ, (hX x hx y hy).2.1, (hX x hx y hy).2.2]

theorem ECE_mul_of_sep {C : Matrix (Lam d L N) (Lam d L N) ℝ} {X₁ X₂ : Set (Lam d L N)}
    (hX : ∀ x ∈ X₁, ∀ y ∈ X₂, x ≠ y ∧ C x y = 0 ∧ C y x = 0)
    {F₁ F₂ : EvR (Lam d L N ⊕ Lam d L N)}
    (hF₁ : (F₁ : Alg2 d L N) ∈ NX2 X₁) (hF₂ : (F₂ : Alg2 d L N) ∈ NX2 X₂) :
    ECE C (F₁ * F₂) = ECE C F₁ * ECE C F₂ :=
  Subtype.ext (EC_mul_of_sep hX hF₁ hF₂)

/-! ### The membership principle -/

/-- The preimage of a subalgebra in the even subalgebra. -/
abbrev SE {Λ : Type*} (S : Subalgebra ℂ (Grassmann.N Λ)) : Subalgebra ℂ (EvR Λ) :=
  S.comap (Ev Λ).val

theorem mem_SE {Λ : Type*} {S : Subalgebra ℂ (Grassmann.N Λ)} {x : EvR Λ} :
    x ∈ SE S ↔ (x : Grassmann.N Λ) ∈ S := Iff.rfl

theorem gexp_mem_SE {Λ : Type*} [DecidableEq Λ] {S : Subalgebra ℂ (Grassmann.N Λ)} {x : EvR Λ}
    (hx : x ∈ SE S) : gexp x ∈ SE S := by
  rw [gexp, IsNilpotent.exp]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  have : ((i.factorial : ℚ)⁻¹ • x ^ i : EvR Λ) =
      (algebraMap ℚ ℂ (i.factorial : ℚ)⁻¹) • x ^ i := rfl
  have h2 := Subalgebra.smul_mem (SE S) (pow_mem hx i) (algebraMap ℚ ℂ (i.factorial : ℚ)⁻¹)
  convert h2 using 1

theorem mem_smallSets {j : ℕ} {X : Finset (Lam d L N)} : X ∈ smallSets j ↔ IsSmall j X := by
  simp [smallSets]

/-- The hypotheses of the membership principle for `K_{j+1}(U)`. -/
structure MemHyp (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (U : Finset (Lam d L N)) (S : Subalgebra ℂ (Alg d L N)) (S2 : Subalgebra ℂ (Alg2 d L N)) :
    Prop where
  hθ : ∀ F ∈ S, theta F ∈ S2
  hι : ∀ F ∈ S, incl F ∈ S2
  hK : ∀ Y, IsConn j Y → Y ⊆ U → (K Y : Alg d L N) ∈ S
  hJ : ∀ (b : Fin d → ℕ) (Y : Finset (Lam d L N)), j + 1 < N → blockSet j b ⊆ U →
    IsSmall j Y → blockSet j b ⊆ Y → LocXY Y (blockSet j b) (K Y) ∈ S
  hV : ∀ b : Fin d → ℕ, blockSet j b ⊆ U → V.eval (blockSet (L := L) (N := N) j b) ∈ S
  hV' : ∀ b : Fin d → ℕ, blockSet j b ⊆ U →
    (uVnext j C V K).2.eval (blockSet (L := L) (N := N) j b) ∈ S

/-- The index type of `𝒢(U)`. -/
abbrev GT (d L N : ℕ) [NeZero L] :=
  Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)

theorem mem_Gset' {j : ℕ} {U : Finset (Lam d L N)} {g : GT d L N} :
    g ∈ Gset j U ↔ IsPolymer j g.2 ∧ g.1 ⊆ pairsU j ∧
      (∀ p ∈ g.1, ∀ q ∈ g.1, p.2 = q.2 → p = q) ∧
      (∀ p ∈ g.1, ∀ q ∈ g.1, p.2 ≠ q.2 → ¬ Touch p.2 q.2) ∧
      ¬ Touch (Xcal g.1) g.2 ∧ clo j (g.2 ∪ Bbox j g.1) = U := mem_Gset

/-- Facts about the elements of `𝒢(U)`. -/
theorem Gset_facts {j : ℕ} {U : Finset (Lam d L N)}
    {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)} (hg : g ∈ Gset j U) :
    IsPolymer j g.2 ∧ g.2 ⊆ U ∧ Xcal g.1 ⊆ U ∧ ∀ p ∈ g.1, p ∈ pairsU j ∧
      nbhd j (blockSet j p.1) ⊆ U ∧ blockSet j p.1 ⊆ U ∧ p.2 ⊆ U := by
  have hg' := mem_Gset'.1 hg
  have h1 := hg'.1
  have h2 := hg'.2.1
  have h6 : clo j (g.2 ∪ Bbox j g.1) = U := hg'.2.2.2.2.2
  have hB : ∀ p ∈ g.1, nbhd j (blockSet j p.1) ⊆ U := fun p hp => by
    have e1 : nbhd j (blockSet j p.1) ⊆ Bbox j g.1 := by
      intro z hz
      exact mem_biUnion.2 ⟨p, hp, hz⟩
    have e2 : Bbox j g.1 ⊆ clo j (g.2 ∪ Bbox j g.1) := subset_union_right.trans (subset_clo j _)
    rw [← h6]; exact e1.trans e2
  have hp2 : ∀ p ∈ g.1, p.2 ⊆ nbhd j (blockSet j p.1) := fun p hp => by
    obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 (h2 hp)
    exact subset_nbhd_of_small hs hbs (mem_blockIdx.1 hb)
  refine ⟨h1, ?_, ?_, fun p hp => ⟨h2 hp, hB p hp,
    (subset_nbhd (isPolymer_blockSet j p.1)).trans (hB p hp), (hp2 p hp).trans (hB p hp)⟩⟩
  · rw [← h6]; exact subset_union_left.trans (subset_clo j _)
  · exact biUnion_subset.2 fun p hp => (hp2 p hp).trans (hB p hp)

section Mem

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K : Act d L N}
  {U : Finset (Lam d L N)} {S : Subalgebra ℂ (Alg d L N)} {S2 : Subalgebra ℂ (Alg2 d L N)}

theorem MemHyp.thetaE' (h : MemHyp j C V K U S S2) {x : EvR (Lam d L N)} (hx : x ∈ SE S) :
    thetaE x ∈ SE S2 := h.hθ _ hx

theorem MemHyp.inclE' (h : MemHyp j C V K U S S2) {x : EvR (Lam d L N)} (hx : x ∈ SE S) :
    inclE x ∈ SE S2 := h.hι _ hx

theorem MemHyp.Jb_mem (h : MemHyp j C V K U S S2) {b : Fin d → ℕ} (hb : blockSet j b ⊆ U)
    (X : Finset (Lam d L N)) : Jb j K b X ∈ SE S := by
  unfold Jb
  split_ifs with h1 h2
  · refine neg_mem (Subalgebra.sum_mem _ fun Y hY => ?_)
    obtain ⟨hY1, hY2, -⟩ := mem_filter.1 hY
    exact h.hJ b Y h1.1 hb (mem_smallSets.1 hY1) hY2
  · exact h.hJ b X h1.1 hb h1.2.1 h1.2.2
  · exact zero_mem _

theorem MemHyp.Kext_mem (h : MemHyp j C V K U S S2) {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    (hWU : W ⊆ U) : Kext j K W ∈ SE S :=
  prod_mem fun Y hY => h.hK Y (isConn_of_mem_comp hW hY) ((subset_of_mem_comp hY).trans hWU)

theorem MemHyp.Inext_mem (h : MemHyp j C V K U S S2) {b : Fin d → ℕ} (hb : blockSet j b ⊆ U) :
    Inext j C V K b ∈ SE S :=
  Subalgebra.smul_mem _ (gexp_mem_SE (neg_mem (h.hV' b hb))) _

theorem MemHyp.InextPow_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : X ⊆ U) : InextPow j C V K X ∈ SE S :=
  prod_mem fun b hb => h.Inext_mem (blockSet_subset hU (blocks_mono hX hb))

theorem MemHyp.dI_mem (h : MemHyp j C V K U S S2) {b : Fin d → ℕ} (hb : blockSet j b ⊆ U) :
    dI j C V K b ∈ SE S2 :=
  sub_mem (h.thetaE' (gexp_mem_SE (neg_mem (h.hV b hb)))) (h.inclE' (h.Inext_mem hb))

theorem MemHyp.dIPow_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : X ⊆ U) : dIPow j C V K X ∈ SE S2 :=
  prod_mem fun b hb => h.dI_mem (blockSet_subset hU (blocks_mono hX hb))

theorem MemHyp.Ktil_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer j U)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) : Ktil j C V K W ∈ SE S2 :=
  Subalgebra.sum_mem _ fun Y hY => mul_mem
    (h.thetaE' (h.Kext_mem (IsPolymer.sdiff hW (mem_Pj.1 hY).2) (sdiff_subset.trans hWU)))
    (h.dIPow_mem hU ((mem_Pj.1 hY).1.trans hWU))

theorem MemHyp.KchkC_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer j U)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) (hWU : W ⊆ U) : KchkC j C V K W ∈ SE S2 :=
  sub_mem (h.Ktil_mem hU hW hWU) (Subalgebra.sum_mem _ fun b hb =>
    h.thetaE' (h.Jb_mem (blockSet_subset hU (blocks_mono hWU hb)) W))

theorem MemHyp.Kchk_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer j U)
    {X : Finset (Lam d L N)} (hX : IsPolymer j X) (hXU : X ⊆ U) : Kchk j C V K X ∈ SE S2 :=
  prod_mem fun W hW => h.KchkC_mem hU (isPolymer_of_mem_comp hX hW)
    ((subset_of_mem_comp hW).trans hXU)

theorem MemHyp.inner_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer j U)
    {g : Finset ((Fin d → ℕ) × Finset (Lam d L N)) × Finset (Lam d L N)}
    (h2 : IsPolymer j g.2) (h2U : g.2 ⊆ U) (h1 : ∀ p ∈ g.1, blockSet j p.1 ⊆ U) :
    Kchk j C V K g.2 * ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2) ∈ SE S2 :=
  mul_mem (h.Kchk_mem hU h2 h2U) (prod_mem fun p hp => h.thetaE' (h.Jb_mem (h1 p hp) p.2))

/-- **The membership principle**: `K_{j+1}(U) ∈ S`. -/
theorem MemHyp.Knext_mem (h : MemHyp j C V K U S S2) (hU : IsPolymer (j + 1) U)
    (hE : ∀ F ∈ S2, EC C F ∈ S) : Knext j C V K U ∈ SE S := by
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun g hg => ?_) _
  obtain ⟨h1, h2, -, h4⟩ := Gset_facts hg
  exact mul_mem (h.InextPow_mem (IsPolymer.of_succ hU) sdiff_subset)
    (hE _ (h.inner_mem (IsPolymer.of_succ hU) h1 h2 fun p hp => (h4 p hp).2.2.1))

/-- Locality: the building blocks of `K_{j+1}(U)` lie in `𝒩(U^□)` (scale `j`). -/
theorem memHyp_loc (hd : 1 ≤ d) (hK : InK j K) :
    MemHyp j C V K U (NX (nbhd j U : Set (Lam d L N))) (NX2 (nbhd j U : Set (Lam d L N))) where
  hθ _ hF := theta_mem_NX2 hF
  hι _ hF := incl_mem_NX2 hF
  hK Y hY hYU := NX_mono (coe_subset.2 (nbhd_mono hYU)) (hK.loc Y hY)
  hJ b Y _ hb _ _ := NX_mono (coe_subset.2 (nbhd_mono hb)) (LocXY_mem hd (isPolymer_blockSet j b) Y _)
  hV b hb := NX_mono (coe_subset.2 (nbhd_mono hb)) (eval_mem_NX hd (isPolymer_blockSet j b) V)
  hV' b hb := NX_mono (coe_subset.2 (nbhd_mono hb)) (eval_mem_NX hd (isPolymer_blockSet j b) _)

/-- `U(1)` invariance of the building blocks. -/
theorem memHyp_sym (hK : InK j K) :
    MemHyp j C V K U (SymS (Lam d L N)) (SymS (Lam d L N ⊕ Lam d L N)) where
  hθ F hF := mem_SymS.2 (by rw [← theta_scal, mem_SymS.1 hF])
  hι F hF := mem_SymS.2 (by rw [← incl_scal, mem_SymS.1 hF])
  hK Y hY _ := (isSym_iff_mem_SymS _).1 (hK.sym Y hY)
  hJ _ _ _ _ _ _ := (isSym_iff_mem_SymS _).1 (isSym_LocXY _ _ _)
  hV _ _ := (isSym_iff_mem_SymS _).1 (isSym_eval _ _)
  hV' _ _ := (isSym_iff_mem_SymS _).1 (isSym_eval _ _)

theorem EC_mem_SymS {F : Alg2 d L N} (hF : F ∈ SymS (Lam d L N ⊕ Lam d L N)) :
    EC C F ∈ SymS (Lam d L N) :=
  mem_SymS.2 (by rw [← EC_scal C two_ne_zero, mem_SymS.1 hF])

/-- `J` invariance of the building blocks. -/
theorem memHyp_jinv (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hK : InK j K) :
    MemHyp j C V K U (AlgHom.equalizer Jsym (AlgHom.id ℂ (Alg d L N)))
      (AlgHom.equalizer Jsym2 (AlgHom.id ℂ (Alg2 d L N))) where
  hθ F hF := by
    rw [AlgHom.mem_equalizer] at hF ⊢
    rw [AlgHom.id_apply, ← theta_Jsym, hF, AlgHom.id_apply]
  hι F hF := by
    rw [AlgHom.mem_equalizer] at hF ⊢
    rw [AlgHom.id_apply, ← incl_Jsym, hF, AlgHom.id_apply]
  hK Y hY _ := by rw [AlgHom.mem_equalizer, AlgHom.id_apply]; exact hK.jinv Y hY
  hJ b Y hj _ hY _ := by
    rw [AlgHom.mem_equalizer, AlgHom.id_apply]
    exact Jsym_LocXY_of_patch (patch_small hd hL hj hY) hY.2.1.1 _ (hK.jinv Y ⟨hY.1, hY.2.1⟩)
  hV _ _ := by rw [AlgHom.mem_equalizer, AlgHom.id_apply]; exact Jsym_eval _ _
  hV' _ _ := by rw [AlgHom.mem_equalizer, AlgHom.id_apply]; exact Jsym_eval _ _

theorem EC_mem_equalizer (hCs : ∀ x y, C x y = C y x) {F : Alg2 d L N}
    (hF : F ∈ AlgHom.equalizer Jsym2 (AlgHom.id ℂ (Alg2 d L N))) :
    EC C F ∈ AlgHom.equalizer Jsym (AlgHom.id ℂ (Alg d L N)) := by
  rw [AlgHom.mem_equalizer] at hF ⊢
  rw [AlgHom.id_apply, ← EC_Jsym2 hCs, hF, AlgHom.id_apply]

end Mem

/-! ### Factorisation over non-touching polymers -/

/-- The summand of `K_{j+1}(U)`. -/
def Kterm (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    (U : Finset (Lam d L N)) (g : GT d L N) : EvR (Lam d L N) :=
  InextPow j C V K (U \ (g.2 ∪ Xcal g.1)) *
    ECE C (Kchk j C V K g.2 * ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2))

theorem Knext_eq_Kterm (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup)
    (K : Act d L N) (U : Finset (Lam d L N)) :
    Knext j C V K U = Complex.exp ((uVnext j C V K).1 * U.card) •
      ∑ g ∈ Gset j U, Kterm j C V K U g := rfl

theorem ECE_one (C : Matrix (Lam d L N) (Lam d L N) ℝ) :
    ECE C (1 : EvR (Lam d L N ⊕ Lam d L N)) = 1 :=
  Subtype.ext (EC_one C)

theorem Gset_empty (j : ℕ) : Gset j (∅ : Finset (Lam d L N)) = {(∅, ∅)} := by
  ext g
  rw [mem_singleton]
  constructor
  · intro hg
    obtain ⟨-, f2, -, f4⟩ := Gset_facts hg
    refine Prod.ext ?_ (subset_empty.1 f2)
    refine eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨hb, -, -⟩ := mem_pairsU.1 (f4 p hp).1
    obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
    exact notMem_empty x ((f4 p hp).2.2.1 hx)
  · rintro rfl
    exact mem_Gset_empty.2 ⟨isPolymer_empty j, clo_empty j⟩

theorem Knext_empty' (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup)
    (K : Act d L N) : Knext j C V K ∅ = 1 := by
  rw [Knext_eq_Kterm, Gset_empty, sum_singleton, Kterm]
  simp only [card_empty, Nat.cast_zero, mul_zero, Complex.exp_zero, one_smul, Xcal_empty,
    empty_union, empty_sdiff, Kchk_empty, prod_empty, mul_one, ECE_one]
  simp [InextPow, blocks]

theorem eq_left_of_union_eq {α : Type*} [DecidableEq α] {A B U₁ U₂ : Finset α} (hA : A ⊆ U₁)
    (hB : B ⊆ U₂) (hU : Disjoint U₁ U₂) (h : A ∪ B = U₁ ∪ U₂) : A = U₁ := by
  refine Subset.antisymm hA fun x hx => ?_
  have : x ∈ A ∪ B := h ▸ mem_union_left _ hx
  rcases mem_union.1 this with h1 | h1
  · exact h1
  · exact absurd (hB h1) (Finset.disjoint_left.1 hU hx)

/-- `B^□` lies on the side of `B` for non-touching `(j+1)`-polymers. -/
theorem nbhd_subset_side (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
    {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
    (h : ¬ Touch U₁ U₂) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hsub : nbhd j (blockSet j b) ⊆ U₁ ∪ U₂) {x : Lam d L N} (hx : x ∈ blockSet j b)
    (hx₁ : x ∈ U₁) : nbhd j (blockSet j b) ⊆ U₁ := by
  have hs := isSmall_clo_nbhd hd hL hj b hb
  have hXU : clo j (nbhd j (blockSet j b)) ⊆ U₁ ∪ U₂ := clo_subset (IsPolymer.union hU₁ hU₂) hsub
  exact (subset_clo j _).trans (subset_of_conn_aux ⟨hs.1, hs.2.1⟩ hU₁ hU₂ h hXU
    (subset_clo j _ (subset_nbhd (isPolymer_blockSet j b) hx)) hx₁)

/-- Joining elements of `𝒢(U_1)` and `𝒢(U_2)`. -/
def gjoin (x : GT d L N × GT d L N) : GT d L N := (x.1.1 ∪ x.2.1, x.1.2 ∪ x.2.2)

/-- Splitting an element of `𝒢(U_1 ∪ U_2)`. -/
def gsplit (j : ℕ) (U₁ U₂ : Finset (Lam d L N)) (g : GT d L N) : GT d L N × GT d L N :=
  ((g.1.filter (fun p => blockSet j p.1 ⊆ U₁), g.2 ∩ U₁),
    (g.1.filter (fun p => ¬ blockSet j p.1 ⊆ U₁), g.2 ∩ U₂))

theorem Xcal_union (s t : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    Xcal (s ∪ t) = Xcal s ∪ Xcal t := union_biUnion

theorem Bbox_union (j : ℕ) (s t : Finset ((Fin d → ℕ) × Finset (Lam d L N))) :
    Bbox j (s ∪ t) = Bbox j s ∪ Bbox j t := union_biUnion

theorem Xcal_mono {s t : Finset ((Fin d → ℕ) × Finset (Lam d L N))} (h : s ⊆ t) :
    Xcal s ⊆ Xcal t := biUnion_subset_biUnion_of_subset_left _ h

theorem nonempty_of_mem_pairsU {j : ℕ} {p : (Fin d → ℕ) × Finset (Lam d L N)}
    (hp : p ∈ pairsU j) : (blockSet (L := L) (N := N) j p.1).Nonempty :=
  mem_blockIdx.1 (mem_pairsU.1 hp).1

section Union

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 2) ≤ L) {j : ℕ} (hj : j + 1 ≤ N)
  {U₁ U₂ : Finset (Lam d L N)} (hU₁ : IsPolymer (j + 1) U₁) (hU₂ : IsPolymer (j + 1) U₂)
  (h : ¬ Touch U₁ U₂)
include hd hL hj hU₁ hU₂ h

theorem gsplit_mem {g : GT d L N} (hg : g ∈ Gset j (U₁ ∪ U₂)) :
    (gsplit j U₁ U₂ g).1 ∈ Gset j U₁ ∧ (gsplit j U₁ U₂ g).2 ∈ Gset j U₂ := by
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ := mem_Gset'.1 hg
  obtain ⟨-, f2, -, f4⟩ := Gset_facts hg
  have hD := disjoint_of_not_touch h
  have side1 : ∀ p ∈ g.1, blockSet j p.1 ⊆ U₁ → nbhd j (blockSet j p.1) ⊆ U₁ := by
    intro p hp hs
    have hb := (mem_pairsU.1 (f4 p hp).1).1
    obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
    exact nbhd_subset_side hd hL hj hU₁ hU₂ h hb (f4 p hp).2.1 hx (hs hx)
  have side2 : ∀ p ∈ g.1, ¬ blockSet j p.1 ⊆ U₁ → nbhd j (blockSet j p.1) ⊆ U₂ := by
    intro p hp hs
    have hb := (mem_pairsU.1 (f4 p hp).1).1
    obtain ⟨x, hx, hx1⟩ := not_subset.1 hs
    have hx2 : x ∈ U₂ := (mem_union.1 ((f4 p hp).2.2.1 hx)).resolve_left hx1
    exact nbhd_subset_side hd hL hj hU₂ hU₁ (fun t => h (touch_symm t)) hb
      (by rw [union_comm]; exact (f4 p hp).2.1) hx hx2
  set A₁ := g.2 ∩ U₁ ∪ Bbox j (g.1.filter (fun p => blockSet j p.1 ⊆ U₁)) with hA₁
  set A₂ := g.2 ∩ U₂ ∪ Bbox j (g.1.filter (fun p => ¬ blockSet j p.1 ⊆ U₁)) with hA₂
  have hA₁U : A₁ ⊆ U₁ := union_subset inter_subset_right (biUnion_subset.2 fun p hp =>
    side1 p (mem_filter.1 hp).1 (mem_filter.1 hp).2)
  have hA₂U : A₂ ⊆ U₂ := union_subset inter_subset_right (biUnion_subset.2 fun p hp =>
    side2 p (mem_filter.1 hp).1 (mem_filter.1 hp).2)
  have hA : A₁ ∪ A₂ = g.2 ∪ Bbox j g.1 := by
    rw [hA₁, hA₂, union_union_union_comm, ← inter_union_distrib_left, inter_eq_left.2 f2,
      ← Bbox_union, filter_union_filter_not_eq]
  have hc : clo j A₁ ∪ clo j A₂ = U₁ ∪ U₂ := by rw [← clo_union, hA, hg6]
  have e₁ : clo j A₁ = U₁ := eq_left_of_union_eq (clo_subset hU₁ hA₁U) (clo_subset hU₂ hA₂U) hD hc
  have e₂ : clo j A₂ = U₂ := eq_left_of_union_eq (clo_subset hU₂ hA₂U) (clo_subset hU₁ hA₁U)
    hD.symm (by rw [union_comm, hc, union_comm])
  refine ⟨mem_Gset'.2 ⟨IsPolymer.inter hg1 (IsPolymer.of_succ hU₁),
    (filter_subset _ _).trans hg2,
    fun p hp q hq => hg3 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    fun p hp q hq => hg4 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    not_touch_mono hg5 (Xcal_mono (filter_subset _ _)) inter_subset_left, e₁⟩,
    mem_Gset'.2 ⟨IsPolymer.inter hg1 (IsPolymer.of_succ hU₂),
    (filter_subset _ _).trans hg2,
    fun p hp q hq => hg3 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    fun p hp q hq => hg4 p (mem_of_mem_filter _ hp) q (mem_of_mem_filter _ hq),
    not_touch_mono hg5 (Xcal_mono (filter_subset _ _)) inter_subset_left, e₂⟩⟩

omit hd hL hj in
theorem gjoin_mem {x : GT d L N × GT d L N} (h₁ : x.1 ∈ Gset j U₁) (h₂ : x.2 ∈ Gset j U₂) :
    gjoin x ∈ Gset j (U₁ ∪ U₂) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := mem_Gset'.1 h₁
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := mem_Gset'.1 h₂
  obtain ⟨-, fa2, fa3, fa4⟩ := Gset_facts h₁
  obtain ⟨-, fb2, fb3, fb4⟩ := Gset_facts h₂
  have hD := disjoint_of_not_touch h
  have cross : ∀ p ∈ x.1.1, ∀ q ∈ x.2.1, p.2 ≠ q.2 ∧ ¬ Touch p.2 q.2 ∧ ¬ Touch q.2 p.2 := by
    intro p hp q hq
    refine ⟨fun e => ?_, not_touch_mono h (fa4 p hp).2.2.2 (fb4 q hq).2.2.2,
      not_touch_mono (fun t => h (touch_symm t)) (fb4 q hq).2.2.2 (fa4 p hp).2.2.2⟩
    obtain ⟨z, hz⟩ := (nonempty_of_mem_pairsU (fa4 p hp).1).mono
      (mem_pairsU.1 (fa4 p hp).1).2.2
    exact Finset.disjoint_left.1 hD ((fa4 p hp).2.2.2 hz) ((fb4 q hq).2.2.2 (e ▸ hz))
  refine mem_Gset'.2 ⟨IsPolymer.union a1 b1, union_subset a2 b2, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq e
    rcases mem_union.1 hp with hp | hp <;> rcases mem_union.1 hq with hq | hq
    · exact a3 p hp q hq e
    · exact absurd e (cross p hp q hq).1
    · exact absurd e.symm (cross q hq p hp).1
    · exact b3 p hp q hq e
  · intro p hp q hq e
    rcases mem_union.1 hp with hp | hp <;> rcases mem_union.1 hq with hq | hq
    · exact a4 p hp q hq e
    · exact (cross p hp q hq).2.1
    · exact (cross q hq p hp).2.2
    · exact b4 p hp q hq e
  · rintro ⟨a, ha, c, hc, hac⟩
    simp only [gjoin] at ha hc
    rw [Xcal_union] at ha
    rcases mem_union.1 ha with ha | ha <;> rcases mem_union.1 hc with hc | hc
    · exact a5 ⟨a, ha, c, hc, hac⟩
    · exact h ⟨a, fa3 ha, c, fb2 hc, hac⟩
    · exact h ⟨c, fa2 hc, a, fb3 ha, by rwa [supNorm_sub_comm]⟩
    · exact b5 ⟨a, ha, c, hc, hac⟩
  · show clo j (x.1.2 ∪ x.2.2 ∪ Bbox j (x.1.1 ∪ x.2.1)) = U₁ ∪ U₂
    rw [Bbox_union, union_union_union_comm, clo_union, a6, b6]

omit hd hL hj in
theorem gsplit_gjoin {x : GT d L N × GT d L N} (h₁ : x.1 ∈ Gset j U₁) (h₂ : x.2 ∈ Gset j U₂) :
    gsplit j U₁ U₂ (gjoin x) = x := by
  obtain ⟨-, fa2, -, fa4⟩ := Gset_facts h₁
  obtain ⟨-, fb2, -, fb4⟩ := Gset_facts h₂
  have hD := disjoint_of_not_touch h
  have hn : ∀ q ∈ x.2.1, ¬ blockSet j q.1 ⊆ U₁ := fun q hq hs => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (fb4 q hq).1
    exact Finset.disjoint_left.1 hD (hs hz) ((fb4 q hq).2.2.1 hz)
  have e1 : (x.1.2 ∪ x.2.2) ∩ U₁ = x.1.2 := by
    rw [union_inter_distrib_right, inter_eq_left.2 fa2,
      disjoint_iff_inter_eq_empty.1 (hD.symm.mono_left fb2), union_empty]
  have e2 : (x.1.2 ∪ x.2.2) ∩ U₂ = x.2.2 := by
    rw [union_inter_distrib_right, inter_eq_left.2 fb2,
      disjoint_iff_inter_eq_empty.1 (hD.mono_left fa2), empty_union]
  simp only [gsplit, gjoin, filter_union, e1, e2]
  rw [filter_true_of_mem fun p hp => (fa4 p hp).2.2.1, filter_false_of_mem hn, union_empty,
    filter_false_of_mem fun p hp hs => hs (fa4 p hp).2.2.1,
    filter_true_of_mem hn, empty_union]

omit hd hL hj in
theorem gjoin_gsplit {g : GT d L N} (hg : g ∈ Gset j (U₁ ∪ U₂)) :
    gjoin (gsplit j U₁ U₂ g) = g := by
  obtain ⟨-, f2, -, -⟩ := Gset_facts hg
  simp only [gsplit, gjoin]
  rw [filter_union_filter_not_eq, ← inter_union_distrib_left, inter_eq_left.2 f2]

omit hd hL hj hU₁ hU₂ h in
theorem Kchk_union' {j : ℕ} (C : Matrix (Lam d L N) (Lam d L N) ℝ) (V : Vcoup) (K : Act d L N)
    {A B : Finset (Lam d L N)} (hA : IsPolymer j A) (hB : IsPolymer j B) (hAB : ¬ Touch A B) :
    Kchk j C V K (A ∪ B) = Kchk j C V K A * Kchk j C V K B := by
  rw [Kchk, comp_union hA hB hAB, prod_union (disjoint_comp hA hAB), Kchk, Kchk]

omit hd hL hj hU₁ hU₂ h in
theorem prop_aux {a b c e f g : Prop} (i1 : c → a) (i2 : f → a) (i3 : e → b) (i4 : g → b)
    (i5 : a → ¬ b) :
    ((a ∨ b) ∧ ¬((c ∨ e) ∨ f ∨ g)) ↔ ((a ∧ ¬(c ∨ f)) ∨ (b ∧ ¬(e ∨ g))) := by
  tauto

/-- The summands factorise. -/
theorem Kterm_gjoin {ℓ₀ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C)
    (V : Vcoup) {K : Act d L N} (hK : InK j K) {x : GT d L N × GT d L N}
    (h₁ : x.1 ∈ Gset j U₁) (h₂ : x.2 ∈ Gset j U₂) :
    Kterm j C V K (U₁ ∪ U₂) (gjoin x) = Kterm j C V K U₁ x.1 * Kterm j C V K U₂ x.2 := by
  obtain ⟨a1, a2, -, -, -, -⟩ := mem_Gset'.1 h₁
  obtain ⟨b1, b2, -, -, -, -⟩ := mem_Gset'.1 h₂
  obtain ⟨-, fa2, fa3, fa4⟩ := Gset_facts h₁
  obtain ⟨-, fb2, fb3, fb4⟩ := Gset_facts h₂
  have hD := disjoint_of_not_touch h
  have hP₁ := IsPolymer.of_succ hU₁
  have hP₂ := IsPolymer.of_succ hU₂
  have e1 : (U₁ ∪ U₂) \ (x.1.2 ∪ x.2.2 ∪ Xcal (x.1.1 ∪ x.2.1)) =
      (U₁ \ (x.1.2 ∪ Xcal x.1.1)) ∪ (U₂ \ (x.2.2 ∪ Xcal x.2.1)) := by
    rw [Xcal_union]
    ext z
    have i1 := @fa2 z
    have i2 := @fa3 z
    have i3 := @fb2 z
    have i4 := @fb3 z
    have i5 : z ∈ U₁ → z ∉ U₂ := fun hz => Finset.disjoint_left.1 hD hz
    simp only [mem_union, mem_sdiff]
    exact prop_aux i1 i2 i3 i4 i5
  have hI := InextPow_union j C V K
    (IsPolymer.sdiff hP₁ (IsPolymer.union a1 (isPolymer_Xcal a2)))
    (IsPolymer.sdiff hP₂ (IsPolymer.union b1 (isPolymer_Xcal b2)))
    (hD.mono sdiff_subset sdiff_subset)
  have hdisj : Disjoint x.1.1 x.2.1 := Finset.disjoint_left.2 fun p hp hq => by
    obtain ⟨z, hz⟩ := nonempty_of_mem_pairsU (fa4 p hp).1
    exact Finset.disjoint_left.1 hD ((fa4 p hp).2.2.1 hz) ((fb4 p hq).2.2.1 hz)
  have hsep : ∀ y ∈ (nbhd j U₁ : Set (Lam d L N)), ∀ z ∈ (nbhd j U₂ : Set (Lam d L N)),
      y ≠ z ∧ C y z = 0 ∧ C z y = 0 := fun y hy z hz =>
    C_eq_zero_of_nbhd hL hj hC hU₁ hU₂ h hy hz
  have hF₁ := (memHyp_loc (C := C) (V := V) (U := U₁) hd hK).inner_mem hP₁ a1 fa2
    fun p hp => (fa4 p hp).2.2.1
  have hF₂ := (memHyp_loc (C := C) (V := V) (U := U₂) hd hK).inner_mem hP₂ b1 fb2
    fun p hp => (fb4 p hp).2.2.1
  simp only [Kterm, gjoin]
  rw [e1, hI, Kchk_union' C V K a1 b1 (not_touch_mono h fa2 fb2), prod_union hdisj,
    show ∀ a b c e : EvR (Lam d L N ⊕ Lam d L N), a * b * (c * e) = (a * c) * (b * e) from
      fun a b c e => by ring,
    ECE_mul_of_sep hsep (mem_SE.1 hF₁) (mem_SE.1 hF₂)]
  ring

theorem Knext_union' {ℓ₀ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : GoodCov j ℓ₀ C)
    (V : Vcoup) {K : Act d L N} (hK : InK j K) :
    Knext j C V K (U₁ ∪ U₂) = Knext j C V K U₁ * Knext j C V K U₂ := by
  have hD := disjoint_of_not_touch h
  rw [Knext_eq_Kterm, Knext_eq_Kterm, Knext_eq_Kterm, smul_mul_smul_comm, sum_mul_sum,
    ← sum_product', card_union_of_disjoint hD, Nat.cast_add, mul_add, Complex.exp_add]
  congr 1
  symm
  refine sum_nbij' gjoin (gsplit j U₁ U₂) (fun x hx => ?_) (fun g hg => ?_) (fun x hx => ?_)
    (fun g hg => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gjoin_mem hU₁ hU₂ h h1 h2
  · exact mem_product.2 (gsplit_mem hd hL hj hU₁ hU₂ h hg)
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact gsplit_gjoin hU₁ hU₂ h h1 h2
  · exact gjoin_gsplit hU₁ hU₂ h hg
  · obtain ⟨h1, h2⟩ := mem_product.1 hx
    exact (Kterm_gjoin hd hL hj hU₁ hU₂ h hC V hK h1 h2).symm

end Union

/-! ### Locality (`prop:consistency`) -/

/-- Small sets meeting `U` lie in the scale-`(j+1)` neighbourhood `U^□`. -/
theorem subset_nbhd_succ_of_small {j : ℕ} {X U : Finset (Lam d L N)} (hX : IsSmall j X)
    {x : Lam d L N} (hxX : x ∈ X) (hxU : x ∈ U) : X ⊆ nbhd (j + 1) U := by
  intro y hy
  simp only [nbhd, mem_filter, mem_univ, true_and]
  refine ⟨clo j X, isSmall_clo hX, subset_clo j X hy, blk (j + 1) x, blk_mem_blocks hxU, ?_⟩
  intro z hz
  exact isPolymer_clo j X x z (mem_blockSet.1 hz).symm (subset_clo j X hxX)

section Local

variable {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K K' : Act d L N}

theorem Inext_congr (huV : uVnext j C V K = uVnext j C V K') (b : Fin d → ℕ) :
    Inext j C V K b = Inext j C V K' b := by
  unfold Inext; rw [huV]

theorem InextPow_congr (huV : uVnext j C V K = uVnext j C V K') (X : Finset (Lam d L N)) :
    InextPow j C V K X = InextPow j C V K' X :=
  prod_congr rfl fun b _ => Inext_congr huV b

theorem dIPow_congr (huV : uVnext j C V K = uVnext j C V K') (X : Finset (Lam d L N)) :
    dIPow j C V K X = dIPow j C V K' X :=
  prod_congr rfl fun b _ => by unfold dI; rw [Inext_congr huV]

theorem Kext_congr {W : Finset (Lam d L N)} (hW : IsPolymer j W)
    (h : ∀ Y, IsConn j Y → Y ⊆ W → K Y = K' Y) : Kext j K W = Kext j K' W :=
  prod_congr rfl fun Y hY => h Y (isConn_of_mem_comp hW hY) (subset_of_mem_comp hY)

theorem Jb_congr {b : Fin d → ℕ} (h : ∀ X, IsSmall j X → blockSet j b ⊆ X → K X = K' X)
    (X : Finset (Lam d L N)) : Jb j K b X = Jb j K' b X := by
  unfold Jb
  split_ifs with h1 h2
  · congr 1
    refine sum_congr rfl fun Y hY => ?_
    obtain ⟨hY1, hY2, -⟩ := mem_filter.1 hY
    rw [h Y (mem_smallSets.1 hY1) hY2]
  · rw [h X h1.2.1 h1.2.2]
  · rfl

theorem Kterm_congr {U : Finset (Lam d L N)} (hU : IsPolymer j U)
    (huV : uVnext j C V K = uVnext j C V K')
    (hc : ∀ Y, IsConn j Y → Y ⊆ U → K Y = K' Y)
    (hs : ∀ b, blockSet j b ⊆ U → (blockSet (L := L) (N := N) j b).Nonempty →
      ∀ X, IsSmall j X → blockSet j b ⊆ X → K X = K' X)
    {g : GT d L N} (hg : g ∈ Gset j U) : Kterm j C V K U g = Kterm j C V K' U g := by
  obtain ⟨f1, f2, -, f4⟩ := Gset_facts hg
  have hKtil : ∀ W, IsPolymer j W → W ⊆ U → Ktil j C V K W = Ktil j C V K' W := by
    intro W hW hWU
    refine sum_congr rfl fun Y hY => ?_
    rw [Kext_congr (IsPolymer.sdiff hW (mem_Pj.1 hY).2)
      (fun Z hZ hZW => hc Z hZ (hZW.trans (sdiff_subset.trans hWU))), dIPow_congr huV]
  have hJ : ∀ b, blockSet j b ⊆ U → (blockSet (L := L) (N := N) j b).Nonempty →
      ∀ X, Jb j K b X = Jb j K' b X := fun b hb hne X => Jb_congr (hs b hb hne) X
  have hKchk : Kchk j C V K g.2 = Kchk j C V K' g.2 := by
    refine prod_congr rfl fun W hW => ?_
    have hWp := isPolymer_of_mem_comp f1 hW
    have hWU := (subset_of_mem_comp hW).trans f2
    rw [KchkC, KchkC, hKtil W hWp hWU]
    refine congrArg (fun t => Ktil j C V K' W - t) ?_
    refine sum_congr rfl fun b hb => ?_
    rw [hJ b (blockSet_subset hU (blocks_mono hWU hb)) (blockSet_nonempty_of_mem_blocks hb)]
  have hP : ∏ p ∈ g.1, thetaE (Jb j K p.1 p.2) = ∏ p ∈ g.1, thetaE (Jb j K' p.1 p.2) :=
    prod_congr rfl fun p hp => by
      rw [hJ p.1 (f4 p hp).2.2.1 (nonempty_of_mem_pairsU (f4 p hp).1)]
  unfold Kterm
  rw [InextPow_congr huV, hKchk, hP]

/-- **Proposition `prop:consistency`** for `V_{j+1}`. -/
theorem uVnext_local' (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hC : CovInv C)
    (hCs : ∀ x y, C x y = C y x) (hK : InK j K) (hK' : InK j K') {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hKK' : ∀ X, IsSmall j X → blockSet j b ⊆ X → K X = K' X) :
    uVnext j C V K = uVnext j C V K' := by
  have hQ : Qb j K b = Qb j K' b := by
    unfold Qb
    split_ifs
    · refine sum_congr rfl fun X hX => ?_
      obtain ⟨h1, h2⟩ := mem_filter.1 hX
      rw [hKK' X (mem_smallSets.1 h1) h2]
    · rfl
  by_cases hjN : j + 1 < N
  swap
  · have h0 : ∀ K'' : Act d L N, Qb j K'' 0 = 0 := fun K'' => by rw [Qb, if_neg hjN]
    unfold uVnext
    rw [h0, h0]
  have hBp : Patch (blockSet (L := L) (N := N) j b) := by
    obtain ⟨x, -, rfl⟩ := mem_image.1 hb
    exact patch_small hd hL hjN (isSmall_blockSet j x)
  have h1 := uVnext_spec hd hL hj hC hCs V hK hb
  have h2 := uVnext_spec hd hL hj hC hCs V hK' hb
  rw [hQ, h2] at h1
  have hLN : 3 ≤ L ^ N := by
    have h8 : 2 ^ 3 ≤ 2 ^ (d + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 3 ≤ L := by omega
      _ ≤ L ^ N := Nat.le_self_pow (by omega) L
  obtain ⟨e1, e2⟩ := coup_injective hd hLN (mem_blockIdx.1 hb) hBp h1
  exact Prod.ext e1.symm e2.symm

/-- **Proposition `prop:consistency`** for `K_{j+1}`. -/
theorem Knext_local' (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j < N) (hC : CovInv C)
    (hCs : ∀ x y, C x y = C y x) (hK : InK j K) (hK' : InK j K') {U : Finset (Lam d L N)}
    (hU : IsPolymer (j + 1) U) (hUne : U.Nonempty)
    (hKK' : ∀ X, IsConn j X → X ⊆ nbhd (j + 1) U → K X = K' X) :
    Knext j C V K U = Knext j C V K' U := by
  have hs : ∀ b, blockSet j b ⊆ U → (blockSet (L := L) (N := N) j b).Nonempty →
      ∀ X, IsSmall j X → blockSet j b ⊆ X → K X = K' X := by
    intro b hbU hne X hX hbX
    obtain ⟨z, hz⟩ := hne
    exact hKK' X ⟨hX.1, hX.2.1⟩ (subset_nbhd_succ_of_small hX (hbX hz) (hbU hz))
  have hc : ∀ Y, IsConn j Y → Y ⊆ U → K Y = K' Y := fun Y hY hYU =>
    hKK' Y hY (hYU.trans (subset_nbhd hU))
  obtain ⟨x, hx⟩ := hUne
  have hbU : blockSet j (blk j x) ⊆ U :=
    blockSet_subset (IsPolymer.of_succ hU) (blk_mem_blocks hx)
  have hne : (blockSet (L := L) (N := N) j (blk j x)).Nonempty := ⟨x, mem_blockSet_blk j x⟩
  have huV : uVnext j C V K = uVnext j C V K' :=
    uVnext_local' hd hL hj hC hCs hK hK' (mem_image_of_mem _ (mem_univ x)) (hs _ hbU hne)
  rw [Knext_eq_Kterm, Knext_eq_Kterm, huV]
  refine congrArg (fun t => Complex.exp ((uVnext j C V K').1 * U.card) • t) ?_
  exact sum_congr rfl fun g hg => Kterm_congr (IsPolymer.of_succ hU) huV hc hs hg

end Local

/-! ### Automorphism invariance -/

/-- `T` acting on even elements. -/
def AE (T : AffAut d L N) : EvR (Lam d L N) →ₐ[ℂ] EvR (Lam d L N) := mapE (autV T.E)

/-- `T` acting on even elements of the doubled algebra. -/
def AE2 (T : AffAut d L N) : EvR (Lam d L N ⊕ Lam d L N) →ₐ[ℂ] EvR (Lam d L N ⊕ Lam d L N) :=
  mapE (autV2 T.E)

@[simp] theorem coe_AE (T : AffAut d L N) (x : EvR (Lam d L N)) :
    (AE T x : Alg d L N) = autAlg T.E x := rfl

@[simp] theorem coe_AE2 (T : AffAut d L N) (x : EvR (Lam d L N ⊕ Lam d L N)) :
    (AE2 T x : Alg2 d L N) = autAlg2 T.E x := rfl

section Aut

variable (T : AffAut d L N)

theorem AE2_thetaE (x : EvR (Lam d L N)) : AE2 T (thetaE x) = thetaE (AE T x) :=
  Subtype.ext (theta_autAlg T.E x).symm

theorem AE2_inclE (x : EvR (Lam d L N)) : AE2 T (inclE x) = inclE (AE T x) :=
  Subtype.ext (incl_autAlg T.E x).symm

theorem AE_ECE {C : Matrix (Lam d L N) (Lam d L N) ℝ} (hC : ∀ x y, C (T.E x) (T.E y) = C x y)
    (F : EvR (Lam d L N ⊕ Lam d L N)) : AE T (ECE C F) = ECE C (AE2 T F) :=
  Subtype.ext (EC_autAlg2 T.E hC F).symm

theorem AE_gexp {x : EvR (Lam d L N)} (hx : IsNilpotent x) : AE T (gexp x) = gexp (AE T x) :=
  IsNilpotent.map_exp hx (AE T)

theorem AE_VE {T : AffAut d L N} (hT : IsGen T) (V : Vcoup) (X : Finset (Lam d L N)) :
    AE T (VE V X) = VE V (T.img X) :=
  Subtype.ext (hT.eval_img V X)

theorem img_singleton' (x : Lam d L N) : T.img {x} = {T.E x} := by
  simp [AffAut.img]

theorem E_inv_of_img {T T' : AffAut d L N} (e : ∀ X, T'.img (T.img X) = X) (x : Lam d L N) :
    T'.E (T.E x) = x := by
  have := e {x}
  rw [img_singleton', img_singleton'] at this
  exact singleton_inj.1 this

theorem img_biUnion {ι : Type*} (s : Finset ι) (f : ι → Finset (Lam d L N)) :
    T.img (s.biUnion f) = s.biUnion fun i => T.img (f i) := by
  ext y
  simp only [mem_img_iff, mem_biUnion]
  constructor
  · rintro ⟨x, ⟨i, hi, hx⟩, rfl⟩
    exact ⟨i, hi, x, hx, rfl⟩
  · rintro ⟨i, hi, x, hx, rfl⟩
    exact ⟨x, ⟨i, hi, hx⟩, rfl⟩

variable {T} {j : ℕ}

theorem img_blockSet_bmap (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) : T.img (blockSet j b) = blockSet j (bmap j T b) := by
  obtain ⟨b', -, e⟩ := hP.img_blockSet hT hj hb
  obtain ⟨x, hx⟩ := mem_blockIdx.1 hb
  have h1 : T.E x ∈ blockSet j b' := e ▸ (E_mem_img T).2 hx
  rw [e, ← mem_blockSet.1 hx, bmap_blk hP, ← mem_blockSet.1 h1]

theorem bmap_mem_blockIdx (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) : bmap j T b ∈ blockIdx (L := L) (N := N) j := by
  rw [mem_blockIdx, ← img_blockSet_bmap hT hj hP hb]
  exact T.img_nonempty (mem_blockIdx.1 hb)

theorem blocks_img_bmap (hP : PresBlocks j T) (X : Finset (Lam d L N)) :
    blocks j (T.img X) = (blocks j X).image (bmap j T) := by
  rw [blocks_img, blocks, image_image]
  exact image_congr fun x _ => (bmap_blk hP x).symm

theorem bmap_injOn (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) :
    Set.InjOn (bmap j T) ((blockIdx (L := L) (N := N) j : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)) := by
  intro b hb b' hb' e
  obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
  obtain ⟨y, -, rfl⟩ := mem_image.1 (mem_coe.1 hb')
  rw [bmap_blk hP, bmap_blk hP] at e
  exact (hP.blk_iff hT hj).1 e

theorem bmap_bmap {T' : AffAut d L N} (hP : PresBlocks j T) (hP' : PresBlocks j T')
    (e : ∀ x, T'.E (T.E x) = x) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    bmap j T' (bmap j T b) = b := by
  obtain ⟨x, -, rfl⟩ := mem_image.1 hb
  rw [bmap_blk hP, bmap_blk hP', e]

theorem blocks_subset_blockIdx (X : Finset (Lam d L N)) :
    blocks j X ⊆ blockIdx (L := L) (N := N) j := blocks_mono (subset_univ X)

variable {C : Matrix (Lam d L N) (Lam d L N) ℝ} {V : Vcoup} {K : Act d L N}

theorem AE_Inext (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE T (Inext j C V K b) = Inext j C V K (bmap j T b) := by
  rw [Inext, Inext, map_smul, AE_gexp T (isNilpotent_VE _ _).neg, map_neg, AE_VE hT,
    img_blockSet_bmap hT hj hP hb, ← img_blockSet_bmap hT hj hP hb, T.card_img]

theorem AE_InextPow (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) (X : Finset (Lam d L N)) :
    AE T (InextPow j C V K X) = InextPow j C V K (T.img X) := by
  rw [InextPow, InextPow, map_prod, blocks_img_bmap hP,
    prod_image fun b hb b' hb' => bmap_injOn hT hj hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact prod_congr rfl fun b hb => AE_Inext hT hj hP (blocks_subset_blockIdx X hb)

theorem AE2_dI (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) {b : Fin d → ℕ}
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    AE2 T (dI j C V K b) = dI j C V K (bmap j T b) := by
  rw [dI, dI, map_sub, AE2_thetaE, AE2_inclE, AE_Inext hT hj hP hb,
    AE_gexp T (isNilpotent_VE _ _).neg, map_neg, AE_VE hT, img_blockSet_bmap hT hj hP hb]

theorem AE2_dIPow (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) (X : Finset (Lam d L N)) :
    AE2 T (dIPow j C V K X) = dIPow j C V K (T.img X) := by
  rw [dIPow, dIPow, map_prod, blocks_img_bmap hP,
    prod_image fun b hb b' hb' => bmap_injOn hT hj hP (blocks_subset_blockIdx X hb)
      (blocks_subset_blockIdx X hb')]
  exact prod_congr rfl fun b hb => AE2_dI hT hj hP (blocks_subset_blockIdx X hb)

theorem AE_K (hK : InK j K) (hT : IsGen T) (hP : PresBlocks j T) {Y : Finset (Lam d L N)}
    (hY : IsConn j Y) : AE T (K Y) = K (T.img Y) :=
  Subtype.ext (hK.aut T hT hP Y hY)

theorem AE_Kext (hK : InK j K) (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) : AE T (Kext j K W) = Kext j K (T.img W) := by
  rw [Kext, Kext, map_prod, hP.comp_img hT hj,
    prod_image fun Y _ Y' _ e => img_injective T e]
  exact prod_congr rfl fun Y hY => AE_K hK hT hP (isConn_of_mem_comp hW hY)

theorem Pj_img (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) (W : Finset (Lam d L N)) :
    Pj j (T.img W) = (Pj j W).image T.img := by
  obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
  ext Y
  rw [mem_image]
  constructor
  · intro hY
    obtain ⟨h1, h2⟩ := mem_Pj.1 hY
    refine ⟨T'.img Y, mem_Pj.2 ⟨?_, (hP'.isPolymer_img hT' hj).2 h2⟩, e' Y⟩
    have := img_mono T' h1
    rwa [e] at this
  · rintro ⟨Y', hY', rfl⟩
    obtain ⟨h1, h2⟩ := mem_Pj.1 hY'
    exact mem_Pj.2 ⟨img_mono T h1, (hP.isPolymer_img hT hj).2 h2⟩

theorem AE2_Ktil (hK : InK j K) (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T)
    {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    AE2 T (Ktil j C V K W) = Ktil j C V K (T.img W) := by
  rw [Ktil, Ktil, map_sum, Pj_img hT hj hP, sum_image fun Y _ Y' _ e => img_injective T e]
  refine sum_congr rfl fun Y hY => ?_
  rw [map_mul, AE2_thetaE, AE_Kext hK hT hj hP (IsPolymer.sdiff hW (mem_Pj.1 hY).2),
    AE2_dIPow hT hj hP, img_sdiff]

theorem AE_LocE (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j + 1 < N) (hK : InK j K)
    (hT : IsGen T) (hP : PresBlocks j T) {Y : Finset (Lam d L N)} (hY : IsSmall j Y)
    (B : Finset (Lam d L N)) : AE T (LocE Y B (K Y)) = LocE (T.img Y) (T.img B) (K (T.img Y)) :=
  Subtype.ext (by
    rw [coe_AE, coe_LocE, coe_LocE, T.LocXY_aut (region_small hd hL hj hY) hY.2.1.1 _
      (hK.loc Y ⟨hY.1, hY.2.1⟩), hK.aut T hT hP Y ⟨hY.1, hY.2.1⟩])

theorem AE_Jb (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hK : InK j K) (hT : IsGen T)
    (hj : j ≤ N) (hP : PresBlocks j T) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) : AE T (Jb j K b X) = Jb j K (bmap j T b) (T.img X) := by
  have hB := img_blockSet_bmap hT hj hP hb
  have c1 : (j + 1 < N ∧ IsSmall j (T.img X) ∧ blockSet j (bmap j T b) ⊆ T.img X) ↔
      (j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X) := by
    rw [← hB, hP.isSmall_img hT hj, AffAut.img, AffAut.img, Finset.map_subset_map]
  have c2 : T.img X = blockSet j (bmap j T b) ↔ X = blockSet j b := by
    rw [← hB]; exact (img_injective T).eq_iff
  unfold Jb
  by_cases hc : j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X
  · rw [if_pos hc, if_pos (c1.2 hc)]
    by_cases hx : X = blockSet j b
    · rw [if_pos hx, if_pos (c2.2 hx), map_neg, map_sum]
      congr 1
      obtain ⟨T', hT', hP', e, e'⟩ := hP.exists_inv hT hj
      have hS : ((smallSets j).filter fun Y => blockSet j (bmap j T b) ⊆ Y ∧
          Y ≠ blockSet j (bmap j T b)) =
          ((smallSets j).filter fun Y => blockSet j b ⊆ Y ∧ Y ≠ blockSet j b).image T.img := by
        ext Y
        simp only [mem_filter, mem_image, mem_smallSets]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨T'.img Y, ⟨(hP'.isSmall_img hT' hj).2 h1, ?_, ?_⟩, e' Y⟩
          · have := img_mono T' h2
            rwa [← hB, e] at this
          · intro h4
            apply h3
            rw [← e' Y, h4, hB]
        · rintro ⟨Y', ⟨h1, h2, h3⟩, rfl⟩
          refine ⟨(hP.isSmall_img hT hj).2 h1, ?_, ?_⟩
          · rw [← hB]; exact img_mono T h2
          · rw [← hB]; exact fun h4 => h3 (img_injective T h4)
      rw [hS, sum_image fun Y _ Y' _ e => img_injective T e]
      refine sum_congr rfl fun Y hY => ?_
      rw [AE_LocE hd hL hc.1 hK hT hP (mem_smallSets.1 (mem_filter.1 hY).1), hB]
    · rw [if_neg hx, if_neg (mt c2.1 hx), AE_LocE hd hL hc.1 hK hT hP hc.2.1, hB]
  · rw [if_neg hc, if_neg (mt c1.1 hc), map_zero]

theorem AE2_KchkC (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hK : InK j K) (hT : IsGen T)
    (hj : j ≤ N) (hP : PresBlocks j T) {W : Finset (Lam d L N)} (hW : IsPolymer j W) :
    AE2 T (KchkC j C V K W) = KchkC j C V K (T.img W) := by
  rw [KchkC, KchkC, map_sub, AE2_Ktil hK hT hj hP hW, map_sum, blocks_img_bmap hP,
    sum_image fun b hb b' hb' => bmap_injOn hT hj hP (blocks_subset_blockIdx W hb)
      (blocks_subset_blockIdx W hb')]
  congr 1
  refine sum_congr rfl fun b hb => ?_
  rw [AE2_thetaE, AE_Jb hd hL hK hT hj hP (blocks_subset_blockIdx W hb)]

theorem AE2_Kchk (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hK : InK j K) (hT : IsGen T)
    (hj : j ≤ N) (hP : PresBlocks j T) {X : Finset (Lam d L N)} (hX : IsPolymer j X) :
    AE2 T (Kchk j C V K X) = Kchk j C V K (T.img X) := by
  rw [Kchk, Kchk, map_prod, hP.comp_img hT hj, prod_image fun Y _ Y' _ e => img_injective T e]
  exact prod_congr rfl fun W hW => AE2_KchkC hd hL hK hT hj hP (isPolymer_of_mem_comp hX hW)

/-- The action of `T` on the index set `𝒢(U)`. -/
def gimg (j : ℕ) (T : AffAut d L N) (g : GT d L N) : GT d L N :=
  (g.1.image fun p => (bmap j T p.1, T.img p.2), T.img g.2)

theorem Xcal_gimg (g : GT d L N) : Xcal (gimg j T g).1 = T.img (Xcal g.1) := by
  show (g.1.image fun p => (bmap j T p.1, T.img p.2)).biUnion Prod.snd =
    T.img (g.1.biUnion Prod.snd)
  rw [image_biUnion, img_biUnion]

theorem Bbox_gimg (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T) {g : GT d L N}
    (hg : g.1 ⊆ pairsU j) : Bbox j (gimg j T g).1 = T.img (Bbox j g.1) := by
  show (g.1.image fun p => (bmap j T p.1, T.img p.2)).biUnion
      (fun p => nbhd j (blockSet j p.1)) =
    T.img (g.1.biUnion fun p => nbhd j (blockSet (L := L) (N := N) j p.1))
  rw [image_biUnion, img_biUnion]
  refine biUnion_congr rfl fun p hp => ?_
  rw [← img_blockSet_bmap hT hj hP (mem_pairsU.1 (hg hp)).1, hP.nbhd_img hT hj]

theorem gimg_mem (hT : IsGen T) (hj : j + 1 ≤ N) (hP : PresBlocks j T)
    (hP1 : PresBlocks (j + 1) T) {U : Finset (Lam d L N)} {g : GT d L N} (hg : g ∈ Gset j U) :
    gimg j T g ∈ Gset j (T.img U) := by
  have hj' : j ≤ N := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_Gset'.1 hg
  refine mem_Gset'.2 ⟨(hP.isPolymer_img hT hj').2 h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro p' hp'
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
    obtain ⟨hb, hs, hbs⟩ := mem_pairsU.1 (h2 hp)
    refine mem_pairsU.2 ⟨bmap_mem_blockIdx hT hj' hP hb, (hP.isSmall_img hT hj').2 hs, ?_⟩
    rw [← img_blockSet_bmap hT hj' hP hb]
    exact img_mono T hbs
  · intro p' hp' q' hq' e
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hq'
    rw [h3 p hp q hq (img_injective T e)]
  · intro p' hp' q' hq' e
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hq'
    rw [hT.touch_img]
    exact h4 p hp q hq fun e' => e (by simp only [e'])
  · show ¬ Touch (Xcal (gimg j T g).1) (T.img g.2)
    rw [Xcal_gimg, hT.touch_img]; exact h5
  · show clo j (T.img g.2 ∪ Bbox j (gimg j T g).1) = T.img U
    rw [Bbox_gimg hT hj' hP h2, ← img_union, hP1.clo_img hT hj, h6]

theorem gimg_gimg {T' : AffAut d L N} (hP : PresBlocks j T) (hP' : PresBlocks j T')
    (e : ∀ X, T'.img (T.img X) = X) {U : Finset (Lam d L N)} {g : GT d L N}
    (hg : g ∈ Gset j U) : gimg j T' (gimg j T g) = g := by
  obtain ⟨-, h2, -, -, -, -⟩ := mem_Gset'.1 hg
  have e₁ := E_inv_of_img e
  simp only [gimg, image_image, e]
  refine Prod.ext ?_ rfl
  conv_rhs => rw [← image_id (s := g.1)]
  refine image_congr fun p hp => ?_
  simp only [Function.comp_apply, id, e]
  rw [bmap_bmap hP hP' e₁ (mem_pairsU.1 (h2 hp)).1]

theorem AE_Kterm (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hK : InK j K) (hT : IsGen T)
    (hj : j ≤ N) (hP : PresBlocks j T) (hC : ∀ x y, C (T.E x) (T.E y) = C x y)
    {U : Finset (Lam d L N)} {g : GT d L N} (hg : g ∈ Gset j U) :
    AE T (Kterm j C V K U g) = Kterm j C V K (T.img U) (gimg j T g) := by
  obtain ⟨h1, h2, h3, -, -, -⟩ := mem_Gset'.1 hg
  have hinj : Set.InjOn (fun p : (Fin d → ℕ) × Finset (Lam d L N) => (bmap j T p.1, T.img p.2))
      (g.1 : Set _) := by
    intro p hp q hq e
    exact h3 p hp q hq (img_injective T (congrArg Prod.snd e))
  rw [Kterm, Kterm, map_mul, AE_InextPow hT hj hP, AE_ECE T hC, map_mul, AE2_Kchk hd hL hK hT hj hP h1,
    map_prod, img_sdiff, img_union, ← Xcal_gimg]
  simp only [gimg]
  rw [prod_image hinj]
  congr 3
  refine prod_congr rfl fun p hp => ?_
  rw [AE2_thetaE, AE_Jb hd hL hK hT hj hP (mem_pairsU.1 (h2 hp)).1]

/-- **Automorphism invariance of `K_{j+1}`**. -/
theorem AE_Knext (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j + 1 < N) (hK : InK j K)
    (hT : IsGen T) (hP1 : PresBlocks (j + 1) T) (hC : ∀ T : AffAut d L N, IsGen T →
      ∀ x y, C (T.E x) (T.E y) = C x y) (U : Finset (Lam d L N)) :
    AE T (Knext j C V K U) = Knext j C V K (T.img U) := by
  have hP := hP1.of_succ hT hj
  obtain ⟨T', hT', hP1', e, e'⟩ := hP1.exists_inv hT (by omega : j + 1 ≤ N)
  have hP' := hP1'.of_succ hT' hj
  rw [Knext_eq_Kterm, Knext_eq_Kterm, map_smul, map_sum, T.card_img]
  congr 1
  refine sum_nbij' (gimg j T) (gimg j T') (fun g hg => gimg_mem hT (by omega) hP hP1 hg)
    (fun g hg => ?_) (fun g hg => gimg_gimg hP hP' e hg) (fun g hg => gimg_gimg hP' hP e' hg)
    (fun g hg => AE_Kterm hd hL hK hT (by omega) hP (hC T hT) hg)
  have := gimg_mem hT' (by omega) hP' hP1' hg
  rwa [e] at this

end Aut

end

end Step
