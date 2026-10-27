module

public import ArborealDecay.Wiring.Events
public import ArborealDecay.Wiring.Indep
public import ArborealDecay.Wiring.Gamma
public import ArborealDecay.Wiring.Stable
public import ArborealDecay.Separator
public import ArborealDecay.ForestPoly

/-!
# Separator-wiring monotonicity (`prop:separator-wiring`)

`τ_G(a, b) ≤ τ_{G/S}(a, b)` for a vertex separator `S`.

* `separator_wiring_of_stable`: with real stability of `P_G` as the (only) hypothesis;
* `separator_wiring`: unconditional, using `ArborealDecay.ForestPoly.forestPolynomial_isRealStable`.
-/

@[expose] public section

universe u

namespace ArborealDecay.Wiring

noncomputable section

open Finset Classical ArborealDecay.Surgery MvPolynomial

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem mon_insert {σ : Type*} [DecidableEq σ] {x : σ} {U : Finset σ} (hx : x ∉ U) :
    mon (insert x U) = Finsupp.single x 1 + mon U := by
  unfold mon
  rw [Finset.sum_insert hx]

theorem mon_US (S : Finset V) : mon (US S) = ArborealDecay.Separator.sMonomial ↥S := by
  unfold mon US ArborealDecay.Separator.sMonomial
  rw [Finset.sum_image (fun x _ y _ h => Sum.inr_injective h)]

theorem sum_eq_Z_mul_prob {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {w : Λ → Λ → ℝ}
    (hw : ∀ i j, w i j = w j i) (hw0 : ∀ i j, 0 ≤ w i j) (Q : SimpleGraph Λ → Prop) :
    ∑ F : SimpleGraph Λ with F.IsAcyclic ∧ Q F, H02.forestWeight w hw F =
      H02.Zforest w hw * H02.arborealProb w hw Q := by
  have := (H02.Zforest_pos hw hw0).ne'
  unfold H02.arborealProb
  field_simp

theorem coeff_eq_prob {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S) (a b : V) {β : V → V → ℝ}
    (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j) (U : Finset (Var S))
    (Q : SimpleGraph (Option {v // v ∉ S}) → Prop)
    (hU : ∀ F : SimpleGraph V,
      Set.InjOn (cmp a b S F) ↑U ↔ (SepS S F ∧ Q (edgeQuot (collapse S) F.edgeFinset))) :
    (wpoly β hβ a b S).coeff (mon U) =
      H02.Zforest (mapW β (collapse S)) (mapW_symm hβ (collapse S)) *
        H02.arborealProb (mapW β (collapse S)) (mapW_symm hβ (collapse S)) Q := by
  rw [coeff_wpoly]
  exact (sum_inj_eq hs₀ a b hβ U Q hU).trans
    (sum_eq_Z_mul_prob _ (mapW_nonneg hβ0 (collapse S)) Q)

/-- Splitting the weighted sum over forests according to `a ↔ b`. -/
theorem sum_split {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (a b : V) (x y : ℝ) :
    (∑ F : SimpleGraph V with F.IsAcyclic, (∏ e ∈ F.edgeFinset, Sym2.lift ⟨β, hβ⟩ e) *
        if F.Reachable a b then x else y) =
      (∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b, H02.forestWeight β hβ F) * x +
        (H02.Zforest β hβ -
          ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b, H02.forestWeight β hβ F) * y := by
  have hZ : H02.Zforest β hβ = (∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b,
      H02.forestWeight β hβ F) + ∑ F : SimpleGraph V with F.IsAcyclic ∧ ¬ F.Reachable a b,
      H02.forestWeight β hβ F := by
    unfold H02.Zforest
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h1 : F.IsAcyclic <;> by_cases h2 : F.Reachable a b <;> simp [h1, h2]
  rw [hZ, add_sub_cancel_left, Finset.sum_mul, Finset.sum_mul, Finset.sum_filter,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun F _ => ?_
  by_cases h1 : F.IsAcyclic <;> by_cases h2 : F.Reachable a b <;> simp [h1, h2, H02.forestWeight]

theorem wiring_core {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    {a b : V} {S : Finset V} {s₀ : V} (hs₀ : s₀ ∈ S) (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S)
    (hPma : ∀ v, (forestPolynomial β hβ).degreeOf v ≤ 1)
    (hPst : ∀ z : V → ℂ, (∀ j, 0 < (z j).im) → aeval z (forestPolynomial β hβ) ≠ 0) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) ≤
      H02.arborealProb (mapW β (collapse S)) (mapW_symm hβ (collapse S))
        (fun F => F.Reachable (collapse S a) (collapse S b)) := by
  have hab : a ≠ b := by
    rintro rfl
    obtain ⟨v, hv, hvS⟩ := hsep SimpleGraph.Walk.nil
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv; exact ha hvS
  obtain ⟨V₁, V₂, hU, hcross, hea, heb⟩ := gamma_structure hβ ha hb hsep
  have hm : ∀ i j, mapW β (collapse S) i j = mapW β (collapse S) j i :=
    mapW_symm hβ (collapse S)
  have hm0 : ∀ i j, 0 ≤ mapW β (collapse S) i j := mapW_nonneg hβ0 (collapse S)
  set m := mapW β (collapse S) with hmdef
  set ra := H02.arborealProb m hm (fun F => ¬ F.Reachable (some ⟨a, ha⟩) none) with hra_def
  set rb := H02.arborealProb m hm (fun F => ¬ F.Reachable (some ⟨b, hb⟩) none) with hrb_def
  have hbot : ∀ x : {v // v ∉ S}, ¬ (⊥ : SimpleGraph (Option {v // v ∉ S})).Reachable (some x) none := by
    intro x h
    rw [SimpleGraph.reachable_bot] at h
    exact absurd h (by simp)
  have hra : 0 < ra := prob_pos_of_bot m hm hm0 _ (hbot _)
  have hrb : 0 < rb := prob_pos_of_bot m hm hm0 _ (hbot _)
  have hZg : 0 < H02.Zforest m hm := H02.Zforest_pos hm hm0
  have hZG : 0 < H02.Zforest β hβ := H02.Zforest_pos hβ hβ0
  have hpair := prob_not_reach_triple hU hm hm0 hcross hea heb
  -- the four coefficients
  have c0 : (wpoly β hβ a b S).coeff (mon (US S)) = H02.Zforest m hm * 1 := by
    rw [coeff_eq_prob hs₀ a b hβ hβ0 (US S) (fun _ => True)
      (fun F => by rw [injOn_US]; exact (and_true _).symm.to_iff)]
    rw [H02.arborealProb_true hm hm0]
  have hq1 : ∀ F : SimpleGraph V, (∀ s ∈ S, ¬ F.Reachable a s) ↔
      ¬ (edgeQuot (collapse S) F.edgeFinset).Reachable (some ⟨a, ha⟩) none := by
    intro F
    rw [reach_none_iff hs₀ F ha]
    exact ⟨fun h ⟨s, hs, hr⟩ => h s hs hr, fun h s hs hr => h ⟨s, hs, hr⟩⟩
  have hq2 : ∀ F : SimpleGraph V, (∀ s ∈ S, ¬ F.Reachable b s) ↔
      ¬ (edgeQuot (collapse S) F.edgeFinset).Reachable (some ⟨b, hb⟩) none := by
    intro F
    rw [reach_none_iff hs₀ F hb]
    exact ⟨fun h ⟨s, hs, hr⟩ => h s hs hr, fun h s hs hr => h ⟨s, hs, hr⟩⟩
  have cx : (wpoly β hβ a b S).coeff (mon (insert (Sum.inl 0) (US S))) =
      H02.Zforest m hm * ra := by
    exact coeff_eq_prob hs₀ a b hβ hβ0 _ (fun F => ¬ F.Reachable (some ⟨a, ha⟩) none)
      (fun F => by rw [injOn_Ux a b S F, hq1])
  have cy : (wpoly β hβ a b S).coeff (mon (insert (Sum.inl 1) (US S))) =
      H02.Zforest m hm * rb := by
    exact coeff_eq_prob hs₀ a b hβ hβ0 _ (fun F => ¬ F.Reachable (some ⟨b, hb⟩) none)
      (fun F => by rw [injOn_Uy a b S F, hq2])
  have cxy : (wpoly β hβ a b S).coeff (mon (insert (Sum.inl 0) (insert (Sum.inl 1) (US S)))) =
      H02.Zforest m hm * (ra * rb) := by
    rw [coeff_eq_prob hs₀ a b hβ hβ0 _ (fun F => ¬ F.Reachable (some ⟨a, ha⟩) none ∧
      ¬ F.Reachable (some ⟨b, hb⟩) none ∧ ¬ F.Reachable (some ⟨a, ha⟩) (some ⟨b, hb⟩)) ?_,
      hpair]
    · intro F
      rw [injOn_Uxy a b S F]
      refine and_congr Iff.rfl ?_
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨(hq1 F).1 h1, (hq2 F).1 h2, ?_⟩
        rw [reach_some_iff hs₀ F ha hb (fun ⟨s, hs, hr⟩ => h1 s hs hr)]
        exact h3
      · rintro ⟨h1, h2, h3⟩
        refine ⟨(hq1 F).2 h1, (hq2 F).2 h2, ?_⟩
        rw [reach_some_iff hs₀ F ha hb (by
          rintro ⟨s, hs, hr⟩; exact h1 ((reach_none_iff hs₀ F ha).2 ⟨s, hs, hr⟩))] at h3
        exact h3
  -- apply the stable separator lemma
  have hst := wpoly_aeval_ne_zero_of_forest hβ0 hPma hPst hab ha hb
  have hma := wpoly_degreeOf_le_one β hβ hPma a b S
  have hpos := fun (d : Var S →₀ ℕ) (hd : ∀ v, d v ≤ 1) =>
    coeff_wpoly_pos β hβ hβ0 hab ha hb d hd
  have hc : 0 < H02.Zforest m hm * (ra * rb) := mul_pos hZg (mul_pos hra hrb)
  have hsepl := ArborealDecay.Separator.stable_separator (wpoly β hβ a b S) hst hma hpos
    (H02.Zforest m hm * (ra * rb)) ra⁻¹ rb⁻¹ hc (inv_pos.2 hra) (inv_pos.2 hrb) (by
      have hn : ∀ i : Fin 2, (Sum.inl i : Var S) ∉ US S := fun i => inl_notMem_US S i
      have h01 : (Sum.inl 0 : Var S) ∉ insert (Sum.inl 1) (US S) := by
        simp [inl_notMem_US S 0]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have : ArborealDecay.Separator.sMonomial ↥S + Finsupp.single (Sum.inl 0) 1 +
            Finsupp.single (Sum.inl 1) 1 =
            mon (insert (Sum.inl 0) (insert (Sum.inl 1) (US S))) := by
          rw [mon_insert h01, mon_insert (hn 1), mon_US]; abel
        rw [this, cxy]
      · have : ArborealDecay.Separator.sMonomial ↥S + Finsupp.single (Sum.inl 0) 1 =
            mon (insert (Sum.inl 0) (US S)) := by
          rw [mon_insert (hn 0), mon_US]; abel
        rw [this, cx]; field_simp
      · have : ArborealDecay.Separator.sMonomial ↥S + Finsupp.single (Sum.inl 1) 1 =
            mon (insert (Sum.inl 1) (US S)) := by
          rw [mon_insert (hn 1), mon_US]; abel
        rw [this, cy]; field_simp
      · rw [← mon_US, c0]; field_simp)
  have hev := eval_wpoly_two β hβ a b S ra⁻¹ rb⁻¹
  have h0fun : (0 : ↥S → ℝ) = fun _ => 0 := rfl
  rw [h0fun, hev, sum_split hβ a b] at hsepl
  -- final algebra
  set SR := ∑ F : SimpleGraph V with F.IsAcyclic ∧ F.Reachable a b, H02.forestWeight β hβ F
    with hSR
  have key : SR ≤ H02.Zforest β hβ * ((1 - ra) * (1 - rb)) := by
    have h1 := mul_nonneg (mul_pos hra hrb).le hsepl
    have e : ra * rb * (SR * (1 - ra⁻¹ - rb⁻¹) + (H02.Zforest β hβ - SR) *
        ((1 - ra⁻¹) * (1 - rb⁻¹))) = -SR + H02.Zforest β hβ * ((1 - ra) * (1 - rb)) := by
      field_simp
      ring
    linarith
  have hSRτ : SR = H02.Zforest β hβ * H02.arborealProb β hβ (fun F => F.Reachable a b) :=
    (Finset.sum_congr (Finset.ext fun F => by simp) (fun _ _ => rfl)).trans
      (sum_eq_Z_mul_prob hβ hβ0 (fun F : SimpleGraph V => F.Reachable a b))
  rw [hSRτ] at key
  have hτle := le_of_mul_le_mul_left key hZG
  have hreach := prob_reach_eq hU hm hm0 hcross hea heb
  have hca : collapse S a = some ⟨a, ha⟩ := collapse_of_notMem ha
  have hcb : collapse S b = some ⟨b, hb⟩ := collapse_of_notMem hb
  rw [hca, hcb, hreach]
  exact hτle

/-- Without a separator vertex, the hypothesis forces `a`, `b` to be disconnected. -/
theorem prob_reach_eq_zero_of_empty {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    {a b : V} (hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ (∅ : Finset V)) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) = 0 := by
  unfold H02.arborealProb
  rw [Finset.sum_eq_zero, zero_div]
  intro F hF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
  by_contra hw
  have hle : F ≤ suppGraph β hβ := by
    intro u v huv
    refine ⟨huv.ne, fun h0 => hw ?_⟩
    exact forestWeight_eq_zero_of_adj hβ h0 huv
  obtain ⟨p⟩ := hF.2.mono hle
  obtain ⟨v, _, hv⟩ := hsep p
  simp at hv

/-- **Separator-wiring monotonicity**, from the stability of the forest polynomial of `G` and its
multi-affinity. -/
theorem separator_wiring_aux {β : V → V → ℝ} (hβ : ∀ i j, β i j = β j i)
    (hβ0 : ∀ i j, 0 ≤ β i j) {a b : V} {S : Finset V} (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S)
    (hPma : ∀ v, (forestPolynomial β hβ).degreeOf v ≤ 1)
    (hPst : ∀ z : V → ℂ, (∀ j, 0 < (z j).im) → aeval z (forestPolynomial β hβ) ≠ 0) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) ≤
      H02.arborealProb (mapW β (collapse S)) (mapW_symm hβ (collapse S))
        (fun F => F.Reachable (collapse S a) (collapse S b)) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · rw [prob_reach_eq_zero_of_empty hβ hsep]
    exact H02.arborealProb_nonneg (mapW_symm hβ (collapse (∅ : Finset V)))
      (mapW_nonneg hβ0 (collapse (∅ : Finset V))) _
  · exact wiring_core hβ hβ0 hs₀ ha hb hsep hPma hPst

/-- **`prop:separator-wiring`**, conditional on the real stability of the forest polynomial
(`lem:PG-stable`): `τ_G(a, b) ≤ τ_{G/S}(a, b)` for a vertex separator `S`. -/
theorem separator_wiring_of_stable
    (hstab : ∀ (U : Type u) [Fintype U] [DecidableEq U] (β : U → U → ℝ)
      (hβ : ∀ i j, β i j = β j i), (∀ i j, 0 ≤ β i j) → ∀ z : U → ℂ, (∀ j, 0 < (z j).im) →
        MvPolynomial.aeval z (forestPolynomial β hβ) ≠ 0)
    (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (a b : V) (S : Finset V) (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) ≤
      H02.arborealProb (mapW β (collapse S)) (mapW_symm hβ (collapse S))
        (fun F => F.Reachable (collapse S a) (collapse S b)) :=
  separator_wiring_aux hβ hβ0 ha hb hsep
    (fun v => ArborealDecay.ForestPoly.forestPolynomial_isMultiAffine β hβ hβ0 v)
    (hstab V β hβ hβ0)

/-- **`prop:separator-wiring`** (unconditional): `τ_G(a, b) ≤ τ_{G/S}(a, b)` for a vertex
separator `S`. -/
theorem separator_wiring (β : V → V → ℝ) (hβ : ∀ i j, β i j = β j i) (hβ0 : ∀ i j, 0 ≤ β i j)
    (a b : V) (S : Finset V) (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : (suppGraph β hβ).Walk a b, ∃ v ∈ p.support, v ∈ S) :
    H02.arborealProb β hβ (fun F => F.Reachable a b) ≤
      H02.arborealProb (mapW β (collapse S)) (mapW_symm hβ (collapse S))
        (fun F => F.Reachable (collapse S a) (collapse S b)) :=
  separator_wiring_aux hβ hβ0 ha hb hsep
    (fun v => ArborealDecay.ForestPoly.forestPolynomial_isMultiAffine β hβ hβ0 v)
    (ArborealDecay.ForestPoly.forestPolynomial_isRealStable β hβ hβ0)

end

end ArborealDecay.Wiring
