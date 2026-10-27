import Step2.Last.LastNBlock
import Step2.Map.Hol

/-!
# The last step `j = N - 1`: second-order expansion and holomorphy

Copies of `Step2.Map.Second` and `Step2.Map.Hol` for the map of `Step2.Last.LastNDefs`:

* `IpN_exp`: `I_N(B)(tV, t²𝒲) = 1 - t V'_B + t² (V'_B²/2 + S(B)) + O(t³)`. This is the same
  expansion as `Ip_exp` for the map with localisation, since there the `Loc S` terms cancel at
  second order; hence `D1`, `D2` and their expectations are those of `Step2.Map.Second`;
* `KN_expansion`: `K_N(tV, t²𝒲, 0)(U) = t² K^{(2)}(U) + O(t³)` for nonempty `U`;
* `KN_hol`: holomorphy of `K_N(U)` in holomorphic families of coordinates.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

namespace LastN

section Scale

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {V : Fam d L N} (W : Fam d L N)

theorem upN_scale (t : ℂ) (b : Fin d → ℕ) :
    upN C (Vt V t) b = t * ε (Vpr C V b : Alg d L N) := by
  rw [upN, Vpr_scale, ε_smulE]

theorem IpN_exp (b : Fin d → ℕ) :
    ExpE2 (fun t => IpN j C (Vt V t) (Wt W t) b) 1 (-Vpr C V b)
      ((1 / 2 : ℂ) • Vpr C V b ^ 2 + Sb j C V W b) := by
  set a : ℂ := ε (Vpr C V b : Alg d L N)
  set V' := Vpr C V b
  have hVp : ∀ t, -VpN C (Vt V t) b = t • (-(V' - algebraMap ℂ _ a)) := by
    intro t
    rw [VpN, Vpr_scale, upN_scale]
    simp only [smul_eq_alg, map_mul]
    ring
  have h1 : ExpE2 (fun t => -VpN C (Vt V t) b) 0 (-(V' - algebraMap ℂ _ a)) 0 :=
    (ExpE2.lin _).congr hVp
  have h2 := ExpE2.gexp h1 (fun t => by
    have := ε_VpN C (Vt V t) b
    simp [this])
  have h3 : ExpE2 (fun t => 1 + Sb j C (Vt V t) (Wt W t) b) 1 0 (Sb j C V W b) :=
    (((ExpE2.const 1).add (ExpE2.quad (Sb j C V W b))).congr fun t => by
      simp [Sb_scale]).coeffs (by simp) (by simp) (by simp)
  have h4 : ExpS2 (fun t => -upN C (Vt V t) b) 0 (-a) 0 :=
    OrdS.congr (OrdS.zero 3) fun t => by beta_reduce; rw [upN_scale]; ring
  have h5 := (ExpS2.exp h4).congr (ψ := fun t => Complex.exp (-upN C (Vt V t) b))
    fun t => rfl
  have := ExpE2.smulS h5 (h2.mul h3)
  refine (this.congr fun t => rfl).coeffs ?_ ?_ ?_
  · simp
  · simp only [smul_eq_alg, map_neg, map_one, one_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  · have hh : algebraMap ℂ (EvR (Lam d L N)) (1 / 2) * 2 = 1 := by
      rw [show (2 : EvR (Lam d L N)) = algebraMap ℂ _ 2 from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    simp only [show ((-a) ^ 2 / 2 : ℂ) = a ^ 2 * (1 / 2) by ring]
    simp only [smul_eq_alg, map_neg, map_one, one_mul, mul_one, mul_zero, add_zero, zero_add,
      map_add, map_pow, map_mul]
    linear_combination (V' * algebraMap ℂ (EvR (Lam d L N)) a -
      algebraMap ℂ (EvR (Lam d L N)) a ^ 2) * hh

theorem dIN_exp (hV : ∀ b, ε (V b : Alg d L N) = 0) (b : Fin d → ℕ) :
    ExpE2 (fun t => gdI (Ib (Vt V t) (Wt W t)) (IpN j C (Vt V t) (Wt W t)) b) 0
      (D1 C V b) (D2 j C V W b) := by
  have h1 := (Ib_exp W hV b).mapA thetaE
  have h2 := (IpN_exp j C (V := V) W b).mapA inclE
  exact ((h1.sub h2).congr fun t => rfl).coeffs (by simp) (by simp [D1]) (by simp [D2])

theorem uXN_exp (U : Finset (Lam d L N)) :
    ∃ a₁ a₂, ExpS2 (fun t => Complex.exp (uXN j C (Vt V t) U)) 1 a₁ a₂ := by
  have h : ExpS2 (fun t => uXN j C (Vt V t) U)
      (∑ b ∈ blocks j U, (0 : ℂ))
      (∑ b ∈ blocks j U, ε (Vpr C V b : Alg d L N))
      (∑ b ∈ blocks j U, (0 : ℂ)) := by
    refine (ExpS2.sum _ fun b _ => ?_).congr fun t => rfl
    exact OrdS.congr (OrdS.zero 3) fun t => by beta_reduce; rw [upN_scale]; ring
  rw [sum_const_zero] at h
  exact ⟨_, _, ExpS2.exp h⟩

theorem prefN_exp (U X : Finset (Lam d L N)) :
    ∃ P₁ P₂, ExpE2 (fun t => Complex.exp (uXN j C (Vt V t) U) •
      bpow j (IpN j C (Vt V t) (Wt W t)) (U \ X)) 1 P₁ P₂ := by
  obtain ⟨a₁, a₂, ha⟩ := uXN_exp j C (V := V) U
  obtain ⟨P₁, P₂, hP⟩ := ExpE2.prod_one (blocks j (U \ X))
    (f := fun b t => IpN j C (Vt V t) (Wt W t) b) fun b _ => ⟨_, _, IpN_exp j C W b⟩
  exact ⟨_, _, ((ExpE2.smulS ha hP).congr fun t => rfl).coeffs (by simp) rfl rfl⟩

theorem E_dIPowN_exp (hV : ∀ b, ε (V b : Alg d L N) = 0) {X : Finset (Lam d L N)}
    (hX : X.Nonempty) :
    ExpE2 (fun t => ECCE C (gdIPow j (Ib (Vt V t) (Wt W t)) (IpN j C (Vt V t) (Wt W t)) X))
      0 0 (k2 j C V X) := by
  have hb : ∀ b, ExpE2 (fun t => gdI (Ib (Vt V t) (Wt W t)) (IpN j C (Vt V t) (Wt W t)) b) 0
      (D1 C V b) (D2 j C V W b) := dIN_exp j C W hV
  have hne : nb j X ≠ 0 := by
    intro h
    rw [nb, card_eq_zero] at h
    obtain ⟨x, hx⟩ := hX
    exact notMem_empty _ (h ▸ blk_mem_blocks hx)
  by_cases h1 : nb j X = 1
  · obtain ⟨b, hbX⟩ := card_eq_one.1 h1
    have := (hb b).map (ECCE C)
    refine (this.congr fun t => by rw [gdIPow, hbX, prod_singleton]).coeffs (by simp)
      (ECCE_D1 C b).symm ?_
    rw [k2, if_pos h1, hbX, sum_singleton, ECCE_D2]
  by_cases h2 : nb j X = 2
  · obtain ⟨b, b', hbb', hbX⟩ := card_eq_two.1 h2
    have := ((hb b).mul (hb b')).map (ECCE C)
    refine (this.congr fun t => by rw [gdIPow, hbX, prod_pair hbb']).coeffs (by simp)
      (by simp) ?_
    have e1 : ({b, b'} : Finset (Fin d → ℕ)).erase b = {b'} := by
      ext c; simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hc, hc' | hc'⟩
        · exact absurd hc' hc
        · exact hc'
      · rintro rfl; exact ⟨fun h => hbb' h.symm, Or.inr rfl⟩
    have e2 : ({b, b'} : Finset (Fin d → ℕ)).erase b' = {b} := by
      ext c; simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hc, hc' | hc'⟩
        · exact hc'
        · exact absurd hc' hc
      · rintro rfl; exact ⟨hbb', Or.inl rfl⟩
    rw [k2, if_neg h1, if_pos h2, hbX, sum_pair hbb', e1, e2, sum_singleton, sum_singleton,
      FCE_comm C (Vpr C V b')]
    simp only [mul_zero, zero_mul, add_zero, zero_add, ECCE_D1_mul]
    module
  · have h3 : 3 ≤ nb j X := by omega
    have hO : OrdE 3 (fun t => gdIPow j (Ib (Vt V t) (Wt W t)) (IpN j C (Vt V t) (Wt W t)) X) :=
      OrdE.mono h3 (OrdE.prod (blocks j X) fun b _ => (hb b).ord1)
    refine ((ExpE2.of_ord3 hO).map (ECCE C)).coeffs (by simp) (by simp) ?_
    rw [k2, if_neg h1, if_neg h2, map_zero]

/-- **The second-order part of `K_N`**: for `K = 0` and the coordinates `(t V, t² 𝒲)`,
`K_N(U) = t² K^{(2)}(U) + O(t³)` for every nonempty `U`. -/
theorem KN_expansion (hV : ∀ b, ε (V b : Alg d L N) = 0) {U : Finset (Lam d L N)}
    (hU : U.Nonempty) :
    ExpE2 (fun t => KN j C (Vt V t) (Wt W t) 0 U) 0 0 (K2 j C V U) := by
  classical
  have hterm : ∀ X ∈ (Pj j univ).filter (fun X => clo j X = U),
      ExpE2 (fun t => (Complex.exp (uXN j C (Vt V t) U) •
          bpow j (IpN j C (Vt V t) (Wt W t)) (U \ X)) *
        ECCE C (gdIPow j (Ib (Vt V t) (Wt W t)) (IpN j C (Vt V t) (Wt W t)) X))
        0 0 (k2 j C V X) := by
    intro X hX
    have hXne : X.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      rw [(mem_filter.1 hX).2.symm, clo_empty] at hU
      exact not_nonempty_empty hU
    obtain ⟨P₁, P₂, hP⟩ := prefN_exp j C W U X
    exact (hP.mul (E_dIPowN_exp j C W hV hXne)).coeffs (by simp) (by simp) (by simp)
  have := ExpE2.sum _ hterm
  refine (this.congr fun t => ?_).coeffs (by simp) (by simp) (by rw [K2])
  rw [KN, gKnext_zero, smul_sum]
  refine sum_congr rfl fun X _ => ?_
  rw [smul_mul_assoc]

end Scale

/-! ### Holomorphy -/

section Hol

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) {Vf Wf : E → Fam d L N}
  {Kf : E → Act d L N} (hVf : ∀ b, HolE (fun e => Vf e b)) (hWf : ∀ b, HolE (fun e => Wf e b))
  (hKf : ∀ X, HolE (fun e => Kf e X))

include hVf in
theorem upN_diff (b : Fin d → ℕ) : Differentiable ℂ (fun e => upN C (Vf e) b) :=
  (Vpr_hol C hVf b).ε

include hVf in
theorem VpN_hol (b : Fin d → ℕ) : HolE (fun e => VpN C (Vf e) b) :=
  (Vpr_hol C hVf b).sub (HolE.algMap (upN_diff C hVf b))

include hVf hWf in
theorem IpN_hol (b : Fin d → ℕ) : HolE (fun e => IpN j C (Vf e) (Wf e) b) :=
  HolE.smul ((upN_diff C hVf b).neg.cexp)
    (((VpN_hol C hVf b).neg.gexp fun e => by
      rw [NegMemClass.coe_neg, map_neg, ε_VpN, neg_zero]).mul
      ((HolE.const 1).add (Sb_hol j C hVf hWf b)))

include hVf in
theorem uXN_diff (X : Finset (Lam d L N)) : Differentiable ℂ (fun e => uXN j C (Vf e) X) :=
  Differentiable.fun_sum fun b _ => upN_diff C hVf b

include hVf hWf hKf in
/-- **Holomorphy of `K_N`.** -/
theorem KN_hol (hV0 : ∀ e b, ε (Vf e b : Alg d L N) = 0) (U : Finset (Lam d L N)) :
    HolE (fun e => KN j C (Vf e) (Wf e) (Kf e) U) :=
  HolE.smul (uXN_diff j C hVf U).cexp
    (gKnext_hol j C hKf (Ib_hol hVf hWf hV0) (IpN_hol j C hVf hWf) (J2_hol j hKf) U)

end Hol

end LastN

end

end Step2
