import Step.EstNonlinAux

/-!
# The non-linear part (Section `sec:K-nonlinear`)

Lemmas `lem:NonlinearCheckK` and `lem:Ri-bd`, hence Proposition `prop:K-linear-nonlinear`:
`‖K_{j+1} - 𝓛_{j+1}‖_{j+1} ≤ A^ν O(‖K_j‖_j (‖K_j‖_j + ‖V_j‖_j))`, with `ν = 2^{d+3}`.

The paper refers to the proof of Lemma 6.17 of MR2523458 for the combinatorial sum over
`𝒢_2(U)`; it is proved here directly (in `Step.EstNonlinAux`), crudely:

* `𝓡^1`: by `∑_X J(B, X) = 0` (`J_zero`), `𝓡^1(U)` is a sum of terms
  `e^{u|U|} e^{-(u+V)(U ∖ X)} (1 - e^{-(u+V)(X)}) 𝔼 θ J(B, X)` (`R1_eq`), each `O(‖V‖+‖K‖) ‖K‖`,
  and `U = \bar{B^□}` is small.
* `𝓡^2`, `𝓡^3`: the integrand is bounded by `κ β^{m-1} (4/A)^{|𝓑_j(X̌)|}` with
  `m = |𝒳| + |Comp(X̌)| ≥ 2`, `κ = O(A^{2^d} ‖K‖)`, `β = O(A^{2^d} (‖V‖ + ‖K‖))`
  (Lemma `lem:NonlinearCheckK`, `KHyp.KchkC_bounds`, `KHyp.R2_integrand_le`).  Lemma `lem:comb1`
  gives `(1+2η) |𝓑_{j+1}(U)| ≤ |𝓑_j(X̌)| + (1+2η) 2^d m` (`nU_bound`), so the weight
  `A^{|𝓑_{j+1}(U)|}` is absorbed by `A^{-|𝓑_j(X̌)|}` up to `A^{2^d m}` (`geom_real`), and the
  number `|𝒢(U)| ≤ 2^{(1+c) L^d |𝓑_{j+1}(U)|}` of summands (`card_Gset_le`) by
  `A^{-2η/(1+2η)}` per `j`-block (for `A ≥ A₀(L)`) and by the smallness of `β` per factor
  (for `ε₀ = ε₀(L, A)`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD


/-- Consequences of the smallness of `ε₀`. -/
theorem eps_facts {d : ℕ} {C₀B C₁ C₀J L' A D ε₀ vr kr : ℝ} (hC₀B : 0 ≤ C₀B) (hC₁ : 0 ≤ C₁)
    (hC₀J : 0 ≤ C₀J) (hL' : 0 < L') (hA : 1 ≤ A) (hD : 0 ≤ D) (hv : 0 ≤ vr) (hk : 0 ≤ kr)
    (hvk : vr + kr ≤ ε₀) (e2 : ε₀ ≤ 1 / (40 * (1 + C₀B))) (e3 : ε₀ ≤ 1 / (8 * (1 + C₀B) * L'))
    (e4 : ε₀ ≤ 1 / A ^ 2 ^ d) (e5 : ε₀ ≤ 1 / (C₁ * A + 1))
    (e6 : ε₀ ≤ 1 / (D * ((1 + 2 ^ d * C₀J) * A ^ 2 ^ d + C₁ * A) + 1)) :
    vr + C₀B * kr ≤ 1 / 40 ∧ 4 * (vr + C₀B * kr) * L' ≤ 1 / 2 ∧ A ^ 2 ^ d * kr ≤ 1 ∧
      C₁ * (vr + kr) * A ≤ 1 ∧
      D * ((1 + 2 ^ d * C₀J) * (A ^ 2 ^ d * kr) + C₁ * (vr + kr) * A) ≤ 1 := by
  have hA0 : 0 < A := by linarith
  have hε : 0 ≤ ε₀ := le_trans (by positivity) hvk
  have hAd : 0 < A ^ 2 ^ d := by positivity
  set t := vr + kr with ht
  set G := (1 + 2 ^ d * C₀J) * A ^ 2 ^ d + C₁ * A with hG
  have hG0 : 0 ≤ G := by positivity
  have f2 := (le_div_iff₀ (by positivity)).1 e2
  have f3 := (le_div_iff₀ (by positivity)).1 e3
  have f4 := (le_div_iff₀ (by positivity)).1 e4
  have f5 := (le_div_iff₀ (by positivity)).1 e5
  have f6 := (le_div_iff₀ (by positivity)).1 e6
  have h0 : vr + C₀B * kr ≤ (1 + C₀B) * ε₀ := by
    have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hv : kr ≤ vr + kr) hC₀B
    have := mul_le_mul_of_nonneg_left hvk hC₀B
    nlinarith
  have hkε : kr ≤ ε₀ := by linarith
  refine ⟨by nlinarith, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right h0 hL'.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left hkε hAd.le
    nlinarith
  · have := mul_le_mul_of_nonneg_left hvk (by positivity : (0 : ℝ) ≤ C₁ * A)
    nlinarith
  · have hb : (1 + 2 ^ d * C₀J) * (A ^ 2 ^ d * kr) + C₁ * t * A ≤ G * ε₀ := by
      have h1 := mul_le_mul_of_nonneg_left hkε (by positivity : (0 : ℝ) ≤ (1 + 2 ^ d * C₀J) * A ^ 2 ^ d)
      have h2 := mul_le_mul_of_nonneg_left hvk (by positivity : (0 : ℝ) ≤ C₁ * A)
      rw [hG]; nlinarith
    have := mul_le_mul_of_nonneg_left hb hD
    nlinarith

/-- The final real inequality. -/
theorem final_real {d : ℕ} {A P C₀B C₁ C₀J vr kr : ℝ} (hA1 : 1 ≤ A) (hP1 : 1 ≤ P)
    (hPA : P ^ 2 ^ (d + 1) ≤ A) (hC₀B : 0 ≤ C₀B) (hC₁ : 0 ≤ C₁) (hC₀J : 0 ≤ C₀J) (hv0 : 0 ≤ vr)
    (hk0 : 0 ≤ kr) :
    (A * P) ^ 2 ^ d * (2 ^ d * (10 * (vr + C₀B * kr)) * 2 ^ 2 ^ d) *
        (C₀J * (A ^ 2 ^ d * kr) * A⁻¹ ^ 2 ^ d) +
      ((A * P) ^ 2 ^ d) ^ 2 * ((1 + 2 ^ d * C₀J) * (A ^ 2 ^ d * kr) *
        ((1 + 2 ^ d * C₀J) * (A ^ 2 ^ d * kr) + C₁ * (vr + kr) * A)) +
      (A * P) ^ 2 ^ d * ((A ^ 2 ^ d * kr) * (C₁ * (vr + kr) * A)) ≤
    ((1 + 2 ^ d * C₀J) * (1 + 2 ^ d * C₀J + C₁) + C₁ + 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J) *
      A ^ (((2 ^ (d + 3) : ℕ) : ℝ)) * kr * (kr + vr) := by
  have hA0 : 0 < A := by linarith
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  rw [Real.rpow_natCast]
  set X := A ^ 2 ^ d with hX
  set T := kr * (kr + vr) with hT
  have hT0 : 0 ≤ T := by positivity
  have hX1 : 1 ≤ X := one_le_pow₀ hA1
  have hX0 : 0 < X := by linarith
  have hAX : A ≤ X := le_self_pow₀ hA1 (by positivity)
  have hPd : P ^ 2 ^ d ≤ A :=
    (pow_le_pow_right₀ hP1 (Nat.pow_le_pow_right (by norm_num) (by omega))).trans hPA
  have hP2 : (P ^ 2 ^ d) ^ 2 ≤ A := by
    rw [← pow_mul]; exact (pow_le_pow_right₀ hP1 (le_of_eq (pow_succ 2 d).symm)).trans hPA
  have hD1 : (A * P) ^ 2 ^ d ≤ X * A := by rw [hX, mul_pow]; gcongr
  have hD2 : ((A * P) ^ 2 ^ d) ^ 2 ≤ X ^ 2 * A := by
    rw [hX, mul_pow, mul_pow]; gcongr
  have hpow : ∀ e : ℕ, e ≤ 2 ^ (d + 3) → A ^ e ≤ A ^ (2 ^ (d + 3)) :=
    fun e he => pow_le_pow_right₀ hA1 he
  have p2d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have q1 : X ^ 4 * A ≤ A ^ (2 ^ (d + 3)) := by
    rw [hX, ← pow_mul, ← pow_succ]; exact hpow _ (by omega)
  have q2 : X ^ 2 * A ^ 2 ≤ A ^ (2 ^ (d + 3)) := by
    rw [hX, ← pow_mul, ← pow_add]; exact hpow _ (by omega)
  have q3 : X * A ≤ A ^ (2 ^ (d + 3)) := by
    rw [hX, ← pow_succ]; exact hpow _ (by omega)
  set Z := A ^ (2 ^ (d + 3)) with hZ
  set c₂ := (1 + 2 ^ d * C₀J) * (1 + 2 ^ d * C₀J + C₁) with hc₂
  have hQ2 : ((A * P) ^ 2 ^ d) ^ 2 * ((1 + 2 ^ d * C₀J) * (X * kr) *
        ((1 + 2 ^ d * C₀J) * (X * kr) + C₁ * (vr + kr) * A)) ≤ c₂ * Z * T := by
    have hb1 : (1 + 2 ^ d * C₀J) * (X * kr) + C₁ * (vr + kr) * A ≤
        (1 + 2 ^ d * C₀J + C₁) * X * (kr + vr) := by
      have h1 := mul_le_mul_of_nonneg_left hAX (by positivity : (0 : ℝ) ≤ C₁ * (vr + kr))
      have h2 : kr ≤ kr + vr := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (1 + 2 ^ d * C₀J) * X)
      nlinarith
    calc ((A * P) ^ 2 ^ d) ^ 2 * ((1 + 2 ^ d * C₀J) * (X * kr) *
          ((1 + 2 ^ d * C₀J) * (X * kr) + C₁ * (vr + kr) * A))
        ≤ (X ^ 2 * A) * ((1 + 2 ^ d * C₀J) * (X * kr) *
          ((1 + 2 ^ d * C₀J + C₁) * X * (kr + vr))) := by gcongr
      _ = c₂ * (X ^ 4 * A) * T := by rw [hc₂, hT]; ring
      _ ≤ c₂ * Z * T := by gcongr
  have hQ3 : (A * P) ^ 2 ^ d * ((X * kr) * (C₁ * (vr + kr) * A)) ≤ C₁ * Z * T := by
    calc (A * P) ^ 2 ^ d * ((X * kr) * (C₁ * (vr + kr) * A))
        ≤ (X * A) * ((X * kr) * (C₁ * (vr + kr) * A)) := by gcongr
      _ = C₁ * (X ^ 2 * A ^ 2) * T := by rw [hT]; ring
      _ ≤ C₁ * Z * T := by gcongr
  have hQ1 : (A * P) ^ 2 ^ d * (2 ^ d * (10 * (vr + C₀B * kr)) * 2 ^ 2 ^ d) *
        (C₀J * (X * kr) * A⁻¹ ^ 2 ^ d) ≤ 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J * Z * T := by
    have hk' : X * kr * A⁻¹ ^ 2 ^ d = kr := by
      rw [hX, inv_pow, mul_comm (A ^ 2 ^ d) kr, mul_assoc, mul_inv_cancel₀ (by positivity),
        mul_one]
    have ha' : vr + C₀B * kr ≤ (1 + C₀B) * (kr + vr) := by
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv0 : kr ≤ kr + vr) hC₀B
      nlinarith
    calc (A * P) ^ 2 ^ d * (2 ^ d * (10 * (vr + C₀B * kr)) * 2 ^ 2 ^ d) *
          (C₀J * (X * kr) * A⁻¹ ^ 2 ^ d)
        = (A * P) ^ 2 ^ d * (2 ^ d * (10 * (vr + C₀B * kr)) * 2 ^ 2 ^ d) * (C₀J * kr) := by
          rw [mul_assoc C₀J, hk']
      _ ≤ (X * A) * (2 ^ d * (10 * ((1 + C₀B) * (kr + vr))) * 2 ^ 2 ^ d) * (C₀J * kr) := by
          gcongr
      _ = 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J * (X * A) * T := by rw [hT]; ring
      _ ≤ 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J * Z * T := by gcongr
  have e : (c₂ + C₁ + 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J) * Z * kr * (kr + vr) =
      c₂ * Z * T + C₁ * Z * T + 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J * Z * T := by
    rw [hT]; ring
  rw [e]
  linarith


set_option maxHeartbeats 1000000 in
/-- **Lemma `lem:Ri-bd`** for `𝓡^1 + 𝓡^2 + 𝓡^3`. Here `ν` depends only on `d`. -/
theorem nonlinear_bound {d : ℕ} (hd : 3 ≤ d) : ∃ (C₀ ν : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < ν ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (N j : ℕ), j < N → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
    ∀ (C : Matrix (Lam d L N) (Lam d L N) ℝ), GoodCov j ℓ₀ C →
    ∀ (V : Vcoup) (K : Act d L N), InK j K →
      Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V + Knorm j (ellj d L ℓ₀ j) A K ≤ ENNReal.ofReal ε₀ →
      ∀ U : Finset (Lam d L N), IsConn (j + 1) U →
        wnorm (j + 1) (ellj d L ℓ₀ (j + 1)) A U (R1 j C V K U + R2 j C V K U + R3 j C V K U) ≤
          ENNReal.ofReal (C₀ * A ^ ν) * Knorm j (ellj d L ℓ₀ j) A K *
            (Knorm j (ellj d L ℓ₀ j) A K + Vnorm (d := d) (L := L) (N := N) j (ellj d L ℓ₀ j) V) := by
  obtain ⟨C₀B, LB, hC₀B, hLB, hbr⟩ := block_real hd
  obtain ⟨C₁, ε₁, Ld, hC₁, hε₁, -, hdIb⟩ := dI_bounds hd
  obtain ⟨C₀J, LJ, hC₀J, -, hJb⟩ := thetaJ_bounds hd
  obtain ⟨η, hη0, hη1, hcomb⟩ := comb2 d
  obtain ⟨c, hc⟩ := card_small_containing d
  set c₂ : ℝ := (1 + 2 ^ d * C₀J) * (1 + 2 ^ d * C₀J + C₁) with hc₂
  set Cf : ℝ := c₂ + C₁ + 2 ^ d * 10 * (1 + C₀B) * 2 ^ 2 ^ d * C₀J with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf, hc₂]; positivity
  refine ⟨Cf, ((2 ^ (d + 3) : ℕ) : ℝ), max LB (max Ld LJ), hCf0, by positivity, ?_⟩
  intro L _ hL
  have hLB' : LB ≤ L := le_trans (le_max_left _ _) hL
  have hLd' : Ld ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLJ' : LJ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL4 : (4 : ℝ) ≤ L := four_le_of_L₀ (hLB.trans hLB')
  have hL0 : (0 : ℝ) < L := by linarith
  have hd8 : 2 ^ (d + 3) = 2 ^ d * 8 := by ring
  have hd4 : 2 ^ (d + 2) = 2 ^ d * 4 := by ring
  have hLL := hLB.trans hLB'
  have hL2 : 2 ^ (d + 2) ≤ L := by
    rw [hd8] at hLL; rw [hd4]; generalize 2 ^ d = t at hLL ⊢; omega
  have hL1 : 2 ^ d + 1 ≤ L := by
    rw [hd8] at hLL; generalize 2 ^ d = t at hLL ⊢; omega
  set M : ℕ := 2 ^ ((1 + c) * L ^ d) with hMdef
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  set P : ℝ := 2 * M with hPdef
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hP0 : 0 < P := by linarith
  have hη2 : 2 * η ≠ 0 := by positivity
  have hη3 : 1 + 2 * η ≠ 0 := by positivity
  have hη' : 0 < 2 * η / (1 + 2 * η) := by positivity
  set A₀ : ℝ := max (P ^ 2 ^ (d + 1)) ((4 * P) ^ ((1 + 2 * η) / (2 * η))) with hA₀
  have hA₀1 : 1 ≤ A₀ := le_trans (one_le_pow₀ hP1) (le_max_left _ _)
  refine ⟨A₀, hA₀1, ?_⟩
  intro A hA
  have hA1 : 1 ≤ A := hA₀1.trans hA
  have hA0 : 0 < A := by linarith
  have hA0' : A ≠ 0 := hA0.ne'
  have hAd : A ^ 2 ^ d ≠ 0 := by positivity
  have hPA : P ^ 2 ^ (d + 1) ≤ A := le_trans (le_max_left _ _) hA
  have hAP : 4 * P ≤ A ^ (2 * η / (1 + 2 * η)) := by
    calc 4 * P = ((4 * P) ^ ((1 + 2 * η) / (2 * η))) ^ (2 * η / (1 + 2 * η)) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show (1 + 2 * η) / (2 * η) * (2 * η / (1 + 2 * η)) = 1 by field_simp]
          rw [Real.rpow_one]
      _ ≤ A ^ (2 * η / (1 + 2 * η)) :=
          Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hA) hη'.le
  set D : ℝ := (A * P) ^ 2 ^ d with hD
  have hD0 : 0 < D := by positivity
  set G : ℝ := (1 + 2 ^ d * C₀J) * A ^ 2 ^ d + C₁ * A with hG
  have hG0 : 0 ≤ G := by positivity
  set ε₀ : ℝ := min ε₁ (min (1 / (40 * (1 + C₀B))) (min (1 / (8 * (1 + C₀B) * (L : ℝ) ^ d))
    (min (1 / A ^ 2 ^ d) (min (1 / (C₁ * A + 1)) (1 / (D * G + 1)))))) with hε₀
  have hε₀0 : 0 < ε₀ := by
    refine lt_min hε₁ (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))))
  refine ⟨ε₀, hε₀0, ?_⟩
  intro N j hj ℓ₀ hℓ₀ C hC V K hK hvk U hU
  classical
  obtain ⟨hv, hk, hv0, hk0, hvkr, hblk⟩ :=
    hbr L hLB' N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK ε₀ hε₀0.le hvk
  set ℓ := ellj d L ℓ₀ j with hℓdef
  set ℓ' := ellj d L ℓ₀ (j + 1) with hℓ'def
  set vr := (Vnorm (d := d) (L := L) (N := N) j ℓ V).toReal with hvr
  set kr := (Knorm j ℓ A K).toReal with hkr
  have e1 : ε₀ ≤ ε₁ := min_le_left _ _
  have e2 : ε₀ ≤ 1 / (40 * (1 + C₀B)) := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε₀ ≤ 1 / (8 * (1 + C₀B) * (L : ℝ) ^ d) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε₀ ≤ 1 / A ^ 2 ^ d :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : ε₀ ≤ 1 / (C₁ * A + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have e6 : ε₀ ≤ 1 / (D * G + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  obtain ⟨ha1, ha2, hκ₀1, hδ₁1, hDβ⟩ := eps_facts (d := d) hC₀B hC₁ hC₀J hLd hA1 hD0.le hv0 hk0
    hvkr e2 e3 e4 e5 (by rw [hG] at e6; exact e6)
  set a := vr + C₀B * kr with ha
  have ha0 : 0 ≤ a := by positivity
  set κ₀ := A ^ 2 ^ d * kr with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  set δ₁ := C₁ * (vr + kr) * A with hδ₁
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  -- the norms
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hh' : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by positivity
  have hℓ0 : 0 < ℓ := ellj_pos hL0 hℓ₀ j
  have hℓ'0 : 0 < ℓ' := ellj_pos hL0 hℓ₀ (j + 1)
  have hvk' : Vnorm (d := d) (L := L) (N := N) j ℓ V + Knorm j ℓ A K ≤ ENNReal.ofReal ε₁ :=
    hvk.trans (ENNReal.ofReal_le_ofReal e1)
  have H : KHyp j C V K ((L : ℝ) ^ j) ℓ ((L : ℝ) ^ (j + 1)) ℓ' A κ₀ δ₁ C₀J :=
    { hh := hh, hℓ := hℓ0, hh' := hh', hℓ' := hℓ'0, hA := hA1, hκ₀ := by positivity,
      hκ₀1 := hκ₀1, hδ₁ := by positivity, hδ₁1 := hδ₁1, hcJ := hC₀J
      hθ := fun F => (tNorm_theta_le hh' hℓ'0 F).trans (Tj_succ_le hd hL4 hℓ₀ j F).2
      hK := fun W hW => by
        have hw := wnorm_le_Knorm (ℓ := ℓ) (A := A) (K := K) hW
        rw [wnorm, hk] at hw
        set n := nb j W
        have hAn : (1 : ℝ) ≤ A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d) := by
          have h1 : A ^ n ≤ A ^ 2 ^ d * A ^ (n - 2 ^ d) := by
            rw [← pow_add]; exact pow_le_pow_right₀ hA1 (by omega)
          have hAn0 : 0 < A ^ n := by positivity
          rw [inv_pow]
          calc (1 : ℝ) = A ^ n * (A ^ n)⁻¹ := (mul_inv_cancel₀ hAn0.ne').symm
            _ ≤ (A ^ 2 ^ d * A ^ (n - 2 ^ d)) * (A ^ n)⁻¹ := by gcongr
            _ = _ := by ring
        calc tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (K W : Alg d L N)
            ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n * A ^ (n - 2 ^ d)) *
                tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (K W : Alg d L N) := by
              refine le_mul_of_one_le_left zero_le ?_
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hAn
          _ = ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * (ENNReal.ofReal (A ^ (n - 2 ^ d)) *
                tNorm (Dir d) (pPhi d) ((L : ℝ) ^ j) ℓ (K W : Alg d L N)) := by
              rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
          _ ≤ ENNReal.ofReal (A ^ 2 ^ d * A⁻¹ ^ n) * ENNReal.ofReal kr := by gcongr
          _ = ENNReal.ofReal (κ₀ * A⁻¹ ^ n) := by
              rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      hdI := fun b hb => by
        refine (hdIb L hLd' N j hj ℓ₀ hℓ₀ C hC V K A hA1 hK hvk' b hb).1.trans (le_of_eq ?_)
        rw [hv, hk, ← ENNReal.ofReal_add hv0 hk0, ← ENNReal.ofReal_mul hC₁]
        congr 1; rw [hδ₁, mul_assoc, mul_inv_cancel₀ hA0', mul_one]
      hJ := fun b hb X => by
        refine ((hJb L hLJ' N j hj ℓ₀ hℓ₀ C hC K A hA1 hK b hb).1 X).1.trans (le_of_eq ?_)
        rw [hk, ← ENNReal.ofReal_mul hC₀J]
        congr 1; rw [hκ₀, inv_pow]; field_simp }
  have hUj : IsPolymer j U := IsPolymer.of_succ hU.1
  have R : RHyp j C V K U ((L : ℝ) ^ j) ℓ ((L : ℝ) ^ (j + 1)) ℓ' A κ₀ δ₁ C₀J a η P M :=
    { H with
      hE := fun F => tNorm_EC_le hh' hℓ'0 hC.psd hC.norm F
      hU := hU.1
      ha := ha0
      ha1 := ha1
      hu := fun b hb => (hblk b hb).2.1
      hV := fun b hb => (hblk b hb).2.2
      hpref := by
        have hnb : (nb j U : ℝ) ≤ (L : ℝ) ^ d * nb (j + 1) U := by
          exact_mod_cast nb_le_of_succ hU.1
        have hx : 4 * a * nb j U ≤ (nb (j + 1) U : ℝ) * (1 / 2) := by
          have : 4 * a * nb j U ≤ 4 * a * ((L : ℝ) ^ d * nb (j + 1) U) := by gcongr
          nlinarith [mul_le_mul_of_nonneg_right ha2 (Nat.cast_nonneg (α := ℝ) (nb (j + 1) U))]
        have he : Real.exp (1 / 2) ≤ 2 := by
          have := (abs_le.1 (Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num))).2
          norm_num at this ⊢; linarith
        calc Real.exp (4 * a * nb j U) ≤ Real.exp ((nb (j + 1) U : ℝ) * (1 / 2)) :=
              Real.exp_le_exp.2 hx
          _ = Real.exp (1 / 2) ^ nb (j + 1) U := Real.exp_nat_mul _ _
          _ ≤ 2 ^ nb (j + 1) U := pow_le_pow_left₀ (Real.exp_pos _).le he _
      hcount := by
        refine (card_Gset_le (fun b hb => hc L N j b hb) hUj).trans ?_
        rw [hMdef, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (nb_le_of_succ hU.1))
      hη := hη0.le
      hgeom := fun g hg => nU_bound (fun X hX => (hcomb L hL1 N j X hj hX).1)
        (fun b hb => (isSmall_clo_nbhd (by omega) hL2 hj b hb).2.2) hη0.le hg
      hP := rfl
      hM := hM1
      hAP := hAP }
  have b1 := R.R1_le
  have b2 := R.R2_le hDβ
  have b3 := R.R3_le
  -- assemble
  have hsplit : wnorm (j + 1) ℓ' A U (R1 j C V K U + R2 j C V K U + R3 j C V K U) ≤
      ENNReal.ofReal (A ^ nb (j + 1) U) *
        (tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' (R1 j C V K U : Alg d L N) +
          tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' (R2 j C V K U : Alg d L N) +
          tNorm (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' (R3 j C V K U : Alg d L N)) := by
    rw [wnorm]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hA1 (Nat.sub_le _ _))) ?_
    rw [AddMemClass.coe_add, AddMemClass.coe_add]
    exact (tNorm_add_le _ _).trans (add_le_add (tNorm_add_le _ _) le_rfl)
  refine hsplit.trans ?_
  rw [mul_add, mul_add]
  refine (add_le_add (add_le_add b1 b2) b3).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), hk, hv,
    ← ENNReal.ofReal_add hk0 hv0, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (final_real (d := d) hA1 hP1 hPA hC₀B hC₁ hC₀J hv0 hk0)

end

end Step
