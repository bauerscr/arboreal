import Obs2.Est.EstNorm

/-!
# Block bounds for the observable part of the second-order map (single sources)

The analogue of `Step2.Map.Block` (the block bounds `Vpr_le`, `Sb_le`, `LS_le`, `Q2_le`, `uVp_le`,
`Vp_le`, `Wp_le` of `Step2.BH`) for the **observable components** of the map with sources
(`Obs2.Map.Map`), measured in the observable part `oTo w` of the norm with single-source weights
(`w_ab = 0`, see `Obs2.Est.EstNorm`; the `ab` components are not covered). With bulk radius `r`
(`‖V^∅(B)‖_{T_j(ℓ)} ≤ r`) and observable sizes `m_V, m_W, k`
(`‖V^{obs}(B)‖, ‖𝒲^{obs}(B)‖ ≤ m_V, m_W`, `‖K^{obs}(X)‖ ≤ k` on small sets):

* `Vpr_o`: `‖V'^{obs}_B‖_{T_{j+1}(ℓ')} ≤ Q₁ m_V`;
* `pair_o`: `‖F(V'_B, V'_{B'})^{obs}‖ ≤ 4Q₁² r m_V` (products of two observable parts only feed
  the `ab` component, `FCO_obs_obs_eabZero`);
* `Sb_o`: `‖S(B)^{obs}‖ ≤ 2 c_near Q₁² r m_V + Q₁ m_W` (finite range of `C`);
* `LS_o`: `‖(Loc_{B_+,B} S(B_+))^{obs}‖ ≤ C_l L^d (⋯)`;
* `Q_o`: `‖(𝔼θQ(B))^{obs}‖ ≤ Q₁ q² c_S C_l k` (the pointed `loc^a` puts `Q(B)_a` on
  `B^□ ∪ {a, b}`, `hlocl`, discharged by `LocO2_cmpIn_pts`);
* `uVp_o`, `Vp_o`, `Wp_o`: the observable parts of `(u+V)_{j+1}(B)`, `V_{j+1}(B)`, `𝒲_{j+1}(B)`.

The observable flow is linear in `(m_V, m_W, k)` with coefficients `O(1)` (the `V'` and `K` terms)
and `O(r) = O(ḡ)` (the second-order term): `‖𝒲^{obs}_{j+1}(B)‖ ≤ C(L)(r m_V + m_W)`,
`‖V^{obs}_{j+1}(B)‖ ≤ 2(Q₁ m_V + C k + C(L)(r m_V + m_W))`. The localisation enters only through
the bound `hloc` and the locality `hlocl` (supports `Y^□ ∪ {a, b}`), discharged for the pointed
`LocO2` by `exists_LocO2_obs_bound` and `LocO2_cmpIn_pts` (`Obs2.Est.EstLoc`; `BHO.hlocl_of`, `Obs2.Est.KObs2`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The hypotheses for the observable block bounds at scale `j` (single-source weights). -/
structure BHO (P : ObsPts d L N) (j : ℕ) (ℓ ℓ' ℓC : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam c d L N) (K : OAct c d L N) (w : Wt) (r mV mW k Cl cS : ℝ) : Prop where
  hd : 1 ≤ d
  hLp : pauliL0 d ≤ L
  hL8 : 2 ^ (d + 3) + 8 * d < L
  hjN : j + 1 < N
  hℓ : 0 < ℓ
  hℓ' : 0 < ℓ'
  hℓC : 0 < ℓC
  hsum : ℓ' + ℓC ≤ 2 * ℓ
  hC : Step2.GoodCov2 j ℓC C
  hw : w.Sub
  hw0 : w.ab = 0
  hVl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (V b : SA c (Lam d L N))
  hWl : ∀ b, CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (W b : SA c (Lam d L N))
  hKl : ∀ X, IsSmall j X → CmpIn (nbhd j X : Set (Lam d L N)) (K X : SA c (Lam d L N))
  hr : 0 ≤ r
  hmV : 0 ≤ mV
  hmW : 0 ≤ mW
  hk : 0 ≤ k
  hVr : ∀ b ∈ blockIdx (L := L) (N := N) j,
    Tj d (L : ℝ) j ℓ (V b : SA c (Lam d L N)).e ≤ ENNReal.ofReal r
  hVm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (V b) ≤ ENNReal.ofReal mV
  hWm : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j ℓ (W b) ≤ ENNReal.ofReal mW
  hKk : ∀ X, IsSmall j X → oTo w j ℓ (K X) ≤ ENNReal.ofReal k
  hCl : 0 ≤ Cl
  hloc : ∀ k' : ℕ, k' < N → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → ∀ X Y : Finset (Lam d L N), IsSmall k' X →
    Y ⊆ X → ∀ F : OE c (Lam d L N), CmpIn (nbhd k' X : Set (Lam d L N)) (F : SA c (Lam d L N)) →
      oTo w k' ℓ₀ (LocO2 P X Y F) ≤ ENNReal.ofReal Cl * oTo w k' ℓ₀ F
  hlocl : ∀ X Y : Finset (Lam d L N), IsPolymer j Y → ∀ F : OE c (Lam d L N),
    CmpIn (↑(nbhd j Y ∪ {P.a, P.b}) : Set (Lam d L N)) (LocO2 P X Y F : SA c (Lam d L N))
  hcS : 1 ≤ cS
  hcount : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j,
    (((smallSets (d := d) (L := L) (N := N) j).filter (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS

/-- The observable second-order constant: `‖S(B)^{obs}‖ ≤ sO`. -/
def sO (d L : ℕ) (r mV mW : ℝ) : ℝ :=
  2 * Step2.cNear d L * Step2.Q1 d ^ 2 * (r * mV) + Step2.Q1 d * mW

theorem oTo_FCO_bulk {c : Obs.Case} (w : Wt) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (A B : OE c (Lam d L N)) (j' : ℕ) (ℓ₀ : ℝ) :
    oTo w j' ℓ₀ (FCO C (EthO C (emb (bulk A) : OE c (Lam d L N)))
      (EthO C (emb (bulk B) : OE c (Lam d L N)))) = 0 := by
  rw [EthO_emb, EthO_emb, FCO_emb, oTo_emb]

theorem FCO_eabZero_of_e {c : Obs.Case} (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (X Y : OE c (Lam d L N)) (hX : (X : SA c (Lam d L N)).e = 0)
    (hY : (Y : SA c (Lam d L N)).e = 0) : EabZero (FCO C X Y : SA c (Lam d L N)) := by
  have ht : c.tau (0 : Grassmann.N (Lam d L N)) = 0 := map_zero _
  refine ⟨?_, ?_, ?_⟩
  · rw [FCO_e, hX, FC_zero_left]
  · have := FCO_cmp C true X Y
    simp only [cmp_true] at this
    rw [this, hX, hY, ht, FC_zero_left, FC_zero_right, add_zero]
  · have := FCO_cmp C false X Y
    simp only [cmp_false] at this
    rw [this, hX, hY, ht, FC_zero_left, FC_zero_right, add_zero]

/-- Products of two observable parts only feed the `ab` component. -/
theorem FCO_obs_obs_eabZero {c : Obs.Case} (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (A B : OE c (Lam d L N)) :
    EabZero (FCO C (EthO C (πobs A)) (EthO C (πobs B)) : SA c (Lam d L N)) := by
  refine FCO_eabZero_of_e C _ _ ?_ ?_
  · rw [EthO_e, coe_πobs, piobs_apply]; simp
  · rw [EthO_e, coe_πobs, piobs_apply]; simp

namespace BHO

variable {P : ObsPts d L N} {j : ℕ} {ℓ ℓ' ℓC : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N} {w : Wt} {r mV mW k Cl cS : ℝ}
  (H : BHO P j ℓ ℓ' ℓC C V W K w r mV mW k Cl cS)
include H

theorem hj : j < N := by have := H.hjN; omega

theorem hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)

theorem hQ1 : 1 ≤ Step2.Q1 d := Step2.one_le_Q1 H.hd

theorem hcNear : 0 ≤ Step2.cNear d L := Nat.cast_nonneg _

theorem hQ0 : 0 ≤ Step2.Q1 d := by linarith [H.hQ1]

theorem hsO : 0 ≤ sO d L r mV mW := by
  have := H.hcNear; have := H.hr; have := H.hmV
  unfold sO
  exact add_nonneg (by positivity) (mul_nonneg H.hQ0 H.hmW)

/-! ### `V'_B` -/

theorem Vpr_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (VprO C V b) ≤ ENNReal.ofReal (Step2.Q1 d * mV) := by
  rw [VprO]
  refine (oTo_EthO_le2 H.hw0 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hVl b)).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (H.hVm b hb)

theorem V2_e {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) (V b : SA c (Lam d L N)).e ≤ ENNReal.ofReal (Step2.Q1 d * r) := by
  rw [ENNReal.ofReal_mul (by linarith [H.hQ1])]
  exact (Step2.Tj2_block_le H.hd H.hLp H.hj H.hℓ (H.hVl b).e).trans
    (mul_le_mul_left' (H.hVr b hb) _)

theorem V2_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) (2 * ℓ) (V b) ≤ ENNReal.ofReal (Step2.Q1 d * mV) := by
  refine (oTj_succ_two_le H.hw0 H.hd H.hLp H.hj (H.hVl b).πobs H.hℓ).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (H.hVm b hb)

/-! ### The pair terms `F(V'_B, V'_{B'})` -/

omit H in
theorem FCO_split (A B : OE c (Lam d L N)) :
    FCO C (EthO C A) (EthO C B) = FCO C (EthO C (emb (bulk A) : OE c (Lam d L N)))
        (EthO C (emb (bulk B) : OE c (Lam d L N))) +
      FCO C (EthO C (emb (bulk A) : OE c (Lam d L N))) (EthO C (πobs B)) +
      FCO C (EthO C (πobs A)) (EthO C (emb (bulk B) : OE c (Lam d L N))) +
      FCO C (EthO C (πobs A)) (EthO C (πobs B)) := by
  conv_lhs => rw [eq_emb_add_πobs A, eq_emb_add_πobs B]
  rw [EthO_add, EthO_add, FCO_add_left, FCO_add_right, FCO_add_right]
  abel

theorem pair_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (VprO C V b) (VprO C V b')) ≤
      ENNReal.ofReal (4 * Step2.Q1 d ^ 2 * (r * mV)) := by
  have hQ := H.hQ1; have hr := H.hr; have hm := H.hmV
  rw [VprO, VprO, FCO_split]
  have e1 := oTo_FCO_bulk w C (V b) (V b') (j + 1) ℓ'
  have e4 := oTo_eq_zero_of_eab w (j + 1) ℓ' H.hw0 (FCO_obs_obs_eabZero C (V b) (V b'))
  have h2 : oTo w (j + 1) ℓ' (FCO C (EthO C (emb (bulk (V b)) : OE c (Lam d L N)))
      (EthO C (πobs (V b')))) ≤
      ENNReal.ofReal (2 * ((Step2.Q1 d * r) * (Step2.Q1 d * mV))) := by
    refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    refine mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 hr) ?_ ?_) _
    · rw [oTj_emb]; exact H.V2_e hb
    · exact H.V2_o hb'
  have h3 : oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
      (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) ≤
      ENNReal.ofReal (2 * ((Step2.Q1 d * mV) * (Step2.Q1 d * r))) := by
    refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    refine mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 hm) (H.V2_o hb) ?_) _
    rw [oTj_emb]; exact H.V2_e hb'
  refine (oTo_add_le w _ _ _ _).trans ?_
  rw [e4, add_zero]
  refine ((oTo_add_le w _ _ _ _).trans (add_le_add ((oTo_add_le w _ _ _ _).trans
    (add_le_add (le_of_eq e1) h2)) h3)).trans ?_
  have hQ0 := H.hQ0
  rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-! ### `S(B)` -/

theorem far_sep {b b' : Fin d → ℕ} (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (h : b' ∉ Step2.nearSet (L := L) (N := N) j b) :
    CovSep C (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) := by
  set Y1 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b)
  set Y2 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b')
  have hfar : ∀ x ∈ Y1, ∀ y ∈ Y2, L ^ (j + 1) ≤ 2 * supNorm (x - y) :=
    fun x hx y hy => Step2.not_near_far hb' h hx hy
  have hpos : 0 < L ^ (j + 1) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdis : Disjoint (Y1 : Set (Lam d L N)) (Y2 : Set (Lam d L N)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h3 := hfar z hz z hz'
    rw [sub_self, supNorm_zero, mul_zero] at h3
    omega
  have hCz : ∀ x ∈ (Y1 : Set (Lam d L N)), ∀ y ∈ (Y2 : Set (Lam d L N)),
      C x y = 0 ∧ C y x = 0 := by
    intro x hx y hy
    have h1 : L ^ (j + 1) ≤ 2 * supNorm (x - y) := hfar x hx y hy
    have h1' : ((L : ℝ) ^ (j + 1)) / 2 ≤ (supNorm (x - y) : ℝ) := by
      have h4 : ((L ^ (j + 1) : ℕ) : ℝ) ≤ ((2 * supNorm (x - y) : ℕ) : ℝ) := Nat.cast_le.2 h1
      rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at h4
      linarith
    have h2 : supNorm (y - x) = supNorm (x - y) := by
      rw [← neg_sub, supNorm_neg]
    exact ⟨H.hC.range H.hjN x y h1', H.hC.range H.hjN y x (by rw [h2]; exact h1')⟩
  exact ⟨hdis, hCz⟩

/-- Far blocks do not interact (bulk and single-source components). -/
theorem far_gen {b b' : Fin d → ℕ} (hb' : b' ∈ blockIdx (L := L) (N := N) j)
    (h : b' ∉ Step2.nearSet (L := L) (N := N) j b) {A B : OE c (Lam d L N)}
    (hA : CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (A : SA c (Lam d L N)))
    (hB : CmpIn (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N))
      (B : SA c (Lam d L N))) :
    EabZero (FCO C A B : SA c (Lam d L N)) :=
  FCO_eabZero_of_sep C (H.far_sep hb' h) hA hB

theorem EthW_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (EthO C (W b)) ≤ ENNReal.ofReal (Step2.Q1 d * mW) := by
  refine (oTo_EthO_le2 H.hw0 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.hWl b)).trans ?_
  exact le_ofReal_mul (by linarith [H.hQ1])
    (ENNReal.ofReal_le_ofReal (Step2.pq_pow_le_Q1 H.hd H.hj.le b)) (H.hWm b hb)

/-- The half pair `F(𝔼θ V^{obs}(B), 𝔼θ V^∅(B'))`. -/
theorem pairh_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (EthO C (πobs (V b)))
      (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) ≤
      ENNReal.ofReal (2 * Step2.Q1 d ^ 2 * (r * mV)) := by
  have hm := H.hmV
  refine (oTo_le w _ _ _).trans ((oTj_FCO_le H.hℓ' H.hℓC H.hsum H.hC H.hw _ _).trans ?_)
  have e : 2 * Step2.Q1 d ^ 2 * (r * mV) = 2 * ((Step2.Q1 d * mV) * (Step2.Q1 d * r)) := by ring
  rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine mul_le_mul_left' (le_ofReal_mul (mul_nonneg H.hQ0 hm) (H.V2_o hb) ?_) _
  rw [oTj_emb]; exact H.V2_e hb'

theorem pairπ_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (FCO C (πobs (VprO C V b)) (VprO C V b')) ≤
      ENNReal.ofReal (2 * Step2.Q1 d ^ 2 * (r * mV)) := by
  rw [VprO, VprO, πobs_EthO, eq_emb_add_πobs (V b'), EthO_add, FCO_add_right]
  refine (oTo_add_le w _ _ _ _).trans ?_
  rw [oTo_eq_zero_of_eab w _ _ H.hw0 (FCO_obs_obs_eabZero C (V b) (V b')), add_zero]
  exact H.pairh_o hb hb'

/-- `‖G(B, B')^{obs}‖ ≤ 4 Q₁² r m_V`. -/
theorem pairG_o {b b' : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (GO C V b b') ≤ ENNReal.ofReal (4 * Step2.Q1 d ^ 2 * (r * mV)) := by
  have hr := H.hr; have hm := H.hmV
  rw [GO, FCO_comm C (VprO C V b)]
  refine (oTo_sub_le w _ _ _ _).trans ?_
  refine (add_le_add (H.pairπ_o hb hb') (H.pairπ_o hb' hb)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

omit H in
/-- The single-source components of the sharp second-order part only see
`F(𝔼θ V^{obs}(B), 𝔼θ V^∅(Λ))`. -/
theorem oTo_SFO_eq (hw0 : w.ab = 0) (b : Fin d → ℕ) (j' : ℕ) (ℓ₀ : ℝ) :
    oTo w j' ℓ₀ (SFO j C V b) =
      oTo w j' ℓ₀ (∑ b' ∈ blockIdx (L := L) (N := N) j, FCO C (EthO C (πobs (V b)))
        (EthO C (emb (bulk (V b')) : OE c (Lam d L N)))) := by
  rw [← FCO_sum_right, oTo_eq_comp hw0, oTo_eq_comp hw0]
  have h := fun i => SFO_cmp j C V i b
  have h' := fun i => FCO_cmp C i (EthO C (πobs (V b)))
    (∑ b' ∈ blockIdx (L := L) (N := N) j, EthO C (emb (bulk (V b')) : OE c (Lam d L N)))
  have k1 : ((EthO C (πobs (V b)) : OE c (Lam d L N)) : SA c (Lam d L N)).e = 0 := by
    rw [← πobs_EthO, πobs_e']
  have k2 : ∀ i, cmp i ((∑ b' ∈ blockIdx (L := L) (N := N) j,
      EthO C (emb (bulk (V b')) : OE c (Lam d L N)) : OE c (Lam d L N)) : SA c (Lam d L N)) = 0 := by
    intro i
    rw [AddSubmonoidClass.coe_finsetSum, cmp_sum]
    refine sum_eq_zero fun b' _ => ?_
    rw [EthO_emb]; cases i <;> rfl
  have k3 : ((∑ b' ∈ blockIdx (L := L) (N := N) j,
      EthO C (emb (bulk (V b')) : OE c (Lam d L N)) : OE c (Lam d L N)) : SA c (Lam d L N)).e =
      (VprLO j C V : SA c (Lam d L N)).e := by
    rw [VprLO, AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum, sum_e, sum_e]
    refine sum_congr rfl fun b' _ => ?_
    rw [EthO_emb]; rfl
  have k4 : ∀ i, cmp i ((EthO C (πobs (V b)) : OE c (Lam d L N)) : SA c (Lam d L N)) =
      cmp i (VprO C V b : SA c (Lam d L N)) := by
    intro i; rw [← πobs_EthO, πobs_cmp']; rfl
  have ea : ∀ i, cmp i (SFO j C V b : SA c (Lam d L N)) =
      cmp i (FCO C (EthO C (πobs (V b)))
        (∑ b' ∈ blockIdx (L := L) (N := N) j, EthO C (emb (bulk (V b')) : OE c (Lam d L N))) :
          SA c (Lam d L N)) := by
    intro i; rw [h i, h' i, k1, k2, k3, k4, map_zero, FC_zero_left, zero_add]
  have e1 := ea true
  have e2 := ea false
  simp only [cmp_true, cmp_false] at e1 e2
  rw [e1, e2]

/-- **`‖S^{(2)}(B)^{obs}‖_{T_{j+1}(ℓ')} ≤ 2 c_near Q₁² r m_V`** (sharp splitting). -/
theorem SF_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SFO j C V b) ≤
      ENNReal.ofReal (Step2.cNear d L * (2 * Step2.Q1 d ^ 2 * (r * mV))) := by
  classical
  have hQ := H.hQ1; have hr := H.hr; have hm := H.hmV
  rw [oTo_SFO_eq H.hw0]
  refine (oTo_sum_le w _ _ _ _).trans ?_
  rw [← sum_filter_add_sum_filter_not (blockIdx (L := L) (N := N) j)
    (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)]
  rw [sum_eq_zero (s := filter (fun b' => ¬ _) _) fun b' hb' =>
    oTo_eq_zero_of_eab w _ _ H.hw0 (H.far_gen (mem_filter.1 hb').1 (mem_filter.1 hb').2
      ((H.hVl b).πobs.EthO C) (((H.hVl b').πe).EthO C)), add_zero]
  refine (le_ofReal_sum_const _ (by positivity) fun b' hb' =>
    H.pairh_o hb (mem_filter.1 hb').1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hn : ((filter (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)
      (blockIdx (L := L) (N := N) j)).card : ℝ) ≤ Step2.cNear d L := by
    have h1 : (filter (fun b' => b' ∈ Step2.nearSet (L := L) (N := N) j b)
        (blockIdx (L := L) (N := N) j)).card ≤ (Step2.nearSet (L := L) (N := N) j b).card :=
      card_le_card fun b' hb' => (mem_filter.1 hb').2
    unfold Step2.cNear
    exact_mod_cast h1.trans (Step2.card_nearSet_le H.hj.le b hb)
  exact mul_le_mul_of_nonneg_right hn (by positivity)

/-- **`‖S(B)^{obs}‖_{T_{j+1}(ℓ')} ≤ 2 c_near Q₁² r m_V + Q₁ m_W`.** -/
theorem Sb_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (SbO j C V W b) ≤ ENNReal.ofReal (sO d L r mV mW) := by
  have hQ := H.hQ1; have hr := H.hr; have hm := H.hmV; have hmW := H.hmW
  have hn := H.hcNear
  rw [SbO]
  refine (oTo_add_le w _ _ _ _).trans ?_
  refine (le_ofReal_add (by positivity) (mul_nonneg H.hQ0 hmW) (H.SF_o hb) (H.EthW_o hb)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold sO; ring

theorem hL8' : 2 ^ (d + 3) ≤ L := by have := H.hL8; omega

theorem nbhd_block_sub {b b' : Fin d → ℕ} (hb' : b' ∈ Step2.nearSet (L := L) (N := N) j b) :
    (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N)) ⊆
      (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N)) := fun _ hy =>
  Step2.mem_nbhd_succ_of_near H.hd H.hL8' H.hjN.le hb' hy

theorem FCsum_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) {A : OE c (Lam d L N)}
    (hA : CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N)) (A : SA c (Lam d L N)))
    {Bf : (Fin d → ℕ) → OE c (Lam d L N)}
    (hB : ∀ b', CmpIn (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N))
      (Bf b' : SA c (Lam d L N))) :
    CmpIn (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N))
      (FCO C A (∑ b' ∈ blockIdx (L := L) (N := N) j, Bf b') : SA c (Lam d L N)) := by
  classical
  have hs := H.nbhd_block_sub (Step2.mem_nearSet_self hb)
  rw [FCO_sum_right, AddSubmonoidClass.coe_finsetSum]
  refine CmpIn.sum _ fun b' hb' => ?_
  by_cases hn : b' ∈ Step2.nearSet (L := L) (N := N) j b
  · exact CmpIn.FCO C (hA.mono hs) ((hB b').mono (H.nbhd_block_sub hn))
  · exact (H.far_gen hb' hn hA (hB b')).cmpIn

theorem Sb_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    CmpIn (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N))
      (SbO j C V W b : SA c (Lam d L N)) := by
  have hs := H.nbhd_block_sub (Step2.mem_nearSet_self hb)
  have hX := (H.hVl b).EthO C
  have hY : ∀ b', CmpIn (nbhd j (blockSet (L := L) (N := N) j b') : Set (Lam d L N))
      (VprO C V b' : SA c (Lam d L N)) := fun b' => (H.hVl b').EthO C
  rw [SbO, SFO, SCorO]
  refine CmpIn.add (CmpIn.add (CmpIn.smul _ ?_) (CmpIn.smul _ (CmpIn.sub ?_ ?_)))
    (((H.hWl b).EthO C).mono hs)
  · rw [VprLO]; exact H.FCsum_mem hb hX hY
  · rw [VprLO]; exact H.FCsum_mem hb hX.πobs hY
  · rw [VprLO, map_sum]; exact H.FCsum_mem hb hX fun b' => (hY b').πobs

omit H in
theorem nb_Bp_le (b : Fin d → ℕ) : nb j (Step2.Bp (L := L) (N := N) j b) ≤ L ^ d := by
  have h1 := nb_le_of_succ (isPolymer_clo (L := L) (N := N) j (blockSet j b))
  have h2 := (nb_clo_le (L := L) (N := N) j (blockSet j b)).trans (nb_blockSet_le j b)
  calc nb j (Step2.Bp (L := L) (N := N) j b) ≤ L ^ d * nb (j + 1) (clo j (blockSet j b)) := h1
    _ ≤ L ^ d * 1 := Nat.mul_le_mul_left _ h2
    _ = L ^ d := mul_one _

theorem SX_mem {b : Fin d → ℕ} :
    CmpIn (nbhd (j + 1) (Step2.Bp (L := L) (N := N) j b) : Set (Lam d L N))
      (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA c (Lam d L N)) := by
  rw [SXO, AddSubmonoidClass.coe_finsetSum]
  refine CmpIn.sum _ fun b'' hb'' => ?_
  exact (H.Sb_mem (mem_blockIdx_of_mem_blocks hb'')).mono
    (by exact_mod_cast nbhd_mono (Step2.BH.Bp_sub hb''))

theorem SX_o (b : Fin d → ℕ) :
    oTo w (j + 1) ℓ' (SXO j C V W (Step2.Bp (L := L) (N := N) j b)) ≤
      ENNReal.ofReal ((L : ℝ) ^ d * sO d L r mV mW) := by
  have := H.hsO
  rw [SXO]
  refine (oTo_sum_le w _ _ _ _).trans ((le_ofReal_sum_const _ this fun b'' hb'' =>
    H.Sb_o (mem_blockIdx_of_mem_blocks hb'')).trans (ENNReal.ofReal_le_ofReal ?_))
  have h' : ((blocks j (Step2.Bp (L := L) (N := N) j b)).card : ℝ) ≤ (L : ℝ) ^ d := by
    exact_mod_cast nb_Bp_le b
  exact mul_le_mul_of_nonneg_right h' this

/-! ### `Loc S`, `𝔼θQ` and the coordinates at scale `j + 1` -/

theorem LS_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (LSO P j C V W b) ≤ ENNReal.ofReal (Cl * ((L : ℝ) ^ d * sO d L r mV mW)) := by
  have := H.hsO
  rw [LSO]
  refine (H.hloc (j + 1) H.hjN ℓ' H.hℓ' _ _ (isSmall_clo (isSmall_blockSet_of_mem hb))
    (subset_clo j _) _ H.SX_mem).trans ?_
  exact le_ofReal_mul H.hCl le_rfl (H.SX_o b)

theorem Q_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    CmpIn (↑(nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b}) : Set (Lam d L N))
      (Q2O P j K b : SA c (Lam d L N)) := by
  classical
  rw [Q2O, if_pos H.hjN, AddSubmonoidClass.coe_finsetSum]
  exact CmpIn.sum _ fun X _ => H.hlocl X _ (isSmall_blockSet_of_mem hb).1 (K X)

omit H in
theorem nb_union_pts_le (A : Finset (Lam d L N)) (a b : Lam d L N) :
    nb j (A ∪ {a, b}) ≤ nb j A + 2 := by
  classical
  unfold nb blocks
  rw [image_union]
  refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  exact card_image_le.trans ((card_insert_le _ _).trans (by simp))

theorem pq_pow_pts_le {b : Fin d → ℕ} :
    Step2.pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b}) ≤
      Step2.Q1 d * Step2.pq d ^ 2 := by
  have h1 := Step2.one_le_pq H.hd
  calc Step2.pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b) ∪ {P.a, P.b})
      ≤ Step2.pq d ^ (nb j (nbhd j (blockSet (L := L) (N := N) j b)) + 2) :=
        pow_le_pow_right₀ h1 (nb_union_pts_le _ _ _)
    _ = Step2.pq d ^ nb j (nbhd j (blockSet (L := L) (N := N) j b)) * Step2.pq d ^ 2 := pow_add _ _ _
    _ ≤ Step2.Q1 d * Step2.pq d ^ 2 :=
        mul_le_mul_of_nonneg_right (Step2.pq_pow_le_Q1 H.hd H.hj.le b) (by positivity)

theorem Q_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (EthO C (Q2O P j K b)) ≤
      ENNReal.ofReal (Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl * k))) := by
  classical
  have hk := H.hk; have hCl := H.hCl; have hcS := H.hcS
  have hpq := Step2.one_le_pq H.hd
  refine (oTo_EthO_le2 H.hw0 H.hd H.hLp H.hj H.hℓ' H.hℓC H.hsum H.hC (H.Q_mem hb)).trans ?_
  refine le_ofReal_mul (mul_nonneg H.hQ0 (by positivity))
    (ENNReal.ofReal_le_ofReal H.pq_pow_pts_le) ?_
  rw [Q2O, if_pos H.hjN]
  refine (oTo_sum_le w _ _ _ _).trans ((le_ofReal_sum_const _ (mul_nonneg hCl hk) fun X hX => ?_).trans
    (ENNReal.ofReal_le_ofReal ?_))
  · obtain ⟨hs, hbX⟩ := mem_smallSets_filter.1 hX
    exact (H.hloc j H.hj ℓ H.hℓ X _ hs hbX (K X) (H.hKl X hs)).trans
      (le_ofReal_mul hCl le_rfl (H.hKk X hs))
  · exact mul_le_mul_of_nonneg_right (H.hcount b hb) (mul_nonneg hCl hk)

/-- The constant of `(u+V)^{obs}_{j+1}(B)`. -/
def uO (d L : ℕ) (r mV mW k Cl cS : ℝ) : ℝ :=
  Step2.Q1 d * mV + Step2.Q1 d * Step2.pq d ^ 2 * (cS * (Cl * k)) +
    Cl * ((L : ℝ) ^ d * sO d L r mV mW)

theorem huO : 0 ≤ uO d L r mV mW k Cl cS := by
  unfold uO
  have hpq := Step2.one_le_pq H.hd
  exact add_nonneg (add_nonneg (mul_nonneg H.hQ0 H.hmV) (mul_nonneg
    (mul_nonneg H.hQ0 (by positivity))
    (mul_nonneg (by linarith [H.hcS]) (mul_nonneg H.hCl H.hk))))
    (mul_nonneg H.hCl (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO))

theorem uVp_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (uVpO P j C V W K b) ≤ ENNReal.ofReal (uO d L r mV mW k Cl cS) := by
  have p1 := mul_nonneg H.hQ0 H.hmV
  have hpq := Step2.one_le_pq H.hd
  have p2 := mul_nonneg (mul_nonneg H.hQ0 (by positivity : (0 : ℝ) ≤ Step2.pq d ^ 2))
    (mul_nonneg (by linarith [H.hcS] : (0 : ℝ) ≤ cS) (mul_nonneg H.hCl H.hk))
  have p3 := mul_nonneg H.hCl (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO)
  rw [uVpO]
  refine (oTo_sub_le w _ _ _ _).trans ?_
  exact le_ofReal_add (add_nonneg p1 p2) p3 ((oTo_sub_le w _ _ _ _).trans
    (le_ofReal_add p1 p2 (H.Vpr_o hb) (H.Q_o hb))) (H.LS_o hb)

/-- **`‖V^{obs}_{j+1}(B)‖_{T_{j+1}(ℓ')} ≤ 2 (Q₁ m_V + Q₁ c_S C_l k + C_l L^d s^{obs})`.** -/
theorem Vp_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (VpO P j C V W K b) ≤ ENNReal.ofReal (2 * uO d L r mV mW k Cl cS) := by
  have h0 := H.huO
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := pow_pos H.hL0 _
  have e0 : oTo w (j + 1) ℓ' (algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b)) = 0 :=
    oTo_algebraMap w _ _ _
  have e1 : oTo w (j + 1) ℓ' (upO P j C V W K b) ≤ ENNReal.ofReal (uO d L r mV mW k Cl cS) := by
    rw [upO, oTo_πobs]; exact (oTo_epsO_le w hh H.hℓ' _).trans (H.uVp_o hb)
  have e2 : oTo w (j + 1) ℓ' (uVpO P j C V W K b -
      algebraMap ℂ (OE c (Lam d L N)) (upB P j C V W K b)) ≤
      ENNReal.ofReal (uO d L r mV mW k Cl cS) := by
    refine (oTo_sub_le w _ _ _ _).trans ?_
    rw [e0, add_zero]; exact H.uVp_o hb
  rw [VpO]
  refine (oTo_sub_le w _ _ _ _).trans ((add_le_add e2 e1).trans ?_)
  rw [← ENNReal.ofReal_add h0 h0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **`‖𝒲^{obs}_{j+1}(B)‖_{T_{j+1}(ℓ')} ≤ (1 + C_l L^d) s^{obs}`.** -/
theorem Wp_o {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    oTo w (j + 1) ℓ' (WpO P j C V W b) ≤
      ENNReal.ofReal (sO d L r mV mW + Cl * ((L : ℝ) ^ d * sO d L r mV mW)) := by
  rw [WpO]
  exact (oTo_sub_le w _ _ _ _).trans (le_ofReal_add H.hsO
    (mul_nonneg H.hCl (mul_nonneg (pow_nonneg H.hL0.le d) H.hsO)) (H.Sb_o hb) (H.LS_o hb))

end BHO

end

end Obs2
