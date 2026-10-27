import PtCorr2.Restart.RerepK
import PtCorr2.Pair.PairInitU
import PtCorr2.Pair.PairLin1

set_option autoImplicit false

/-!
# B3, T6, route (c): the `σ_aσ_b` part of the relocation correction

The difference datum at `ms` is `δ = plDiffSt (rrSt o) o'`; its `ab` activity is
`δ.K(Y)_{ab} = (o.K(Y)_{ab} + corr(Y)_{ab}) − o'.K(Y)_{ab}` (**`zab_delta_ab_eq`**), with
`corr(Y) = ∑_{B ⊆ Y} δ(B)(K♭+o.K)^{Y∖B}` (`zabCorr`), `δ(B) = −rrD(B)·I'(B)`. `rr_corr_norm` only
covers the `σ_a` part. Since `rrD` is pure `σ_a`, the `ab` part of a correction term is
`−β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})·(I'(B)(K♭+o.K)^{Y∖B})_b` (`zab_rrD_mul_ab`), so only `σ_b` sizes of
`I'` and of the large-set factor enter. They are measured in the `σ_b` weight
`wB(M_b) = (0, M_b^{-1}, 0)` (`wB_sub`; `T(F_b) ≤ M_b‖F‖_{wB}`, `zab_b_le_wB`;
`‖·‖^{obs}_{wB} ≤ ‖·‖^{obs}_{wM1}`, `zab_oTo_wB_le`):

* `zab_kext_oTj`: the weighted large-set regulator: `A^{|𝓑(W)|}‖F(W)‖_w ≤ 1` (connected `W`)
  gives `A^{|𝓑(Z)|}‖F^Z‖_w ≤ 1` for polymers `Z` (any `w.Sub`);
* **`zab_corr_ab_le`**: with `‖I'(B)‖_{wB} ≤ ι` (`B ⊆ Y`), the regulator for `K♭ + o.K` in `wB`,
  and `∑_{B ⊆ Y}T(β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})) ≤ d̄`:
  `A^{(|𝓑(Y)|−4)_+}T(corr(Y)_{ab}) ≤ M_b d̄ιA`;
* `zab_tri`: the triangle inequality in the `ab` weight.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist ENNReal

variable {L N : ℕ} [NeZero L]

/-- **The weighted large-set regulator for the product over components.** -/
theorem zab_kext_oTj {w : Wt} (hw : w.Sub) {j : ℕ} {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 0 ≤ A)
    (F : OAct .two 2 L N)
    (hF : ∀ W, IsConn j W → ENNReal.ofReal (A ^ nb j W) *
      oTj 2 L w j ℓ (F W : SA .two (Lam 2 L N)) ≤ 1)
    {Z : Finset (Lam 2 L N)} (hZ : IsPolymer j Z) :
    ENNReal.ofReal (A ^ nb j Z) * oTj 2 L w j ℓ (KextO j F Z : SA .two (Lam 2 L N)) ≤ 1 := by
  rw [← prod_comp_pow hZ A, ENNReal.ofReal_prod_of_nonneg (fun W _ => by positivity)]
  calc (∏ W ∈ Comp j Z, ENNReal.ofReal (A ^ nb j W)) *
        oTj 2 L w j ℓ (KextO j F Z : SA .two (Lam 2 L N))
      ≤ (∏ W ∈ Comp j Z, ENNReal.ofReal (A ^ nb j W)) *
        ∏ W ∈ Comp j Z, oTj 2 L w j ℓ (F W : SA .two (Lam 2 L N)) := by
        gcongr
        exact oTj_prod_le hw hℓ _ _
    _ = ∏ W ∈ Comp j Z, ENNReal.ofReal (A ^ nb j W) *
        oTj 2 L w j ℓ (F W : SA .two (Lam 2 L N)) := (prod_mul_distrib).symm
    _ ≤ 1 := prod_le_one' fun W hW => hF W (isConn_of_mem_comp hZ hW)

/-- The triangle inequality in the `ab` weight. -/
theorem zab_tri (w : Wt) {j : ℕ} {ℓ : ℝ} (x z y : Alg 2 L N) {c : ℝ≥0∞}
    (hc : w.ab * Tj 2 (L : ℝ) j ℓ z ≤ c) :
    w.ab * Tj 2 (L : ℝ) j ℓ (x + z - y) ≤
      w.ab * Tj 2 (L : ℝ) j ℓ x + c + w.ab * Tj 2 (L : ℝ) j ℓ y := by
  have ht : Tj 2 (L : ℝ) j ℓ (x + z - y) ≤ Tj 2 (L : ℝ) j ℓ x + Tj 2 (L : ℝ) j ℓ z +
      Tj 2 (L : ℝ) j ℓ y := by
    refine (tNorm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact tNorm_add_le _ _
  calc w.ab * Tj 2 (L : ℝ) j ℓ (x + z - y)
      ≤ w.ab * (Tj 2 (L : ℝ) j ℓ x + Tj 2 (L : ℝ) j ℓ z + Tj 2 (L : ℝ) j ℓ y) :=
        mul_le_mul_left' ht _
    _ = w.ab * Tj 2 (L : ℝ) j ℓ x + w.ab * Tj 2 (L : ℝ) j ℓ z + w.ab * Tj 2 (L : ℝ) j ℓ y := by
        ring
    _ ≤ _ := add_le_add (add_le_add le_rfl hc) le_rfl

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)
  (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)

/-- The relocation correction of `rrSt` on the polymer `Y`. -/
def zabCorr (o : ObsSt .two L N) (Y : Finset (Lam 2 L N)) : OE .two (Lam 2 L N) :=
  ∑ b ∈ blocks j Y, rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K) (Y \ blockSet j b)

/-- The `σ_b`-only weight `(0, M_b^{-1}, 0)`. -/
def wB (Mb : ℝ) : Wt := ⟨0, ENNReal.ofReal Mb⁻¹, 0⟩

theorem wB_sub (Mb : ℝ) : (wB Mb).Sub := zero_le

/-- `‖F‖^{obs}_{wB} ≤ ‖F‖^{obs}_{wM1}`. -/
theorem zab_oTo_wB_le (Ma Mb : ℝ) (j' : ℕ) (ℓ : ℝ) (F : OE .two (Lam 2 L N)) :
    oTo (wB Mb) j' ℓ F ≤ oTo (wM1 Ma Mb) j' ℓ F :=
  oNorm_mono (w := wB Mb) (w' := wM1 Ma Mb) (fun _ => le_rfl) zero_le le_rfl le_rfl _

/-- `T(F_b) ≤ M_b‖F‖_{wB}`. -/
theorem zab_b_le_wB {Mb : ℝ} (hMb : 0 < Mb) (j' : ℕ) (ℓ : ℝ) (F : SA .two (Lam 2 L N)) :
    Tj 2 (L : ℝ) j' ℓ F.b ≤ ENNReal.ofReal Mb * oTj 2 L (wB Mb) j' ℓ F := by
  have e : ENNReal.ofReal Mb * ENNReal.ofReal Mb⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hMb.le, mul_inv_cancel₀ hMb.ne', ENNReal.ofReal_one]
  calc Tj 2 (L : ℝ) j' ℓ F.b = ENNReal.ofReal Mb * (ENNReal.ofReal Mb⁻¹ * Tj 2 (L : ℝ) j' ℓ F.b) := by
        rw [← mul_assoc, e, one_mul]
    _ ≤ ENNReal.ofReal Mb * oTj 2 L (wB Mb) j' ℓ F := by
        refine mul_le_mul_left' ?_ _
        show _ ≤ Tj 2 (L : ℝ) j' ℓ F.e + 0 * Tj 2 (L : ℝ) j' ℓ F.a +
          ENNReal.ofReal Mb⁻¹ * Tj 2 (L : ℝ) j' ℓ F.b + 0 * Tj 2 (L : ℝ) j' ℓ F.ab
        rw [zero_mul, zero_mul, add_zero, add_zero]
        exact le_add_self

/-- The `σ_aσ_b` part of `−rrD(B)·F`: `−β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})F_b`. -/
theorem zab_rrD_mul_ab (F : OE .two (Lam 2 L N)) (b : Fin 2 → ℕ) :
    ((-rrD a a' β b * F : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab =
      -((β b • (pbp a - pbp a')) * (F : SA .two (Lam 2 L N)).b) := by
  simp [Case.tau, Case.s]

set_option maxHeartbeats 1000000 in
/-- **The `σ_aσ_b` part of the relocation correction** (per connected polymer), in the `σ_b` weight
`wB(M_b)`: with `‖I'(B)‖_{wB} ≤ ι` (`B ⊆ Y`), the regulator `A^{|𝓑(W)|}‖(K♭+o.K)(W)‖_{wB} ≤ 1` and
`∑_{B ⊆ Y}T(β_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})) ≤ d̄`:
`A^{(|𝓑(Y)|−4)_+}T(corr(Y)_{ab}) ≤ M_b d̄ ιA`. -/
theorem zab_corr_ab_le {Mb : ℝ} (hMb : 0 < Mb) {ℓ A : ℝ} (hℓ : 0 < ℓ) (hA : 1 ≤ A)
    (o : ObsSt .two L N) {Y : Finset (Lam 2 L N)} (hY : IsConn j Y) {ι dbar : ℝ}
    (hι : 0 ≤ ι)
    (hI : ∀ b ∈ blocks j Y, oTj 2 L (wB Mb) j ℓ ((IbO (fun b' => emb (stVf R j st g μ b' +
      stDelta R j st b') + (o.V b' - rrD a a' β b')) (fullW st D o) b : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)) ≤ ENNReal.ofReal ι)
    (hKw : ∀ W, IsConn j W → ENNReal.ofReal (A ^ nb j W) *
      oTj 2 L (wB Mb) j ℓ (((embF K + o.K : OAct .two 2 L N) W : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)) ≤ 1)
    (hd : ∑ b ∈ blocks j Y, Tj 2 (L : ℝ) j ℓ (β b • (pbp a - pbp a')) ≤ ENNReal.ofReal dbar) :
    ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ ((zabCorr R j st g μ D K a a' β o Y : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (Mb * dbar * ι * A) := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hw := wB_sub Mb
  have hterm : ∀ b ∈ blocks j Y, ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
      Tj 2 (L : ℝ) j ℓ ((rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K)
        (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ≤
      ENNReal.ofReal (Mb * ι * A) * Tj 2 (L : ℝ) j ℓ (β b • (pbp a - pbp a')) := by
    intro b hb
    have hBY : blockSet (L := L) (N := N) j b ⊆ Y := blockSet_subset hY.1 hb
    have hZ : IsPolymer j (Y \ blockSet j b) := IsPolymer.sdiff hY.1 (isPolymer_blockSet j b)
    have hnb := nb_sdiff_add hY.1 (isPolymer_blockSet (L := L) (N := N) j b) hBY
    have hnb1 := nb_blockSet_le (L := L) (N := N) j b
    have hpow := rr_pow_nb_le hA (j := j) (Y := Y) (Z := Y \ blockSet j b) (by omega)
    have hext := zab_kext_oTj hw hℓ hA0 (embF K + o.K) hKw hZ
    have hIb := hI b hb
    have hrr : rrDel R j st g μ D a a' β o b = -rrD a a' β b * IbO (fun b' =>
        emb (stVf R j st g μ b' + stDelta R j st b') + (o.V b' - rrD a a' β b'))
        (fullW st D o) b := rfl
    rw [hrr, mul_assoc, zab_rrD_mul_ab]
    generalize KextO j (embF K + o.K) (Y \ blockSet j b) = E at hext ⊢
    generalize IbO (fun b' => emb (stVf R j st g μ b' + stDelta R j st b') +
      (o.V b' - rrD a a' β b')) (fullW st D o) b = G at hIb ⊢
    generalize β b • (pbp a - pbp a') = r
    generalize nb j (Y \ blockSet j b) = n at hpow hext
    have h1 : Tj 2 (L : ℝ) j ℓ (-(r * ((G * E : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b)) ≤
        Tj 2 (L : ℝ) j ℓ r * (ENNReal.ofReal Mb * (ENNReal.ofReal ι *
          oTj 2 L (wB Mb) j ℓ (E : SA .two (Lam 2 L N)))) := by
      rw [Tj_neg']
      refine (tNorm_mul_le hh hℓ _ _).trans (mul_le_mul_left' ?_ _)
      refine (zab_b_le_wB hMb j ℓ _).trans (mul_le_mul_left' ?_ _)
      exact (oTj_mul_le hw hℓ _ _).trans (mul_le_mul_right' hIb _)
    calc ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
          Tj 2 (L : ℝ) j ℓ (-(r * ((G * E : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b))
        ≤ ENNReal.ofReal (A * A ^ n) * (Tj 2 (L : ℝ) j ℓ r * (ENNReal.ofReal Mb *
            (ENNReal.ofReal ι * oTj 2 L (wB Mb) j ℓ (E : SA .two (Lam 2 L N))))) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) h1
      _ = ENNReal.ofReal (Mb * ι * A) * Tj 2 (L : ℝ) j ℓ r *
          (ENNReal.ofReal (A ^ n) * oTj 2 L (wB Mb) j ℓ (E : SA .two (Lam 2 L N))) := by
          rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Mb * ι),
            ENNReal.ofReal_mul hMb.le]
          ring
      _ ≤ ENNReal.ofReal (Mb * ι * A) * Tj 2 (L : ℝ) j ℓ r * 1 := mul_le_mul_left' hext _
      _ = _ := mul_one _
  have hsum : ((zabCorr R j st g μ D K a a' β o Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab =
      ∑ b ∈ blocks j Y, ((rrDel R j st g μ D a a' β o b * KextO j (embF K + o.K)
        (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab := by
    rw [zabCorr, AddSubmonoidClass.coe_finsetSum, SA.sum_ab]
  rw [hsum]
  calc ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ (∑ b ∈ blocks j Y, ((rrDel R j st g μ D a a' β o b * KextO j
          (embF K + o.K) (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab)
      ≤ ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        ∑ b ∈ blocks j Y, Tj 2 (L : ℝ) j ℓ ((rrDel R j st g μ D a a' β o b * KextO j
          (embF K + o.K) (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab :=
        mul_le_mul_left' (tNorm_sum_le _ _) _
    _ = ∑ b ∈ blocks j Y, ENNReal.ofReal (A ^ (nb j Y - 2 ^ 2)) *
        Tj 2 (L : ℝ) j ℓ ((rrDel R j st g μ D a a' β o b * KextO j
          (embF K + o.K) (Y \ blockSet j b) : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab :=
        mul_sum _ _ _
    _ ≤ ∑ b ∈ blocks j Y, ENNReal.ofReal (Mb * ι * A) *
        Tj 2 (L : ℝ) j ℓ (β b • (pbp a - pbp a')) := sum_le_sum hterm
    _ = ENNReal.ofReal (Mb * ι * A) *
        ∑ b ∈ blocks j Y, Tj 2 (L : ℝ) j ℓ (β b • (pbp a - pbp a')) := (mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (Mb * ι * A) * ENNReal.ofReal dbar := mul_le_mul_left' hd _
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

set_option maxHeartbeats 1000000 in
/-- **The `ab` activity of the difference datum**:
`δ.K(Y)_{ab} = (o.K(Y)_{ab} + corr(Y)_{ab}) − o'.K(Y)_{ab}`. -/
theorem zab_delta_ab_eq (o o' : ObsSt .two L N) (Y : Finset (Lam 2 L N)) :
    (((plDiffSt (rrSt R j st g μ D K a a' β o) o').K Y : OE .two (Lam 2 L N)) :
        SA .two (Lam 2 L N)).ab =
      (((o.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab +
        ((zabCorr R j st g μ D K a a' β o Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) -
        ((o'.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab := by
  have e1 : (((plDiffSt (rrSt R j st g μ D K a a' β o) o').K Y : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).ab =
      ((((rrSt R j st g μ D K a a' β o).K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab) -
        ((o'.K Y : OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab := rfl
  have e2 : (rrSt R j st g μ D K a a' β o).K Y = o.K Y + zabCorr R j st g μ D K a a' β o Y := rfl
  rw [e1, e2, AddMemClass.coe_add, SA.add_ab]

end

end PtCorr2
