import Step2.Map.Gen
import Step2.Map.TNorm2
import Step.EstNonlinAux

/-!
# A crude bound for the general polymer map

For the general map `gKnext` of `Step2.Map.Gen` with block bounds

* `‖θ K(W)‖ ≤ κ₀ ρ^{|𝓑_j(W)|}` for connected `W`,
* `‖δI(B)‖ ≤ δ₁ ρ`,
* `‖θ J(B, X)‖ ≤ c_J κ₀ ρ^{2^d}`, `J(B, X) = 0` unless `X` is small,

(all in the norm of the doubled algebra at scale `j + 1`) and a bound `2^{|𝓑_{j+1}(U)|}` on the
prefactors `c I_{j+1}^{U ∖ (X̌ ∪ 𝒳)}`, we get `(A_r Q)^{|𝓑_{j+1}(U)|} ‖c K_{j+1}(U)‖ ≤ 1` if
`ρ = A_r⁻¹` and `(2 A_r Q M)^{2^d} β ≤ 1`, `β = (1 + 2^d c_J) κ₀ + δ₁`
(`GH.gKnext_le`). This is the argument of `RHyp.R2_le` (`Step.EstNonlinAux`) for the whole sum
over `𝒢(U)`; the factor `Q` is the loss from Lemma `lem:pauli` in the bound for `θ K`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- The block hypotheses for the general map. -/
structure GH (j : ℕ) (Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)) (K : Act d L N)
    (J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)) (h' ℓ' ℓC ρ κ₀ δ₁ cJ : ℝ) : Prop where
  hh' : 0 < h'
  hℓ' : 0 < ℓ'
  hρ : 0 ≤ ρ
  hρ1 : ρ ≤ 1
  hκ₀ : 0 ≤ κ₀
  hκ₀1 : κ₀ ≤ 1
  hδ₁ : 0 ≤ δ₁
  hδ₁1 : δ₁ ≤ 1
  hcJ : 0 ≤ cJ
  hK : ∀ W : Finset (Lam d L N), IsConn j W →
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (thetaE (K W) : Alg2 d L N) ≤ ENNReal.ofReal (κ₀ * ρ ^ nb j W)
  hdI : ∀ b ∈ blockIdx (L := L) (N := N) j,
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (gdI Ib Ip b : Alg2 d L N) ≤ ENNReal.ofReal (δ₁ * ρ)
  hJ : ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ X : Finset (Lam d L N),
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (thetaE (J b X) : Alg2 d L N) ≤
      ENNReal.ofReal (cJ * κ₀ * ρ ^ 2 ^ d)
  hJs : ∀ b (X : Finset (Lam d L N)), ¬ IsSmall j X → J b X = 0

namespace GH

variable {j : ℕ} {Ib Ip : (Fin d → ℕ) → EvR (Lam d L N)} {K : Act d L N}
  {J : (Fin d → ℕ) → Finset (Lam d L N) → EvR (Lam d L N)} {h' ℓ' ℓC ρ κ₀ δ₁ cJ : ℝ}
  (H : GH j Ib Ip K J h' ℓ' ℓC ρ κ₀ δ₁ cJ)
include H

theorem Kext_le {Z : Finset (Lam d L N)} (hZ : IsPolymer j Z) :
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (thetaE (Kext j K Z) : Alg2 d L N) ≤
      ENNReal.ofReal (κ₀ ^ (Comp j Z).card * ρ ^ nb j Z) := by
  have hρ := H.hρ
  have hκ := H.hκ₀
  rw [Kext, map_prod]
  have := t2_prodE (E := Dir d) (p := pPhi d) (ℓC := ℓC) H.hh' H.hℓ' (Comp j Z) (fun W => thetaE (K W))
    (fun W => κ₀ * ρ ^ nb j W) (fun W _ => by positivity)
    (fun W hW => H.hK W (isConn_of_mem_comp hZ hW))
  rwa [prod_mul_distrib, prod_const, prod_comp_pow hZ] at this

theorem dIPow_le (W : Finset (Lam d L N)) :
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (gdIPow j Ib Ip W : Alg2 d L N) ≤
      ENNReal.ofReal ((δ₁ * ρ) ^ nb j W) := by
  have hρ := H.hρ
  have hδ := H.hδ₁
  have := t2_prodE (E := Dir d) (p := pPhi d) (ℓC := ℓC) H.hh' H.hℓ' (blocks j W) (gdI Ib Ip)
    (fun _ => δ₁ * ρ) (fun _ _ => by positivity)
    (fun b hb => H.hdI b (mem_blockIdx_of_mem_blocks hb))
  rwa [prod_const] at this

/-- `‖K̃(Y)‖ ≤ (κ₀ + δ₁) (2ρ)^{|𝓑(Y)|}` for a non-empty polymer `Y`. -/
theorem Ktil_le {Y : Finset (Lam d L N)} (hY : IsPolymer j Y) (hne : Y ≠ ∅) :
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (gKtil j Ib Ip K Y : Alg2 d L N) ≤
      ENNReal.ofReal ((κ₀ + δ₁) * (2 * ρ) ^ nb j Y) := by
  have hρ := H.hρ
  have hκ := H.hκ₀
  have hδ := H.hδ₁
  rw [gKtil]
  refine (t2_sum_const (E := Dir d) (p := pPhi d) _ _ (r := (κ₀ + δ₁) * ρ ^ nb j Y)
    (by positivity) fun W hW => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hWs, hWp⟩ := mem_Pj.1 hW
    have hYW : IsPolymer j (Y \ W) := IsPolymer.sdiff hY hWp
    refine (t2_mulE H.hh' H.hℓ' (by positivity) (H.Kext_le hYW) (H.dIPow_le W)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have e : ρ ^ nb j (Y \ W) * ρ ^ nb j W = ρ ^ nb j Y := by
      rw [← pow_add, nb_sdiff_add hY hWp hWs]
    have hkd : κ₀ ^ (Comp j (Y \ W)).card * δ₁ ^ nb j W ≤ κ₀ + δ₁ := by
      by_cases hW0 : W = Y
      · have hn : nb j W ≠ 0 := fun h0 => hne (hW0 ▸ nb_eq_zero_iff.1 h0)
        have h1 : κ₀ ^ (Comp j (Y \ W)).card ≤ 1 := pow_le_one₀ hκ H.hκ₀1
        have h2 : δ₁ ^ nb j W ≤ δ₁ := pow_le_of_le_one hδ H.hδ₁1 hn
        calc κ₀ ^ (Comp j (Y \ W)).card * δ₁ ^ nb j W ≤ 1 * δ₁ := by gcongr
          _ ≤ κ₀ + δ₁ := by linarith
      · have hne' : Y \ W ≠ ∅ := by
          intro he
          exact hW0 (Subset.antisymm hWs (sdiff_eq_empty_iff_subset.1 he))
        have hc : (Comp j (Y \ W)).card ≠ 0 := fun h0 => hne' ((comp_card_eq_zero_iff hYW).1 h0)
        have h1 : κ₀ ^ (Comp j (Y \ W)).card ≤ κ₀ := pow_le_of_le_one hκ H.hκ₀1 hc
        have h2 : δ₁ ^ nb j W ≤ 1 := pow_le_one₀ hδ H.hδ₁1
        calc κ₀ ^ (Comp j (Y \ W)).card * δ₁ ^ nb j W ≤ κ₀ * 1 := by gcongr
          _ ≤ κ₀ + δ₁ := by linarith
    calc κ₀ ^ (Comp j (Y \ W)).card * ρ ^ nb j (Y \ W) * (δ₁ * ρ) ^ nb j W
        = (κ₀ ^ (Comp j (Y \ W)).card * δ₁ ^ nb j W) * (ρ ^ nb j (Y \ W) * ρ ^ nb j W) := by
          rw [mul_pow]; ring
      _ ≤ (κ₀ + δ₁) * ρ ^ nb j Y := by rw [e]; gcongr
  · have hc : ((Pj j Y).card : ℝ) = 2 ^ nb j Y := by exact_mod_cast card_Pj hY
    rw [hc, mul_pow]
    linarith [show (0 : ℝ) ≤ (κ₀ + δ₁) * ρ ^ nb j Y * 2 ^ nb j Y by positivity]

theorem Jsum_le {Y : Finset (Lam d L N)} :
    T2 (Dir d) (pPhi d) h' ℓ' ℓC
      ((∑ b ∈ blocks j Y, thetaE (J b Y) : EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal (2 ^ d * cJ * κ₀ * ρ ^ nb j Y) := by
  have hρ := H.hρ
  have hκ := H.hκ₀
  have hc := H.hcJ
  classical
  by_cases hs : IsSmall j Y
  · have := t2_sum_const (E := Dir d) (p := pPhi d) (ℓC := ℓC) (blocks j Y) (fun b => thetaE (J b Y))
      (r := cJ * κ₀ * ρ ^ 2 ^ d) (by positivity)
      (fun b hb => H.hJ b (mem_blockIdx_of_mem_blocks hb) Y)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have hn : ((blocks j Y).card : ℝ) ≤ 2 ^ d := by exact_mod_cast hs.2.2
    have hp : ρ ^ 2 ^ d ≤ ρ ^ nb j Y := pow_le_pow_of_le_one hρ H.hρ1 hs.2.2
    calc ((blocks j Y).card : ℝ) * (cJ * κ₀ * ρ ^ 2 ^ d)
        ≤ 2 ^ d * (cJ * κ₀ * ρ ^ nb j Y) := by gcongr
      _ = 2 ^ d * cJ * κ₀ * ρ ^ nb j Y := by ring
  · have h0 : (∑ b ∈ blocks j Y, thetaE (J b Y) : EvR (Lam d L N ⊕ Lam d L N)) = 0 := by
      refine sum_eq_zero fun b _ => ?_
      rw [H.hJs b Y hs, map_zero]
    rw [h0, ZeroMemClass.coe_zero, T2_zero]
    exact zero_le

/-- `‖Ǩ(Y)‖ ≤ β (2ρ)^{|𝓑(Y)|}` for connected `Y`. -/
theorem KchkC_le {Y : Finset (Lam d L N)} (hY : IsConn j Y) :
    T2 (Dir d) (pPhi d) h' ℓ' ℓC (gKchkC j Ib Ip K J Y : Alg2 d L N) ≤
      ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) * (2 * ρ) ^ nb j Y) := by
  have hρ := H.hρ
  have hκ := H.hκ₀
  have hδ := H.hδ₁
  have hc := H.hcJ
  have hne : Y ≠ ∅ := fun h => not_isConn_empty (h ▸ hY)
  rw [gKchkC]
  refine (t2_subE (by positivity) (by positivity) (H.Ktil_le hY.1 hne) H.Jsum_le).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have : ρ ^ nb j Y ≤ (2 * ρ) ^ nb j Y := pow_le_pow_left₀ hρ (by linarith) _
  have h0 : 0 ≤ 2 ^ d * cJ * κ₀ := by positivity
  calc (κ₀ + δ₁) * (2 * ρ) ^ nb j Y + 2 ^ d * cJ * κ₀ * ρ ^ nb j Y
      ≤ (κ₀ + δ₁) * (2 * ρ) ^ nb j Y + 2 ^ d * cJ * κ₀ * (2 * ρ) ^ nb j Y := by gcongr
    _ = _ := by ring

/-- The integrand of `K_{j+1}(U)`: `‖Ǩ(X̌) ∏_{𝒳} θ J‖ ≤ β^m (2ρ)^{|𝓑(X̌)|}`. -/
theorem integrand_le {g : GT d L N} (hg2 : IsPolymer j g.2)
    (hg1 : ∀ p ∈ g.1, p.1 ∈ blockIdx (L := L) (N := N) j) :
    T2 (Dir d) (pPhi d) h' ℓ' ℓC ((gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2) :
      EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal (((1 + 2 ^ d * cJ) * κ₀ + δ₁) ^ ((Comp j g.2).card + g.1.card) *
        (2 * ρ) ^ nb j g.2) := by
  have hρ := H.hρ
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁
  have hβ0 : 0 ≤ β := by positivity
  have hK1 : T2 (Dir d) (pPhi d) h' ℓ' ℓC (gKchk j Ib Ip K J g.2 : Alg2 d L N) ≤
      ENNReal.ofReal (β ^ (Comp j g.2).card * (2 * ρ) ^ nb j g.2) := by
    have := t2_prodE (E := Dir d) (p := pPhi d) (ℓC := ℓC) H.hh' H.hℓ' (Comp j g.2) (gKchkC j Ib Ip K J)
      (fun Y => β * (2 * ρ) ^ nb j Y) (fun _ _ => by positivity)
      (fun Y hY => H.KchkC_le (isConn_of_mem_comp hg2 hY))
    rwa [prod_mul_distrib, prod_const, prod_comp_pow hg2] at this
  have hJ : T2 (Dir d) (pPhi d) h' ℓ' ℓC
      ((∏ p ∈ g.1, thetaE (J p.1 p.2) : EvR (Lam d L N ⊕ Lam d L N)) : Alg2 d L N) ≤
      ENNReal.ofReal (β ^ g.1.card) := by
    have := t2_prodE (E := Dir d) (p := pPhi d) (ℓC := ℓC) H.hh' H.hℓ' g.1
      (fun p => thetaE (J p.1 p.2)) (fun _ => β) (fun _ _ => hβ0)
      (fun p hp => (H.hJ p.1 (hg1 p hp) p.2).trans (ENNReal.ofReal_le_ofReal (by
        have h1 : ρ ^ 2 ^ d ≤ 1 := pow_le_one₀ hρ H.hρ1
        have h2 : cJ ≤ 2 ^ d * cJ := le_mul_of_one_le_left hc (one_le_pow₀ (by norm_num))
        calc cJ * κ₀ * ρ ^ 2 ^ d ≤ cJ * κ₀ * 1 := by gcongr
          _ ≤ β := by nlinarith)))
    rwa [prod_const] at this
  refine (t2_mulE H.hh' H.hℓ' (by positivity) hK1 hJ).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [pow_add]; ring_nf; rfl

/-- **The crude bound** for the whole sum over `𝒢(U)`. -/
theorem gKnext_le (C : Matrix (Lam d L N) (Lam d L N) ℂ) {U : Finset (Lam d L N)} (c : ℂ)
    {Ar Q η P : ℝ} {M : ℕ} (hAr : 1 ≤ Ar) (hρA : ρ = Ar⁻¹) (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    (hE : ∀ F : Alg2 d L N, tNorm (Dir d) (pPhi d) h' ℓ' (ECC C F) ≤ T2 (Dir d) (pPhi d) h' ℓ' ℓC F)
    (hpref : ∀ g ∈ Gset j U, tNorm (Dir d) (pPhi d) h' ℓ'
      ((c • bpow j Ip (U \ (g.2 ∪ Xcal g.1)) : EvR (Lam d L N)) : Alg d L N) ≤
        ENNReal.ofReal (2 ^ nb (j + 1) U))
    (hcount : (Gset j U).card ≤ M ^ nb (j + 1) U)
    (hgeom : ∀ g ∈ Gset j U, (1 + 2 * η) * (nb (j + 1) U : ℝ) ≤
      nb j g.2 + (1 + 2 * η) * 2 ^ d * ((Comp j g.2).card + g.1.card))
    (hP : P = Q * (2 * M)) (hM : 1 ≤ M) (hAP : 4 * P ≤ Ar ^ (2 * η / (1 + 2 * η)))
    (hDβ : (Ar * P) ^ 2 ^ d * ((1 + 2 ^ d * cJ) * κ₀ + δ₁) ≤ 1) :
    ENNReal.ofReal ((Ar * Q) ^ nb (j + 1) U) *
      tNorm (Dir d) (pPhi d) h' ℓ' ((c • gKnext j C Ib Ip K J U : EvR (Lam d L N)) : Alg d L N) ≤
      ENNReal.ofReal 1 := by
  classical
  have hA0 : 0 < Ar := by linarith
  have hρ := H.hρ
  have hκ := H.hκ₀
  have hc := H.hcJ
  have hδ := H.hδ₁
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hP1 : 1 ≤ P := by rw [hP]; nlinarith
  set x := nb (j + 1) U
  set β := (1 + 2 ^ d * cJ) * κ₀ + δ₁ with hβdef
  have hβ0 : 0 ≤ β := by positivity
  have e : c • gKnext j C Ib Ip K J U = ∑ g ∈ Gset j U,
      (c • bpow j Ip (U \ (g.2 ∪ Xcal g.1))) *
        ECCE C (gKchk j Ib Ip K J g.2 * ∏ p ∈ g.1, thetaE (J p.1 p.2)) := by
    rw [gKnext, smul_sum]; exact sum_congr rfl fun g _ => (smul_mul_assoc _ _ _).symm
  rw [e]
  refine wsum_bound _ _ (M ^ x) hcount (by positivity) fun g hg => ?_
  obtain ⟨f1, -, -, f4⟩ := Gset_facts hg
  have hI := H.integrand_le f1 (fun p hp => (mem_pairsU.1 (f4 p hp).1).1)
  have hT := tn_mulE (E := Dir d) (p := pPhi d) H.hh' H.hℓ' (by positivity) (hpref g hg)
    (show tNorm (Dir d) (pPhi d) h' ℓ' (ECCE C (gKchk j Ib Ip K J g.2 *
        ∏ p ∈ g.1, thetaE (J p.1 p.2)) : Alg d L N) ≤ _ from (hE _).trans hI)
  refine (mul_le_mul_left' hT _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set m := (Comp j g.2).card + g.1.card
  set t := nb j g.2
  have hgeo := geom_real (d := d) (x := x) (t := t) (m := m) hAr hP1 hη
    (by
      rw [show ((m : ℕ) : ℝ) = ((Comp j g.2).card : ℝ) + g.1.card by push_cast [m]; ring]
      exact hgeom g hg) hAP
  have h2 : (2 * ρ) ^ t ≤ (4 * Ar⁻¹) ^ t := by
    rw [hρA]; gcongr; norm_num
  have hpm : ((Ar * P) ^ 2 ^ d) ^ m * β ^ m ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by positivity) hDβ
  calc ((M ^ x : ℕ) : ℝ) * (Ar * Q) ^ x * (2 ^ x * (β ^ m * (2 * ρ) ^ t))
      ≤ ((M ^ x : ℕ) : ℝ) * (Ar * Q) ^ x * (2 ^ x * (β ^ m * (4 * Ar⁻¹) ^ t)) := by gcongr
    _ = (Ar ^ x * P ^ x * (4 * Ar⁻¹) ^ t) * β ^ m := by
        rw [hP, mul_pow, mul_pow, mul_pow]; push_cast; ring
    _ ≤ (Ar * P) ^ (2 ^ d * m) * β ^ m := by gcongr
    _ = ((Ar * P) ^ 2 ^ d) ^ m * β ^ m := by rw [pow_mul]
    _ ≤ 1 := hpm

end GH

end

end Step2
