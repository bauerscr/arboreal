import DressedFRD.Adapted
import DressedFRD.MainFull

/-!
# `thm:main`(ii): holomorphy

`Γ^int_{j+1}(ζ)` and `Γ_{j+1}(ζ)` are, for each momentum, holomorphic functions of
`(ζ_0, …, ζ_j)` on the polydisc `|ζ_i| < ζ̄` (`thm_main_hol`). All objects are finite rational
expressions in the `ζ_i`; the denominators `1 + ζ_i`, `Z_k`, `1 - ζ'_k ε_k` and
`1 + z_j A Γ_j` do not vanish there by `thm_main`.

The couplings `z : Fin J → ℂ` are extended by zero (`ext`), and `Dz D z = D` with couplings `z`.
-/

namespace DressedFRD

noncomputable section

open Finset Complex FRD Grassmann

variable {d n : ℕ} [NeZero n]

/-- Functions differentiable at `z₀`. -/
def holSub {J : ℕ} (z₀ : Fin J → ℂ) : Subring ((Fin J → ℂ) → ℂ) where
  carrier := {F | DifferentiableAt ℂ F z₀}
  mul_mem' ha hb := DifferentiableAt.mul ha hb
  one_mem' := differentiableAt_const _
  add_mem' ha hb := DifferentiableAt.add ha hb
  zero_mem' := differentiableAt_const _
  neg_mem' ha := DifferentiableAt.neg ha

namespace Data

variable {J : ℕ}

/-- Extension by zero. -/
def ext (z : Fin J → ℂ) : ℕ → ℂ := fun i => if h : i < J then z ⟨i, h⟩ else 0

/-- `D` with couplings `z`. -/
def Dz (D : Data d n) (z : Fin J → ℂ) : Data d n := D.withζ (ext z)

variable {D : Data d n} {z₀ : Fin J → ℂ}

namespace Hol

local notation "H" => holSub z₀

theorem mem_holSub {F : (Fin J → ℂ) → ℂ} : F ∈ H ↔ DifferentiableAt ℂ F z₀ := Iff.rfl

theorem const_mem (c : ℂ) : (fun _ => c) ∈ H := differentiableAt_const c

theorem ext_mem (i : ℕ) : (fun z : Fin J → ℂ => ext z i) ∈ H := by
  unfold ext
  by_cases h : i < J
  · simp only [h, dif_pos]; exact differentiableAt_apply (𝕜 := ℂ) _ _
  · simp only [h, dif_neg, not_false_eq_true]; exact const_mem 0

theorem inv_mem {F : (Fin J → ℂ) → ℂ} (hF : F ∈ H) (h0 : F z₀ ≠ 0) :
    (fun z => (F z)⁻¹) ∈ H := (mem_holSub.1 hF).inv h0

theorem div_mem' {F G : (Fin J → ℂ) → ℂ} (hF : F ∈ H) (hG : G ∈ H) (h0 : G z₀ ≠ 0) :
    (fun z => F z / G z) ∈ H := by
  simp_rw [div_eq_mul_inv]; exact Subring.mul_mem _ hF (inv_mem hG h0)

theorem fsum_mem {ι : Type*} (s : Finset ι) {g : ι → (Fin J → ℂ) → ℂ} (h : ∀ i ∈ s, g i ∈ H) :
    (fun z => ∑ i ∈ s, g i z) ∈ H := by
  have := Subring.sum_mem (holSub z₀) h; rwa [Finset.sum_fn] at this

theorem fprod_mem {ι : Type*} (s : Finset ι) {g : ι → (Fin J → ℂ) → ℂ} (h : ∀ i ∈ s, g i ∈ H) :
    (fun z => ∏ i ∈ s, g i z) ∈ H := by
  have := Subring.prod_mem (holSub z₀) h; rwa [Finset.prod_fn] at this

theorem Z_mem (k : ℕ) : (fun z => (D.Dz z).Z k) ∈ H := by
  simp only [Z]
  refine fprod_mem _ fun i _ => ?_
  exact Subring.add_mem _ (Subring.one_mem _) (ext_mem i)

theorem zp_mem {k : ℕ} (h : 1 + ext z₀ k ≠ 0) : (fun z => (D.Dz z).zp k) ∈ H :=
  div_mem' (ext_mem k) (Subring.add_mem _ (Subring.one_mem _) (ext_mem k)) h

/-- A family of tails, holomorphic at `z₀` at each momentum. -/
def HolFam (R : (Fin J → ℂ) → ℕ → Sym d n) : Prop := ∀ r m, (fun z => R z r m) ∈ H

theorem letV_mem {k : ℕ} {R : (Fin J → ℂ) → ℕ → Sym d n} (hR : HolFam (z₀ := z₀) R)
    (κ : Fin 3) (ℓ : Option ℕ) (m : Torus d n) :
    (fun z => (D.Dz z).letV k (R z) κ ℓ m) ∈ H := by
  have hZ := Z_mem (D := D) (z₀ := z₀) k
  rcases ℓ with _ | r <;> fin_cases κ
  · exact const_mem (Cle D.C k m)
  · exact const_mem ((1 - Ehat D.msq D.C k) m)
  · exact const_mem (Ehat D.msq D.C k m)
  · exact Subring.neg_mem _ (Subring.mul_mem _ hZ (hR r m))
  · exact Subring.mul_mem _ hZ (Subring.mul_mem _ (const_mem (Asym D.msq m)) (hR r m))
  · exact Subring.neg_mem _ (Subring.mul_mem _ hZ
      (Subring.mul_mem _ (const_mem (Asym D.msq m)) (hR r m)))

theorem eps_mem {k : ℕ} {R : (Fin J → ℂ) → ℕ → Sym d n} (hR : HolFam (z₀ := z₀) R)
    (m : Torus d n) : (fun z => (D.Dz z).eps k (R z) m) ∈ H := by
  simp only [eps, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  exact Subring.sub_mem _ (const_mem (Ehat D.msq D.C k m)) (fsum_mem (Ioc k D.N) fun r _ =>
    Subring.mul_mem _ (Z_mem (D := D) k) (Subring.mul_mem _ (const_mem (Asym D.msq m)) (hR r m)))

theorem wLen_mem {k : ℕ} {R : (Fin J → ℂ) → ℕ → Sym d n} (hR : HolFam (z₀ := z₀) R)
    (s l : ℕ) (m : Torus d n) : (fun z => (D.Dz z).wLen k (R z) s l m) ∈ H := by
  show (fun z => (∑ w ∈ (words k D.N l).filter (fun w => scale D.L k D.N (rbar (D.rbV k) w) = s),
    wordVal ((D.Dz z).letV k (R z)) w) m) ∈ H
  simp only [Finset.sum_apply, wordVal, Finset.prod_apply]
  exact fsum_mem _ fun w _ => fprod_mem _ fun i _ => letV_mem hR _ _ m

theorem wLow_mem {k : ℕ} (h : 1 + ext z₀ k ≠ 0) {R : (Fin J → ℂ) → ℕ → Sym d n}
    (hR : HolFam (z₀ := z₀) R) (s : ℕ) (m : Torus d n) :
    (fun z => (D.Dz z).wLow k (R z) s m) ∈ H := by
  show (fun z => (∑ l ∈ range (D.L ^ s), (D.Dz z).zp k ^ (l + 1) • (D.Dz z).wLen k (R z) s l) m) ∈ H
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact fsum_mem _ fun l _ =>
    Subring.mul_mem _ (Subring.pow_mem _ (zp_mem h) _) (wLen_mem hR s l m)

theorem wTot_mem {k : ℕ} (h : 1 + ext z₀ k ≠ 0) {R : (Fin J → ℂ) → ℕ → Sym d n}
    (hR : HolFam (z₀ := z₀) R) (m : Torus d n)
    (hden : 1 - (D.Dz z₀).zp k * (D.Dz z₀).eps k (R z₀) m ≠ 0) :
    (fun z => (D.Dz z).wTot k (R z) m) ∈ H := by
  simp only [wTot]
  have he := eps_mem (D := D) (k := k) hR m
  have hz := zp_mem (D := D) h
  refine div_mem' (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hz (const_mem (Asym D.msq m)⁻¹)) he)
    (Subring.sub_mem _ (Subring.one_mem _) he))
    (Subring.sub_mem _ (Subring.one_mem _) (Subring.mul_mem _ hz he)) hden

theorem wSc_mem {k : ℕ} (h : 1 + ext z₀ k ≠ 0) {R : (Fin J → ℂ) → ℕ → Sym d n}
    (hR : HolFam (z₀ := z₀) R) (s : ℕ) (m : Torus d n)
    (hden : 1 - (D.Dz z₀).zp k * (D.Dz z₀).eps k (R z₀) m ≠ 0) :
    (fun z => (D.Dz z).wSc k (R z) s m) ∈ H := by
  by_cases hs : s < D.N
  · show (fun z => (if s < D.N then (D.Dz z).wLow k (R z) s else (D.Dz z).wTop k (R z)) m) ∈ H
    simp only [hs, if_true]; exact wLow_mem h hR s m
  · show (fun z => (if s < D.N then (D.Dz z).wLow k (R z) s else (D.Dz z).wTop k (R z)) m) ∈ H
    simp only [hs, if_false]
    show (fun z => ((D.Dz z).wTot k (R z) - ∑ s ∈ Ico (k + 1) D.N, (D.Dz z).wLow k (R z) s) m) ∈ H
    simp only [Pi.sub_apply, Finset.sum_apply]
    exact Subring.sub_mem _ (wTot_mem h hR m hden) (fsum_mem _ fun s _ => wLow_mem h hR s m)

theorem Z_ne_zero' (h : ∀ i, 1 + ext z₀ i ≠ 0) (k : ℕ) : (D.Dz z₀).Z k ≠ 0 :=
  prod_ne_zero_iff.2 fun i _ => h i

/-- The tails are holomorphic, given the denominators at `z₀`. -/
theorem tails_mem (h : ∀ i, 1 + ext z₀ i ≠ 0) :
    ∀ k, (∀ k' < k, ∀ m, 1 - (D.Dz z₀).zp k' * (D.Dz z₀).eps k' ((D.Dz z₀).tails k') m ≠ 0) →
      HolFam (z₀ := z₀) fun z => (D.Dz z).tails k
  | 0, _ => fun r m => const_mem 0
  | k + 1, hden => fun r m => by
    have ih := tails_mem h k fun k' hk' => hden k' (by omega)
    show (fun z => (if k + 2 ≤ r ∧ r ≤ D.N then
      ((D.Dz z).Z (k + 1))⁻¹ • ((D.Dz z).Z k • (D.Dz z).tails k r +
        (D.Dz z).wSc k ((D.Dz z).tails k) r) else 0) m) ∈ H
    split_ifs
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      exact Subring.mul_mem _ (inv_mem (Z_mem _) (Z_ne_zero' h _))
        (Subring.add_mem _ (Subring.mul_mem _ (Z_mem k) (ih r m))
          (wSc_mem (h k) ih r m (hden k (by omega) m)))
    · exact const_mem 0

theorem Gam_mem (h : ∀ i, 1 + ext z₀ i ≠ 0) {k : ℕ}
    (hden : ∀ k' < k, ∀ m, 1 - (D.Dz z₀).zp k' * (D.Dz z₀).eps k' ((D.Dz z₀).tails k') m ≠ 0)
    (m : Torus d n) : (fun z => (D.Dz z).Gam k m) ∈ H := by
  show (fun z => ((D.Dz z).Z k)⁻¹ * Cgt D.C D.N k m + (∑ r ∈ Ioc k D.N, (D.Dz z).tails k r) m) ∈ H
  simp only [Finset.sum_apply]
  exact Subring.add_mem _ (Subring.mul_mem _ (inv_mem (Z_mem k) (Z_ne_zero' h k)) (const_mem _))
    (fsum_mem _ fun r _ => tails_mem h k hden r m)

theorem Gint_mem (h : ∀ i, 1 + ext z₀ i ≠ 0) {j : ℕ}
    (hden : ∀ k ≤ j, ∀ m, 1 - (D.Dz z₀).zp k * (D.Dz z₀).eps k ((D.Dz z₀).tails k) m ≠ 0)
    (hden' : ∀ m, 1 + (D.Dz z₀).ζ j * (D.Dz z₀).Z j * Asym D.msq m * (D.Dz z₀).Gam j m ≠ 0)
    (m : Torus d n) : (fun z => (D.Dz z).Gint j m) ∈ H := by
  have hR := tails_mem (D := D) h j fun k hk => hden k hk.le
  by_cases hj : j + 1 < D.N
  · show (fun z => (if j + 1 < D.N then ((D.Dz z).Z (j + 1))⁻¹ • (ofR (D.C (j + 1)) +
      (D.Dz z).Z j • (D.Dz z).tails j (j + 1) + (D.Dz z).wSc j ((D.Dz z).tails j) (j + 1))
      else (D.Dz z).absorbed j) m) ∈ H
    simp only [hj, if_true, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact Subring.mul_mem _ (inv_mem (Z_mem _) (Z_ne_zero' h _))
      (Subring.add_mem _ (Subring.add_mem _ (const_mem _) (Subring.mul_mem _ (Z_mem j) (hR _ m)))
        (wSc_mem (h j) hR _ m (hden j le_rfl m)))
  · show (fun z => (if j + 1 < D.N then ((D.Dz z).Z (j + 1))⁻¹ • (ofR (D.C (j + 1)) +
      (D.Dz z).Z j • (D.Dz z).tails j (j + 1) + (D.Dz z).wSc j ((D.Dz z).tails j) (j + 1))
      else (D.Dz z).absorbed j) m) ∈ H
    simp only [hj, if_false, absorbed]
    have hG := Gam_mem (D := D) h (k := j) (fun k hk => hden k hk.le) m
    exact div_mem' hG (Subring.add_mem _ (Subring.one_mem _) (Subring.mul_mem _
      (Subring.mul_mem _ (Subring.mul_mem _ (ext_mem j) (Z_mem j)) (const_mem (Asym D.msq m))) hG)) (hden' m)

end Hol

end Data

open Data

/-- `thm:main` with (ii): in addition to the conclusions of `thm_main_full`, `Γ^int_{j+1}` and
`Γ_{j+1}` are holomorphic in `(ζ_0, …, ζ_j)` on the polydisc `|ζ_i| < ζ̄`. Reality and
adaptedness are `Data.Gint_mem`, `Data.Gint_congr`. -/
theorem thm_main_hol {d q L M : ℕ} {cS : ℝ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L)
    (hM : q + d + 1 ≤ M) (hcS : 0 ≤ cS) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, ∀ (n : ℕ) [NeZero n] (D : Data d n), D.L = L →
      n = L ^ D.N → StdFull L D.N q M D.msq cS D.C →
      D.msq ≤ (L : ℝ) ^ (-(2 * ((D.N : ℝ) - 1))) →
      ((∀ i, ‖D.ζ i‖ ≤ ζbar) → ∀ j, j < D.N → D.Concl q ζbar K j) ∧
      ∀ j, j < D.N → ∀ m,
        DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => (D.Dz z).Gint j m)
          {z | ∀ i, ‖z i‖ < ζbar} ∧
        DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => (D.Dz z).Gam (j + 1) m)
          {z | ∀ i, ‖z i‖ < ζbar} := by
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main_full hd hq hL hM hcS
  refine ⟨ζbar, hζ, hζ8, K, fun n _ D hDL hn hS hmsq => ⟨hK n D hDL hn hS hmsq, ?_⟩⟩
  intro j hj m
  -- at each point of the polydisc, the conclusions of `thm_main` hold for `D.Dz z₀`
  have key : ∀ z₀ : Fin (j + 1) → ℂ, (∀ i, ‖z₀ i‖ < ζbar) →
      (∀ i, 1 + Data.ext z₀ i ≠ 0) ∧ ∀ k, k < D.N → (D.Dz z₀).Concl q ζbar K k := by
    intro z₀ hz₀
    have hb : ∀ i, ‖Data.ext z₀ i‖ ≤ ζbar := fun i => by
      unfold Data.ext; split_ifs
      · exact (hz₀ _).le
      · simp [hζ.le]
    refine ⟨fun i h0 => ?_, hK n (D.Dz z₀) hDL hn hS hmsq hb⟩
    have : Data.ext z₀ i = -1 := by linear_combination h0
    have := hb i; rw [‹Data.ext z₀ i = -1›] at this; norm_num at this; linarith
  refine ⟨fun z₀ hz₀ => ?_, fun z₀ hz₀ => ?_⟩
  · obtain ⟨h1, hc⟩ := key z₀ hz₀
    exact (Hol.Gint_mem (D := D) h1 (fun k hk => (hc k (by omega)).den_eps)
      (hc j hj).den m).differentiableWithinAt
  · obtain ⟨h1, hc⟩ := key z₀ hz₀
    exact (Hol.Gam_mem (D := D) (k := j + 1) h1 (fun k hk => (hc k (by omega)).den_eps)
      m).differentiableWithinAt

end

end DressedFRD
