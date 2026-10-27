module

public import ArborealDecay.Super.ComposeDiff

/-!
# The composition rule `g(h(a)) = (g ∘ h)(a)`

For an even `a` with body `s` and smooth `h` near `s`, `g` near `h(s)`,
`scomp g (scomp h a) = scomp (g ∘ h) a` (`scomp_scomp`).

Proof (avoiding Faà di Bruno).  Let `n = soul a` and `a_t = s + t n`.  For `φ` smooth near
`h(s)` put `D_φ(t) = φ(h(a_t)) - (φ ∘ h)(a_t)`.  The chain rules (`pd_scomp`) and the product
rule (`scomp_mul_fun`) give `D_φ' = D_{φ'} · h'(a_t) · n`, and `D_φ(0) = 0`.  By downward
induction on `j`, `D_φ · n^j ≡ 0` for every `φ`: it holds for `j = |O| + 1` since `n^{|O|+1} = 0`,
and if it holds for `j + 1` (and all `φ`), then `(D_φ · n^j)' = D_{φ'} n^{j+1} h'(a_t) = 0`, so
`D_φ · n^j` is constant, equal to its value `0` at `t = 0`.  At `j = 0`, `t = 1` this is the claim.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open Filter Topology Finset
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- `g(a)` only depends on the germ of `g` at `body a`. -/
theorem scomp_congr {f₁ f₂ : ℝ → ℝ} {a : Gr O} (h : f₁ =ᶠ[𝓝 (body a)] f₂) :
    scomp f₁ a = scomp f₂ a := by
  unfold scomp jet
  exact sum_congr rfl fun k _ => by rw [h.iteratedDeriv_eq k]

/-- The path `t ↦ s + t n`. -/
def apath (s : ℝ) (n : Gr O) (t : ℝ) : Gr O := s • (1 : Gr O) + t • n

theorem differentiable_id_fun : Differentiable ℝ fun t : ℝ => t := differentiable_id

theorem sdiff_apath (s : ℝ) (n : Gr O) : SDiff (apath s n) :=
  (SDiff.const _).add (SDiff.smul differentiable_id_fun (SDiff.const n))

theorem pd_apath (s : ℝ) (n : Gr O) (t : ℝ) : pd 1 (apath s n) t = n := by
  rw [show apath s n = fun t => s • (1 : Gr O) + t • n from rfl,
    pd_add (SDiff.const _) (SDiff.smul differentiable_id_fun (SDiff.const n)), pd_const,
    pd_smul_const differentiable_id_fun]
  simp

theorem body_apath (s : ℝ) {n : Gr O} (hn : body n = 0) (t : ℝ) : body (apath s n t) = s := by
  simp [apath, hn]

theorem isEven_apath (s : ℝ) {n : Gr O} (hn : IsEven n) (t : ℝ) : IsEven (apath s n t) :=
  (IsEven.one.smul s).add (hn.smul t)

/-- A differentiable `Gr O`-valued function on `ℝ` with vanishing derivative is constant. -/
theorem eq_of_pd_eq_zero {F : ℝ → Gr O} (hF : SDiff F) (h0 : ∀ t, pd 1 F t = 0) (t t' : ℝ) :
    F t = F t' := by
  refine ext_dual fun ℓ => ?_
  have hd : ∀ x, deriv (fun y => ℓ (F y)) x = 0 := fun x => by
    rw [← fderiv_apply_one_eq_deriv, ← dual_pd hF, h0, map_zero]
  exact is_const_of_deriv_eq_zero (hF ℓ) hd t t'

/-- **Composition rule** `g(h(a)) = (g ∘ h)(a)` for even `a`, with `h` smooth on an open set
containing `body a` and `g` smooth on an open set containing `h (body a)`. -/
theorem scomp_scomp {g h : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h V) {a : Gr O} (ha : IsEven a)
    (hs : body a ∈ V) (hhs : h (body a) ∈ U) :
    scomp g (scomp h a) = scomp (fun x => g (h x)) a := by
  set s := body a
  set n := soul a
  have hn : IsEven n := ha.soul
  have hn0 : body n = 0 := body_soul a
  set W := V ∩ h ⁻¹' U
  have hW : IsOpen W := hh.continuousOn.isOpen_inter_preimage hV hU
  have hsW : s ∈ W := ⟨hs, hhs⟩
  have hhW : ContDiffOn ℝ ∞ h W := hh.mono Set.inter_subset_left
  -- facts about the path
  have hP : SDiff (apath s n) := sdiff_apath s n
  have hPE : ∀ t, IsEven (apath s n t) := isEven_apath s hn
  have hPb : ∀ t, body (apath s n t) = s := body_apath s hn0
  have hHb : ∀ t, body (scomp h (apath s n t)) = h s := fun t => by
    rw [body_scomp _ (isNilpotent_soul (hPE t)), hPb]
  have hH : SDiff fun t : ℝ => scomp h (apath s n t) :=
    SDiff.scomp hV hh hP hPE fun t => by rw [hPb]; exact hs
  have hHE : ∀ t, IsEven (scomp h (apath s n t)) := fun t => (hPE t).scomp h
  have hpdH : ∀ t : ℝ, pd 1 (fun t : ℝ => scomp h (apath s n t)) t =
      scomp (deriv h) (apath s n t) * n := fun t => by
    rw [pd_scomp hV hh hP hPE (fun t => by rw [hPb]; exact hs), pd_apath]
  -- the defect `D_φ`
  let D : (ℝ → ℝ) → ℝ → Gr O := fun φ t =>
    scomp φ (scomp h (apath s n t)) - scomp (fun x => φ (h x)) (apath s n t)
  have hcomp : ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → ContDiffOn ℝ ∞ (fun x => φ (h x)) W := fun φ hφ =>
    hφ.comp hhW (fun x hx => hx.2)
  have hD_sdiff : ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → SDiff (D φ) := fun φ hφ =>
    (SDiff.scomp hU hφ hH hHE fun t => by rw [hHb]; exact hhs).sub
      (SDiff.scomp hW (hcomp φ hφ) hP hPE fun t => by rw [hPb]; exact hsW)
  have hD0 : ∀ φ : ℝ → ℝ, D φ 0 = 0 := fun φ => by
    simp only [D, apath, zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, scomp_algebraMap,
      sub_self]
  have hderiv : ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → ∀ t,
      pd 1 (D φ) t = D (deriv φ) t * (scomp (deriv h) (apath s n t) * n) := fun φ hφ t => by
    have h1 := pd_scomp hU hφ hH hHE (fun t => by rw [hHb]; exact hhs) 1 t
    have h2 := pd_scomp hW (hcomp φ hφ) hP hPE (fun t => by rw [hPb]; exact hsW) 1 t
    have hchain : deriv (fun x => φ (h x)) =ᶠ[𝓝 s] fun x => deriv φ (h x) * deriv h x := by
      filter_upwards [hW.mem_nhds hsW] with x hx
      have hφx : DifferentiableAt ℝ φ (h x) :=
        (hφ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx.2)
      have hhx : DifferentiableAt ℝ h x :=
        (hh.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hx.1)
      exact deriv_comp (h := h) (h₂ := φ) x hφx hhx
    have hφ' : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => deriv φ (h x)) s :=
      ((contDiffOn_deriv hU hφ).comp hhW (fun x hx => hx.2)).contDiffAt (hW.mem_nhds hsW)
    have hh' : ContDiffAt ℝ (⊤ : ℕ∞) (deriv h) s :=
      (contDiffOn_deriv hV hh).contDiffAt (hV.mem_nhds hs)
    have h3 : scomp (deriv fun x => φ (h x)) (apath s n t) =
        scomp (fun x => deriv φ (h x)) (apath s n t) * scomp (deriv h) (apath s n t) := by
      rw [scomp_congr (f₁ := deriv fun x => φ (h x)) (f₂ := fun x => deriv φ (h x) * deriv h x)
          (a := apath s n t) (by rw [hPb]; exact hchain),
        scomp_mul_fun (isNilpotent_soul (hPE t)) (by rw [hPb]; exact hφ') (by rw [hPb]; exact hh')]
    rw [show D φ = fun t => scomp φ (scomp h (apath s n t)) -
      scomp (fun x => φ (h x)) (apath s n t) from rfl,
      pd_sub (SDiff.scomp hU hφ hH hHE fun t => by rw [hHb]; exact hhs)
        (SDiff.scomp hW (hcomp φ hφ) hP hPE fun t => by rw [hPb]; exact hsW), h1, h2, hpdH,
      pd_apath, h3]
    simp only [D, sub_mul, mul_assoc]
  -- downward induction
  set K := Fintype.card O + 1
  have hnK : n ^ K = 0 := soul_pow_card_succ ha
  have key : ∀ m, ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ U → ∀ t, D φ t * n ^ (K - m) = 0 := by
    intro m
    induction m with
    | zero => intro φ _ t; rw [Nat.sub_zero, hnK, mul_zero]
    | succ m ih =>
      intro φ hφ t
      by_cases hm : K ≤ m
      · rw [show K - (m + 1) = K - m by omega]; exact ih φ hφ t
      · have hj : K - m = K - (m + 1) + 1 := by omega
        have hconst := eq_of_pd_eq_zero (F := fun t => D φ t * n ^ (K - (m + 1)))
          ((hD_sdiff φ hφ).mul (SDiff.const _)) (fun t => by
            rw [pd_mul (hD_sdiff φ hφ) (SDiff.const _), pd_const, mul_zero, add_zero,
              hderiv φ hφ t]
            have hc : IsEven (scomp (deriv h) (apath s n t)) := (hPE t).scomp _
            calc D (deriv φ) t * (scomp (deriv h) (apath s n t) * n) * n ^ (K - (m + 1))
                = D (deriv φ) t * n ^ (K - m) * scomp (deriv h) (apath s n t) := by
                  rw [mul_assoc, mul_assoc, hc.comm (n * n ^ (K - (m + 1))), ← mul_assoc,
                    ← pow_succ', ← hj]
              _ = 0 := by rw [ih (deriv φ) (contDiffOn_deriv hU hφ) t, zero_mul]) t 0
        rw [hconst, hD0, zero_mul]
  have hfin := key K g hg 1
  rw [Nat.sub_self, pow_zero, mul_one] at hfin
  have ha1 : apath s n 1 = a := by
    rw [apath, one_smul, ← Algebra.algebraMap_eq_smul_one]; exact (eq_body_add_soul a).symm
  simpa only [D, ha1, sub_eq_zero] using hfin

end

end ArborealDecay.Super

end
