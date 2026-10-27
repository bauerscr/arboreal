import Loc.LocProps
import Grassmann.Doubling
import Loc.PolySp

-- Merged from `Loc/Aut.lean` (phase 3).
section

/-!
# Lattice maps acting on `𝒩(Λ)`

A bijection `E` of the torus acts on `𝒩(Λ)` as the algebra homomorphism `E ψ_x = ψ_{Ex}`,
`E ψ̄_x = ψ̄_{Ex}` (`autAlg`).  The ψψ̄-coefficients transform as `(EF)_{x,y} = F_{E⁻¹x, E⁻¹y}`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- The action of a bijection `E` of `Λ` on the generators. -/
def autV (E : Lam d L N ≃ Lam d L N) : V (Lam d L N) →ₗ[ℂ] V (Lam d L N) :=
  LinearMap.funLeft ℂ ℂ fun a : Sf (Lam d L N) => (E.symm a.1, a.2)

/-- The action of a bijection `E` of `Λ` on `𝒩(Λ)`: `E ψ_x = ψ_{Ex}`, `E ψ̄_x = ψ̄_{Ex}`. -/
def autAlg (E : Lam d L N ≃ Lam d L N) : Alg d L N →ₐ[ℂ] Alg d L N :=
  ExteriorAlgebra.map (autV E)

theorem autV_ev (E : Lam d L N ≃ Lam d L N) (a : Sf (Lam d L N)) : autV E (ev a) = ev (E a.1, a.2) := by
  ext ⟨y, τ⟩
  simp only [autV, LinearMap.funLeft_apply, ev, Pi.single_apply, Prod.ext_iff]
  congr 1
  apply propext
  rw [Equiv.symm_apply_eq]

theorem autAlg_psi (E : Lam d L N ≃ Lam d L N) (x : Lam d L N) : autAlg E (psi x) = psi (E x) := by
  rw [autAlg, psi, ψ, ExteriorAlgebra.map_apply_ι, autV_ev]; rfl

theorem autAlg_psibar (E : Lam d L N ≃ Lam d L N) (x : Lam d L N) :
    autAlg E (psibar x) = psibar (E x) := by
  rw [autAlg, psibar, ψ, ExteriorAlgebra.map_apply_ι, autV_ev]; rfl

theorem coord_autV (E : Lam d L N ≃ Lam d L N) (a : Sf (Lam d L N)) :
    coord a ∘ₗ autV E = coord (E.symm a.1, a.2) := by
  ext v; simp [autV]

theorem coeff_autAlg (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) {n : ℕ}
    (z : Fin n → Sf (Lam d L N)) :
    coeff (autAlg E F) z = coeff F (fun i => (E.symm (z i).1, (z i).2)) := by
  rw [coeff, Dseq, autAlg, contr_map, algebraMapInv_map]
  simp only [coord_autV]; rfl

theorem cf2_autAlg (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) (x y : Lam d L N) :
    cf2 (autAlg E F) x y = cf2 F (E.symm x) (E.symm y) := by
  rw [cf2, coeff_autAlg, cf2]
  congr 1; funext i; fin_cases i <;> rfl

theorem ε_autAlg (E : Lam d L N ≃ Lam d L N) (F : Alg d L N) : ε (autAlg E F) = ε F :=
  algebraMapInv_map _ F

/-- `mu` of `E F`: reindexing the sum. -/
theorem mu_autAlg (E : Lam d L N ≃ Lam d L N) (b : Lam d L N) (β : Mono d) (F : Alg d L N) :
    mu b β (autAlg E F) = ∑ x, ∑ y, cf2 F x y * (Qpoly β (lift b (E x)) (lift b (E y)) : ℂ) := by
  simp only [mu, cf2_autAlg]
  refine (Fintype.sum_equiv E.symm _ _ fun x => ?_)
  refine Fintype.sum_equiv E.symm _ _ fun y => ?_
  simp

end

end Loc

end

/-!
# Euclidean invariance of `Loc` (Proposition `prop:Loc` (iv))

An *affine lattice automorphism* `E x = R x + E 0` with `R` additive and lifting to `ℤ^d` (and
linearly to `ℝ^d`), which maps each basis monomial to `±` a basis monomial
(`E M_x = sgn(M) (ρ M)_{Ex}`), satisfies `E Loc_{X,Y} F = Loc_{EX,EY} E F` for `F` supported in a
region `R` of diameter `< L^N/4` containing the neighbourhood of `X` (`LocXY_aut`).
Translations, reflections and coordinate transpositions are such automorphisms
(`Loc/AutGen.lean`), and they are closed under composition.

Scalars: the signs `sgn` are complex (`±1`), the linear part `A` acts on the real coordinate space
`ℝ^d` of the (real) test polynomials, and the transformation matrix `Tc` of the test polynomials
in `mu_aut` is real (cast to `ℂ`).
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- An affine lattice automorphism compatible with the monomial basis. -/
structure AffAut (d L N : ℕ) [NeZero L] where
  E : Lam d L N ≃ Lam d L N
  R : Lam d L N →+ Lam d L N
  hE : ∀ x, E x = R x + E 0
  Rz : Zd d →+ Zd d
  hRz : ∀ a, R (prj a) = prj (Rz a)
  hnorm : ∀ a, supNormZ (Rz a) ≤ supNormZ a
  A : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)
  hA : ∀ a : Zd d, (fun i => ((Rz a) i : ℝ)) = A (fun i => (a i : ℝ))
  ρ : Mono d ≃ Mono d
  sgn : Mono d → ℂ
  hmono : ∀ M x, autAlg E (monoAt M x) = sgn M • monoAt (ρ M) (E x)

namespace AffAut

variable (T : AffAut d L N)

theorem supNorm_R (y : Lam d L N) : supNorm (T.R y) ≤ supNorm y := by
  have : T.R y = prj (T.Rz (rep y)) := by rw [← T.hRz, prj_rep]
  rw [this]
  refine (supNorm_prj_le _).trans ((T.hnorm _).trans ?_)
  rw [supNormZ_rep_eq]

theorem E_sub (x y : Lam d L N) : T.E x - T.E y = T.R (x - y) := by
  rw [T.hE x, T.hE y, map_sub]; abel

theorem supNorm_E_sub (x y : Lam d L N) : supNorm (T.E x - T.E y) ≤ supNorm (x - y) := by
  rw [E_sub]; exact T.supNorm_R _

/-- Lifts transform affinely. -/
theorem lift_E {b b' x : Lam d L N}
    (h : 2 * (supNorm (x - b) + supNorm (T.E b - b')) < L ^ N) :
    lift b' (T.E x) = T.A (lift b x) + lift b' (T.E b) := by
  have hz : rep (T.E x - b') = T.Rz (rep (x - b)) + rep (T.E b - b') := by
    symm
    refine eq_rep ?_ ?_
    · rw [prj_add, ← T.hRz, prj_rep, prj_rep, ← E_sub]; abel
    · have h1 := supNormZ_add_le (T.Rz (rep (x - b))) (rep (T.E b - b'))
      have h2 := T.hnorm (rep (x - b))
      rw [supNormZ_rep_eq] at h1 h2
      omega
  funext i
  have := congrFun (T.hA (rep (x - b))) i
  simp only [lift, hz, Pi.add_apply, Int.cast_add]
  rw [this]; rfl

end AffAut

/-! ### Vanishing of coefficients outside the support -/

theorem cf2_eq_zero_left {R : Set (Lam d L N)} {G : Alg d L N} (hG : G ∈ NX R) {x : Lam d L N}
    (hx : x ∉ R) (y : Lam d L N) : cf2 G x y = 0 := by
  rw [cf2, coeff_two, D_eq_zero_of_mem_NX hG (a := (x, 1)) hx]; simp

theorem cf2_eq_zero_right {R : Set (Lam d L N)} {G : Alg d L N} (hG : G ∈ NX R) (x : Lam d L N)
    {y : Lam d L N} (hy : y ∉ R) : cf2 G x y = 0 := by
  rw [cf2, coeff_two, D_eq_zero_of_mem_NX (D_mem_NX hG (x, 1)) (a := (y, -1)) hy]; simp

/-! ### The region hypothesis -/

/-- `R` contains the neighbourhood of `X` and has diameter `< L^N/4 - 1`. -/
structure Region (X : Finset (Lam d L N)) (R : Set (Lam d L N)) : Prop where
  nbr : ∀ x ∈ X, ∀ a : Zd d, supNormZ a ≤ 1 → x + prj a ∈ R
  diam : ∀ x ∈ R, ∀ y ∈ R, 4 * (supNorm (x - y) + 1) < L ^ N

theorem prj_zero : (prj (0 : Zd d) : Lam d L N) = 0 := by
  show (fun i => (((0 : Zd d) i : ℤ) : ZMod (L ^ N))) = (0 : Fin d → ZMod (L ^ N))
  funext i; simp

theorem Region.mem {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (h : Region X R) {x : Lam d L N}
    (hx : x ∈ X) : x ∈ R := by
  have := h.nbr x hx 0 (by simp [supNormZ_zero])
  rwa [prj_zero, add_zero] at this

theorem base_mem {X : Finset (Lam d L N)} (hne : X.Nonempty) : base X ∈ X := by
  rw [base, dif_pos hne]; exact hne.choose_spec

theorem Region.patch {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (h : Region X R)
    (hne : X.Nonempty) : Patch X := fun x hx => by
  have := h.diam x (h.mem hx) _ (h.mem (base_mem hne)); omega

theorem LocXY_mem_of {X Z : Finset (Lam d L N)} {R : Set (Lam d L N)}
    (h : ∀ x ∈ Z, ∀ a : Zd d, supNormZ a ≤ 1 → x + prj a ∈ R) (F : Alg d L N) :
    LocXY X Z F ∈ NX R :=
  add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.sum_mem _ fun M _ =>
    Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun y hy => monoAt_mem (h y hy)) _)

namespace AffAut

variable (T : AffAut d L N)

/-- `E` applied to a set of points. -/
def img (Z : Finset (Lam d L N)) : Finset (Lam d L N) := Z.map T.E.toEmbedding

/-- Covariance of the pairings: `mu_{b'}(E G) = ∑_{β'} T_{ββ'} mu_b(G)`. -/
theorem mu_aut {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
    (hne : X.Nonempty) {b' : Lam d L N} (hb' : ∃ x ∈ R, b' = T.E x) (β : Mono d) :
    ∃ Tc : Mono d → ℝ, ∀ G ∈ NX R,
      mu b' β (autAlg T.E G) = ∑ β', (Tc β' : ℂ) * mu (base X) β' G := by
  obtain ⟨Tc, hTc⟩ := exists_Qfun_comp T.A (lift b' (T.E (base X))) β
  refine ⟨Tc, fun G hG => ?_⟩
  obtain ⟨x₀, hx₀, rfl⟩ := hb'
  have hbR := hR.mem (base_mem hne)
  have hlift : ∀ x ∈ R, lift (T.E x₀) (T.E x) = T.A (lift (base X) x) + lift (T.E x₀) (T.E (base X)) := by
    intro x hx
    refine T.lift_E ?_
    have h1 := hR.diam x hx _ hbR
    have h2 := hR.diam _ hbR x₀ hx₀
    have h3 := T.supNorm_E_sub (base X) x₀
    omega
  have h1 : ∀ x y, cf2 G x y * (Qpoly β (lift (T.E x₀) (T.E x)) (lift (T.E x₀) (T.E y)) : ℂ) =
      ∑ β', (Tc β' : ℂ) * (cf2 G x y * (Qpoly β' (lift (base X) x) (lift (base X) y) : ℂ)) := by
    intro x y
    by_cases hx : x ∈ R
    · by_cases hy : y ∈ R
      · rw [hlift x hx, hlift y hy, hTc]
        push_cast
        rw [Finset.mul_sum]
        refine sum_congr rfl fun β' _ => by ring
      · simp [cf2_eq_zero_right hG x hy]
    · simp [cf2_eq_zero_left hG hx y]
  rw [mu_autAlg]
  simp only [h1, mu, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  exact Finset.sum_comm

theorem autAlg_monoSet (M : Mono d) (Z : Finset (Lam d L N)) :
    autAlg T.E (monoSet M Z) = T.sgn M • monoSet (T.ρ M) (T.img Z) := by
  rw [monoSet, map_sum, img, monoSet, sum_map, smul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [T.hmono]; rfl

theorem autAlg_sum_monoSet (c : Mono d → ℂ) (Z : Finset (Lam d L N)) :
    autAlg T.E (∑ M, c M • monoSet M Z) =
      ∑ M, (c (T.ρ.symm M) * T.sgn (T.ρ.symm M)) • monoSet M (T.img Z) := by
  rw [map_sum]
  simp only [map_smul, autAlg_monoSet, smul_smul]
  exact Fintype.sum_equiv T.ρ _ _ fun M => by simp

theorem card_img (Z : Finset (Lam d L N)) : (T.img Z).card = Z.card := card_map _

theorem img_nonempty {Z : Finset (Lam d L N)} (h : Z.Nonempty) : (T.img Z).Nonempty := h.map

theorem patch_img {X : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
    (hne : X.Nonempty) : Patch (T.img X) := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
  obtain ⟨y', hy', hy⟩ := Finset.mem_map.1 (base_mem (T.img_nonempty hne))
  have hy'' : T.E y' = base (T.img X) := hy
  simp only [Equiv.coe_toEmbedding]
  rw [← hy'']
  have := T.supNorm_E_sub x' y'
  have := hR.diam x' (hR.mem hx') y' (hR.mem hy')
  simp only [Equiv.coe_toEmbedding] at *
  omega

/-- Proposition `prop:Loc` (iv), Euclidean invariance: `E Loc_{X,Y} F = Loc_{EX,EY} E F`. -/
theorem LocXY_aut {X Y : Finset (Lam d L N)} {R : Set (Lam d L N)} (hR : Region X R)
    (hne : X.Nonempty) (F : Alg d L N) (hF : F ∈ NX R) :
    autAlg T.E (LocXY X Y F) = LocXY (T.img X) (T.img Y) (autAlg T.E F) := by
  set c := locCoef X F
  set c' : Mono d → ℂ := fun M => c (T.ρ.symm M) * T.sgn (T.ρ.symm M)
  have hpX := hR.patch hne
  have hpEX := T.patch_img hR hne
  have hneE := T.img_nonempty hne
  -- the coefficients transform
  have key : locCoef (T.img X) (autAlg T.E F) = c' := by
    have hb' : ∃ x ∈ R, base (T.img X) = T.E x := by
      obtain ⟨x, hx, h⟩ := Finset.mem_map.1 (base_mem hneE)
      exact ⟨x, hR.mem hx, h.symm⟩
    have hz : (locCoef (T.img X) (autAlg T.E F) - c') ᵥ* Amat (T.img X) = 0 := by
      funext β
      obtain ⟨Tc, hTc⟩ := T.mu_aut hR hne hb' β
      have hLX : LocX X F ∈ NX R := LocXY_mem_of hR.nbr F
      have e1 : ((locCoef (T.img X) (autAlg T.E F) - c') ᵥ* Amat (T.img X)) β =
          mu (base (T.img X)) β (LocX (T.img X) (autAlg T.E F)) -
            mu (base (T.img X)) β (autAlg T.E (LocX X F)) := by
        rw [LocX, LocXY, LocX, LocXY, map_add, map_smul, map_one, autAlg_sum_monoSet,
          mu_add, mu_add, mu_smul, mu_smul, mu_one, mu_monoSet_vecMul, mu_monoSet_vecMul]
        simp only [Pi.sub_apply, vecMul, dotProduct, Amat, mul_zero, zero_add, sub_mul,
          Finset.sum_sub_distrib]
        rfl
      rw [e1, mu_LocX hpEX hneE, hTc _ hF, hTc _ hLX]
      simp only [mu_LocX hpX hne, sub_self, Pi.zero_apply]
    have := (vecMul_injective_iff_isUnit.2 (Amat_isUnit hpEX hneE))
      (show (locCoef (T.img X) (autAlg T.E F) - c') ᵥ* Amat (T.img X) = 0 ᵥ* Amat (T.img X) by
        rw [hz, zero_vecMul])
    exact sub_eq_zero.1 this
  rw [LocXY, map_add, map_smul, map_one, autAlg_sum_monoSet, LocXY, key, ε_autAlg,
    T.card_img, T.card_img]

end AffAut

end

end Loc
