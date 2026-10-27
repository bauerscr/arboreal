import Loc.Image

/-!
# Example (i) of Section `sec:Loc`

A monomial in the generators `ψ_x, ψ̄_x` of degree greater than four is annihilated by
`Loc_{X,Y}` (`LocXY_psiPow`).  For our `Loc` this holds for every degree `n ∉ {0, 2}`, since
`Loc_{X,Y} F` depends only on the constant part `F_∅` and the coefficients `F_{(x,+)(y,-)}` of
`F`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD Matrix

variable {d L N : ℕ} [NeZero L]

/-- `Loc_{X,Y} F = 0` if `F` has no constant part and no `ψψ̄` part. -/
theorem LocXY_eq_zero_of (X Y : Finset (Lam d L N)) {F : Alg d L N} (h0 : ε F = 0)
    (h2 : ∀ x y, cf2 F x y = 0) : LocXY X Y F = 0 := by
  have hmu : (fun β => mu (base X) β F) = 0 := by
    funext β; simp [mu, h2]
  have hc : locCoef X F = 0 := by rw [locCoef, hmu, zero_vecMul]
  simp [LocXY, h0, hc]

/-- **Example (i).** A monomial `ψ^z = ψ_{z_1} ⋯ ψ_{z_n}` of degree `n ∉ {0, 2}` (in particular
of degree greater than four) satisfies `Loc_{X,Y} ψ^z = 0`. -/
theorem LocXY_psiPow (X Y : Finset (Lam d L N)) {n : ℕ} (z : Fin n → Grassmann.Sf (Lam d L N))
    (hn0 : n ≠ 0) (hn2 : n ≠ 2) : LocXY X Y (psiPow z) = 0 := by
  refine LocXY_eq_zero_of X Y ?_ fun x y => ?_
  · have := coeff_ιMulti_of_ne (fun i => ev (z i)) (Fin.elim0 : Fin 0 → Grassmann.Sf (Lam d L N))
      (Ne.symm hn0)
    exact this
  · exact coeff_ιMulti_of_ne (fun i => ev (z i)) _ (Ne.symm hn2)

/-- `Loc_X ψ^z = 0` for monomials of degree greater than four. -/
theorem LocX_psiPow (X : Finset (Lam d L N)) {n : ℕ} (z : Fin n → Grassmann.Sf (Lam d L N))
    (hn : 4 < n) : LocX X (psiPow z) = 0 :=
  LocXY_psiPow X X z (by omega) (by omega)

end

end Loc
