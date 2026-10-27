import Step2.Map.Gen
import Loc.Loc2Sym
import Step.EstSetup

/-!
# The second-order renormalisation group map (`h02uv-outline.tex`, Sections `sec:onestep`,
`sec:est`)

Coordinates at scale `j`: families `V, 𝒲` of even elements indexed by the `j`-blocks (with
`ε(V(B)) = 0`) and a polymer activity `K`. The block factor is `I_j(B) = e^{-V(B)}(1 + 𝒲(B))`.
For a complex covariance `C = C'_{j+1}`, with `V'_B = 𝔼_C θ V(B)`, `V'(Λ) = ∑_B V'_B` and
`F = F_C` (`Grassmann.FC`):

* `S(B) = ½ F(V'_B, V'(Λ)) + 𝔼_C θ 𝒲(B)` (`Sb`), and `S(B_+) = ∑_{B ⊆ B_+} S(B)`, where
  `B_+ = \bar B` is the `(j+1)`-block containing `B`;
* `(u+V)_{j+1}(B) = V'_B - 𝔼_C θ Q(B) - Loc_{B_+,B} S(B_+)` (`uVp`), `u_{j+1}(B)` its constant
  term (`up`) and `V_{j+1}(B)` the rest (`Vp`);
* `𝒲_{j+1}(B) = S(B) - Loc_{B_+,B} S(B_+)` (`Wp`);
* `I_{j+1}(B) = e^{-u_{j+1}(B)} e^{-V_{j+1}(B)} (1 + 𝒲_{j+1}(B))` (`Ip`);
* `K_{j+1}(U) = e^{∑_{B ∈ 𝓑_j(U)} u_{j+1}(B)} gKnext(U)` (`Knext2`), the polymer formula of
  `def:K+` with these block factors and with `Q`, `J` built from `Loc = Loc^{(2)} + Loc^{(4)}`
  (`Q2`, `J2`).

`Loc` is `Loc.Loc2sXY` (the quadratic localisation of `h02rg` plus the quartic marginal part).
`K2 V` is the explicit second-order part of `K_{j+1}` (`e:K2`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-! ### Even elements -/

theorem IsOdd.mul_even {Λ : Type*} [DecidableEq Λ] {x y : Grassmann.N Λ} (hx : IsOdd x)
    (hy : y ∈ Ev Λ) : IsOdd (x * y) := by
  unfold IsOdd at *
  rw [map_mul, hx, mem_Ev.1 hy, neg_mul]

theorem gmono4_mem_Ev (e e' : Dir d) (x : Lam d L N) : gmono4 e e' x ∈ Ev (Lam d L N) := by
  rw [gmono4_eq]
  refine mem_Ev_of_odd_mul ((isOdd_ψ _).sub (isOdd_ψ _)) ?_
  refine IsOdd.mul_even ((isOdd_ψ _).sub (isOdd_ψ _)) ?_
  exact mem_Ev_of_odd_mul (isOdd_ψ _) (isOdd_ψ _)

theorem mono4_mem_Ev (i k : Fin d) (x : Lam d L N) : mono4s i k x ∈ Ev (Lam d L N) :=
  mono4s_cases i k x (· ∈ Ev (Lam d L N)) (fun _ _ => add_mem) (fun _ _ => sub_mem)
    (fun c _ h => Subalgebra.smul_mem _ h c) (fun e e' => gmono4_mem_Ev e e' x)

theorem Loc4XY_mem_Ev (X Y : Finset (Lam d L N)) (F : Alg d L N) :
    Loc4sXY X Y F ∈ Ev (Lam d L N) :=
  Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _
    (Subalgebra.sum_mem _ fun x _ => mono4_mem_Ev i k x) _

/-- `Loc_{X,Y} = Loc^{(2)}_{X,Y} + Loc^{(4)}_{X,Y}` on even elements. -/
def Loc2E (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) : EvR (Lam d L N) :=
  ⟨Loc2sXY X Y F, add_mem (LocXY_mem_Ev X Y F) (Loc4XY_mem_Ev X Y F)⟩

@[simp] theorem coe_Loc2E (X Y : Finset (Lam d L N)) (F : EvR (Lam d L N)) :
    (Loc2E X Y F : Alg d L N) = Loc2sXY X Y F := rfl

section FCE

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

theorem FC_mem_Ev (C : Matrix Λ Λ ℂ) {A B : Grassmann.N Λ} (hA : A ∈ Ev Λ) (hB : B ∈ Ev Λ) :
    FC C A B ∈ Ev Λ := by
  have hA' := mem_Ev.1 hA
  have hB' := mem_Ev.1 hB
  refine mem_Ev.2 ?_
  have h1 : inv' (expLC (-C) A * expLC (-C) B) = expLC (-C) A * expLC (-C) B := by
    rw [map_mul inv', expLC_even (-C) hA', expLC_even (-C) hB']
  rw [FC, map_sub, expLC_even C h1, map_mul inv' A B, hA', hB']

/-- `F_C` on even elements. -/
def FCE (C : Matrix Λ Λ ℂ) (A B : EvR Λ) : EvR Λ := ⟨FC C A B, FC_mem_Ev C A.2 B.2⟩

@[simp] theorem coe_FCE (C : Matrix Λ Λ ℂ) (A B : EvR Λ) :
    (FCE C A B : Grassmann.N Λ) = FC C (A : Grassmann.N Λ) B := rfl

theorem FCE_comm (C : Matrix Λ Λ ℂ) (A B : EvR Λ) : FCE C A B = FCE C B A :=
  Subtype.ext (FC_comm C (mem_Ev.1 A.2) (mem_Ev.1 B.2))

/-- `𝔼_C θ` on even elements. -/
def EthE (C : Matrix Λ Λ ℂ) (F : EvR Λ) : EvR Λ := ECCE C (thetaE F)

@[simp] theorem coe_EthE (C : Matrix Λ Λ ℂ) (F : EvR Λ) :
    (EthE C F : Grassmann.N Λ) = expLC C (F : Grassmann.N Λ) := by
  simp [EthE, ECC_theta]

/-- The truncated expectation: `𝔼 θ (AB) = 𝔼 θ A 𝔼 θ B + F(𝔼 θ A, 𝔼 θ B)`. -/
theorem EthE_mul (C : Matrix Λ Λ ℂ) (A B : EvR Λ) :
    EthE C (A * B) = EthE C A * EthE C B + FCE C (EthE C A) (EthE C B) := by
  refine Subtype.ext ?_
  simp only [coe_EthE, Subalgebra.coe_add, Subalgebra.coe_mul, coe_FCE]
  rw [FC_expLC]
  abel

end FCE

/-! ### `Q` and `J` with the localisation of `d = 2` -/

section QJ

variable (j : ℕ) (K : Act d L N)

/-- `Q(B) = ∑_{X ∈ 𝒮_j, X ⊇ B} Loc_{X,B} K(X)`, and `Q = 0` if `j + 1 = N`. -/
def Q2 (b : Fin d → ℕ) : EvR (Lam d L N) :=
  open Classical in
  if j + 1 < N then
    ∑ X ∈ (smallSets j).filter (fun X => blockSet j b ⊆ X), Loc2E X (blockSet j b) (K X)
  else 0

/-- `J(B, X)`, and `J = 0` if `j + 1 = N`. -/
def J2 (b : Fin d → ℕ) (X : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in
  if j + 1 < N ∧ IsSmall j X ∧ blockSet j b ⊆ X then
    if X = blockSet j b then
      -∑ Y ∈ (smallSets j).filter (fun Y => blockSet j b ⊆ Y ∧ Y ≠ blockSet j b),
        Loc2E Y (blockSet j b) (K Y)
    else Loc2E X (blockSet j b) (K X)
  else 0

theorem J2_of_not_small (b : Fin d → ℕ) (X : Finset (Lam d L N)) (hX : ¬ IsSmall j X) :
    J2 j K b X = 0 := by
  rw [J2, if_neg fun h => hX h.2.1]

end QJ

/-! ### The map -/

/-- A family of even elements indexed by the `j`-blocks. -/
abbrev Fam (d L N : ℕ) [NeZero L] := (Fin d → ℕ) → EvR (Lam d L N)

section Map

variable (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N) (K : Act d L N)

/-- `V'_B = 𝔼_C θ V(B)`. -/
def Vpr (b : Fin d → ℕ) : EvR (Lam d L N) := EthE C (V b)

/-- `V'(Λ) = ∑_B V'_B`. -/
def VprL : EvR (Lam d L N) := ∑ b ∈ blockIdx (L := L) (N := N) j, Vpr C V b

/-- `S(B) = ½ F(V'_B, V'(Λ)) + 𝔼_C θ 𝒲(B)`. -/
def Sb (b : Fin d → ℕ) : EvR (Lam d L N) :=
  (1 / 2 : ℂ) • FCE C (Vpr C V b) (VprL j C V) + EthE C (W b)

/-- `S(X) = ∑_{B ∈ 𝓑_j(X)} S(B)`. -/
def SX (X : Finset (Lam d L N)) : EvR (Lam d L N) := ∑ b ∈ blocks j X, Sb j C V W b

/-- The `(j+1)`-block `B_+ = \bar B` containing the `j`-block `B`. -/
def Bp (b : Fin d → ℕ) : Finset (Lam d L N) := clo j (blockSet j b)

/-- `Loc_{B_+, B} S(B_+)`. -/
def LS (b : Fin d → ℕ) : EvR (Lam d L N) :=
  Loc2E (Bp (L := L) (N := N) j b) (blockSet j b) (SX j C V W (Bp j b))

/-- `(u+V)_{j+1}(B) = V'_B - 𝔼_C θ Q(B) - Loc_{B_+,B} S(B_+)`. -/
def uVp (b : Fin d → ℕ) : EvR (Lam d L N) :=
  Vpr C V b - EthE C (Q2 j K b) - LS j C V W b

/-- `u_{j+1}(B)`, the constant term of `(u+V)_{j+1}(B)`. -/
def up (b : Fin d → ℕ) : ℂ := ε (uVp j C V W K b : Alg d L N)

/-- `V_{j+1}(B) = (u+V)_{j+1}(B) - u_{j+1}(B)`. -/
def Vp (b : Fin d → ℕ) : EvR (Lam d L N) := uVp j C V W K b - algebraMap ℂ _ (up j C V W K b)

/-- `𝒲_{j+1}(B) = S(B) - Loc_{B_+,B} S(B_+)`. -/
def Wp (b : Fin d → ℕ) : EvR (Lam d L N) := Sb j C V W b - LS j C V W b

/-- `I_j(B) = e^{-V(B)} (1 + 𝒲(B))`. -/
def Ib (b : Fin d → ℕ) : EvR (Lam d L N) := gexp (-V b) * (1 + W b)

/-- `I_{j+1}(B) = e^{-u_{j+1}(B)} e^{-V_{j+1}(B)} (1 + 𝒲_{j+1}(B))`. -/
def Ip (b : Fin d → ℕ) : EvR (Lam d L N) :=
  Complex.exp (-up j C V W K b) • (gexp (-Vp j C V W K b) * (1 + Wp j C V W b))

/-- `u_{j+1}(X) = ∑_{B ∈ 𝓑_j(X)} u_{j+1}(B)`. -/
def uX (X : Finset (Lam d L N)) : ℂ := ∑ b ∈ blocks j X, up j C V W K b

/-- **`K_{j+1}(U)`** of the second-order map. -/
def Knext2 (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  Complex.exp (uX j C V W K U) • gKnext j C (Ib V W) (Ip j C V W K) K (J2 j K) U

/-! #### Coordinates at scale `j + 1` -/

/-- `V_{j+1}(B_+) = ∑_{B ⊆ B_+} V_{j+1}(B)` for a `(j+1)`-block `B_+`. -/
def Vnext2 (c : Fin d → ℕ) : EvR (Lam d L N) :=
  ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Vp j C V W K b

/-- `𝒲_{j+1}(B_+) = ∏_{B ⊆ B_+} (1 + 𝒲_{j+1}(B)) - 1`, so that
`I_{j+1}(B_+) = ∏_{B ⊆ B_+} I_{j+1}(B)` up to the constant. -/
def Wnext2 (c : Fin d → ℕ) : EvR (Lam d L N) :=
  ∏ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), (1 + Wp j C V W b) - 1

/-! #### The second-order part -/

/-- The second-order part of `K_{j+1}` on a `j`-polymer `X`: `-½ F(V'_B, V'(Λ ∖ B))` if
`X = B` is a block, `F(V'_B, V'_{B'})` if `X = B ∪ B'`, and `0` otherwise. -/
def k2 (X : Finset (Lam d L N)) : EvR (Lam d L N) :=
  if nb j X = 1 then
    ∑ b ∈ blocks j X, (-(1 / 2 : ℂ)) • FCE C (Vpr C V b) (VprL j C V - Vpr C V b)
  else if nb j X = 2 then
    (1 / 2 : ℂ) • ∑ b ∈ blocks j X, ∑ b' ∈ (blocks j X).erase b, FCE C (Vpr C V b) (Vpr C V b')
  else 0

/-- **`K^{(2)}(U)`** (`e:K2`): the sum of `k2 X` over the `j`-polymers `X` with `\bar X = U`. -/
def K2 (U : Finset (Lam d L N)) : EvR (Lam d L N) :=
  open Classical in ∑ X ∈ (Pj j univ).filter (fun X => clo j X = U), k2 j C V X

end Map

/-! ### Norms -/

/-- `‖V‖_j = sup_B ‖V(B)‖_{T_j(ℓ)}` for a block family. -/
def Fnorm (j : ℕ) (ℓ : ℝ) (V : Fam d L N) : ENNReal :=
  ⨆ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (V b : Alg d L N)

/-- The hypotheses on a block family (`V` or `𝒲`) at scale `j`. -/
structure InF (j : ℕ) (V : Fam d L N) : Prop where
  loc : ∀ b, (V b : Alg d L N) ∈ NX (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
  sym : ∀ b, IsSym (V b : Alg d L N)

/-- The hypotheses on a polymer activity: locality and `U(1)` invariance on connected polymers. -/
structure InK2 (j : ℕ) (K : Act d L N) : Prop where
  loc : ∀ X, IsConn j X → (K X : Alg d L N) ∈ NX (nbhd j X : Set (Lam d L N))
  sym : ∀ X, IsConn j X → IsSym (K X : Alg d L N)

end

end Step2
