import Obs2.Map.ExactStep

/-!
# Locality of the observable flow (`sec:obs-flow`)

The support property of the observable flow at every scale: the observable map preserves
`𝒩^{obs}(X^□)`, the elements whose components lie in `𝒩(X^□)` and whose `σ_a` (`σ_b`) and
`σ_aσ_b` components vanish unless `a ∈ X^□` (`b ∈ X^□`) (`osub P S`; the text's `𝒩(X^□)` with
observables, `Obs.compSub` with point conditions).

* `OLocS P j V W K`: `V(B), 𝒲(B) ∈ 𝒩^{obs}(B^□)`, `K(Y) ∈ 𝒩^{obs}(Y^□)` (connected `Y`).
  It implies the locality hypothesis `OLocHyp` of the factorisation (`OLocS.toOLocHyp`).
* **`OLocS.step`**: `OLocS` at scale `j` implies `OLocS` at scale `j + 1` for the outputs
  `V_{j+1}`, `𝒲_{j+1}`, `K_{j+1}` (on connected polymers) of the second-order map with sources,
  for a covariance of range `L^{j+1}/2` and `L ≥ 2^{d+3}`.

The pointed localisation `loc^a_{Y,B}` places `ψ̄_a` at `a ∈ Y^□ ⊆ B^{□□}`; the doubled
neighbourhood of a `j`-block lies in the scale-`(j+1)` neighbourhood of its `(j+1)`-block
(`nb2_subset_succ`), so the outputs are again local at scale `j + 1`. The proofs are the
membership principles of `Step2.Map.Mem` and `Step2.Map.StepFinal` (`Kplus_loc`) on `OE`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD LocObs

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Componentwise maps -/

section Comp

variable {Λ Λ' : Type*} [DecidableEq Λ] [DecidableEq Λ']

theorem compSub_map {T : Subalgebra ℂ (Grassmann.N Λ)} {T' : Subalgebra ℂ (Grassmann.N Λ')}
    {pa pb : Prop} (f : Grassmann.N Λ → Grassmann.N Λ') (hf0 : f 0 = 0)
    (hf : ∀ x ∈ T, f x ∈ T') {F : OE c Λ} {G : OE c Λ'}
    (he : (G : SA c Λ').e = f (F : SA c Λ).e) (ha : (G : SA c Λ').a = f (F : SA c Λ).a)
    (hb : (G : SA c Λ').b = f (F : SA c Λ).b) (hab : (G : SA c Λ').ab = f (F : SA c Λ).ab)
    (hF : F ∈ (compSub T pa pb : Subalgebra ℂ (OE c Λ))) :
    G ∈ (compSub T' pa pb : Subalgebra ℂ (OE c Λ')) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
  refine ⟨he ▸ hf _ h1, ha ▸ hf _ h2, hb ▸ hf _ h3, hab ▸ hf _ h4, fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨x, y⟩ := h5 hp
    rw [ha, hab, x, y, hf0]; exact ⟨rfl, rfl⟩
  · obtain ⟨x, y⟩ := h6 hp
    rw [hb, hab, x, y, hf0]; exact ⟨rfl, rfl⟩

end Comp

/-! ### The supports `𝒩^{obs}(S)` -/

section Sub

variable (P : ObsPts d L N)

/-- **`𝒩^{obs}(S)`**: components in `𝒩(S)`; the `σ_a` (`σ_b`) and `σ_aσ_b` components vanish
unless `a ∈ S` (`b ∈ S`). -/
abbrev osub (S : Finset (Lam d L N)) : Subalgebra ℂ (OE c (Lam d L N)) :=
  compSub (NX (S : Set (Lam d L N))) (P.a ∈ S) (P.b ∈ S)

/-- `𝒩^{obs}(S)` on the doubled lattice (both copies). -/
abbrev osub2 (S : Finset (Lam d L N)) : Subalgebra ℂ (OE c (Lam d L N ⊕ Lam d L N)) :=
  compSub (NX2 (S : Set (Lam d L N))) (P.a ∈ S) (P.b ∈ S)

variable {P}

theorem osub_mono {S S' : Finset (Lam d L N)} (h : S ⊆ S') :
    (osub P S : Subalgebra ℂ (OE c (Lam d L N))) ≤ osub P S' :=
  compSub_mono (NX_mono (coe_subset.2 h)) (fun h' => h h') (fun h' => h h')

variable {S : Finset (Lam d L N)}

theorem thetaO_mem_osub2 {F : OE c (Lam d L N)} (hF : F ∈ osub P S) : thetaO F ∈ osub2 P S :=
  compSub_map theta (map_zero _) (fun _ hx => theta_mem_NX2 hx) rfl rfl rfl rfl hF

theorem inclO_mem_osub2 {F : OE c (Lam d L N)} (hF : F ∈ osub P S) : inclO F ∈ osub2 P S :=
  compSub_map incl (map_zero _) (fun _ hx => incl_mem_NX2 hx) rfl rfl rfl rfl hF

theorem ECCO_mem_osub (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N ⊕ Lam d L N)}
    (hF : F ∈ osub2 P S) : ECCO C F ∈ osub P S :=
  compSub_map (ECC C) (map_zero _) (fun _ hx => ECC_mem_NX C hx) rfl rfl rfl rfl hF

theorem expO_mem_osub (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ osub P S) : expO C F ∈ osub P S :=
  compSub_map (expLC C) (map_zero _) (fun _ hx => expLC_mem_NX C hx) rfl rfl rfl rfl hF

theorem EthO_mem_osub (C : Matrix (Lam d L N) (Lam d L N) ℂ) {F : OE c (Lam d L N)}
    (hF : F ∈ osub P S) : EthO C F ∈ osub P S :=
  ECCO_mem_osub C (thetaO_mem_osub2 hF)

theorem FCO_mem_osub (C : Matrix (Lam d L N) (Lam d L N) ℂ) {A B : OE c (Lam d L N)}
    (hA : A ∈ osub P S) (hB : B ∈ osub P S) : FCO C A B ∈ osub P S :=
  sub_mem (expO_mem_osub C (mul_mem (expO_mem_osub (-C) hA) (expO_mem_osub (-C) hB)))
    (mul_mem hA hB)

theorem epsO_mem_osub {F : OE c (Lam d L N)} (hF : F ∈ osub P S) : epsO F ∈ osub P S :=
  compSub_map (fun x => algebraMap ℂ (Grassmann.N (Lam d L N)) (ε x)) (by simp)
    (fun _ _ => Subalgebra.algebraMap_mem _ _) rfl rfl rfl rfl hF

theorem πobs_mem_osub {F : OE c (Lam d L N)} (hF : F ∈ osub P S) : πobs F ∈ osub P S := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
  rw [mem_compSub, coe_πobs']
  exact ⟨zero_mem _, h2, h3, h4, h5, h6⟩

theorem emb_mem_osub {x : EvR (Lam d L N)} (hx : (x : Alg d L N) ∈ NX (S : Set (Lam d L N))) :
    (emb x : OE c (Lam d L N)) ∈ osub P S :=
  ⟨hx, zero_mem _, zero_mem _, zero_mem _, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

end Sub

/-! ### Finite range of `F_C` with sources -/

theorem FCO_sub_right' {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    (A B B' : OE c Λ) : FCO C A (B - B') = FCO C A B - FCO C A B' := by
  rw [sub_eq_add_neg, FCO_add_right, ← neg_one_smul ℂ B', FCO_smul_right, neg_one_smul,
    ← sub_eq_add_neg]

theorem FCO_eq_zero_far {Λ : Type*} [DecidableEq Λ] [Fintype Λ] (C : Matrix Λ Λ ℂ)
    {S T : Set Λ} (hST : Disjoint S T) (hC : ∀ x ∈ S, ∀ y ∈ T, C x y = 0 ∧ C y x = 0)
    {A B : OE c Λ} (hA : A ∈ (compSub (NX S) True True : Subalgebra ℂ (OE c Λ)))
    (hB : B ∈ (compSub (NX T) True True : Subalgebra ℂ (OE c Λ))) : FCO C A B = 0 := by
  obtain ⟨a1, a2, a3, a4, -, -⟩ := hA
  obtain ⟨b1, b2, b3, b4, -, -⟩ := hB
  have hτe : c.tau (A : SA c Λ).e = (A : SA c Λ).e := Case.tau_of_even c A.par_e
  have hτa : c.tau (A : SA c Λ).a = c.s • (A : SA c Λ).a := Case.tau_of_par c A.par_a
  have hτb : c.tau (A : SA c Λ).b = c.s • (A : SA c Λ).b := Case.tau_of_par c A.par_b
  have z : ∀ {x y}, x ∈ NX S → y ∈ NX T → FC C x y = 0 := fun hx hy =>
    FC_eq_zero_of_disjoint C hST hC hx hy
  have hsa : c.s • (A : SA c Λ).a ∈ NX S := Subalgebra.smul_mem _ a2 _
  have hsb : c.s • (A : SA c Λ).b ∈ NX S := Subalgebra.smul_mem _ a3 _
  have ha := FCO_cmp C true A B
  have hb := FCO_cmp C false A B
  simp only [cmp_true, cmp_false, hτe] at ha hb
  refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
  · rw [FCO_e, z a1 b1]; rfl
  · rw [ha, z a1 b2, z a2 b1, add_zero]; rfl
  · rw [hb, z a1 b3, z a3 b1, add_zero]; rfl
  · rw [FCO_ab, hτa, hτb, z a1 b4, z hsa b3, z hsb b2, z a4 b1]; simp

/-! ### Geometry -/

section Geom

variable {j : ℕ}

/-- `X^{□□}` at scale `j` lies in `X^□` at scale `j + 1` (`L ≥ 2^{d+3}`). -/
theorem nb2_subset_succ (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j + 1 ≤ N)
    (X : Finset (Lam d L N)) : nb2 j X ⊆ nbhd (j + 1) X := by
  intro y hy
  obtain ⟨x, hx, h⟩ := exists_near_of_mem_nb2 hy
  refine mem_nbhd_of_close hd hj hx ?_
  have h6 : 8 * (2 ^ d * L ^ j) ≤ L ^ (j + 1) := by
    calc 8 * (2 ^ d * L ^ j) = 2 ^ (d + 3) * L ^ j := by ring
      _ ≤ L * L ^ j := Nat.mul_le_mul_right _ hL
      _ = L ^ (j + 1) := by ring
  have : 0 < 2 ^ d * L ^ j :=
    Nat.mul_pos (Nat.two_pow_pos d) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)
  omega

theorem nbhd_subset_Bp (b : Fin d → ℕ) :
    nbhd j (blockSet (L := L) (N := N) j b) ⊆ nbhd (j + 1) (Bp (L := L) (N := N) j b) :=
  (nbhd_subset_nbhd_succ _).trans (nbhd_mono (subset_clo j _))

theorem nb2_subset_Bp (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hj : j + 1 ≤ N) (b : Fin d → ℕ) :
    nb2 j (blockSet (L := L) (N := N) j b) ⊆ nbhd (j + 1) (Bp (L := L) (N := N) j b) :=
  (nb2_subset_succ hd hL hj _).trans (nbhd_mono (subset_clo j _))

theorem Bp_nbhd_subset {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) {b : Fin d → ℕ}
    (hbU : blockSet (L := L) (N := N) j b ⊆ U) :
    nbhd (j + 1) (Bp (L := L) (N := N) j b) ⊆ nbhd (j + 1) U :=
  nbhd_mono (clo_subset hU hbU)

theorem Bp_subset_block {c' b : Fin d → ℕ}
    (hb : b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c')) :
    Bp (L := L) (N := N) j b ⊆ blockSet (L := L) (N := N) (j + 1) c' :=
  clo_subset (isPolymer_blockSet (j + 1) c')
    (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb)

end Geom

/-! ### The localisation -/

section LocM

variable {P : ObsPts d L N} {j : ℕ}

theorem LocO2_mem_osub (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) {S : Finset (Lam d L N)}
    (hS : nbhd j (blockSet (L := L) (N := N) j b) ⊆ S) {F : OE c (Lam d L N)}
    (hF : F ∈ osub P S) : LocO2 P X (blockSet j b) F ∈ osub P S := by
  obtain ⟨-, -, -, -, h5, h6⟩ := hF
  refine ⟨?_, ?_, ?_, ?_, fun ha => ?_, fun hb' => ?_⟩
  · exact NX_mono (coe_subset.2 hS) (Loc2E_mem_NB hd hb X (bulk F))
  · show locAp c P.a X (blockSet j b) (F : SA c (Lam d L N)).a ∈ _
    by_cases ha : P.a ∈ S
    · exact NX_mono (by simpa using ha) (locAp_mem _ _ _ _)
    · rw [(h5 ha).1, locAp_zero]; exact zero_mem _
  · show locBp c P.b X (blockSet j b) (F : SA c (Lam d L N)).b ∈ _
    by_cases hb' : P.b ∈ S
    · exact NX_mono (by simpa using hb') (locBp_mem _ _ _ _)
    · rw [(h6 hb').1, locBp_zero]; exact zero_mem _
  · show locABtXY P X (blockSet j b) (F : SA c (Lam d L N)).ab ∈ _
    by_cases ha : P.a ∈ S
    · by_cases hb' : P.b ∈ S
      · refine NX_mono ?_ (locABtXY_mem P _ _ _)
        intro x hx
        rcases hx with rfl | rfl
        · exact mem_coe.2 ha
        · exact mem_coe.2 hb'
      · rw [(h6 hb').2, locABtXY_zero]; exact zero_mem _
    · rw [(h5 ha).2, locABtXY_zero]; exact zero_mem _
  · exact ⟨show locAp c P.a X (blockSet j b) (F : SA c (Lam d L N)).a = 0 by
      rw [(h5 ha).1, locAp_zero],
      show locABtXY P X (blockSet j b) (F : SA c (Lam d L N)).ab = 0 by
      rw [(h5 ha).2, locABtXY_zero]⟩
  · exact ⟨show locBp c P.b X (blockSet j b) (F : SA c (Lam d L N)).b = 0 by
      rw [(h6 hb').1, locBp_zero],
      show locABtXY P X (blockSet j b) (F : SA c (Lam d L N)).ab = 0 by
      rw [(h6 hb').2, locABtXY_zero]⟩

end LocM

/-! ### The locality hypothesis -/

/-- **Locality of the input of one step with sources** (strong form):
`V(B), 𝒲(B) ∈ 𝒩^{obs}(B^□)`, `K(Y) ∈ 𝒩^{obs}(Y^□)` for connected `Y`. -/
structure OLocS (P : ObsPts d L N) (j : ℕ) (V W : OFam c d L N) (K : OAct c d L N) : Prop where
  hV : ∀ b, V b ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b))
  hW : ∀ b, W b ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b))
  hK : ∀ Y, IsConn j Y → K Y ∈ osub P (nbhd j Y)

namespace OLocS

variable {P : ObsPts d L N} {j : ℕ} {C : Matrix (Lam d L N) (Lam d L N) ℂ}
  {V W : OFam c d L N} {K : OAct c d L N}

/-- `OLocS` implies the locality hypothesis `OLocHyp` of the factorisation. -/
theorem toOLocHyp (H : OLocS P j V W K) : OLocHyp P j V W K where
  hV b := compSub_mono le_rfl (fun _ => trivial) (fun _ => trivial) (H.hV b)
  hW b := compSub_mono le_rfl (fun _ => trivial) (fun _ => trivial) (H.hW b)
  hK Y hY := compSub_mono le_rfl (fun _ => trivial) (fun _ => trivial) (H.hK Y hY)
  hKa Y hY ha := (H.hK Y ⟨hY.1, hY.2.1⟩).2.2.2.2.1 ha
  hKb Y hY hb := (H.hK Y ⟨hY.1, hY.2.1⟩).2.2.2.2.2 hb

variable (H : OLocS P j V W K)
include H

theorem Vpr_mem (b : Fin d → ℕ) :
    VprO C V b ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b)) :=
  EthO_mem_osub C (H.hV b)

theorem Q2O_mem (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Q2O P j K b ∈ osub P (nb2 j (blockSet (L := L) (N := N) j b)) := by
  have hne : (blockSet (L := L) (N := N) j b).Nonempty := by
    obtain ⟨x, -, rfl⟩ := mem_image.1 hb
    exact ⟨x, mem_blockSet_blk j x⟩
  unfold Q2O
  split_ifs
  · refine Subalgebra.sum_mem _ fun X hX => ?_
    obtain ⟨hs, hbX⟩ := mem_filter.1 hX
    have hs' := mem_smallSets.1 hs
    exact LocO2_mem_osub hd hb X (nbhd_subset_nb2 j _)
      (osub_mono (nbhd_mono (subset_nbhd_of_small hs' hbX hne)) (H.hK X ⟨hs'.1, hs'.2.1⟩))
  · exact zero_mem _

theorem J2O_mem' (hd : 1 ≤ d) {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j)
    (X : Finset (Lam d L N)) :
    J2O P j K b X ∈ osub P (nb2 j (blockSet (L := L) (N := N) j b)) := by
  have hne : (blockSet (L := L) (N := N) j b).Nonempty := by
    obtain ⟨x, -, rfl⟩ := mem_image.1 hb
    exact ⟨x, mem_blockSet_blk j x⟩
  unfold J2O
  split_ifs with h1 h2
  · refine neg_mem (Subalgebra.sum_mem _ fun Y hY => ?_)
    obtain ⟨hs, hbY, -⟩ := mem_filter.1 hY
    have hs' := mem_smallSets.1 hs
    exact LocO2_mem_osub hd hb Y (nbhd_subset_nb2 j _)
      (osub_mono (nbhd_mono (subset_nbhd_of_small hs' hbY hne)) (H.hK Y ⟨hs'.1, hs'.2.1⟩))
  · exact LocO2_mem_osub hd hb X (nbhd_subset_nb2 j _)
      (osub_mono (nbhd_mono (subset_nbhd_of_small h1.2.1 h1.2.2 hne))
        (H.hK X ⟨h1.2.1.1, h1.2.1.2.1⟩))
  · exact zero_mem _

omit H in
/-- Far blocks do not interact (with sources). -/
theorem FCO_far_gen (hC : CovRange j C) {b b' : Fin d → ℕ}
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) (h : b' ∉ nearSet (L := L) (N := N) j b)
    {A B : OE c (Lam d L N)} (hA : A ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b)))
    (hB : B ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b'))) :
    FCO C A B = 0 := by
  set Y1 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b) with hY1
  set Y2 : Finset (Lam d L N) := nbhd j (blockSet (L := L) (N := N) j b') with hY2
  have hfar : ∀ x ∈ Y1, ∀ y ∈ Y2, L ^ (j + 1) ≤ 2 * supNorm (x - y) :=
    fun x hx y hy => not_near_far hb' h hx hy
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
    exact ⟨hC x y h1', hC y x (by rw [h2]; exact h1')⟩
  exact FCO_eq_zero_far C hdis hCz
    (compSub_mono le_rfl (fun _ => trivial) (fun _ => trivial) hA)
    (compSub_mono le_rfl (fun _ => trivial) (fun _ => trivial) hB)

theorem FCO_Vpr_far (hC : CovRange j C) {b b' : Fin d → ℕ}
    (hb' : b' ∈ blockIdx (L := L) (N := N) j) (h : b' ∉ nearSet (L := L) (N := N) j b) :
    FCO C (VprO C V b) (VprO C V b') = 0 :=
  FCO_far_gen hC hb' h (H.Vpr_mem b) (H.Vpr_mem b')

omit H in
/-- Only the near blocks contribute to `F_C(A, ∑_{B'} B(B'))`. -/
theorem FCO_sum_near (hC : CovRange j C) (b : Fin d → ℕ) {A : OE c (Lam d L N)}
    (hA : A ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b)))
    {Bf : (Fin d → ℕ) → OE c (Lam d L N)}
    (hB : ∀ b', Bf b' ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b'))) :
    FCO C A (∑ b' ∈ blockIdx (L := L) (N := N) j, Bf b') =
      ∑ b' ∈ nearSet (L := L) (N := N) j b, FCO C A (Bf b') := by
  classical
  rw [FCO_sum_right, nearSet, ← sum_filter_add_sum_filter_not (blockIdx j)
    (fun b' => ∃ x ∈ nbhd j (blockSet (L := L) (N := N) j b),
      ∃ y ∈ nbhd j (blockSet (L := L) (N := N) j b'), 2 * supNorm (x - y) < L ^ (j + 1))]
  rw [sum_eq_zero (s := filter (fun b' => ¬ _) _) fun b' hb' => ?_, add_zero]
  obtain ⟨hb'1, hb'2⟩ := mem_filter.1 hb'
  exact FCO_far_gen hC hb'1 (fun h => hb'2 (mem_filter.1 h).2) hA (hB b')

omit H in
theorem FCsum_osub (hC : CovRange j C) (b : Fin d → ℕ) {T : Finset (Lam d L N)}
    (hself : nbhd j (blockSet (L := L) (N := N) j b) ⊆ T)
    (hsub : ∀ b' ∈ nearSet (L := L) (N := N) j b, nbhd j (blockSet (L := L) (N := N) j b') ⊆ T)
    {A : OE c (Lam d L N)} (hA : A ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b)))
    {Bf : (Fin d → ℕ) → OE c (Lam d L N)}
    (hB : ∀ b', Bf b' ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b'))) :
    FCO C A (∑ b' ∈ blockIdx (L := L) (N := N) j, Bf b') ∈ osub P T := by
  rw [FCO_sum_near hC b hA hB]
  exact Subalgebra.sum_mem _ fun b' hb' =>
    FCO_mem_osub C (osub_mono hself hA) (osub_mono (hsub b' hb') (hB b'))

/-- Locality of the sharp second-order part `S^{(2)}(B)`. -/
theorem SF_osub (hC : CovRange j C) (b : Fin d → ℕ) {T : Finset (Lam d L N)}
    (hself : nbhd j (blockSet (L := L) (N := N) j b) ⊆ T)
    (hsub : ∀ b' ∈ nearSet (L := L) (N := N) j b, nbhd j (blockSet (L := L) (N := N) j b') ⊆ T) :
    SFO j C V b ∈ osub P T := by
  have hX := H.Vpr_mem (C := C) b
  rw [SFO, SCorO]
  refine add_mem (Subalgebra.smul_mem _ ?_ _) (Subalgebra.smul_mem _ (sub_mem ?_ ?_) _)
  · rw [VprLO]; exact FCsum_osub hC b hself hsub hX (H.Vpr_mem (C := C))
  · rw [VprLO]; exact FCsum_osub hC b hself hsub (πobs_mem_osub hX) (H.Vpr_mem (C := C))
  · rw [VprLO, map_sum]
    exact FCsum_osub hC b hself hsub hX fun b' => πobs_mem_osub (H.Vpr_mem (C := C) b')

variable (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) (hjN : j + 1 < N) (hC : CovRange j C)
include hd hL hjN hC

theorem Sb_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    SbO j C V W b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) := by
  have hsub : ∀ b' ∈ nearSet (L := L) (N := N) j b,
      nbhd j (blockSet (L := L) (N := N) j b') ⊆ nbhd (j + 1) (Bp (L := L) (N := N) j b) :=
    fun b' hb' _ hy => mem_nbhd_succ_of_near hd hL hjN.le hb' hy
  have hs := hsub b (mem_nearSet_self hb)
  exact add_mem (H.SF_osub hC b hs hsub) (osub_mono hs (EthO_mem_osub C (H.hW b)))

theorem SX_mem (b : Fin d → ℕ) :
    SXO j C V W (Bp (L := L) (N := N) j b) ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  Subalgebra.sum_mem _ fun b'' hb'' => osub_mono (nbhd_mono (BH.Bp_sub hb''))
    (H.Sb_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb''))

theorem LS_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    LSO P j C V W b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  LocO2_mem_osub hd hb _ (nbhd_subset_Bp b) (H.SX_mem hd hL hjN hC b)

theorem uVp_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    uVpO P j C V W K b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  sub_mem (sub_mem (osub_mono (nbhd_subset_Bp b) (H.Vpr_mem b))
    (osub_mono (nb2_subset_Bp hd hL hjN.le b) (EthO_mem_osub C (H.Q2O_mem hd hb))))
    (H.LS_mem hd hL hjN hC hb)

theorem up_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    upO P j C V W K b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  πobs_mem_osub (epsO_mem_osub (H.uVp_mem hd hL hjN hC hb))

theorem Vp_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    VpO P j C V W K b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  sub_mem (sub_mem (H.uVp_mem hd hL hjN hC hb) (Subalgebra.algebraMap_mem _ _))
    (H.up_mem hd hL hjN hC hb)

theorem Wp_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    WpO P j C V W b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  sub_mem (H.Sb_mem hd hL hjN hC hb) (H.LS_mem hd hL hjN hC hb)

theorem Gp_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    GpO P j C V W K b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  mul_mem (oexp_mem (neg_mem (H.Vp_mem hd hL hjN hC hb)))
    (add_mem (one_mem _) (H.Wp_mem hd hL hjN hC hb))

theorem Ip_mem {b : Fin d → ℕ} (hb : b ∈ blockIdx (L := L) (N := N) j) :
    IpO P j C V W K b ∈ osub P (nbhd (j + 1) (Bp (L := L) (N := N) j b)) :=
  mul_mem (expU_mem _ (neg_mem (H.up_mem hd hL hjN hC hb))) (H.Gp_mem hd hL hjN hC hb)

omit hd hL hjN hC in
theorem Ib_mem (b : Fin d → ℕ) :
    IbO V W b ∈ osub P (nbhd j (blockSet (L := L) (N := N) j b)) :=
  mul_mem (oexp_mem (neg_mem (H.hV b))) (add_mem (one_mem _) (H.hW b))

/-- The membership principle with sources applies with the supports `𝒩^{obs}(U^□)`. -/
theorem ogmem {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    OGMem j C (IbO V W) (IpO P j C V W K) K (J2O P j K) U (osub P (nbhd (j + 1) U))
      (osub2 P (nbhd (j + 1) U)) where
  hθ _ hF := thetaO_mem_osub2 hF
  hι _ hF := inclO_mem_osub2 hF
  hE _ hF := ECCO_mem_osub C hF
  hK Y hY hYU := osub_mono ((nbhd_subset_nbhd_succ _).trans (nbhd_mono hYU)) (H.hK Y hY)
  hJ b X hb hbU := osub_mono ((nb2_subset_Bp hd hL hjN.le b).trans (Bp_nbhd_subset hU hbU))
    (H.J2O_mem' hd hb X)
  hIb b _ hbU := osub_mono ((nbhd_subset_Bp b).trans (Bp_nbhd_subset hU hbU)) (H.Ib_mem b)
  hIp b hb hbU := osub_mono (Bp_nbhd_subset hU hbU) (H.Ip_mem hd hL hjN hC hb)

theorem uXO_mem {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    uXO P j C V W K U ∈ osub P (nbhd (j + 1) U) :=
  Subalgebra.sum_mem _ fun b hb => osub_mono
    (Bp_nbhd_subset hU (blockSet_subset (IsPolymer.of_succ hU) hb))
    (H.up_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb))

/-- **Locality of `K_{j+1}` (polymer formula) with sources.** -/
theorem Knext2_mem {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    Knext2O P j C V W K U ∈ osub P (nbhd (j + 1) U) :=
  mul_mem (expU_mem _ (H.uXO_mem hd hL hjN hC hU)) ((H.ogmem hd hL hjN hC hU).gKnextO_mem hU)

theorem k2_mem {U X : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) (hXU : clo j X = U) :
    k2O j C V X ∈ osub P (nbhd (j + 1) U) := by
  have hbU : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ U := fun b hb =>
    (blockSet_subset (IsPolymer.of_succ (isPolymer_clo j X)) (blocks_mono (subset_clo j X) hb)).trans
      (hXU ▸ subset_rfl)
  have hsub : ∀ b ∈ blocks j X, ∀ b' ∈ nearSet (L := L) (N := N) j b,
      nbhd j (blockSet (L := L) (N := N) j b') ⊆ nbhd (j + 1) U := fun b hb b' hb' _ hy =>
    nbhd_mono (clo_subset hU (hbU b hb)) (mem_nbhd_succ_of_near hd hL hjN.le hb' hy)
  have hself : ∀ b ∈ blocks j X, nbhd j (blockSet (L := L) (N := N) j b) ⊆ nbhd (j + 1) U :=
    fun b hb => hsub b hb b (mem_nearSet_self (mem_blockIdx_of_mem_blocks hb))
  unfold k2O; split_ifs with h1 h2
  · refine Subalgebra.sum_mem _ fun b hb => ?_
    rw [k2one_eq]
    exact sub_mem (Subalgebra.smul_mem _ (FCO_mem_osub C (osub_mono (hself b hb) (H.Vpr_mem b))
        (osub_mono (hself b hb) (H.Vpr_mem b))) _) (H.SF_osub hC b (hself b hb) (hsub b hb))
  · refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb => ?_) _
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    exact FCO_mem_osub C (osub_mono (hself b hb) (H.Vpr_mem b))
      (osub_mono (hself b' (mem_of_mem_erase hb')) (H.Vpr_mem b'))
  · exact zero_mem _

theorem K2_mem {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    K2O j C V U ∈ osub P (nbhd (j + 1) U) := by
  classical
  unfold K2O
  exact Subalgebra.sum_mem _ fun X hX => H.k2_mem hd hL hjN hC hU (mem_filter.1 hX).2

theorem Knew_mem {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KnewO P j C V W K U ∈ osub P (nbhd (j + 1) U) := by
  refine sub_mem (H.Knext2_mem hd hL hjN hC hU) (mul_mem ?_ (H.K2_mem hd hL hjN hC hU))
  exact prod_mem fun b hb => osub_mono
    (Bp_nbhd_subset hU (blockSet_subset (IsPolymer.of_succ hU) hb))
    (H.Gp_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb))

theorem kap_mem {U X : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) (hXU : clo j X = U)
    (c' : Fin d → ℕ) : kapO j C V X c' ∈ osub P (nbhd (j + 1) U) := by
  have hbU : ∀ b ∈ blocks j X, blockSet (L := L) (N := N) j b ⊆ U := fun b hb =>
    (blockSet_subset (IsPolymer.of_succ (isPolymer_clo j X)) (blocks_mono (subset_clo j X) hb)).trans
      (hXU ▸ subset_rfl)
  have hsub : ∀ b ∈ blocks j X, ∀ b' ∈ nearSet (L := L) (N := N) j b,
      nbhd j (blockSet (L := L) (N := N) j b') ⊆ nbhd (j + 1) U := fun b hb b' hb' _ hy =>
    nbhd_mono (clo_subset hU (hbU b hb)) (mem_nbhd_succ_of_near hd hL hjN.le hb' hy)
  have hself : ∀ b ∈ blocks j X, nbhd j (blockSet (L := L) (N := N) j b) ⊆ nbhd (j + 1) U :=
    fun b hb => hsub b hb b (mem_nearSet_self (mem_blockIdx_of_mem_blocks hb))
  unfold kapO; split_ifs with h1 h2
  · refine Subalgebra.sum_mem _ fun b hb => ?_
    replace hb := (mem_filter.1 hb).1
    rw [k2one_eq]
    exact sub_mem (Subalgebra.smul_mem _ (FCO_mem_osub C (osub_mono (hself b hb) (H.Vpr_mem b))
        (osub_mono (hself b hb) (H.Vpr_mem b))) _) (H.SF_osub hC b (hself b hb) (hsub b hb))
  · refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun b hb => ?_) _
    replace hb := (mem_filter.1 hb).1
    refine Subalgebra.sum_mem _ fun b' hb' => ?_
    have h1 := osub_mono (hself b hb) (H.Vpr_mem (C := C) b)
    have h2 := osub_mono (hself b' (mem_of_mem_erase hb')) (H.Vpr_mem (C := C) b')
    exact add_mem (FCO_mem_osub C h1 h2) (sub_mem (FCO_mem_osub C (πobs_mem_osub h1) h2)
      (FCO_mem_osub C h1 (πobs_mem_osub h2)))
  · exact zero_mem _

theorem Jh_mem (c' : Fin d → ℕ) {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    JhO j C V c' U ∈ osub P (nbhd (j + 1) U) := by
  classical
  unfold JhO; split_ifs
  · exact Subalgebra.sum_mem _ fun X hX => H.kap_mem hd hL hjN hC hU (mem_filter.1 hX).2 c'
  · exact zero_mem _

/-- **Locality of `K_{j+1}` with sources**: `K_{j+1}(U) ∈ 𝒩^{obs}(U^□)` at scale `j + 1`. -/
theorem Kplus_mem {U : Finset (Lam d L N)} (hU : IsPolymer (j + 1) U) :
    KplusO P j C V W K U ∈ osub P (nbhd (j + 1) U) := by
  refine KoutO_mem (S := osub P (nbhd (j + 1) U)) ?_ ?_ ?_
  · intro X hX hXU
    rw [bpow_ItO P j C V W K hX]
    exact prod_mem fun b hb => osub_mono (nbhd_mono (clo_subset hU
      ((blockSet_subset (IsPolymer.of_succ hX) hb).trans hXU)))
      (H.Gp_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb))
  · intro Y hY hYU
    exact osub_mono (nbhd_mono hYU) (H.Knew_mem hd hL hjN hC hY.1)
  · intro p hp hpU
    exact osub_mono (nbhd_mono hpU) (H.Jh_mem hd hL hjN hC p.1 (mem_pairsU.1 hp).2.1.1)

theorem Vnext_mem (c' : Fin d → ℕ) :
    Vnext2O P j C V W K c' ∈ osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c')) :=
  Subalgebra.sum_mem _ fun b hb => osub_mono (nbhd_mono (Bp_subset_block hb))
    (H.Vp_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb))

theorem Wnext_mem (c' : Fin d → ℕ) :
    Wnext2O P j C V W c' ∈ osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c')) :=
  sub_mem (prod_mem fun b hb => add_mem (one_mem _) (osub_mono (nbhd_mono (Bp_subset_block hb))
    (H.Wp_mem hd hL hjN hC (mem_blockIdx_of_mem_blocks hb)))) (one_mem _)

/-- **Propagation of locality by one step of the observable map** (`L ≥ 2^{d+3}`, covariance of
range `L^{j+1}/2`): the outputs `V_{j+1}`, `𝒲_{j+1}` and `K_{j+1}` (on connected polymers) are
local at scale `j + 1`. -/
theorem step :
    OLocS P (j + 1) (Vnext2O P j C V W K) (Wnext2O P j C V W)
      (KconnO (j + 1) (KplusO P j C V W K)) where
  hV c' := H.Vnext_mem hd hL hjN hC c'
  hW c' := H.Wnext_mem hd hL hjN hC c'
  hK Y hY := by
    unfold KconnO
    rw [if_pos hY]
    exact H.Kplus_mem hd hL hjN hC hY.1

end OLocS

end

end Obs2
