import Step2.Map.XStep

/-!
# The raw step on the coordinate spaces (`h02uv-outline.tex`, Section `sec:reduction`, (O1))

The outputs of the raw step lie in the coordinate spaces at scale `j + 1`:

* `WlinNext_eq`: `W^lin_{j+1}(B_+) = ∑_{B ⊆ B_+} W'(V, W^lin)(B)` (the linear part of `Wnext2`);
* `sumWp_mem`, `WlinNext_mem`, `Dnext_mem`: `W^lin_{j+1}` and `D_{j+1}` are in `BSub (j + 1)`;
* `Kconn`, `Kconn_mem`: `K_{j+1}` restricted to connected polymers is in `ASub (j + 1)`.

The hypotheses (`RawHyp`) are those of the step at a symmetric, lattice-invariant covariance with
`GoodCov2`, for `j + 2 < N`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem blockSet_eq_empty {k : ℕ} {c : Fin d → ℕ} (hc : c ∉ blockIdx (L := L) (N := N) k) :
    blockSet (L := L) (N := N) k c = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => hc ?_
  have := (Finset.mem_filter.1 hx).2
  exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, this⟩

/-- `W^lin_{j+1}` is the linear part `∑_B W'(V, W^lin)(B)` of `Wnext2`. -/
theorem WlinNext_eq (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V Wl : Fam d L N)
    (c : Fin d → ℕ) :
    WlinNext j C V Wl c = ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V Wl b := by
  have hσ : (fun b' => sigE 1 (Wl b')) = Wl := funext fun b' => sigE_one' _
  have h0 : ∀ b, Wp j C 0 0 b = 0 := fun b => by
    simp [Wp, Sb, LS, SX, Vpr, VprL, EthE_zero, FCE_zero_right, Loc2E_zero]
  have h : ∀ b, Wp j C V Wl b = Wp j C V 0 b + Wp j C 0 Wl b := by
    intro b
    rw [Wp_split (W := Wl), Wp_split (V := 0) (W := Wl), h0, zero_add]
  rw [WlinNext, Pi.add_apply, SrcL_eq_Wp, TrL_eq_Wp, hσ]
  simp only [h, sum_add_distrib]

/-- The hypotheses of the raw step. -/
structure RawHyp (j : ℕ) (ℓ : ℝ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V : Fam d L N) : Prop where
  hd : 1 ≤ d
  hL : 2 ^ (d + 3) + 8 * d < L
  hj2 : j + 2 < N
  hC : GoodCov2 j ℓ C
  hCt : TInv C
  hCs : CSym C
  hCsym : ∀ x y, C x y = C y x
  hV : V ∈ BSub (L := L) (N := N) j
  hV0 : ∀ b, ε (V b : Alg d L N) = 0

namespace RawHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V : Fam d L N}
  (H : RawHyp j ℓ C V)
include H

theorem hL' : 2 ^ (d + 3) ≤ L := by have := H.hL; omega

/-- **`∑_B W'(V, W)(B)` is in `BSub (j + 1)`.** -/
theorem sumWp_mem {W : Fam d L N} (hW : W ∈ BSub (L := L) (N := N) j) :
    (fun c => ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V W b) ∈
      BSub (L := L) (N := N) (j + 1) := by
  refine ⟨inF_sumWp H.hd H.hL' (by have := H.hj2; omega) H.hC H.hV.1 hW.1,
    sumWp_cov H.hd H.hL' H.hj2 H.hC H.hCt H.hV.1 hW.1 H.hV.2.1 hW.2.1, ?_, ?_, ?_⟩
  · intro T hT hP1 c hc
    have S : SymHyp j ℓ C V W (0 : Act d L N) T :=
      ⟨H.hd, H.hL', H.hj2, H.hC, H.hCs, H.hV.1, hW.1, H.hV0, ⟨fun X _ => zero_mem _,
        fun X _ n z _ => by simp⟩, H.hV.2.2.1, hW.2.2.1, fun T _ _ X => by simp, hT, hP1⟩
    show AE T (∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V W b) =
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) (bmap (j + 1) T c)), Wp j C V W b
    rw [map_sum, ← img_blockSet_bmap hT (by have := H.hj2; omega) hP1 hc,
      blocks_img_bmap S.hP, sum_image fun b hb b' hb' e => bmap_injOn hT S.hj S.hP
        (mem_blockIdx_of_mem_blocks hb) (mem_blockIdx_of_mem_blocks hb') e]
    exact sum_congr rfl fun b hb => S.AE_Wp (mem_blockIdx_of_mem_blocks hb)
  · intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Subalgebra.sum_mem _ fun b hb => Wp_J H.hCsym H.hL (by have := H.hj2; omega)
      H.hV.2.2.2.1 hW.2.2.2.1 (mem_blockIdx_of_mem_blocks hb)
  · intro c hc
    simp [blockSet_eq_empty hc, blocks]

theorem WlinNext_mem {Wl : Fam d L N} (hWl : Wl ∈ BSub (L := L) (N := N) j) :
    WlinNext j C V Wl ∈ BSub (L := L) (N := N) (j + 1) := by
  have e : WlinNext j C V Wl = fun c =>
      ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c), Wp j C V Wl b :=
    funext (WlinNext_eq j C V Wl)
  rw [e]; exact H.sumWp_mem hWl

/-- **`𝒲_{j+1} = Wnext2(V, W)` is in `BSub (j + 1)`.** -/
theorem Wnext2_mem {W : Fam d L N} (hW : W ∈ BSub (L := L) (N := N) j) :
    Wnext2 j C V W ∈ BSub (L := L) (N := N) (j + 1) := by
  refine ⟨Wnext2_inF H.hd H.hL' (by have := H.hj2; omega) H.hC H.hV.1 hW.1,
    Wnext2_cov H.hd H.hL' H.hj2 H.hC H.hCt H.hV.1 hW.1 H.hV.2.1 hW.2.1,
    Wnext2_latsym (K := (0 : Act d L N)) H.hd H.hL' H.hj2 H.hC H.hCs H.hV.1 hW.1 H.hV0
      ⟨fun X _ => zero_mem _, fun X _ n z _ => by simp⟩ H.hV.2.2.1 hW.2.2.1 (fun T _ _ X => by simp),
    Wnext2_J H.hCsym H.hL (by have := H.hj2; omega) H.hV.2.2.2.1 hW.2.2.2.1, fun c hc => ?_⟩
  simp [Wnext2, blockSet_eq_empty hc, blocks]

/-- **`D_{j+1}` is in `BSub (j + 1)`.** -/
theorem Dnext_mem {Wl D : Fam d L N} (hWl : Wl ∈ BSub (L := L) (N := N) j)
    (hD : D ∈ BSub (L := L) (N := N) j) :
    Dnext j C V Wl D ∈ BSub (L := L) (N := N) (j + 1) := by
  have e : Dnext j C V Wl D = Wnext2 j C V (Wl + D) - WlinNext j C V Wl := rfl
  rw [e]
  exact sub_mem (H.Wnext2_mem (add_mem hWl hD)) (H.WlinNext_mem hWl)

end RawHyp

open Classical in
/-- An activity restricted to connected polymers. -/
def Kconn (k : ℕ) (K : Act d L N) : Act d L N := fun X => if IsConn k X then K X else 0

namespace RawHyp

variable {j : ℕ} {ℓ : ℝ} {C : Matrix (Lam d L N) (Lam d L N) ℂ} {V : Fam d L N}
  (H : RawHyp j ℓ C V)
include H

/-- **`K_{j+1}` (on connected polymers) is in `ASub (j + 1)`.** -/
theorem Kconn_mem {W : Fam d L N} {K : Act d L N} (hW : W ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) :
    Kconn (j + 1) (Kplus j C V W K) ∈ ASub (L := L) (N := N) (j + 1) := by
  have hj1 : j + 1 ≤ N := by have := H.hj2; omega
  have hI := InK2_Kplus H.hd H.hL' (by have := H.hj2; omega) H.hC H.hV.1 hW.1 H.hV0 hK.1
  have hcov := Kplus_cov H.hd H.hL' H.hj2 H.hC H.hCt H.hV.1 hW.1 H.hV0 hK.1 H.hV.2.1 hW.2.1 hK.2.1
  have hsym := Kplus_latsym H.hd H.hL' H.hj2 H.hC H.hCs H.hV.1 hW.1 H.hV0 hK.1 H.hV.2.2.1
    hW.2.2.1 hK.2.2.1
  have hJ := Kplus_J H.hCsym H.hL (by have := H.hj2; omega) H.hV.2.2.2.1 hW.2.2.2.1 hK.2.2.2.1
  refine ⟨⟨fun X hX => ?_, fun X hX => ?_⟩, fun t ht X => ?_, fun T hT hP X => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · simp only [Kconn, if_pos hX]; exact hI.loc X hX
  · simp only [Kconn, if_pos hX]; exact hI.sym X hX
  · have hP := Flow.presBlocks_transl' hj1 t ht
    have hiff := PresBlocks.isConn_img (IsGen.transl t) hj1 hP (X := X)
    simp only [Kconn]
    by_cases hX : IsConn (j + 1) X
    · rw [if_pos (hiff.2 hX), if_pos hX]; exact hcov t ht X
    · rw [if_neg (fun h => hX (hiff.1 h)), if_neg hX]; simp
  · have hiff := PresBlocks.isConn_img hT hj1 hP (X := X)
    simp only [Kconn]
    by_cases hX : IsConn (j + 1) X
    · rw [if_pos (hiff.2 hX), if_pos hX]; exact hsym T hT hP X
    · rw [if_neg (fun h => hX (hiff.1 h)), if_neg hX]; simp
  · simp only [Kconn, if_pos hX]; exact hJ X hX
  · simp only [Kconn, if_neg hX]

end RawHyp

/-- **Coupling polynomials are admissible block families.** -/
theorem VfamL_mem (hd : 1 ≤ d) (hL : 2 ^ (d + 3) + 8 * d < L) {k : ℕ} (hk : k < N)
    (v : Fin 4 → ℂ) : VfamL (d := d) (L := L) (N := N) k v ∈ BSub (L := L) (N := N) k := by
  have hV : ∀ b, (VfamL (d := d) (L := L) (N := N) k v b : Alg d L N) =
      Vcoup (Coup.ofVec v) (blockSet (L := L) (N := N) k b) := fun b => rfl
  refine ⟨inF_VfamL hd hL hk v, famCovG_VfamL hk.le v, famSym_Vcoup hk.le _ hV,
    famJ_Vcoup _ hV, fun b hb => Subtype.ext ?_⟩
  show VcoupL (blockSet (L := L) (N := N) k b) v = 0
  rw [blockSet_eq_empty hb, VcoupL_empty]

/-! ### The activity `K♭` -/

/-- `K♭(X) = ∏_{B ⊆ X} e^{Δ(B)} K(X)`. -/
def Kflat (j : ℕ) (Δ : Fam d L N) (K : Act d L N) : Act d L N :=
  fun Y => bpow j (fun b => gexp (Δ b)) Y * K Y

theorem isNilpotent_of_eps {F : EvR (Lam d L N)} (h : ε (F : Alg d L N) = 0) : IsNilpotent F :=
  ⟨_, pow_eq_zero_of_ε' h (Nat.lt_succ_self _)⟩

theorem coe_prod_mem {ι : Type*} (S : Subalgebra ℂ (Alg d L N)) (s : Finset ι)
    (f : ι → EvR (Lam d L N)) (h : ∀ i ∈ s, (f i : Alg d L N) ∈ S) :
    ((∏ i ∈ s, f i : EvR (Lam d L N)) : Alg d L N) ∈ S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_mem]
  | insert a s ha ih =>
    rw [prod_insert ha, Subalgebra.coe_mul]
    exact mul_mem (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Covariance of `K♭` under a block-preserving lattice map. -/
theorem Kflat_AE {j : ℕ} {T : AffAut d L N} (hT : IsGen T) (hj : j ≤ N) (hP : PresBlocks j T)
    {Δ : Fam d L N} {K : Act d L N}
    (hΔ : ∀ b ∈ blockIdx (L := L) (N := N) j, AE T (Δ b) = Δ (bmap j T b))
    (hΔ0 : ∀ b, ε (Δ b : Alg d L N) = 0) (hK : ∀ X, AE T (K X) = K (T.img X))
    (X : Finset (Lam d L N)) : AE T (Kflat j Δ K X) = Kflat j Δ K (T.img X) := by
  rw [Kflat, Kflat, map_mul, hK, bpow, bpow, map_prod, blocks_img_bmap hP,
    prod_image fun b hb b' hb' e => bmap_injOn hT hj hP (mem_blockIdx_of_mem_blocks hb)
      (mem_blockIdx_of_mem_blocks hb') e]
  congr 1
  refine prod_congr rfl fun b hb => ?_
  rw [AE_gexp T (isNilpotent_of_eps (hΔ0 b)), hΔ b (mem_blockIdx_of_mem_blocks hb)]

/-- **`K♭` is an admissible activity.** -/
theorem Kflat_mem {j : ℕ} (hj : j < N) {Δ : Fam d L N} {K : Act d L N}
    (hΔ : Δ ∈ BSub (L := L) (N := N) j) (hΔ0 : ∀ b, ε (Δ b : Alg d L N) = 0)
    (hK : K ∈ ASub (L := L) (N := N) j) : Kflat j Δ K ∈ ASub (L := L) (N := N) j := by
  have hbp : ∀ X, IsConn j X → ((bpow j (fun b => gexp (Δ b)) X : EvR (Lam d L N)) : Alg d L N) ∈
      NX (nbhd j X : Set (Lam d L N)) ∧
      ((bpow j (fun b => gexp (Δ b)) X : EvR (Lam d L N)) : Alg d L N) ∈ SymS (Lam d L N) ∧
      ((bpow j (fun b => gexp (Δ b)) X : EvR (Lam d L N)) : Alg d L N) ∈ JS d L N := by
    intro X hX
    unfold bpow
    refine ⟨coe_prod_mem _ _ _ fun b hb => ?_, coe_prod_mem _ _ _ fun b hb => ?_,
      coe_prod_mem _ _ _ fun b hb => ?_⟩
    · have h1 : (Δ b : Alg d L N) ∈ NX (nbhd j X : Set (Lam d L N)) := by
        refine NX_mono ?_ (hΔ.1.loc b)
        exact_mod_cast nbhd_mono (blockSet_subset hX.1 hb)
      exact mem_SE.1 (gexp_mem_SE (S := NX (nbhd j X : Set (Lam d L N))) (mem_SE.2 h1))
    · exact mem_SE.1 (gexp_mem_SE (S := SymS (Lam d L N))
        (mem_SE.2 ((isSym_iff_mem_SymS _).1 (hΔ.1.sym b))))
    · exact mem_SE.1 (gexp_mem_SE (S := JS d L N) (mem_SE.2 (hΔ.2.2.2.1 b)))
  refine ⟨⟨fun X hX => ?_, fun X hX => ?_⟩, fun t ht X => ?_, fun T hT hP X => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · rw [Kflat, Subalgebra.coe_mul]; exact mul_mem (hbp X hX).1 (hK.1.loc X hX)
  · rw [isSym_iff_mem_SymS, Kflat, Subalgebra.coe_mul]
    exact mul_mem (hbp X hX).2.1 ((isSym_iff_mem_SymS _).1 (hK.1.sym X hX))
  · have hP := Flow.presBlocks_transl' hj.le t ht
    have := Kflat_AE (IsGen.transl t) hj.le hP (Δ := Δ) (K := K)
      (fun b hb => Subtype.ext (by rw [coe_AE]; exact (hΔ.2.1 t ht b hb).symm)) hΔ0
      (fun X => Subtype.ext (by rw [coe_AE]; exact (hK.2.1 t ht X).symm)) X
    rw [← this, coe_AE]; rfl
  · exact Kflat_AE hT hj.le hP (fun b hb => hΔ.2.2.1 T hT hP b hb) hΔ0
      (fun X => hK.2.2.1 T hT hP X) X
  · rw [Kflat, Subalgebra.coe_mul]; exact mul_mem (hbp X hX).2.2 (hK.2.2.2.1 X hX)
  · rw [Kflat, hK.2.2.2.2 X hX, mul_zero]

end

end Step2
