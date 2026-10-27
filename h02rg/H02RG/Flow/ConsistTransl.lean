import Flow.ConsistStep

/-!
# Compatibility away from the origin

`Compat j D K K'` only asks for `K'(emb X) = emb K(X)` for polymers `X` in the central region
`|x|_∞ ≤ L^N/4`.  By translation invariance (`InK.aut` for translations by multiples of `L^j`),
it follows for all connected `X` of diameter `≤ D` in the larger region
`|x|_∞ ≤ 5 L^N/16` (`compat_ext`).
-/

namespace Flow

noncomputable section

open Finset Grassmann Loc FRD Step

variable {d L : ℕ} [NeZero L] {N M : ℕ}

theorem dvd_val_intCast' {n P : ℕ} [NeZero n] (hP : P ∣ n) {z : ℤ} (hz : (P : ℤ) ∣ z) :
    P ∣ ((z : ZMod n)).val := by
  have h := ZMod.val_intCast (n := n) z
  have : (P : ℤ) ∣ (((z : ZMod n).val : ℕ) : ℤ) := by
    rw [h, Int.emod_def]
    exact dvd_sub hz (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 hP) _)
  exact Int.natCast_dvd_natCast.1 this

theorem presBlocks_transl' {j : ℕ} (hj : j ≤ N) (t : Lam d L N)
    (ht : ∀ i, L ^ j ∣ (co t i).val) : PresBlocks j (AffAut.transl t) := by
  have hkn : L ^ j ∣ L ^ N := pow_dvd_pow L hj
  intro x y hxy
  funext k
  have := congrFun hxy k
  simp only [blk] at this ⊢
  exact presK_add hkn (ht k) _ _ this

theorem autAlg_ψ (E : Lam d L N ≃ Lam d L N) (a : Sf (Lam d L N)) :
    autAlg E (ψ a) = ψ (E a.1, a.2) := by
  rw [autAlg, ψ, ExteriorAlgebra.map_apply_ι, autV_ev]; rfl

theorem le_diam {n : ℕ} [NeZero n] {X : Finset (Torus d n)} {x y : Torus d n} (hx : x ∈ X)
    (hy : y ∈ X) : supNorm (x - y) ≤ diam X :=
  (Finset.le_sup (f := fun y => supNorm (x - y)) hy).trans
    (Finset.le_sup (f := fun x => X.sup fun y => supNorm (x - y)) hx)

theorem diam_le {n : ℕ} [NeZero n] {X : Finset (Torus d n)} {D : ℕ}
    (h : ∀ x ∈ X, ∀ y ∈ X, supNorm (x - y) ≤ D) : diam X ≤ D :=
  Finset.sup_le fun x hx => Finset.sup_le fun y hy => h x hx y hy

/-- The lattice vector `L^j ⌊r(x)/L^j⌋`. -/
def cornerZ (L j : ℕ) (z : Zd d) : Zd d := fun i => (L ^ j : ℤ) * (z i / (L ^ j : ℤ))

theorem cornerZ_spec (j : ℕ) (z : Zd d) (i : Fin d) :
    0 ≤ z i - cornerZ L j z i ∧ z i - cornerZ L j z i < (L ^ j : ℕ) ∧
      ((L ^ j : ℕ) : ℤ) ∣ cornerZ L j z i := by
  have hP : (0 : ℤ) < (L ^ j : ℕ) := by exact_mod_cast pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have e := Int.emod_add_mul_ediv (z i) ((L ^ j : ℕ) : ℤ)
  have h1 := Int.emod_nonneg (z i) hP.ne'
  have h2 := Int.emod_lt_of_pos (z i) hP
  simp only [cornerZ]
  push_cast at e h1 h2 hP ⊢
  refine ⟨by linarith, by linarith, dvd_mul_right _ _⟩

/-- **Compatibility extends from the central region by translation invariance.** -/
theorem compat_ext (hNM : N ≤ M) (hd : 1 ≤ d) (hL : 2 ^ (d + 3) ≤ L) {j : ℕ} (hj : j + 2 ≤ N)
    {K : Act d L N} {K' : Act d L M} (hK : InK j K) (hK' : InK j K') {D : ℕ}
    (hD : 8 * D ≤ L ^ N) (hc : Compat j D K K') {X : Finset (Lam d L N)} (hX : IsConn j X)
    (hX5 : ∀ x ∈ X, 16 * supNorm x ≤ 5 * L ^ N) (hXd : diam X ≤ D) :
    embE N M (K X) = K' (X.image (emb N M)) := by
  classical
  obtain ⟨hQ, h2, h3, h16⟩ := num_facts hd hL hj
  have hjN : j ≤ N := by omega
  have hdP : 64 * (2 ^ d * L ^ j) ≤ L ^ N := by
    calc 64 * (2 ^ d * L ^ j) = 2 ^ (d + 6) * L ^ j := by ring
      _ ≤ L ^ N := h2
  have hP1 : 1 ≤ L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hinj := emb_injective' (d := d) (L := L) hNM
  obtain ⟨x₀, hx₀⟩ := hX.2.1
  set τ : Zd d := cornerZ L j (rep x₀)
  set t : Lam d L N := prj τ
  set t' : Lam d L M := prj τ
  -- the translation on points near `X`
  have key : ∀ y : Lam d L N, (∃ x ∈ X, supNorm (y - x) ≤ 2 ^ d * L ^ j) →
      rep (y - t) = rep y - τ ∧ emb N M (y - t) = emb N M y - t' ∧
        supNorm (y - t) ≤ supNorm (y - x₀) + L ^ j := by
    rintro y ⟨x, hx, hyx⟩
    have hy1 := supNorm_add_le (y - x) x
    rw [sub_add_cancel] at hy1
    have hxx := le_diam hx hx₀
    have hyx₀ := supNorm_add_le (y - x) (x - x₀)
    rw [sub_add_sub_cancel] at hyx₀
    have hx5 := hX5 x hx
    have hx₀5 := hX5 x₀ hx₀
    have hnear : supNorm y + supNorm x₀ + supNorm (y - x₀) < L ^ N := by omega
    have hz : supNormZ (rep y - τ) ≤ supNorm (y - x₀) + L ^ j := by
      rw [supNormZ_le_iff]
      intro i
      have e1 := rep_sub_of hnear
      have e2 := natAbs_rep_le (y - x₀) i
      rw [e1] at e2
      obtain ⟨c1, c2, -⟩ := cornerZ_spec (L := L) j (rep x₀) i
      have hτi : τ i = cornerZ L j (rep x₀) i := rfl
      simp only [Pi.sub_apply] at e2 ⊢
      omega
    have hrep : rep y - τ = rep (y - t) := eq_rep (by rw [prj_sub, prj_rep]) (by omega)
    refine ⟨hrep.symm, ?_, ?_⟩
    · rw [emb, ← hrep, prj_sub]; rfl
    · rw [← supNormZ_rep_eq, ← hrep]; exact hz
  have hτ : ∀ {n : ℕ} [NeZero n], L ^ j ∣ n → ∀ i, L ^ j ∣ (co (-(prj τ : Torus d n)) i).val := by
    intro n _ hn i
    have : co (-(prj τ : Torus d n)) i = ((-(τ i) : ℤ) : ZMod n) := by
      show -((τ i : ℤ) : ZMod n) = _; push_cast; ring
    rw [this]
    exact dvd_val_intCast' hn (dvd_neg.2 (cornerZ_spec (L := L) j (rep x₀) i).2.2)
  set T : AffAut d L N := AffAut.transl (-t)
  set T' : AffAut d L M := AffAut.transl (-t')
  have hT : IsGen T := IsGen.transl _
  have hT' : IsGen T' := IsGen.transl _
  have hPB : PresBlocks j T := presBlocks_transl' hjN _ (hτ (pow_dvd_pow L hjN))
  have hPB' : PresBlocks j T' := presBlocks_transl' (hjN.trans hNM) _
    (hτ (pow_dvd_pow L (hjN.trans hNM)))
  have hTE : ∀ y, T.E y = y - t := fun y => by
    show y + -t = y - t; rw [sub_eq_add_neg]
  have hTE' : ∀ y, T'.E y = y - t' := fun y => by
    show y + -t' = y - t'; rw [sub_eq_add_neg]
  have hXX : ∀ x ∈ X, ∃ x' ∈ X, supNorm (x - x') ≤ 2 ^ d * L ^ j := fun x hx =>
    ⟨x, hx, by rw [sub_self, supNorm_zero]; exact Nat.zero_le _⟩
  -- the translated polymer is central
  set X₁ := T.img X
  have hX₁ : IsConn j X₁ := (hPB.isConn_img hT hjN).2 hX
  have hmem₁ : ∀ w, w ∈ X₁ ↔ ∃ x ∈ X, x - t = w := fun w => by
    simp only [X₁, AffAut.img, mem_map, Equiv.coe_toEmbedding, hTE]
  have hc₁ : ∀ w ∈ X₁, 4 * supNorm w ≤ L ^ N := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := (hmem₁ w).1 hw
    have := (key x (hXX x hx)).2.2
    have := le_diam hx hx₀
    omega
  have hd₁ : diam X₁ ≤ D := by
    refine diam_le fun w hw w' hw' => ?_
    obtain ⟨x, hx, rfl⟩ := (hmem₁ w).1 hw
    obtain ⟨x', hx', rfl⟩ := (hmem₁ w').1 hw'
    rw [sub_sub_sub_cancel_right]
    exact (le_diam hx hx').trans hXd
  have hcX := hc X₁ hX₁ hc₁ hd₁
  have hKX : autAlg T.E (K X : Alg d L N) = K X₁ := hK.aut T hT hPB X hX
  have himg : X₁.image (emb N M) = T'.img (X.image (emb N M)) := by
    ext y'
    simp only [mem_image, AffAut.img, mem_map, Equiv.coe_toEmbedding, hTE']
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hmem₁ w).1 hw
      exact ⟨_, ⟨x, hx, rfl⟩, ((key x (hXX x hx)).2.1).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x - t, (hmem₁ _).2 ⟨x, hx, rfl⟩, (key x (hXX x hx)).2.1⟩
  have hXe : IsConn j (X.image (emb N M)) := (isConn_image_iff hNM hjN h3 hX5).2 hX
  have hK'X : autAlg T'.E (K' (X.image (emb N M)) : Alg d L M) = K' (T'.img (X.image (emb N M))) :=
    hK'.aut T' hT' hPB' _ hXe
  have hcomm : ∀ F ∈ NX (nbhd j X : Set (Lam d L N)),
      embA N M (autAlg T.E F) = autAlg T'.E (embA N M F) := by
    intro F hF
    have := algHom_eqOn_NX (Φ := (embA N M).comp (autAlg T.E))
      (Ψ := (autAlg T'.E).comp (embA N M)) (fun a ha => ?_) hF
    · simpa using this
    · simp only [AlgHom.comp_apply, autAlg_ψ, embA_ψ hNM, hTE, hTE']
      obtain ⟨x, hx, hax⟩ := exists_near_of_mem_nbhd (mem_coe.1 ha)
      rw [(key a.1 ⟨x, hx, hax⟩).2.1]
  have e1 : autAlg T'.E (embA N M (K X)) = autAlg T'.E (K' (X.image (emb N M)) : Alg d L M) := by
    rw [← hcomm _ (hK.loc X hX), hKX, hK'X, ← himg, ← hcX, coe_embE]
  refine Subtype.ext ?_
  rw [coe_embE]
  have := congrArg (autAlg T'.E.symm) e1
  rwa [autAlg_symm_apply, autAlg_symm_apply] at this

end

end Flow
