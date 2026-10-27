import Loc.PauliPU
import Grassmann.TorusC

/-!
# Lemma `lem:pauli` on the torus (`h02uv-outline.tex`)

For `Λ = Λ_N` (side `n = L^N`), `j < N`, `Y ⊆ Λ` and `F ∈ 𝒩(Y)`:

  `‖F‖_{T_{j+1}(2ℓ)} ≤ C_*^{|𝔅|} ‖F‖_{T_j(ℓ)}`   (`pauli`)

with `C_* = (2^{p+2} C_χ)^2`, `p = p_Φ = 2d`, `C_χ = 2^p d (3p+1)`, for `L ≥ L₀(d)`. Here `𝔅` is
the set of B-spline cut-offs at scale `L^j` that do not vanish on `Y`. With `tNorm_ECC_theta_le`
this gives `‖𝔼_{C'} θ F‖_{T_{j+1}(ℓ)} ≤ C_*^{|𝔅|} ‖F‖_{T_j(ℓ)}` for Gram-admissible `C'`
(`pauli_EC`), the `d = 2` replacement of `Tj_EC_theta_le`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

variable {d n : ℕ} [NeZero n]

theorem torus_sum_apply {ι : Type*} (S : Finset ι) (f : ι → Torus d n) (i : Fin d) :
    ((∑ e ∈ S, f e : Torus d n) : Fin d → ZMod n) i = ∑ e ∈ S, ((f e : Torus d n) : Fin d → ZMod n) i :=
  Finset.sum_apply i S (fun e => (f e : Fin d → ZMod n))

/-- The coordinates of `∑_e b(e) e`. -/
theorem dirHom_apply (b : Dir d → ℕ) (i : Fin d) :
    ((dirHom b : Torus d n) : Fin d → ZMod n) i = (b (Sum.inl i) : ZMod n) - b (Sum.inr i) := by
  simp only [dirHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [show ((∑ e, b e • dirVec e : Torus d n) : Fin d → ZMod n) i =
    ∑ e, b e • ((dirVec e : Torus d n) : Fin d → ZMod n) i from by
      rw [torus_sum_apply]; rfl]
  rw [Fintype.sum_sum_type]
  simp only [dirVec, Pi.single_apply, Pi.neg_apply, smul_ite, smul_zero, nsmul_eq_mul, mul_one,
    smul_neg]
  simp [Finset.sum_ite_eq, sub_eq_add_neg]

/-- A derivative which does not vanish sees a nonzero value. -/
theorem exists_ne_zero_of_D1_ne_zero {Y : Type*} {E : Type*} [Fintype E] [DecidableEq E]
    (s : (E → ℕ) → Y → Y) (b : E → ℕ) (f : Y → ℝ) (y : Y) (h : D1 s b f y ≠ 0) :
    ∃ c ∈ Iic b, f (s c y) ≠ 0 := by
  rw [D1_eq_sum] at h
  obtain ⟨c, hc, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  exact ⟨c, hc, right_ne_zero_of_mul hne⟩


/-- The constant vector `(p, …, p)`. -/
def pOne (p : ℕ) : Torus d n := fun _ => (p : ZMod n)

theorem le_mabs_apply (b : Dir d → ℕ) (e : Dir d) : b e ≤ mabs b :=
  single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (mem_univ e)

/-- The path length from the centre `R q - (p, …, p)` near the support. -/
theorem dstT_le {R p : ℕ} {K : ℕ} (q : Fin d → Fin K) {y : Sf (Torus d n)} {b c : Dir d → ℕ}
    (hcb : c ≤ b) (hb : mabs b ≤ p)
    (hsupp : ∀ i, ((((c +ᵥ y.1 : Torus d n) - gridPt R q : Torus d n) : Fin d → ZMod n) i).val <
      (p + 1) * R) :
    dstT (gridPt R q - pOne p) (sh b y) ≤ d * ((p + 1) * R + 2 * p) := by
  unfold dstT
  calc ∑ i, ((((sh b y).1 - (gridPt R q - pOne p) : Torus d n) : Fin d → ZMod n) i).val
      ≤ ∑ _i : Fin d, ((p + 1) * R + 2 * p) := sum_le_sum fun i _ => ?_
    _ = d * ((p + 1) * R + 2 * p) := by simp
  set b' := b - c
  have hbc : b = c + b' := by
    funext e; simp only [b', Pi.add_apply, Pi.sub_apply]; have h' : c e ≤ b e := hcb e; omega
  have hN : (b' (Sum.inl i) : ZMod n) - b' (Sum.inr i) + p =
      ((b' (Sum.inl i) + (p - b' (Sum.inr i)) : ℕ) : ZMod n) := by
    have h1 : b' (Sum.inr i) ≤ p := (Nat.sub_le _ _).trans ((le_mabs_apply b _).trans hb)
    push_cast [Nat.cast_sub h1]; ring
  have heq : (((sh b y).1 - (gridPt R q - pOne p) : Torus d n) : Fin d → ZMod n) i =
      ((((c +ᵥ y.1 : Torus d n) - gridPt R q : Torus d n) : Fin d → ZMod n) i) +
        ((b' (Sum.inl i) + (p - b' (Sum.inr i)) : ℕ) : ZMod n) := by
    rw [← hN]
    have e1 : ((sh b y).1 - (gridPt R q - pOne p) : Torus d n) =
        ((c +ᵥ y.1 : Torus d n) - gridPt R q) + dirHom b' + pOne p := by
      simp only [sh, Grassmann.vadd_def]
      rw [show (∑ e, b e • dirVec e : Torus d n) = dirHom b from rfl, hbc, map_add]
      rw [show (∑ e, c e • dirVec e : Torus d n) = dirHom c from rfl]
      abel
    rw [e1]
    show (((c +ᵥ y.1 : Torus d n) - gridPt R q : Torus d n) : Fin d → ZMod n) i +
      ((dirHom b' : Torus d n) : Fin d → ZMod n) i + (p : ZMod n) = _
    rw [dirHom_apply]; ring
  rw [heq]
  calc _ ≤ _ := ZMod.val_add_le _ _
    _ ≤ (p + 1) * R + (b' (Sum.inl i) + (p - b' (Sum.inr i))) := by
        refine Nat.add_le_add (hsupp i).le ?_
        rw [ZMod.val_natCast]; exact Nat.mod_le _ _
    _ ≤ (p + 1) * R + 2 * p := by
        have : b' (Sum.inl i) ≤ p := (Nat.sub_le _ _).trans ((le_mabs_apply b _).trans hb)
        omega


/-! ### The theorem -/

open Classical in
/-- The blocks whose cut-off does not vanish on `Y`. -/
def nearB (R p K : ℕ) (Y : Set (Torus d n)) : Finset (Fin d → Fin K) :=
  univ.filter fun q => ∃ x ∈ Y, bsp R p (x - gridPt R q) ≠ 0

/-- The constant `C_χ = 2^p d (3p + 1)` of the B-spline partition of unity. -/
def cChi (d p : ℕ) : ℝ := 2 ^ p * d * (3 * p + 1)

/-- The admissible size `L₀` of the scale factor. -/
def pauliL0 (d : ℕ) : ℝ :=
  4 * (2 ^ pPhi d * ((pPhi d + 1 : ℕ) : ℝ) ^ (2 * d) * cChi d (pPhi d))

/-- The constant `C_*` of `lem:pauli`. -/
def pauliC (d : ℕ) : ℝ := (4 * (2 ^ pPhi d * cChi d (pPhi d))) ^ 2

open Classical in
/-- **Lemma `lem:pauli`**: `‖F‖_{T_{j+1}(2ℓ)} ≤ C_*^{|𝔅|} ‖F‖_{T_j(ℓ)}` for `F ∈ 𝒩(Y)`, where
`𝔅 = nearB` are the cut-offs at scale `L^j` which do not vanish on `Y`. -/
theorem pauli (hd : 1 ≤ d) {L Nt j : ℕ} (hL : pauliL0 d ≤ L) (hj : j < Nt) (hn : n = L ^ Nt)
    {Y : Set (Torus d n)} {F : N (Torus d n)} (hF : F ∈ NX Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tj d (L : ℝ) (j + 1) (2 * ℓ) F ≤
      ENNReal.ofReal (pauliC d ^ (nearB (n := n) (L ^ j) (pPhi d) (L ^ (Nt - j)) Y).card) *
        Tj d (L : ℝ) j ℓ F := by
  set p := pPhi d
  set R := L ^ j
  set K := L ^ (Nt - j)
  have hp : 1 ≤ p := by simp only [p, pPhi]; omega
  have hCχ : 1 ≤ cChi d p := by
    unfold cChi
    have h1 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h3 : (1 : ℝ) ≤ 3 * p + 1 := by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith
    have := mul_le_mul h1 h2 zero_le_one (by positivity)
    nlinarith
  have hL1 : (1 : ℝ) ≤ L := by
    refine le_trans ?_ hL
    unfold pauliL0
    have : (1 : ℝ) ≤ cChi d (pPhi d) := hCχ
    have h1 : (1 : ℝ) ≤ 2 ^ pPhi d := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ ((pPhi d + 1 : ℕ) : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
    have := mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) this zero_le_one
      (by positivity)
    nlinarith
  have hLn : 1 ≤ L := by exact_mod_cast hL1
  have hR0 : 0 < R := pow_pos (by omega) j
  have hnRK : n = R * K := by rw [hn, ← pow_add]; congr 1; omega
  have hn1 : 1 < n := by
    have hL2 : 2 ≤ L := by
      by_contra h; push Not at h
      have hL1' : L = 1 := by omega
      have : pauliL0 d ≤ 1 := by rw [hL1'] at hL; exact_mod_cast hL
      have hge : 4 ≤ pauliL0 d := by
        unfold pauliL0
        have : (1 : ℝ) ≤ 2 ^ pPhi d * ((pPhi d + 1 : ℕ) : ℝ) ^ (2 * d) * cChi d (pPhi d) := by
          have h1 : (1 : ℝ) ≤ 2 ^ pPhi d := one_le_pow₀ (by norm_num)
          have h2 : (1 : ℝ) ≤ ((pPhi d + 1 : ℕ) : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
          have := mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) hCχ zero_le_one
            (by positivity)
          linarith
        linarith
      linarith
    rw [hn]
    calc 1 < L := by omega
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ Nt := Nat.pow_le_pow_right (by omega) (by omega)
  set S := nearB (n := n) R p K Y
  -- the blocks, cut-offs, centres and path lengths
  let χ : S → Torus d n → ℝ := fun B x => bsp R p (x - gridPt R B.1)
  let cB : S → Torus d n := fun B => gridPt R B.1 - pOne p
  let Dst : S → Sf (Torus d n) → ℝ := fun B y => (dstT (cB B) y : ℝ)
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR0
  -- sums over the near blocks are bounded by sums over all grid points
  have hsub : ∀ f : (Fin d → Fin K) → ℝ, (∀ q, 0 ≤ f q) → ∑ B : S, f B.1 ≤ ∑ q, f q := by
    intro f hf
    rw [Finset.sum_coe_sort S f]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun q _ _ => hf q
  have hgrid : ∀ (y : Sf (Torus d n)) (b : Dir d → ℕ), mabs b ≤ p →
      ∑ q : Fin d → Fin K, |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y| ≤
        2 ^ p * ((R : ℝ) ^ mabs b)⁻¹ := by
    intro y b hb
    refine (sum_grid_D1_bsp_le hn1 hR0 hnRK (mabs b) p b rfl hb y).trans ?_
    rw [div_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hb) (by positivity)
  have hCp : (2 : ℝ) ^ p ≤ cChi d p := by
    unfold cChi
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h3 : (1 : ℝ) ≤ 3 * p + 1 := by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith
    have := mul_le_mul h2 h3 zero_le_one (by positivity)
    rw [mul_assoc]
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hmain := pauli_abstract (X := Torus d n) (E := Dir d) (Bk := S) (χ := χ) (cB := cB)
    (Dst := Dst) (p := p) (h₀ := (R : ℝ)) (L := (L : ℝ)) (Cχ := cChi d p) hp hRr hL1 hCχ
    (by
      have : Fintype.card (Dir d) = 2 * d := by simp [Dir]; ring
      rw [this]; exact hL)
    (fun B y => Nat.cast_nonneg _) (fun B => pathH_torus hn1 (cB B))
    (fun y b hb => by
      refine (hsub (fun q => |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y|)
        (fun q => abs_nonneg _)).trans ((hgrid y b hb).trans ?_)
      exact mul_le_mul_of_nonneg_right hCp (by positivity))
    (fun y b hb => by
      have hD : ∀ q : Fin d → Fin K, |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y| *
          (dstT (gridPt R q - pOne p) (sh b y) : ℝ) ≤
          |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y| * (d * ((p + 1) * R + 2 * p) : ℕ) := by
        intro q
        by_cases h0 : D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y = 0
        · rw [h0]; simp
        · obtain ⟨c, hc, hne⟩ := exists_ne_zero_of_D1_ne_zero sh b _ y h0
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact_mod_cast dstT_le q (mem_Iic.1 hc) hb fun i => bsp_support p _ hne i
      calc ∑ B : S, |D1 sh b (fun a => χ B a.1) y| * Dst B (sh b y)
          ≤ ∑ q : Fin d → Fin K, |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y| *
              (dstT (gridPt R q - pOne p) (sh b y) : ℝ) :=
            hsub (fun q => |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y| *
              (dstT (gridPt R q - pOne p) (sh b y) : ℝ)) (fun q => by positivity)
        _ ≤ ∑ q : Fin d → Fin K, |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y| *
              (d * ((p + 1) * R + 2 * p) : ℕ) := sum_le_sum fun q _ => hD q
        _ = (∑ q : Fin d → Fin K, |D1 sh b (fun a => bsp R p (a.1 - gridPt R q)) y|) *
              (d * ((p + 1) * R + 2 * p) : ℕ) := by rw [sum_mul]
        _ ≤ (2 ^ p * ((R : ℝ) ^ mabs b)⁻¹) * (d * ((3 * p + 1) * R)) := by
            refine mul_le_mul (hgrid y b hb) ?_ (by positivity) (by positivity)
            push_cast
            have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR0
            have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
            have h1 : ((p : ℝ) + 1) * R + 2 * p ≤ (3 * p + 1) * R := by nlinarith
            exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
        _ = cChi d p * R * ((R : ℝ) ^ mabs b)⁻¹ := by unfold cChi; ring)
    (Y := Y) (fun x hx => by
      show ∑ B : S, bsp R p (x - gridPt R B.1) = 1
      rw [Finset.sum_coe_sort S (fun q => bsp R p (x - gridPt R q))]
      rw [← sum_bsp_grid hR0 hnRK p x]
      refine sum_subset (subset_univ _) fun q _ hq => ?_
      by_contra hne
      exact hq (mem_filter.2 ⟨mem_univ _, x, hx, hne⟩)) hF hℓ
  have hcard : Fintype.card S = S.card := Fintype.card_coe S
  rw [hcard] at hmain
  have hRL : (R : ℝ) * L = (L : ℝ) ^ (j + 1) := by simp only [R]; push_cast; ring
  rw [hRL] at hmain
  refine hmain.trans (le_of_eq ?_)
  have e1 : ((R : ℕ) : ℝ) = (L : ℝ) ^ j := by simp [R]
  rw [e1]
  unfold pauliC
  rw [← pow_mul, mul_comm 2 S.card]

open Classical in
/-- The cells of `Y` at scale `R`: `x ↦ (⌊x_i / R⌋)_i`. -/
def cells (R : ℕ) (Y : Set (Torus d n)) : Finset (Fin d → ℕ) :=
  (univ.filter fun x => x ∈ Y).image fun x => fun i => ((x : Fin d → ZMod n) i).val / R

/-- One coordinate of a near block is determined by the cell and an offset `t ≤ p`. -/
theorem near_coord {R K p : ℕ} (hR0 : 0 < R) (hn : n = R * K) (a : ZMod n) (qi : Fin K)
    (h : (a - ((R * qi : ℕ) : ZMod n)).val < (p + 1) * R) :
    ∃ t : ℕ, t ≤ p ∧ (qi : ℕ) = (a.val / R + (p + 1) * K - t) % K := by
  have hav := ZMod.val_lt a
  obtain ⟨v, hv⟩ : ∃ v, v = a.val := ⟨_, rfl⟩
  rw [← hv] at hav ⊢
  have hdm := Nat.div_add_mod v R
  have hmod := Nat.mod_lt v hR0
  have hq := qi.isLt
  have hRq : R * qi < n := by
    calc R * qi < R * K := Nat.mul_lt_mul_of_pos_left hq hR0
      _ = n := hn.symm
  have hRqv : ((R * qi : ℕ) : ZMod n).val = R * qi := ZMod.val_cast_of_lt hRq
  set c := v / R
  have hcK : c < K := by
    rw [Nat.div_lt_iff_lt_mul hR0, mul_comm, ← hn]; exact hav
  by_cases hle : R * qi ≤ v
  · rw [ZMod.val_sub (by rw [hRqv, ← hv]; exact hle), hRqv, ← hv] at h
    have h1 : (qi : ℕ) ≤ c := by
      rw [Nat.le_div_iff_mul_le hR0, mul_comm]; exact hle
    have h2 : c - qi ≤ p := by
      by_contra h3; push Not at h3
      have : R * (p + 1) ≤ R * (c - qi) := Nat.mul_le_mul_left R h3
      have : R * (c - qi) + R * qi = R * c := by rw [← mul_add, Nat.sub_add_cancel h1]
      have : R * c ≤ v := by rw [mul_comm]; exact Nat.div_mul_le_self v R
      have h4 : R * (c - qi) ≤ v - R * qi := Nat.le_sub_of_add_le (by omega)
      rw [Nat.mul_comm (p + 1) R] at h
      omega
    refine ⟨c - qi, h2, ?_⟩
    have e : c + (p + 1) * K - (c - qi) = qi + (p + 1) * K := by omega
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  · push Not at hle
    rw [val_sub_of_lt (by rw [hRqv, ← hv]; exact hle), hRqv, ← hv] at h
    have h1 : c < qi := by
      by_contra h3; push Not at h3
      have : R * qi ≤ R * c := Nat.mul_le_mul_left R h3
      have : R * c ≤ v := by rw [mul_comm]; exact Nat.div_mul_le_self v R
      omega
    have h2 : K - qi + c ≤ p := by
      by_contra h3; push Not at h3
      have hK : R * (K - qi) + R * qi = n := by rw [← mul_add, Nat.sub_add_cancel hq.le, hn]
      have : R * (p + 1) ≤ R * (K - qi + c) := Nat.mul_le_mul_left R h3
      have h5 : R * c ≤ v := by rw [mul_comm]; exact Nat.div_mul_le_self v R
      have h6 : R * (K - qi + c) = R * (K - qi) + R * c := mul_add _ _ _
      rw [Nat.mul_comm (p + 1) R] at h
      omega
    refine ⟨K - qi + c, h2, ?_⟩
    have e : c + (p + 1) * K - (K - qi + c) = qi + p * K := by
      have : (p + 1) * K = p * K + K := by ring
      omega
    rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

open Classical in
/-- `|𝔅| ≤ (p+1)^d · #cells(Y)`: each cell of `Y` meets at most `(p+1)^d` cut-offs. -/
theorem card_nearB_le {R K p : ℕ} (hR0 : 0 < R) (hn : n = R * K) (Y : Set (Torus d n)) :
    (nearB (n := n) R p K Y).card ≤ (p + 1) ^ d * (cells R Y).card := by
  have hK : 0 < K := Nat.pos_of_ne_zero fun h => by
    subst h; simp at hn; exact NeZero.ne n hn
  set φ : (Fin d → ℕ) × (Fin d → Fin (p + 1)) → (Fin d → Fin K) := fun ct i =>
    ⟨(ct.1 i + (p + 1) * K - ct.2 i) % K, Nat.mod_lt _ hK⟩
  have hsub : nearB (n := n) R p K Y ⊆ (cells R Y ×ˢ (univ : Finset (Fin d → Fin (p + 1)))).image φ := by
    intro q hq
    obtain ⟨-, x, hx, hne⟩ := mem_filter.1 hq
    have hsupp := bsp_support p _ hne
    choose t ht htq using fun i => near_coord hR0 hn ((x : Fin d → ZMod n) i) (q i) (hsupp i)
    refine mem_image.2 ⟨(fun i => ((x : Fin d → ZMod n) i).val / R, fun i => ⟨t i, by
      have := ht i; omega⟩), mem_product.2 ⟨mem_image.2 ⟨x, mem_filter.2 ⟨mem_univ _, hx⟩, rfl⟩,
        mem_univ _⟩, ?_⟩
    funext i
    exact Fin.ext (htq i).symm
  calc (nearB (n := n) R p K Y).card
      ≤ ((cells R Y ×ˢ (univ : Finset (Fin d → Fin (p + 1)))).image φ).card := card_le_card hsub
    _ ≤ (cells R Y ×ˢ (univ : Finset (Fin d → Fin (p + 1)))).card := card_image_le
    _ = (p + 1) ^ d * (cells R Y).card := by
        rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, mul_comm]

/-- The consequence for the Gaussian expectation (the `d = 2` replacement of
`Tj_EC_theta_le`): for a covariance with a Gram representation at scale `j + 1`,
`‖𝔼_C θ F‖_{T_{j+1}(ℓ)} ≤ C_*^{|𝔅|} ‖F‖_{T_j(ℓ)}`. -/
theorem pauli_EC (hd : 1 ≤ d) {L Nt j : ℕ} (hL : pauliL0 d ≤ L) (hj : j < Nt) (hn : n = L ^ Nt)
    {Y : Set (Torus d n)} {F : N (Torus d n)} (hF : F ∈ NX Y) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {C : Matrix (Torus d n) (Torus d n) ℂ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Fv Gv : Torus d n → H} (hC : IsGram C Fv Gv)
    (hB : GramBound (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ Fv Gv) :
    Tj d (L : ℝ) (j + 1) ℓ (ECC C (theta F)) ≤
      ENNReal.ofReal (pauliC d ^ (nearB (n := n) (L ^ j) (pPhi d) (L ^ (Nt - j)) Y).card) *
        Tj d (L : ℝ) j ℓ F := by
  have hL0 : (0 : ℝ) < L := by
    have : (1 : ℝ) ≤ pauliL0 d := by
      unfold pauliL0 cChi
      have h1 : (1 : ℝ) ≤ 2 ^ pPhi d := one_le_pow₀ (by norm_num)
      have h2 : (1 : ℝ) ≤ ((pPhi d + 1 : ℕ) : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ 2 ^ pPhi d * d * (3 * pPhi d + 1) := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have : (1 : ℝ) ≤ 3 * pPhi d + 1 := by
          have : (0 : ℝ) ≤ pPhi d := Nat.cast_nonneg _; linarith
        have := mul_le_mul (mul_le_mul h1 ‹(1 : ℝ) ≤ d› zero_le_one (by positivity))
          this zero_le_one (by positivity)
        linarith
      have := mul_le_mul (mul_le_mul h1 h2 zero_le_one (by positivity)) h3 zero_le_one
        (by positivity)
      linarith
    linarith
  exact (Tj_ECC_theta_le hL0 hℓ (j + 1) hC hB F).trans (pauli hd hL hj hn hF hℓ)

end

end Loc
