import Grassmann.Coeff
import Grassmann.Nabla

/-!
# The norms `Φ_j(ℓ)` and `T_j(ℓ)` (`def:Phi`, `def:Tphi`)

The sites `X` carry a translation action of the multi-indices `ℕ^E`, where `E` is the set of
lattice directions (`b +ᵥ x = x + ∑_e b(e) e`).  The parameters of the norms are

* `p` — the maximal order `p_Φ` of derivatives in each variable;
* `h` — the spatial scale (`h = L^j` for `Φ_j(ℓ)`, `T_j(ℓ)`);
* `ℓ` — the field scale.

A test function is a family `g_n : Λ_f^n → ℂ`, `n ≥ 0`, i.e. a function on `Λ_f^*`, and
`‖g‖_{Φ} = sup_{n, z ∈ Λ_f^n, |α_i| ≤ p} ℓ^{-n} h^{|α_1| + ⋯ + |α_n|} |∇^{α_1}_{z_1} ⋯
∇^{α_n}_{z_n} g_z|` (`e:Phi-def`).  The `T` norm is the dual norm
`‖F‖_T = sup_{‖g‖_Φ ≤ 1} |⟨F, g⟩|`, `⟨F, g⟩ = ∑_z (1/z!) F_z g_z` (`e:Tphi-def`).
Norms take values in `ℝ≥0∞`; `tNorm_ne_top` shows that `‖F‖_T` is finite.

The algebra `𝒩(Λ)` is complex, and so are the test functions (as in `MR3332938`): with
real-valued test functions the product property `e:T-product` fails for complex `F`
(e.g. `F = 1 + i ψ_a` with `p = 0`, `ℓ = 1` has `‖F‖ = √2` but `‖F^2‖ = ‖1 + 2i ψ_a‖ = √5`).
-/

namespace Grassmann

noncomputable section

open Finset Equiv ENNReal

variable {X : Type*} [DecidableEq X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X]

/-- Translation of `(x, σ) ∈ Λ_f` in its spatial part. -/
def sh (b : E → ℕ) (a : Sf X) : Sf X := (b +ᵥ a.1, a.2)

@[simp] theorem sh_zero (a : Sf X) : sh (0 : E → ℕ) a = a := by simp [sh]

/-- Test functions `g : Λ_f^* → ℂ`. -/
abbrev TestFn (X : Type*) := ∀ n : ℕ, (Fin n → Sf X) → ℂ

/-- `∇^{α_1}_{z_1} ⋯ ∇^{α_n}_{z_n}` acting on functions of `z ∈ Λ_f^n`. -/
abbrev nab {W : Type*} [AddCommGroup W] [Module ℝ W] {n : ℕ} (α : Fin n → E → ℕ) :
    ((Fin n → Sf X) → W) →ₗ[ℝ] ((Fin n → Sf X) → W) :=
  nabla (sh (X := X)) α

/-- The total order `|α_1| + ⋯ + |α_n|`. -/
def ord {n : ℕ} (α : Fin n → E → ℕ) : ℕ := ∑ i, mabs (α i)

/-- The weighted size of one derivative of `g`. -/
def phiTerm (h ℓ : ℝ) (g : TestFn X) {n : ℕ} (z : Fin n → Sf X) (α : Fin n → E → ℕ) : ℝ :=
  ℓ⁻¹ ^ n * h ^ ord α * ‖nab α (g n) z‖

variable (E) in
/-- The norm `‖g‖_{Φ}` of `e:Phi-def` (with `p = p_Φ`, `h = L^j`). -/
def phiNorm (p : ℕ) (h ℓ : ℝ) (g : TestFn X) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (z : Fin n → Sf X) (α : Fin n → E → ℕ) (_ : ∀ i, mabs (α i) ≤ p),
    ENNReal.ofReal (phiTerm h ℓ g z α)

/-- The pairing `⟨F, g⟩ = ∑_{z ∈ Λ_f^*} (1/z!) F_z g_z`; only `|z| ≤ |Λ_f|` contribute. -/
def pair [Fintype X] (F : N X) (g : TestFn X) : ℂ :=
  ∑ n ∈ range (Nf X + 1), (n.factorial : ℂ)⁻¹ * ∑ z : Fin n → Sf X, coeff F z * g n z

variable (E) in
/-- The norm `‖F‖_{T}` of `e:Tphi-def` (with `p = p_Φ`, `h = L^j`). -/
def tNorm [Fintype X] (p : ℕ) (h ℓ : ℝ) (F : N X) : ℝ≥0∞ :=
  ⨆ (g : TestFn X) (_ : phiNorm E p h ℓ g ≤ 1), ENNReal.ofReal ‖pair F g‖

/-! ### Basic properties of `phiNorm` -/

section Phi

variable {p : ℕ} {h ℓ : ℝ}

theorem phiTerm_nonneg (hh : 0 ≤ h) (hℓ : 0 < ℓ) (g : TestFn X) {n : ℕ} (z : Fin n → Sf X)
    (α : Fin n → E → ℕ) : 0 ≤ phiTerm h ℓ g z α := by
  unfold phiTerm; positivity

theorem phiTerm_le (g : TestFn X) {n : ℕ} (z : Fin n → Sf X) (α : Fin n → E → ℕ)
    (hα : ∀ i, mabs (α i) ≤ p) : ENNReal.ofReal (phiTerm h ℓ g z α) ≤ phiNorm E p h ℓ g :=
  le_iSup_of_le n <| le_iSup_of_le z <| le_iSup_of_le α <| le_iSup_of_le hα le_rfl

theorem phiNorm_le {g : TestFn X} {M : ℝ}
    (hg : ∀ n (z : Fin n → Sf X) (α : Fin n → E → ℕ), (∀ i, mabs (α i) ≤ p) →
      phiTerm h ℓ g z α ≤ M) : phiNorm E p h ℓ g ≤ ENNReal.ofReal M :=
  iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα =>
    ENNReal.ofReal_le_ofReal (hg n z α hα)

theorem phiTerm_le_of_phiNorm_le (hh : 0 ≤ h) (hℓ : 0 < ℓ) {g : TestFn X} {M : ℝ}
    (hM : 0 ≤ M) (hg : phiNorm E p h ℓ g ≤ ENNReal.ofReal M) {n : ℕ} (z : Fin n → Sf X)
    (α : Fin n → E → ℕ) (hα : ∀ i, mabs (α i) ≤ p) : phiTerm h ℓ g z α ≤ M :=
  (ENNReal.ofReal_le_ofReal_iff hM).1 ((phiTerm_le g z α hα).trans hg)

/-- The bound `|∇^α g_z| ≤ M ℓ^n h^{-|α|}` implied by `‖g‖_Φ ≤ M`. -/
theorem abs_nab_le (hh : 0 < h) (hℓ : 0 < ℓ) {g : TestFn X} {M : ℝ} (hM : 0 ≤ M)
    (hg : phiNorm E p h ℓ g ≤ ENNReal.ofReal M) {n : ℕ} (z : Fin n → Sf X)
    (α : Fin n → E → ℕ) (hα : ∀ i, mabs (α i) ≤ p) :
    ‖nab α (g n) z‖ ≤ M * ℓ ^ n * (h ^ ord α)⁻¹ := by
  have := phiTerm_le_of_phiNorm_le hh.le hℓ hM hg z α hα
  unfold phiTerm at this
  rw [inv_pow] at this
  have h1 : 0 < ℓ ^ n := by positivity
  have h2 : 0 < h ^ ord α := by positivity
  rw [le_mul_inv_iff₀ h2, mul_comm M, ← div_le_iff₀' h1]
  calc ‖nab α (g n) z‖ * h ^ ord α / ℓ ^ n = (ℓ ^ n)⁻¹ * h ^ ord α * ‖nab α (g n) z‖ := by
        field_simp
    _ ≤ M := this

theorem abs_le_of_phiNorm_le (hh : 0 < h) (hℓ : 0 < ℓ) {g : TestFn X} {M : ℝ} (hM : 0 ≤ M)
    (hg : phiNorm E p h ℓ g ≤ ENNReal.ofReal M) {n : ℕ} (z : Fin n → Sf X) :
    ‖g n z‖ ≤ M * ℓ ^ n := by
  have := abs_nab_le hh hℓ hM hg z 0 (fun _ => by simp [mabs])
  rwa [nabla_zero _ (by simp), show ord (0 : Fin n → E → ℕ) = 0 by simp [ord, mabs], pow_zero,
    inv_one, mul_one] at this

theorem phiNorm_smul (hh : 0 ≤ h) (hℓ : 0 < ℓ) (c : ℂ) (g : TestFn X) :
    phiNorm E p h ℓ (c • g) = ENNReal.ofReal ‖c‖ * phiNorm E p h ℓ g := by
  simp only [phiNorm, ENNReal.mul_iSup]
  refine iSup_congr fun n => iSup_congr fun z => iSup_congr fun α => iSup_congr fun _ => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg c)]
  congr 1
  have : nab α ((c • g) n) z = c • nab α (g n) z := nabla_smul _ α c (g n) z
  simp only [phiTerm, this, smul_eq_mul, norm_mul]
  ring

theorem phiNorm_eq_zero (hh : 0 < h) (hℓ : 0 < ℓ) {g : TestFn X}
    (hg : phiNorm E p h ℓ g = 0) (n : ℕ) (z : Fin n → Sf X) : g n z = 0 := by
  have := abs_le_of_phiNorm_le hh hℓ le_rfl (by rw [hg, ENNReal.ofReal_zero]) z
  simpa using this

end Phi

/-! ### The pairing -/

section Pair

variable [Fintype X]

/-- `F ↦ ⟨F, g⟩` is linear. -/
def pairL (g : TestFn X) : N X →ₗ[ℂ] ℂ where
  toFun F := pair F g
  map_add' F G := by
    simp only [pair, coeff_add, add_mul, sum_add_distrib, mul_add]
  map_smul' c F := by
    simp only [pair, coeff_smul, mul_sum, RingHom.id_apply, smul_eq_mul]
    refine sum_congr rfl fun n _ => sum_congr rfl fun z _ => by ring

/-- `g ↦ ⟨F, g⟩` is linear. -/
def pairR (F : N X) : TestFn X →ₗ[ℂ] ℂ where
  toFun g := pair F g
  map_add' g g' := by
    simp only [pair, Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c g := by
    simp only [pair, Pi.smul_apply, smul_eq_mul, mul_sum, RingHom.id_apply]
    refine sum_congr rfl fun n _ => sum_congr rfl fun z _ => by ring

theorem pair_add (F G : N X) (g : TestFn X) : pair (F + G) g = pair F g + pair G g :=
  map_add (pairL g) F G

theorem pair_smul (c : ℂ) (F : N X) (g : TestFn X) : pair (c • F) g = c * pair F g :=
  map_smul (pairL g) c F

theorem pair_sum {ι : Type*} (s : Finset ι) (F : ι → N X) (g : TestFn X) :
    pair (∑ i ∈ s, F i) g = ∑ i ∈ s, pair (F i) g := map_sum (pairL g) F s

theorem pair_smul_right (F : N X) (c : ℂ) (g : TestFn X) : pair F (c • g) = c * pair F g :=
  map_smul (pairR F) c g

end Pair

/-- The antisymmetrisation `(A g)_z = (1/n!) ∑_σ sgn σ g_{z ∘ σ}`. -/
def asym (g : TestFn X) : TestFn X := fun n z =>
  (n.factorial : ℂ)⁻¹ * ∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * g n (z ∘ σ)

theorem asym_eq_zero_of_not_injective (g : TestFn X) {n : ℕ} {z : Fin n → Sf X}
    (hz : ¬Function.Injective z) : asym g n z = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, z i = z j ∧ i ≠ j := by
    simpa [Function.Injective, not_forall] using hz
  have h1 : z ∘ Equiv.swap i j = z := by
    funext k
    by_cases hki : k = i
    · subst hki; simp [hij]
    · by_cases hkj : k = j
      · subst hkj; simp [hij]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hS : ∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * g n (z ∘ σ) =
      -∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * g n (z ∘ σ) := by
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap i j)) _ _ fun σ => ?_
    simp only [Equiv.coe_mulLeft, Perm.sign_mul, Perm.sign_swap hne, Perm.coe_mul]
    rw [← Function.comp_assoc, h1]
    push_cast; ring
  have h0 : ∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * g n (z ∘ σ) = 0 := by
    linear_combination hS / 2
  simp only [asym]; rw [h0, mul_zero]

/-- `⟨ψ^u, g⟩ = (A g)_u`. -/
theorem pair_psiPow [Fintype X] {m : ℕ} (u : Fin m → Sf X) (g : TestFn X) :
    pair (psiPow u) g = asym g m u := by
  by_cases hm : m ≤ Nf X
  · rw [pair, sum_eq_single_of_mem m (mem_range.2 (by omega))]
    · simp_rw [coeff_psiPow, sum_mul]
      rw [asym, sum_comm]
      congr 1
      refine Fintype.sum_equiv (Equiv.inv (Perm (Fin m))) _ _ fun σ => ?_
      rw [sum_eq_single (u ∘ ⇑(σ⁻¹))]
      · have : u = (u ∘ ⇑(σ⁻¹)) ∘ σ := by ext i <;> simp
        rw [if_pos this]
        simp [Perm.sign_inv]
      · intro w _ hw
        rw [if_neg]; · simp
        intro hc; apply hw; rw [hc]; ext i <;> simp
      · simp
    · intro n _ hn
      rw [sum_eq_zero fun z _ => by rw [psiPow, coeff_ιMulti_of_ne _ _ hn, zero_mul], mul_zero]
  · have hu : ¬Function.Injective u := fun hu => by
      have := Fintype.card_le_of_injective u hu
      rw [Fintype.card_fin] at this; exact hm this
    rw [asym_eq_zero_of_not_injective g hu, psiPow,
      ExteriorAlgebra.ιMulti_eq_zero_of_not_inj fun h => hu fun a b hab => h (by simp [hab])]
    simp [pair]

variable {p : ℕ} {h ℓ : ℝ}

/-- `‖A g‖_Φ ≤ ‖g‖_Φ`. -/
theorem phiNorm_asym_le (hh : 0 ≤ h) (hℓ : 0 < ℓ) (g : TestFn X) :
    phiNorm E p h ℓ (asym g) ≤ phiNorm E p h ℓ g := by
  refine iSup_le fun n => iSup_le fun z => iSup_le fun α => iSup_le fun hα => ?_
  have key : ∀ σ : Perm (Fin n),
      nab α (fun w => g n (w ∘ σ)) z = nab (α ∘ σ) (g n) (z ∘ σ) := fun σ => by
    have := nabla_reindex (sh (X := X)) σ.symm (α ∘ σ) (g n) (z ∘ σ)
    have e1 : (α ∘ σ) ∘ σ.symm = α := by funext i; simp
    have e2 : (z ∘ σ) ∘ σ.symm = z := by funext i; simp
    rw [e1, e2, Equiv.symm_symm] at this
    exact this
  have hord : ∀ σ : Perm (Fin n), ord (α ∘ σ) = ord α := fun σ =>
    Fintype.sum_equiv σ _ _ fun i => rfl
  have hterm : ∀ σ : Perm (Fin n), ENNReal.ofReal (phiTerm h ℓ g (z ∘ σ) (α ∘ σ)) ≤
      phiNorm E p h ℓ g := fun σ => phiTerm_le g (z ∘ σ) (α ∘ σ) fun i => hα (σ i)
  by_cases htop : phiNorm E p h ℓ g = ⊤
  · rw [htop]; exact le_top
  set M := (phiNorm E p h ℓ g).toReal
  rw [← ENNReal.ofReal_toReal htop]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb : ∀ σ : Perm (Fin n), phiTerm h ℓ g (z ∘ σ) (α ∘ σ) ≤ M := fun σ =>
    (ENNReal.ofReal_le_iff_le_toReal htop).1 (hterm σ)
  have hnab : nab α (asym g n) z = (n.factorial : ℂ)⁻¹ *
      ∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * nab (α ∘ σ) (g n) (z ∘ σ) := by
    have : asym g n = fun w => (n.factorial : ℂ)⁻¹ • ∑ σ : Perm (Fin n),
        (Perm.sign σ : ℂ) • g n (w ∘ σ) := by
      ext w; simp [asym]
    rw [this, nabla_smul, nabla_sum, smul_eq_mul]
    congr 1
    refine sum_congr rfl fun σ _ => ?_
    rw [nabla_smul, key, smul_eq_mul]
  unfold phiTerm
  rw [hnab, norm_mul, norm_inv, Complex.norm_natCast]
  calc ℓ⁻¹ ^ n * h ^ ord α * ((n.factorial : ℝ)⁻¹ *
        ‖∑ σ : Perm (Fin n), (Perm.sign σ : ℂ) * nab (α ∘ σ) (g n) (z ∘ σ)‖)
      ≤ ℓ⁻¹ ^ n * h ^ ord α * ((n.factorial : ℝ)⁻¹ *
        ∑ σ : Perm (Fin n), ‖nab (α ∘ σ) (g n) (z ∘ σ)‖) := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine sum_congr rfl fun σ _ => ?_
        rw [norm_mul]
        rcases Int.units_eq_one_or (Perm.sign σ) with hs | hs <;> simp [hs]
    _ = (n.factorial : ℝ)⁻¹ * ∑ σ : Perm (Fin n), phiTerm h ℓ g (z ∘ σ) (α ∘ σ) := by
        simp only [phiTerm, hord, mul_sum]
        refine sum_congr rfl fun σ _ => by ring
    _ ≤ (n.factorial : ℝ)⁻¹ * ∑ _σ : Perm (Fin n), M := by gcongr with σ; exact hb σ
    _ = M := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end

end Grassmann
