import Obs2.Flow.MuChain2

/-!
# The Case-(2) tadpole `τ₂` and the one-loop coefficient `𝔫^{(2)}` explicitly

Case (2) analogue of `Obs2.Flow.MuTad2` (`tauC`, `tauC_TI`), without any Grassmann computation:

* **`expLC_FC_eq`**: `e^{ℒ_Γ}F_C(A,B) = F_{C+Γ}(e^{ℒ_Γ}A, e^{ℒ_Γ}B) - F_Γ(e^{ℒ_Γ}A, e^{ℒ_Γ}B)`;
* `lfunX C Γ a`: the polarisation of the bubble `𝔩_C(a)` (`lfunC_add`:
  `𝔩_{C+Γ} = 𝔩_C + 𝔩_Γ + 𝔩_{C,Γ}`), bilinear (`lfunX_add_left`, `lfunX_add_right`,
  `lfunX_sum_left`); `rowS C a = ∑_x C(a,x) + ∑_x C(x,a)` (linear);
* **`tau2_Vcoup`**: for `Γ(x,x) = c₀`, `Γ(x ± e, x) = Γ(x, x ± e) = c₀ + δ`,
  `τ₂(C, Γ)(V_κ(Λ) + r) = g (2dδ·rowS_C(a) - 𝔩_{C,Γ}(a))` (the first term is the tadpole on the
  legs of the quartic, i.e. the `ν`-shift of `κ.shift`, the second the gradient bubble with one
  line `C` and one line `Γ`);
* `Bulk2`: the bulk parts `V'_k(Λ)_∅ = V_{κ_k}(Λ) + r_k` and the lattice constants `(c₀_k, δ_k)`
  of the covariances for `k < n`;
* **`Bulk2.tadInc2_eq`**: `tadInc2 k j = g_k(2dδ_j rowS_{C_k}(a) - 𝔩_{C_k,C_j}(a))`;
  **`Bulk2.frakN2_eq`**: `𝔫^{(2)}_j = ν_j rowS_{C_j} - g_j𝔩_{C_j} + ∑_{k<j} tadInc2 k j`;
* **`Bulk2.frakN2_split`** (exact): with `S_j = ∑_{k<j} rowS_{C_k}(a)`, `w_j = ∑_{k<j} C_k`,
  `ν♭_j = ν_j - 2d g_j δ_j` (the unshifted coupling),
  `𝔫^{(2)}_j = ν_jS_{j+1} - ν♭_jS_j - g_j(𝔩_{w_{j+1}} - 𝔩_{w_j}) - 2dδ_j∑_{k<j}(g_j - g_k)rowS_{C_k}
     + ∑_{k<j}(g_j - g_k)𝔩_{C_k,C_j}`:
  a telescoping `ν` part, the bubble increment of the accumulated covariance (the
  `(β/3)ǧ_j` of `prop:gamma`), and two drift terms (`O(ǧ²)` for slowly varying `g`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 LocObs

variable {d L N : ℕ} [NeZero L]

/-- **`e^{ℒ_Γ}F_C(A,B) = F_{C+Γ}(e^{ℒ_Γ}A, e^{ℒ_Γ}B) - F_Γ(e^{ℒ_Γ}A, e^{ℒ_Γ}B)`.** -/
theorem expLC_FC_eq (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (A B : Alg d L N) :
    expLC Γ (FC C A B) =
      FC (C + Γ) (expLC Γ A) (expLC Γ B) - FC Γ (expLC Γ A) (expLC Γ B) := by
  have h1 : ∀ F : Alg d L N, expLC (-(C + Γ)) (expLC Γ F) = expLC (-C) F := fun F => by
    rw [neg_add, expLC_add, expLC_neg_expLC]
  rw [FC_expLC]
  simp only [FC]
  rw [h1, h1, show C + Γ = Γ + C from add_comm _ _, expLC_add, map_sub]
  abel

/-! ### The polarised bubble -/

section Bubble

variable (C C' Γ Γ' : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N)

/-- One polarised gradient leg pair. -/
def gpX (e : Dir d) (z : Lam d L N) : ℂ :=
  (C a (z + dirVec e) - C a z) * (Γ (z + dirVec e) a - Γ z a) +
    (Γ a (z + dirVec e) - Γ a z) * (C (z + dirVec e) a - C z a)

/-- The polarisation `𝔩_{C,Γ}(a) = 𝔩_{C+Γ}(a) - 𝔩_C(a) - 𝔩_Γ(a)` of the bubble. -/
def lfunX : ℂ :=
  ∑ i : Fin d, ∑ z, (1 / 2 : ℂ) * (gpX C Γ a (Sum.inl i) z + gpX C Γ a (Sum.inr i) z)

/-- `∑_x C(a,x) + ∑_x C(x,a)`. -/
def rowS : ℂ := ∑ x, C a x + ∑ x, C x a

theorem gpC_add (e : Dir d) (z : Lam d L N) :
    gpC (C + Γ) a e z = gpC C a e z + gpC Γ a e z + gpX C Γ a e z := by
  simp only [gpC, gpX, Matrix.add_apply]; ring

theorem lfunC_add : lfunC (C + Γ) a = lfunC C a + lfunC Γ a + lfunX C Γ a := by
  unfold lfunC lfunX
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  rw [gpC_add, gpC_add]; ring

theorem lfunX_add_left : lfunX (C + C') Γ a = lfunX C Γ a + lfunX C' Γ a := by
  unfold lfunX gpX
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  simp only [Matrix.add_apply]; ring

theorem lfunX_add_right : lfunX C (Γ + Γ') a = lfunX C Γ a + lfunX C Γ' a := by
  unfold lfunX gpX
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  simp only [Matrix.add_apply]; ring

theorem lfunX_zero_left : lfunX (0 : Matrix (Lam d L N) (Lam d L N) ℂ) Γ a = 0 := by
  simp [lfunX, gpX]

theorem lfunX_sum_left {ι : Type*} (s : Finset ι) (Cs : ι → Matrix (Lam d L N) (Lam d L N) ℂ) :
    lfunX (∑ k ∈ s, Cs k) Γ a = ∑ k ∈ s, lfunX (Cs k) Γ a := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, lfunX_zero_left]
  | insert k s hk ih => rw [sum_insert hk, sum_insert hk, lfunX_add_left, ih]

theorem rowS_add : rowS (C + Γ) a = rowS C a + rowS Γ a := by
  simp only [rowS, Matrix.add_apply, sum_add_distrib]; ring

end Bubble

/-! ### `τ₂` with the bulk polynomial -/

/-- `m₂F_C(ψ̄_aψ_a + s, V_κ(Λ) + t) = ν rowS_C(a) - g𝔩_C(a)`. -/
theorem mass2_FC_pbp_const (C : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) (s t : ℂ)
    (κ : Coup) :
    mass2 (FC C (pbp a + s • (1 : Alg d L N)) (Vcoup κ univ + t • (1 : Alg d L N))) =
      κ.nu * rowS C a - κ.g * lfunC C a := by
  rw [FC_add_left, Step2.FC_const_left, add_zero, FC_add_right, FC_smul_right, FC_one_right,
    smul_zero, add_zero, mass2_FC_pbp_Vcoup, rowS]

/-- **The tadpole `τ₂` explicitly**: for `Γ` with the lattice constants `(c₀, δ)`,
`τ₂(C, Γ)(V_κ(Λ) + r) = g(2dδ rowS_C(a) - 𝔩_{C,Γ}(a))`. -/
theorem tau2_Vcoup (C Γ : Matrix (Lam d L N) (Lam d L N) ℂ) (a : Lam d L N) {c₀ δ : ℂ}
    (hc : ∀ x, Γ x x = c₀) (hδ : ∀ x e, Γ (x + dirVec e) x = c₀ + δ)
    (hδ' : ∀ x e, Γ x (x + dirVec e) = c₀ + δ) (κ : Coup) (r : ℂ) :
    tau2 C Γ a (Vcoup κ univ + r • (1 : Alg d L N)) =
      κ.g * (2 * d * δ * rowS C a - lfunX C Γ a) := by
  obtain ⟨s, hs⟩ := expLC_pbp Γ a
  obtain ⟨r', hr'⟩ := expLC_Vcoup hc hδ hδ' κ univ
  have hB : expLC Γ (Vcoup κ univ + r • (1 : Alg d L N)) =
      Vcoup (κ.shift d c₀ δ) univ + (r' + r) • (1 : Alg d L N) := by
    rw [map_add, hr', map_smul, expLC_one', add_smul, add_assoc]
  have h0 : FC C (pbp a) (Vcoup κ univ + r • (1 : Alg d L N)) =
      FC C (pbp a + (0 : ℂ) • (1 : Alg d L N)) (Vcoup κ univ + r • (1 : Alg d L N)) := by
    rw [zero_smul, add_zero]
  rw [tau2, expLC_FC_eq, hs, hB, Obs2.mass2_sub, mass2_FC_pbp_const, mass2_FC_pbp_const, h0,
    mass2_FC_pbp_const, lfunC_add, rowS_add]
  simp only [Coup.shift]
  ring

/-! ### Along a chain of steps -/

/-- **The bulk data of a chain** (`k < n`): `V'_k(Λ)_∅ = V_{κ_k}(Λ) + r` and the lattice constants
`C_k(x,x) = c₀_k`, `C_k(x ± e, x) = C_k(x, x ± e) = c₀_k + δ_k`. -/
structure Bulk2 (C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ) (V : ℕ → OFam .two d L N)
    (κ : ℕ → Coup) (c₀ δ : ℕ → ℂ) (n : ℕ) : Prop where
  he : ∀ k < n, ∃ r : ℂ, bulkE2 C V k = Vcoup (κ k) univ + r • (1 : Alg d L N)
  hc : ∀ k < n, ∀ x, C k x x = c₀ k
  hδ : ∀ k < n, ∀ x e, C k (x + dirVec e) x = c₀ k + δ k
  hδ' : ∀ k < n, ∀ x e, C k x (x + dirVec e) = c₀ k + δ k

namespace Bulk2

variable {C : ℕ → Matrix (Lam d L N) (Lam d L N) ℂ} {V : ℕ → OFam .two d L N} {κ : ℕ → Coup}
  {c₀ δ : ℕ → ℂ} {n : ℕ} (H : Bulk2 C V κ c₀ δ n)
include H

/-- The lattice constants of a sum `∑_{i ∈ s} C_i`. -/
theorem sum_consts {s : Finset ℕ} (hs : ∀ i ∈ s, i < n) :
    (∀ x, (∑ i ∈ s, C i) x x = ∑ i ∈ s, c₀ i) ∧
    (∀ x e, (∑ i ∈ s, C i) (x + dirVec e) x = ∑ i ∈ s, c₀ i + ∑ i ∈ s, δ i) ∧
    (∀ x e, (∑ i ∈ s, C i) x (x + dirVec e) = ∑ i ∈ s, c₀ i + ∑ i ∈ s, δ i) := by
  refine ⟨fun x => ?_, fun x e => ?_, fun x e => ?_⟩
  · rw [Matrix.sum_apply]; exact sum_congr rfl fun i hi => H.hc i (hs i hi) x
  · rw [Matrix.sum_apply, ← sum_add_distrib]; exact sum_congr rfl fun i hi => H.hδ i (hs i hi) x e
  · rw [Matrix.sum_apply, ← sum_add_distrib]; exact sum_congr rfl fun i hi => H.hδ' i (hs i hi) x e

/-- **`tadInc2 k j = g_k(2dδ_j rowS_{C_k}(a) - 𝔩_{C_k,C_j}(a))`** for `k < j < n`. -/
theorem tadInc2_eq (P : ObsPts d L N) {k j : ℕ} (hkj : k < j) (hj : j < n) :
    tadInc2 P C V k j = (κ k).g * (2 * d * δ j * rowS (C k) P.a - lfunX (C k) (C j) P.a) := by
  obtain ⟨r, hr⟩ := H.he k (by omega)
  have hs : ∀ i ∈ Ioo k j, i < n := fun i hi => by have := (mem_Ioo.1 hi).2; omega
  obtain ⟨hS0, hS1, hS2⟩ := H.sum_consts hs
  have hT0 : ∀ x, (C j + cumBetween C k j) x x = c₀ j + ∑ i ∈ Ioo k j, c₀ i := fun x => by
    rw [Matrix.add_apply, H.hc j hj, cumBetween, hS0]
  have hT1 : ∀ x e, (C j + cumBetween C k j) (x + dirVec e) x =
      (c₀ j + ∑ i ∈ Ioo k j, c₀ i) + (δ j + ∑ i ∈ Ioo k j, δ i) := fun x e => by
    rw [Matrix.add_apply, H.hδ j hj, cumBetween, hS1]; ring
  have hT2 : ∀ x e, (C j + cumBetween C k j) x (x + dirVec e) =
      (c₀ j + ∑ i ∈ Ioo k j, c₀ i) + (δ j + ∑ i ∈ Ioo k j, δ i) := fun x e => by
    rw [Matrix.add_apply, H.hδ' j hj, cumBetween, hS2]; ring
  rw [tadInc2, hr, tau2_Vcoup _ _ _ hT0 hT1 hT2,
    tau2_Vcoup (C k) (cumBetween C k j) P.a (c₀ := ∑ i ∈ Ioo k j, c₀ i)
      (δ := ∑ i ∈ Ioo k j, δ i) (by rw [cumBetween]; exact hS0) (by rw [cumBetween]; exact hS1)
      (by rw [cumBetween]; exact hS2), lfunX_add_right]
  ring

/-- **`𝔫^{(2)}_j = ν_j rowS_{C_j} - g_j𝔩_{C_j} + ∑_{k<j} g_k(2dδ_j rowS_{C_k} - 𝔩_{C_k,C_j})`.** -/
theorem frakN2_eq (P : ObsPts d L N) {j : ℕ} (hj : j < n) :
    frakN2 P C V j = (κ j).nu * rowS (C j) P.a - (κ j).g * lfunC (C j) P.a +
      ∑ k ∈ range j, (κ k).g * (2 * d * δ j * rowS (C k) P.a - lfunX (C k) (C j) P.a) := by
  obtain ⟨r, hr⟩ := H.he j hj
  have h0 : bulkE2 C V j = Vcoup (κ j) univ + r • (1 : Alg d L N) := hr
  rw [frakN2, nuBar2, h0]
  have h1 : FC (C j) (pbp P.a) (Vcoup (κ j) univ + r • (1 : Alg d L N)) =
      FC (C j) (pbp P.a + (0 : ℂ) • (1 : Alg d L N)) (Vcoup (κ j) univ + r • (1 : Alg d L N)) := by
    rw [zero_smul, add_zero]
  rw [h1, mass2_FC_pbp_const]
  congr 1
  exact sum_congr rfl fun k hk => H.tadInc2_eq P (mem_range.1 hk) hj

/-- **The exact split of `𝔫^{(2)}_j`**: telescoping `ν` part, bubble increment of the
accumulated covariance, drift terms. -/
theorem frakN2_split (P : ObsPts d L N) {j : ℕ} (hj : j < n) :
    frakN2 P C V j =
      (κ j).nu * (∑ k ∈ range (j + 1), rowS (C k) P.a) -
        ((κ j).nu - 2 * d * (κ j).g * δ j) * (∑ k ∈ range j, rowS (C k) P.a) -
        (κ j).g * (lfunC (∑ k ∈ range (j + 1), C k) P.a - lfunC (∑ k ∈ range j, C k) P.a) -
        2 * d * δ j * ∑ k ∈ range j, ((κ j).g - (κ k).g) * rowS (C k) P.a +
        ∑ k ∈ range j, ((κ j).g - (κ k).g) * lfunX (C k) (C j) P.a := by
  rw [H.frakN2_eq P hj, sum_range_succ, sum_range_succ, lfunC_add, lfunX_sum_left]
  have e1 : ∑ k ∈ range j, (κ k).g * (2 * d * δ j * rowS (C k) P.a - lfunX (C k) (C j) P.a) =
      2 * d * δ j * ∑ k ∈ range j, (κ k).g * rowS (C k) P.a -
        ∑ k ∈ range j, (κ k).g * lfunX (C k) (C j) P.a := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have e2 : ∑ k ∈ range j, ((κ j).g - (κ k).g) * rowS (C k) P.a =
      (κ j).g * ∑ k ∈ range j, rowS (C k) P.a - ∑ k ∈ range j, (κ k).g * rowS (C k) P.a := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have e3 : ∑ k ∈ range j, ((κ j).g - (κ k).g) * lfunX (C k) (C j) P.a =
      (κ j).g * ∑ k ∈ range j, lfunX (C k) (C j) P.a -
        ∑ k ∈ range j, (κ k).g * lfunX (C k) (C j) P.a := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [e1, e2, e3]
  ring

end Bulk2

end

end Obs2
