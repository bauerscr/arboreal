import Loc.EstDefs

/-!
# The `T` norm of the local monomials

`‖M_x‖_{T(h, ℓ)} ≤ ℓ^2 h^{-deg M}`: each field contributes `ℓ` and each derivative `h^{-1}`.
-/

namespace Loc

noncomputable section

open Finset Grassmann FRD

namespace MonoEst

section Generic

variable {X : Type*} [DecidableEq X] [Fintype X] {E : Type*} [Fintype E] [DecidableEq E]
  [AddAction (E → ℕ) X] {p : ℕ} {h ℓ : ℝ}

/-- The generalised derivative `∇^a ψ_u` of a generator. -/
def Dψ (a : E → ℕ) (u : Sf X) : Grassmann.N X :=
  nab (W := Grassmann.N X) (fun _ : Fin 1 => a) (fun z => ψ (z 0)) (fun _ => u)

theorem pair_Dψ (a : E → ℕ) (u : Sf X) (g : TestFn X) :
    pair (Dψ a u) g = nab (fun _ : Fin 1 => a) (g 1) (fun _ => u) := by
  have := nabla_comp_linear (sh (X := X)) (fun _ : Fin 1 => a) ((pairL g).restrictScalars ℝ)
    (fun z => ψ (z 0)) (fun _ => u)
  simp only [LinearMap.coe_restrictScalars] at this
  rw [Dψ, ← show pairL g _ = pair _ g from rfl, ← this]
  have e : (fun z : Fin 1 → Sf X => pairL g (ψ (z 0))) = g 1 := by
    funext z
    show pair (ψ (z 0)) g = g 1 z
    rw [pair_ψ]
    congr 1
    funext i; fin_cases i; rfl
  rw [e]

theorem abs_pair_Dψ_le (hh : 0 < h) (hℓ : 0 < ℓ) {a : E → ℕ} (ha : Grassmann.mabs a ≤ p)
    (u : Sf X) {g : TestFn X} (hg : phiNorm E p h ℓ g ≤ 1) :
    ‖pair (Dψ a u) g‖ ≤ ℓ * (h ^ Grassmann.mabs a)⁻¹ := by
  rw [pair_Dψ]
  have := abs_nab_le hh hℓ zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g) (fun _ => u)
    (fun _ : Fin 1 => a) (fun _ => ha)
  simpa [ord] using this

theorem Dψ_zero (u : Sf X) : Dψ (0 : E → ℕ) u = ψ u := by
  rw [Dψ, show (fun _ : Fin 1 => (0 : E → ℕ)) = 0 from rfl, nabla_zero _ (fun _ => sh_zero _)]

theorem Dψ_one (e : E) (u : Sf X) :
    Dψ (Pi.single e 1 : E → ℕ) u = ψ (sh (Pi.single e 1) u) - ψ u := by
  rw [Dψ, show (fun _ : Fin 1 => (Pi.single e 1 : E → ℕ)) = Pi.single 0 (Pi.single e 1) by
    funext i; fin_cases i; rfl, nabla_single _ (fun _ => sh_zero _) sh_add]
  simp [ediff]

theorem Dψ_two (e e' : E) (u : Sf X) :
    Dψ (Pi.single e 1 + Pi.single e' 1 : E → ℕ) u =
      ψ (sh (Pi.single e' 1) (sh (Pi.single e 1) u)) - ψ (sh (Pi.single e 1) u)
        - ψ (sh (Pi.single e' 1) u) + ψ u := by
  rw [Dψ, show (fun _ : Fin 1 => (Pi.single e 1 + Pi.single e' 1 : E → ℕ)) =
      Pi.single 0 (Pi.single e 1) + Pi.single 0 (Pi.single e' 1) by
    funext i; fin_cases i; rfl, nabla_succ _ sh_add, nabla_single _ (fun _ => sh_zero _) sh_add]
  simp [ediff]
  abel

theorem abs_pair_le_of_tNorm_le (hh : 0 < h) (hℓ : 0 < ℓ) {F : Grassmann.N X} {c : ℝ}
    (hc : 0 ≤ c) (hF : tNorm E p h ℓ F ≤ ENNReal.ofReal c) {g : TestFn X}
    (hg : phiNorm E p h ℓ g ≤ 1) : ‖pair F g‖ ≤ c := by
  have := abs_pair_le hh hℓ F zero_le_one (by rwa [ENNReal.ofReal_one]) (g := g)
  rw [mul_one] at this
  exact this.trans (ENNReal.toReal_le_of_le_ofReal hc hF)

theorem pair_sub' (F G : Grassmann.N X) (g : TestFn X) : pair (F - G) g = pair F g - pair G g :=
  map_sub (pairL g) F G

theorem pair_neg' (F : Grassmann.N X) (g : TestFn X) : pair (-F) g = -pair F g :=
  map_neg (pairL g) F

theorem norm_half_sub_le {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖(1 / 2 : ℂ) * (a - b)‖ ≤ M := by
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  linarith [norm_sub_le a b]

theorem norm_half_add_le {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖(1 / 2 : ℂ) * (a + b)‖ ≤ M := by
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  linarith [norm_add_le a b]

theorem norm_quarter_le {a b c e : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M)
    (he : ‖e‖ ≤ M) : ‖(1 / 4 : ℂ) * (a - b - c + e)‖ ≤ M := by
  rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
  linarith [norm_add_le (a - b - c) e, norm_sub_le (a - b) c, norm_sub_le a b]

end Generic

variable {d L N : ℕ} [NeZero L] {p : ℕ} {h ℓ : ℝ}

theorem sh_single_T (e : Dir d) (x : Lam d L N) (σ : ℤˣ) :
    sh (Pi.single e 1 : Dir d → ℕ) ((x, σ) : Sf (Lam d L N)) = (x + dirVec e, σ) := by
  simp [sh, single_vadd]

theorem Dψ_one_T (e : Dir d) (x : Lam d L N) (σ : ℤˣ) :
    Dψ (Pi.single e 1 : Dir d → ℕ) ((x, σ) : Sf (Lam d L N)) = ψ (x + dirVec e, σ) - ψ (x, σ) := by
  rw [Dψ_one, sh_single_T]

theorem Dψ_two_T (e e' : Dir d) (x : Lam d L N) (σ : ℤˣ) :
    Dψ (Pi.single e 1 + Pi.single e' 1 : Dir d → ℕ) ((x, σ) : Sf (Lam d L N)) =
      ψ (x + dirVec e + dirVec e', σ) - ψ (x + dirVec e, σ) - ψ (x + dirVec e', σ) + ψ (x, σ) := by
  rw [Dψ_two, sh_single_T, sh_single_T, sh_single_T]

theorem prj_zero' : (prj (0 : Zd d) : Lam d L N) = 0 := by
  have := prj_add (n := L ^ N) (0 : Zd d) 0
  simpa using this

theorem prj_ez (i : Fin d) : (prj (ez i) : Lam d L N) = dirVec (Sum.inl i) :=
  prj_dirZ (Sum.inl i)

theorem prj_negez (i : Fin d) : (prj (-ez i) : Lam d L N) = dirVec (Sum.inr i) :=
  prj_dirZ (Sum.inr i)

theorem dirVec_inl_add_inr (i : Fin d) :
    (dirVec (Sum.inl i) : Lam d L N) + dirVec (Sum.inr i) = 0 :=
  add_neg_cancel (G := Fin d → ZMod (L ^ N)) _

theorem mabs_two (e e' : Dir d) :
    Grassmann.mabs (Pi.single e 1 + Pi.single e' 1 : Dir d → ℕ) = 2 := by
  rw [mabs_add, mabs_single, mabs_single]

/-- A 1-d stencil applied to the generators of spin `σ` at `x`. -/
def ψS (s : St1 d) (σ : ℤˣ) (x : Lam d L N) : Alg d L N :=
  (s.map fun q => (q.1 : ℂ) • ψ (x + prj q.2, σ)).sum

/-- The pairing bound for a 1-d stencil of order `k`. -/
def Good (p : ℕ) (h ℓ : ℝ) (s : St1 d) (k : ℕ) : Prop :=
  ∀ (σ : ℤˣ) (x : Lam d L N) (g : TestFn (Lam d L N)), phiNorm (Dir d) p h ℓ g ≤ 1 →
    ‖pair (ψS s σ x) g‖ ≤ ℓ * (h ^ k)⁻¹

theorem ψS_id1 (σ : ℤˣ) (x : Lam d L N) :
    ψS id1 σ x = Dψ (0 : Dir d → ℕ) ((x, σ) : Sf (Lam d L N)) := by
  simp [ψS, id1, prj_zero', Dψ_zero]

theorem ψS_dpt (i : Fin d) (σ : ℤˣ) (x : Lam d L N) :
    ψS (dpt i) σ x = (1 / 2 : ℂ) • (Dψ (Pi.single (Sum.inl i) 1 : Dir d → ℕ) ((x, σ) : Sf _) -
      Dψ (Pi.single (Sum.inr i) 1 : Dir d → ℕ) ((x, σ) : Sf _)) := by
  simp only [ψS, dpt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prj_ez,
    prj_negez, Dψ_one_T]
  push_cast
  module

theorem ψS_lap1 (i : Fin d) (σ : ℤˣ) (x : Lam d L N) :
    ψS (lap1 i) σ x =
      -Dψ (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 : Dir d → ℕ) ((x, σ) : Sf _) := by
  rw [Dψ_two_T, add_assoc x, dirVec_inl_add_inr, add_zero]
  simp only [ψS, lap1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prj_ez,
    prj_negez, prj_zero', add_zero]
  push_cast
  module

theorem ψS_fw_pos (i : Fin d) (σ : ℤˣ) (x : Lam d L N) :
    ψS (fw (ez i)) σ x = Dψ (Pi.single (Sum.inl i) 1 : Dir d → ℕ) ((x, σ) : Sf _) := by
  simp only [ψS, fw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prj_ez,
    prj_zero', add_zero, Dψ_one_T]
  push_cast
  module

theorem ψS_fw_neg (i : Fin d) (σ : ℤˣ) (x : Lam d L N) :
    ψS (fw (-ez i)) σ x = Dψ (Pi.single (Sum.inr i) 1 : Dir d → ℕ) ((x, σ) : Sf _) := by
  simp only [ψS, fw, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, prj_negez,
    prj_zero', add_zero, Dψ_one_T]
  push_cast
  module

theorem ψS_conv (i k : Fin d) (σ : ℤˣ) (x : Lam d L N) :
    ψS (conv (dpt i) (dpt k)) σ x = (1 / 4 : ℂ) •
      (Dψ (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1 : Dir d → ℕ) ((x, σ) : Sf _) -
       Dψ (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr k) 1 : Dir d → ℕ) ((x, σ) : Sf _) -
       Dψ (Pi.single (Sum.inr i) 1 + Pi.single (Sum.inl k) 1 : Dir d → ℕ) ((x, σ) : Sf _) +
       Dψ (Pi.single (Sum.inr i) 1 + Pi.single (Sum.inr k) 1 : Dir d → ℕ) ((x, σ) : Sf _)) := by
  simp only [ψS, conv, dpt, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, prj_add,
    prj_ez, prj_negez, Dψ_two_T, ← add_assoc]
  push_cast
  module

variable (hp : 2 ≤ p) (hh : 0 < h) (hℓ : 0 < ℓ)
include hp hh hℓ

theorem good_id1 : Good (d := d) (L := L) (N := N) p h ℓ id1 0 := by
  intro σ x g hg
  rw [ψS_id1]
  simpa [Grassmann.mabs] using abs_pair_Dψ_le (p := p) hh hℓ (a := (0 : Dir d → ℕ))
    (by simp [Grassmann.mabs]) _ hg

theorem good_dpt (i : Fin d) : Good (d := d) (L := L) (N := N) p h ℓ (dpt i) 1 := by
  intro σ x g hg
  have h1 := abs_pair_Dψ_le hh hℓ (by rw [mabs_single]; omega) ((x, σ) : Sf _) hg
    (a := (Pi.single (Sum.inl i) 1 : Dir d → ℕ))
  have h2 := abs_pair_Dψ_le hh hℓ (by rw [mabs_single]; omega) ((x, σ) : Sf _) hg
    (a := (Pi.single (Sum.inr i) 1 : Dir d → ℕ))
  rw [mabs_single] at h1 h2
  rw [ψS_dpt, pair_smul, pair_sub']
  exact norm_half_sub_le h1 h2

theorem good_fw_pos (i : Fin d) : Good (d := d) (L := L) (N := N) p h ℓ (fw (ez i)) 1 := by
  intro σ x g hg
  rw [ψS_fw_pos]
  simpa [mabs_single] using abs_pair_Dψ_le hh hℓ (by rw [mabs_single]; omega) ((x, σ) : Sf _) hg
    (a := (Pi.single (Sum.inl i) 1 : Dir d → ℕ))

theorem good_fw_neg (i : Fin d) : Good (d := d) (L := L) (N := N) p h ℓ (fw (-ez i)) 1 := by
  intro σ x g hg
  rw [ψS_fw_neg]
  simpa [mabs_single] using abs_pair_Dψ_le hh hℓ (by rw [mabs_single]; omega) ((x, σ) : Sf _) hg
    (a := (Pi.single (Sum.inr i) 1 : Dir d → ℕ))

theorem good_lap1 (i : Fin d) : Good (d := d) (L := L) (N := N) p h ℓ (lap1 i) 2 := by
  intro σ x g hg
  rw [ψS_lap1, pair_neg', norm_neg]
  have := abs_pair_Dψ_le hh hℓ (by rw [mabs_two]; omega) ((x, σ) : Sf _) hg
    (a := (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 : Dir d → ℕ))
  rwa [mabs_two] at this

theorem good_conv (i k : Fin d) : Good (d := d) (L := L) (N := N) p h ℓ (conv (dpt i) (dpt k)) 2 := by
  intro σ x g hg
  have H : ∀ e e' : Dir d, ‖pair (Dψ (Pi.single e 1 + Pi.single e' 1 : Dir d → ℕ)
      ((x, σ) : Sf (Lam d L N))) g‖ ≤ ℓ * (h ^ 2)⁻¹ := fun e e' => by
    have := abs_pair_Dψ_le hh hℓ (by rw [mabs_two]; omega) ((x, σ) : Sf _) hg
      (a := (Pi.single e 1 + Pi.single e' 1 : Dir d → ℕ))
    rwa [mabs_two] at this
  rw [ψS_conv, pair_smul, pair_add, pair_sub', pair_sub']
  exact norm_quarter_le (H _ _) (H _ _) (H _ _) (H _ _)

theorem good_Dsym (s : Sym2 (Fin d)) : Good (d := d) (L := L) (N := N) p h ℓ (Dsym s) 2 := by
  induction s using Sym2.ind with
  | h i k =>
    simp only [Dsym, Sym2.lift_mk, Dik]
    split_ifs
    · exact good_lap1 hp hh hℓ _
    · exact good_conv hp hh hℓ _ _

omit hp in
theorem tNorm_ψS_le {s : St1 d} {k : ℕ} (hs : Good (d := d) (L := L) (N := N) p h ℓ s k)
    (σ : ℤˣ) (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (ψS s σ x) ≤ ENNReal.ofReal (ℓ * (h ^ k)⁻¹) :=
  tNorm_le fun g hg => hs σ x g hg

omit hp in
theorem tNorm_ψS_mul_le {s t : St1 d} {k k' : ℕ} (hs : Good (d := d) (L := L) (N := N) p h ℓ s k)
    (ht : Good (d := d) (L := L) (N := N) p h ℓ t k') (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (ψS s 1 x * ψS t (-1) x) ≤ ENNReal.ofReal (ℓ ^ 2 * (h ^ (k + k'))⁻¹) := by
  refine (tNorm_mul_le hh hℓ _ _).trans ?_
  refine (mul_le_mul' (tNorm_ψS_le hh hℓ hs 1 x) (tNorm_ψS_le hh hℓ ht (-1) x)).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), pow_add, mul_inv]
  exact le_of_eq (congrArg _ (by ring))

omit hp hh hℓ in
theorem sum_tens_aux (f g : Zd d → Alg d L N) (c : ℝ) (u : Zd d) (t : St1 d) :
    ((t.map fun q => (c * q.1, u, q.2)).map fun q => (q.1 : ℂ) • (f q.2.1 * g q.2.2)).sum =
      (c : ℂ) • f u * (t.map fun q => (q.1 : ℂ) • g q.2).sum := by
  induction t with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Complex.ofReal_mul] at ih ⊢
    rw [ih, mul_smul, smul_mul_smul_comm, mul_smul]

omit hp hh hℓ in
theorem sum_tens (f g : Zd d → Alg d L N) (s t : St1 d) :
    ((tens s t).map fun q => (q.1 : ℂ) • (f q.2.1 * g q.2.2)).sum =
      (s.map fun q => (q.1 : ℂ) • f q.2).sum * (t.map fun q => (q.1 : ℂ) • g q.2).sum := by
  induction s with
  | nil => simp [tens]
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, add_mul, ← ih, ← sum_tens_aux f g a.1 a.2 t]
    simp only [tens, List.flatMap_cons, List.map_append, List.sum_append]

omit hp hh hℓ in
theorem monoAt_tens {M : Mono d} {s t : St1 d} (hM : stencil M = tens s t) (x : Lam d L N) :
    monoAt M x = ψS s 1 x * ψS t (-1) x := by
  rw [monoAt, hM]
  exact sum_tens (fun a => psi (x + prj a)) (fun b => psibar (x + prj b)) s t

omit hp hh hℓ in
theorem sum_sc (F : Zd d × Zd d → Alg d L N) (r : ℝ) (m : St d) :
    ((sc r m).map fun q => (q.1 : ℂ) • F q.2).sum =
      (r : ℂ) • (m.map fun q => (q.1 : ℂ) • F q.2).sum := by
  induction m with
  | nil => simp [sc]
  | cons a m ih =>
    simp only [sc, List.map_cons, List.sum_cons, smul_add, Complex.ofReal_mul, mul_smul] at ih ⊢
    rw [ih]

theorem tNorm_monoAt_le' (M : Mono d) (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (monoAt M x) ≤ ENNReal.ofReal (ℓ ^ 2 * (h ^ M.deg)⁻¹) := by
  cases M with
  | c => rw [monoAt_tens rfl]; exact tNorm_ψS_mul_le hh hℓ (good_id1 hp hh hℓ) (good_id1 hp hh hℓ) x
  | a1 i =>
    rw [monoAt_tens rfl]; exact tNorm_ψS_mul_le hh hℓ (good_dpt hp hh hℓ i) (good_id1 hp hh hℓ) x
  | b1 i =>
    rw [monoAt_tens rfl]; exact tNorm_ψS_mul_le hh hℓ (good_id1 hp hh hℓ) (good_dpt hp hh hℓ i) x
  | a2 s =>
    rw [monoAt_tens rfl]; exact tNorm_ψS_mul_le hh hℓ (good_Dsym hp hh hℓ s) (good_id1 hp hh hℓ) x
  | b2 s =>
    rw [monoAt_tens rfl]; exact tNorm_ψS_mul_le hh hℓ (good_id1 hp hh hℓ) (good_Dsym hp hh hℓ s) x
  | m2 i k =>
    by_cases hik : i = k
    · subst hik
      have hst : monoAt (Mono.m2 i i) x = ((1 / 2 : ℝ) : ℂ) •
          (ψS (fw (ez i)) 1 x * ψS (fw (ez i)) (-1) x +
            ψS (fw (-ez i)) 1 x * ψS (fw (-ez i)) (-1) x) := by
        rw [monoAt, stencil, if_pos rfl]
        rw [sum_sc (fun q => psi (x + prj q.1) * psibar (x + prj q.2)), List.map_append,
          List.sum_append]
        congr 2
        · exact sum_tens (fun a => psi (x + prj a))
            (fun b => psibar (x + prj b)) _ _
        · exact sum_tens (fun a => psi (x + prj a))
            (fun b => psibar (x + prj b)) _ _
      rw [hst]
      refine tNorm_le fun g hg => ?_
      have h1 := abs_pair_le_of_tNorm_le hh hℓ (by positivity)
        (tNorm_ψS_mul_le hh hℓ (good_fw_pos hp hh hℓ i) (good_fw_pos hp hh hℓ i) x) hg
      have h2 := abs_pair_le_of_tNorm_le hh hℓ (by positivity)
        (tNorm_ψS_mul_le hh hℓ (good_fw_neg hp hh hℓ i) (good_fw_neg hp hh hℓ i) x) hg
      rw [pair_smul, pair_add, show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring]
      exact norm_half_add_le h1 h2
    · rw [monoAt_tens (s := dpt i) (t := dpt k) (by simp [stencil, hik])]
      exact tNorm_ψS_mul_le hh hℓ (good_dpt hp hh hℓ i) (good_dpt hp hh hℓ k) x

end MonoEst

variable {d L N : ℕ} [NeZero L]

open MonoEst in
theorem tNorm_monoAt_le {p : ℕ} (hp : 2 ≤ p) {h ℓ : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (M : Mono d)
    (x : Lam d L N) :
    tNorm (Dir d) p h ℓ (monoAt M x) ≤ ENNReal.ofReal (ℓ ^ 2 * (h ^ M.deg)⁻¹) :=
  tNorm_monoAt_le' hp hh hℓ M x

end

end Loc
