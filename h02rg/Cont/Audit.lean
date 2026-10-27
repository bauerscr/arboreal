import Cont

/-!
# Audit of the `Cont` library (B1: continuum torus objects)

Zero-mode-free Green function of `-Δ` on `𝕋² = UnitAddTorus (Fin 2)` (heat-kernel definition via
Mathlib's `cosKernel`) and the zero-mode-free lattice Green function on `Torus d n`.

Run with `lake env lean Cont/Audit.lean` (after `lake build Cont`). Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

-- continuum torus Green function
#check @Cont.torusGreen
#check @Cont.torusGreen_eq_heat
#print axioms Cont.torusGreen_integrableOn
#print axioms Cont.torusGreen_continuousAt
#print axioms Cont.torusGreen_continuousOn
#print axioms Cont.torusGreen_neg
#print axioms Cont.torusGreen_perm
#print axioms Cont.torusGreen_swap
#print axioms Cont.torusGreen_reflect
#print axioms Cont.torusGreen_sub_comm
#print axioms Cont.torusGreen_log_singularity
#print axioms Cont.torusGreen_proj_log
#print axioms Cont.torusGreen_eq_heat

-- heat kernel ingredients
#print axioms Cont.b1_cosK_eq_evenK
#print axioms Cont.b1_torusHeat_large
#print axioms Cont.b1_torusHeat_small
#print axioms Cont.b1_tendsto_sing_add_log

-- lattice zero-mode-free Green function
#check @Cont.latGreen
#print axioms Cont.negLap_mul_latGreenMat
#print axioms Cont.latGreenMat_mul_latQ
#print axioms Cont.sum_latGreen
#print axioms Cont.latGreen_neg
#print axioms Cont.latGreenMat_symm

-- lattice heat kernel (B1 scaling limit)
#check @Cont.latHeat
#print axioms Cont.latHeat_add
#print axioms Cont.latHeat_nonneg
#print axioms Cont.latHeat_le_zero
#print axioms Cont.sum_latHeat_mul_char
#print axioms Cont.sum_lam_mul_latHeat_le
#print axioms Cont.lam_mul_latHeat_add_le
#print axioms Cont.latHeat_zero_le
#print axioms Cont.lam_mul_latHeat_le

-- Fourier series of the torus heat kernel, splitting of G_𝕋
#print axioms Cont.b1c_hasSum_heat
#print axioms Cont.b1c_integral_large
#print axioms Cont.b1c_torusGreen_split
#print axioms Cont.b1c_abs_small_cont_le

-- scaling limit of the lattice Green function
#check @Cont.latPt
#check @Cont.latPtN
#print axioms Cont.b1c_lat_decomp
#print axioms Cont.b1c_abs_small_lat_le
#print axioms Cont.b1c_Tn_eq
#print axioms Cont.b1c_tsum_D_tendsto
#print axioms Cont.b1c_abs_Tn_sub_le
#check @Cont.latGreen_latPt_uniform
#print axioms Cont.latGreen_latPt_uniform
#check @Cont.latGreen_latPtN_tendstoUniformlyOn
#print axioms Cont.latGreen_latPtN_tendstoUniformlyOn

-- asymptotic Arzelà–Ascoli (T7)
#print axioms Cont.ascoli_asymp_finite_net
#print axioms Cont.ascoli_asymp_totallyBounded
#print axioms Cont.ascoli_asymp_uniformContinuous_of_tendstoUniformly
#check @Cont.ascoli_asymp_exists_subseq
#print axioms Cont.ascoli_asymp_exists_subseq
#check @Cont.ascoli_asymp_exists_subseq_exhaust
#print axioms Cont.ascoli_asymp_exists_subseq_exhaust
#check @Cont.ascoli_asymp_exists_subseq_punctured
#print axioms Cont.ascoli_asymp_exists_subseq_punctured
#check @Cont.ascoli_asymp_exists_subseq_torus
#print axioms Cont.ascoli_asymp_exists_subseq_torus
#print axioms Cont.ascoli_asymp_limit_eq_of_tendsto_sub
#print axioms Cont.ascoli_asymp_limit_invariant
#print axioms Cont.ascoli_asymp_limit_abs_sub_le

-- lattice points as torus points, signed permutations (`Cont/LatEmb`)
#print axioms Cont.latPt_latEmb
#print axioms Cont.dist_latEmb_latPt_le
#print axioms Cont.norm_latEmb_le
#print axioms Cont.norm_le_supNorm_latPt
#print axioms Cont.abs_zabs_latPt_sub_le
#print axioms Cont.norm_clSgn
#print axioms Cont.dist_clSgn
#print axioms Cont.ascoli_asymp_exists_subseq_on
#print axioms Cont.ascoli_asymp_exists_subseq_annulus
