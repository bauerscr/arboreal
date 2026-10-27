import Flow2

/-! Audit of the `Flow2` package (`h02uv-outline.tex`, Proposition `prop:fh-flow`). -/

#check @Flow2.fh_flow
#check @Flow2.exists_admissible
#check @Flow2.admissible_unique
#check @Flow2.ginv_admissible
#check @Flow2.ginv_sum
#check @Flow2.continuousOn_muc
#check @Flow2.continuousOn_gN
#check @Flow2.shooting
#check @Flow2.eps0_pos
#check @Flow2.a0_pos

#print axioms Flow2.fh_flow
#print axioms Flow2.ginv_sum
#print axioms Flow2.shooting

#check @Flow2.w_uniform          -- Corollary `cor:W-uniform`
#print axioms Flow2.w_uniform

#check @Flow2.Hist.fh_flow_hist  -- Proposition `prop:C6` (history-dependent flow)
#print axioms Flow2.Hist.fh_flow_hist
#print axioms Flow2.Hist.shooting
#check @Flow2.Hist.F3_of_rg
#check @Flow2.Hist.LT_of_rg
#check @Flow2.Hist.hhyp_of_rg
#check @Flow2.Hist.flow_of_rg
#print axioms Flow2.Hist.flow_of_rg
#check @Flow2.Hist.flow_of_rg2     -- separate constants for (Kb)/(Yb) and (KL)/(YL)
#print axioms Flow2.Hist.flow_of_rg2
#check @Flow2.Hist.continuousOn_muc_param   -- joint continuity of μ₀^c in (parameter, b)
#check @Flow2.Hist.continuousOn_traj_param  -- joint continuity of all couplings
#print axioms Flow2.Hist.continuousOn_muc_param
#print axioms Flow2.Hist.continuousOn_traj_param
#check @Flow2.Hist.exists_eq_of_continuousOn_Ioc  -- generic IVT on (0, b₁]
#check @Flow2.Hist.gN_surj                  -- every value in (0, ǧ_N(b_max)] is attained
#check @Flow2.Hist.exists_gN_eq_inv         -- shooting: ǧ_N(b) = 1/β_R for β_R ≥ 1/ǧ_N(b_max)
#print axioms Flow2.Hist.gN_surj
#print axioms Flow2.Hist.exists_gN_eq_inv
#check @Flow2.Hist.MonoHyp                  -- difference form of (LG) + fading memory
#check @Flow2.Hist.traj_strict_mono
#check @Flow2.Hist.strictMonoOn_of_admissible
#check @Flow2.Hist.gN_strictMonoOn          -- `thm:flow`(ii) abstract: ǧ_N strictly increasing
#check @Flow2.Hist.monoCoef_of_small        -- the numerical conditions hold for small a
#print axioms Flow2.Hist.gN_strictMonoOn
#print axioms Flow2.Hist.monoCoef_of_small
#check @Flow2.hasDerivAt_implicit           -- 1-d implicit function lemma (expansion instead of C¹)
#check @Flow2.Hist.HDiff                    -- differentiability of G, m, T on the open domain
#check @Flow2.Hist.traj_diffAt              -- the trajectory is differentiable in (b, μ₀)
#check @Flow2.Hist.differentiableAt_muc
#check @Flow2.Hist.fh_flow_hist_diff        -- `thm:flow`(iii) abstract: μ₀^c, ǧ_N, s_j differentiable
#print axioms Flow2.hasDerivAt_implicit
#print axioms Flow2.Hist.fh_flow_hist_diff
#check @Flow2.Hist.fh_flow_histK     -- `prop:C6` on any set of `b` keeping all clamped flows in `D_ε`
#check @Flow2.Hist.trajc_InDhS       -- a priori bound of the sharp range: `1/g_i ≥ 1/b - Φ_i`
#check @Flow2.Hist.keepD_of_bmaxS
#check @Flow2.Hist.fh_flow_range     -- the flow on `(0, b_maxS]`, final couplings `≥ ginvS` attained
#check @Flow2.Hist.ginv_log          -- `|1/ǧ_n - 1/b + βn| ≤ 2(1+β)E + (5C/β) log(ǧ_n/b)`
#print axioms Flow2.Hist.fh_flow_histK
#print axioms Flow2.Hist.fh_flow_range
#print axioms Flow2.Hist.ginv_log
#check @Flow2.Hist.cone_signed       -- signed cone: μ' ≤ μ ⇒ μ - μ' ≤ μ_N - μ'_N
#check @Flow2.Hist.local_adm         -- local continuation of the admissible μ₀ in b
#check @Flow2.Hist.exists_traj_eq    -- every ǧ_N = y ∈ (0, ε] is attained (no range of b)
#check @Flow2.Hist.fh_flow_fixedR    -- shooting at fixed β_R ≥ 1/ε, with MonoHyp
#print axioms Flow2.Hist.exists_traj_eq
#print axioms Flow2.Hist.fh_flow_fixedR
#check @Flow2.Hist.admissible_unique_z  -- uniqueness with a separate channel for a hidden coupling
#check @Flow2.Hist.fh_flow_hist_u       -- prop:C6 from HHyp (any (A, a)) and a uniqueness statement
#print axioms Flow2.Hist.admissible_unique_z
#print axioms Flow2.Hist.fh_flow_hist_u
#check @Flow2.Hist.fh_flow_fixedR_diff   -- differentiability in b on Ufix (thm:flow (iii))
#check @Flow2.Hist.local_adm_param       -- parametric local continuation of the admissible μ₀
#check @Flow2.Hist.continuousOn_bsh      -- joint continuity of the shooting solution (p, y) ↦ b
#check @Flow2.Hist.fh_flow_final         -- consolidated abstract theorem (FixedConcl)
#check @Flow2.Hist.fh_flow_final_param   -- parametric conclusions (ParamConcl)
#print axioms Flow2.Hist.fh_flow_fixedR_diff
#print axioms Flow2.Hist.fh_flow_final
#print axioms Flow2.Hist.fh_flow_final_param
#check @Flow2.Hist.cone_signed_z         -- signed cone with a hidden ζ-channel (ZHyp)
#check @Flow2.Hist.traj_strict_mono_z    -- strict monotonicity with a hidden ζ-channel (MonoZHyp)
#check @Flow2.Hist.monoZCoef_of_small    -- MonoZCoef for small a
#check @Flow2.Hist.fh_flow_final_g       -- FixedConcl from ConeS + strict monotonicity (any HHyp constants)
#check @Flow2.Hist.fh_flow_final_param_g -- ParamConcl, generic form
#print axioms Flow2.Hist.cone_signed_z
#print axioms Flow2.Hist.traj_strict_mono_z
#print axioms Flow2.Hist.monoZCoef_of_small
#print axioms Flow2.Hist.fh_flow_final_g
#check @Flow2.exists_eq_of_perturb
#check @Flow2.Hist.traj_cone_top_z
