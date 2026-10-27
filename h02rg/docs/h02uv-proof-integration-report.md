# Integration report for `h02uv-proof.tex` (2026-10-24)

Master: `/home/roland/math/h02-lean/h02uv-proof.tex`; sections in `/home/roland/math/h02-lean/sections/`.
PDF: `/home/roland/math/h02-lean/h02uv-proof.pdf`, **162 pages**, 11,403 lines of section source
(plus 215 lines master). Compile from `/home/roland/math/h02-lean`:
`pdflatex` (nonstopmode, halt-on-error) → `bibtex` (BIBINPUTS=/home/roland/math/h02-lean:) → `pdflatex` ×2:
exit 0, **0 undefined references/citations, 0 multiply-defined labels, 0 overfull boxes > 20pt**
(30 overfull boxes ≤ 20pt remain; 1 bibtex warning "empty journal in 1910.13564", pre-existing).
Nothing was committed or `git add`ed.

## 1. Cross-section consistency: decisions and edits

Global notation decisions (made where two sections disagreed):

| Item | Decision | Files touched |
|---|---|---|
| gradient couplings $z,y$ | $z$ multiplies the gradient square, $y$ the Laplacian term (the convention of §6 and of O); remark on the interchange relative to R (3.35) | `sec-grassmann` (`e:V-def` swapped, remark added), `sec-pt` (`e:kappa-first` → $(z-gC'(0,0),y-g\delta,\nu+2dg\delta,g)$) |
| field scale / Gram scale | $\ell=4\ell_C$, Gram scale $\ell_{j+1}/4$ (T4's `e:causal-scale`) | `sec-grassmann` (§4.2 twice), `sec-flow` (Step 2 of `thm:flow`), `sec-obs` ($\ell_{C,j}=\frac14\ell|Z_{j+1}|^{-1/2}$) |
| flow coordinates | normalised by $Z_{j+1}$ (`e:flow-coords`) | `sec-flow` §8.1 definition and Step 3 of `thm:flow` |
| universal differences | $\fB(w'_j+C'_{j+1})-\fB(w'_j)$, $\fl(\cdot)$ likewise, $F_{w'_j+C'_{j+1}}$ (exact `e:Cw`) | `sec-flow` (`e:gflow`, `e:flow-univ`, §8.1 text), `sec-est` (`prop:F1`(iii) proof), `sec-obs` (`e:obs-flow` text) |
| $a_k$ | $L^{-2k}+m^2L^{2(k+1)}$, $a_0=1$ everywhere (already consistent; `lem:corr-gamint` error form simplified to $K_0a_k$) | `sec-corr` |
| zero-mode names | $\cE_j$, $\hat\cE_j(0)$ (T2) | `sec-corr` (`lem:corr-dress`, `prop:suscept` proof, `prop:h0-window` proof) |
| dressing coupling | $a_j=\zeta_jZ_j$ in §6 and §10 ($z_j$ only inside §3) | `sec-corr` (all `det(1+a_jA\Gamma_j)`, `c_j=a_jm^2`, shift lemma application) |
| $M_0$, $M_2$ | new `lem:pt-zeromode` (§5.4) states and proves $|Z_{j+1}w^{(1)}_j|\le M_0L^{2j}$, $|\delta_j|\le M_2L^{-2(j+1)}$; `prop:F1`(ii), `prop:last-bounds`(iv), `prop:Z` now cite it | `sec-pt`, `sec-est`, `sec-flow` |
| per-step band | `rem:macro0` uses `e:beta-step` in the form $K_ba_i+C_{\rm gu}/\beta_i$ | `sec-reduction` |
| `lem:bracket` hypotheses | $g_0\le\epsilon_0/4$ and $100C_b\le\beta_R$ stated after `thm:rg-main`; folded in `lem:bracket-h0` | `sec-reduction` |
| `e:kappa-first` | `prop:C2`(i) now literally equals `e:kappa-first` (after the $z/y$ fix) | — |
| constant-name clashes in §11 | $K_c\to K_{\rm cdd}$, $K_e\to K_{\rm env}$, $K_A\to K_{\rm top}$, $K_2\to K_{ab}$, $K_p\to K_{\rm gr}$, $K_Z$ (in $K_T$) $\to K_{T0}$; $K_g$ defined from `e:beta-step`; $c_W,c_\delta,B,c=c_R$ identified with the constants of §9 in `prop:restart`; $c_J,c_u,K_4,K_O,K_M$ identified with §10/§9 in `prop:T5`; $(1+K_M\gcheck)\to(1+K_M'\gcheck)$ | `sec-cont` |
| `lem:corr-massflow` | now a corollary of `e:est-nu-last` (`prop:last-bounds`(iii)) | `sec-corr` |
| proof of `thm:rg-main` | removed references to §11 constants $K_A$, $K_p$; generic description of the mass windows | `sec-corr` |

Provided-statement checks (all verified in the text): `thm:rg-main`(ii) monotonicity ← `prop:beta-asym`(i);
`e:beta-scale` clean form ← `prop:beta-asym`(iii) `e:flow-betascale`; `prop:window-flow` form used in §10.5
(θ=¾c_μ, 2pθ≤1/8) matches §8.4; `prop:last-bounds`(iii)/(v) and `e:atilde` match `e:corr-utilde`, `prop:h0-window`;
`prop:lip-flow` at $j=N-2$ is stated and used in `thm:flow` Step 5; `prop:case2` is stated for every vertex
position; `lem:coal` for $j\le j_{ab}$ is what §10.3 uses.

Statements added because §11 relied on them:
* `prop:step-obs`(iv) (sec-obs): the **linear form** of the observable $K$-step
  ($\|K_{j+1}(U)_a\|\le(\theta_0+C_1'\bar g)\|K_a\|+C_1'(\bar g^2\|V_a\|+\bar g\|\cW_a\|)$ without smallness of the
  observable sizes), with a proof paragraph (nilpotency ⇒ linearity, λ-trick one input at a time, Cauchy).
  `prop:restart` now cites it. **Authors should check this proof paragraph.**
* `lem:corr-gamtop` (sec-corr) extended by the bound $|\gamma_{a,N-1}-\vartheta_{N_h}|\le K_O\vartheta_{N_h}\gcheck_{N_h}$
  (previously only inside the proof of `prop:top`); `prop:top` and `prop:cases` cite it.
* §11's other dependencies on §10.4 (reduced history, $n_{ab}$ split, Pauli elimination, far-point bounds, last-step
  defect) are stated in §10.4 (`e:corr-reduced`, `e:corr-pauli-elim`, `prop:zbelow`(iii), `e:corr-last-c2`, `e:corr-jets`).

`e:waiting` is in §11.4 (plan said §11.5) and `e:K2`/`e:Kout` in §6.2(D) (plan said §7.1); all references point to the
right places, so nothing was moved.

## 2. Citations of `h02rg` (`\cite{BCH24}`)
`h02rg.tex` was compiled once in the scratchpad to obtain its aux file; **all** numbers used in the paper were mapped to
R's labels (≈75 distinct citations), not only 15. Every one agrees with plan §5.4 (Thm 3.13 = `thm:step`,
Prop 3.11 = `prop:ZVK`, Prop 3.8 = `prop:Loc`, Thm 3.24 = `thm:flow`, (3.34) = `e:normcontract`, (3.31) doubling,
(3.44) $Q$, (3.72) linear part, (3.93) choice of $A$, (3.78) block cancellation, (5.24)–(5.25), Prop 4.1/4.2,
Lemma 5.13, Prop 5.6, Def 5.1, Def 5.7, (5.21), (3.71), Lemmas 3.15–3.23, Props 3.14/3.19/3.21, (3.90)–(3.98),
(3.3), (3.7), (3.10), (3.26), (3.30), (3.32)–(3.33), (3.40), Defs 3.1–3.3, 3.5, (1.13), (1.16)–(1.18), (1.28),
(2.3), (2.4), (2.11)–(2.15), Prop A.1, Lemma 5.3, (5.3), (5.6), (5.9), (5.37), Props 6.1–6.2, Lemma 2.6, Cor 2.2,
Prop 1.4, Thm 1.5, (B.1), and the section numbers 1.1, 1.2, 2, 2.2, 3.1–3.9, 3.8.1–3.8.5, 4, 5.1, 5.5, 6, App. B).
No corrections were needed.

## 3. Open items / Lean text
Exactly one list of open points: `rem:main`(ii)–(iii) (§1.1). `rem:macro0` (§2.4), the remark after `prop:top`
(§10.4), the remark after `prop:h0-window` (§10.5), `rem:flow-smooth` (§8.2) and the closing remark of §11 only
state what a particular statement does not claim and point to `rem:main` where relevant. `grep` for
`texttt|Lean|status|outline|Expected|F-<digit>` in the body: no hits outside the one sentence of §1.3 and Appendix B.

## 4. Source corrections
Collected in `/home/roland/.claude/jobs/f52f9c7e/tmp/paper/source_corrections.md` (26 items with O/R/F locations).

## 5. Length / duplicated prose
No proofs were cut. Each section's opening paragraph states what is as in R and what is new (all present).
The strategy appears once in §1.3; §11.1 has its own plan (needed, different content). Nothing removed.

## 6. Front matter
Title and abstract as in `h02uv.tex`/plan, three authors with addresses (from `h02rg`), `\tableofcontents`
present. The abstract was moved before `\maketitle` (amsart requirement; removed the class warning).
An `Acknowledgements` placeholder section was added before the appendices (`h02rg` has one; text to be supplied).
Appendix B: every Lean name in `tab:lean` and in the text was checked against the Lean sources
(`grep` for the declaration); all exist (`fx_clEqui` is `MasterFacts.fx_clEqui` in `H02UV/Spin2/Cont/ContFx5b.lean`,
as listed). `H02UV/Audit.lean` (then `Audit/H02UV.lean`) itself `#check`s 32 declarations; the table lists more (library-internal) names,
which is consistent with the appendix text ("the entry point ... lists the main statements").

## 7. Per-file change summary
* `h02uv-proof.tex`: abstract before `\maketitle`; Acknowledgements placeholder.
* `sec-intro.tex`: unchanged.
* `sec-reduction.tex`: `rem:macro0` band in the `e:beta-step` form; $100C_b\le\beta_R$ added to the discussion of $g_0$.
* `sec-frd.tex`, `app-frd.tex`: unchanged.
* `sec-grassmann.tex`: `e:V-def` ($z$ on the gradient square) + remark; $\ell=4\ell_C$, Gram scale $\ell_{j+1}/4$; one display rebroken.
* `sec-pt.tex`: `e:kappa-first` corrected to the $z/y$ convention; new `lem:pt-zeromode`; one item rephrased (overfull).
* `sec-rgmap.tex`: two displays rebroken (`e:rg-QJ`, `e:rawstep`).
* `sec-est.tex`: `prop:F1`(ii), `prop:last-bounds`(iv) cite `lem:pt-zeromode`; universal differences in `prop:F1`(iii); displays rebroken.
* `sec-flow.tex`: coordinates normalised by $Z_{j+1}$; `e:gflow`/`e:flow-univ` with $w'_j+C'_{j+1}$; Gram scale $/4$; $M_0$ in `prop:Z`.
* `sec-obs.tex`: `e:obs-flow` universal difference; Gram scale constant; new `prop:step-obs`(iv) with proof; pointer after `e:kobs-step`.
* `sec-corr.tex`: dressing coupling $a_j$; zero-mode names $\hat\cE_j$; `lem:corr-massflow` ← `e:est-nu-last`; `lem:corr-gamtop` extended (+$K_O$); `prop:top` cites it; `lem:corr-gamint` error form; proof of `thm:rg-main` without §11 constants; 9 displays rebroken.
* `sec-cont.tex`: constant renames (see table); `prop:restart`/`prop:T5` constants identified with §9/§10; cites `prop:step-obs`(iv) and `lem:corr-gamtop`; $K_g$ from `e:beta-step`.
* `app-lean.tex`: unchanged (names verified).

## 8. Remaining weak spots (for the authors' review)
Proof sketches and mechanism-level arguments, by section:
1. **§5.4** `lem:lattice-radial`(i): numerical constants "obtained by keeping track of the factors π"; `lem:bubble-density`: the finite Wick sum behind `e:pt-bubble-momentum` is described, not displayed (computer-algebra check mentioned in `rem:universal`).
2. **§7.2** `lem:est-crude`: proof by reference to R §§3.8.3–3.8.5 with the replacements (U1)–(U4) (cite-and-list form, as the style sheet allows, but the list of changes is terse).
3. **§7.5** `prop:F1`(i): the exact expansion is derived by expanding $(1+n_{j+1})/(1+n_j)$; `prop:lip-flow`: the Cauchy estimate "one variable $\zeta_k$ at a time" with the radius enlarged by $2^{j-k}$ is argued, not computed; the dependence on $u_j$ through the field scales is stated at mechanism level.
4. **§8.2** `rem:flow-zeta` (hidden ζ-channel): the proofs of `prop:C6`, `prop:sharp-range`, `prop:fixedR` are said to go through "verbatim with adjusted cone constants"; the cone constants for (M) are a "routine computation" with an indicated choice.
5. **§8.3** `thm:flow` Step 5: the constants $b_\mu,b_W$ of the last-step monotonicity are asserted as $O_L(1)$.
6. **§9.2** `prop:step-obs`(iv) (new, written by the integrator): linear form of the observable $K$-step; the proof is a paragraph (nilpotency ⇒ linearity; λ-trick per input; Cauchy estimates). **Check.**
7. **§9.4** `prop:rel` Step 2 (product parts, Pauli Lipschitz bound `e:pauli-lip`): the cut-off of the Gram representation and the conversion of field scales are described, not estimated line by line; the constants of `e:kobs-rec` ($B$, $\bar\theta$) are asserted.
8. **§9.5** `prop:case2`(iii) (horizon step): crude bound on $\fn^{(2)}_{N_h}$ with constants asserted.
9. **§10.4** `lem:corr-pairsizes`(ii)–(iii) and `e:corr-jets`: structured argument with mechanisms and named constants but not every intermediate estimate (flagged by the writer as the least detailed part); the Gronwall step in (iv) gives an explicit but unverified constant $X$. `prop:top`: $E$ is bounded "exactly as in the proof of `prop:pair-above`".
10. **§10.5** `e:corr-slack` ($5(c_{\nu,{\rm last}}+2)+5L^2\le3L^4c_\mu$) asserted for $L\ge L_0$ via $c_{\nu,{\rm last}}=O(L^2)$.
11. **§11.2** relaxed coalescence invariant for the relocated state: justified in prose after `lem:rerep` (margin $2(4+2^d)\le L$), not as a lemma.
12. **§11.3** `prop:restart`: mechanism-level reproduction of the outline's sketch (rates $6^{-1}$, $8/15$, $7/30$, $56/75$, the constant 1344, $|\fn^F|\le\frac17$, $K_{\rm env}$, $E_{N_h}$); `lem:restart-data`: the share-deviation bound of the two reference histories is quoted from `prop:rel` with an $L$-dependent constant.
13. **§11.4** `prop:T5`: the one-point bound $|n_a(Y_{N_h+1})|$ for a general state is argued "exactly as in the pair case" (by analogy); the sizes $v_T,w_T,k_{xT}$ at the top are given by explicit but unverified expressions; `lem:cont-aconst` backwards recursion uses `prop:zbelow` "for a general state".
14. **§11.5/11.6** the closing remark quotes $g(r)\asymp\Theta(r)^{-2}$, $\mu(r)\asymp\exp(-C\Theta(r)^2)$ (descriptive only).
15. **App. A.3** `lem:tail`: saddle-point asymptotics of $\hat g_0$ sketched (used only for the positivity statement `thm:dressed`(vii), not for `thm:main`).
16. **§2.3/§10.6**: the constants $K,K_c$ of `thm:rg-main` are assembled from several sections; `prop:short` enlarges $K_c$ "without changing notation" (explicit, but the reader must track it).

## 9. Not done / notes
* The 30 overfull boxes ≤ 20pt were left (within the stated tolerance).
* `\providecommand{\fc}{\mathfrak c}` sits at the top of `sec-pt.tex`; could be moved to the master preamble.
* `pdftitle`/`pdfauthor` in `\hypersetup` are empty (as in `h02rg.tex`).
