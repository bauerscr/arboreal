module

public import ArborealDecay.Annulus.RootChange
public import ArborealDecay.Annulus.Integr
public import ArborealDecay.Annulus.MMatrix
public import ArborealDecay.Annulus.MapW
public import ArborealDecay.Annulus.Bridge
public import ArborealDecay.Annulus.CondId
public import ArborealDecay.Annulus.Energy
public import ArborealDecay.Annulus.Restrict
public import ArborealDecay.Annulus.Wired
public import ArborealDecay.Annulus.Moment
public import ArborealDecay.Annulus.Main

/-!
# The wired annulus (supplement `thm:annulus`), conditional on (A) and (C)

Aggregator for `ArborealDecay/Annulus/*`. The two BCHS identities enter only as explicit
hypotheses of the `_of_inputs` theorems, stated for the `TLaw` definitions at `a = 3/2`, for
every finite weighted graph with connected support and every root:

* (A) `Z w ρ (3/2) = ENNReal.ofReal (H02.Zforest w _)`;
* (C) `expect w ρ (3/2) (fun τ => (Hmat w ρ (ext ρ τ))⁻¹ i j) =
  H02.arborealProb w _ (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ)`.

Results:

* `B_of_inputs` (`thm:B`, from (A) at two roots and `prop:root-change`),
  `Zmono_of_inputs` (`cor:Zmon`), `H1_of_inputs`;
* `conductance_identity_of_inputs` (note `prop:conductance-identity`, from (C));
* `annulus_of_inputs` (note `prop:annulus` via supplement `thm:annulus`, from (A), (C)).
-/
