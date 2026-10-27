module

public import ArborealDecay.CondComb.Edge
public import ArborealDecay.CondComb.Main
public import ArborealDecay.CondComb.Conn
public import ArborealDecay.CondComb.Zc

/-!
# Combinatorial half of `prop:conductance-identity`

Aggregator.  With `Γ = G/(a=b)` (`gammaW β a b = mapW β (collapse {a, b})`, `ρ = none`):

* `Zd_eq_ZGamma` (`eq:Zd-ZGamma`): `Z_d = Z_Γ`;
* `Zc_eq`, `Zc_div_ZGamma`: `Z_c / Z_Γ = w_ab + ∑_{i,j ∈ I} w_ai w_jb P_Γ(i ↔ j, i ↮ ρ)`;
* `Zc_div_Zd`, `tau_le_Zc_div_Zd`, `tau_lt_one`: `Z_c/Z_d = τ/(1-τ)`, `τ ≤ Z_c/Z_d`, `τ < 1`.
-/
