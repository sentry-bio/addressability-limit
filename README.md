# The Addressability Limit

A process that retains distinguishable histories cannot outgrow the room its
representation gives it to keep them apart:

$$\beta \le c\, h_{\mathrm{pack}}.$$

This repository is the **machine-checked companion** to the manuscript
*The Addressability Limit: A Geometric Capacity Bound for Information-Generating
Hierarchies* (Fenn & Fenn). It holds the manuscript and its expository overview
(`paper/`) and the Lean 4 kernel that certifies the algebraic and finite-radius
core (`theory/lean/`). **The manuscript is the source of truth; this README maps
the Lean to it.**

## The paper

- [`paper/addressability-limit.pdf`](paper/addressability-limit.pdf) — the
  manuscript: full proofs, `math.MG` / `math.GR`.
- [`paper/addressability-limit-overview.pdf`](paper/addressability-limit-overview.pdf)
  — a five-page expository companion: the whole argument in one pass, with the
  kernel of each proof, no formal proofs.

The result is a *limit principle* — an inequality nothing beats, with an
idealized equality case — in the lineage of the second law, Carnot, and Shannon.
Read as a trichotomy: a process that keeps its history occupies exponential
room, or its address radius outruns any finite rate, or it forgets.

## The Lean kernel

Lean 4 + Mathlib, zero `sorry`/`admit`; the only trusted axioms are Lean's
standard `propext`, `Classical.choice`, `Quot.sound`.

```bash
cd theory/lean
lake build
```

### What the Lean certifies, and where it sits in the paper

| Lean declaration | Certifies |
|---|---|
| `Packing.convergent_rate_addressability_limit` | the **addressability bound** $\beta\le c\,h_{\mathrm{pack}}$ (ordinary-limit case) |
| `Packing.logCard_div_radius_le_packingRate` | the **directly measurable** finite-depth form $\log N(R)/r(R)\le\log P(B(o,r(R)),\varepsilon)/r(R)$ |
| `Packing.exists_optimal_blockCode`, `Packing.card_le_packingCount` | the exact **block identity** $C_{\mathrm{block}}=c\,h_{\mathrm{pack}}$ (finite radius) |
| `Packing.subball_fraction_le_packing_fraction` | the finite sub-ball count behind the **radial-concentration** theorem |
| `Constrained.packingNumberOn` | constrained packing, for **intrinsic host-side** obligations |
| `Constrained.Source`, `Code`, `Obligation` | the three separated objects of the **capacity profile** |
| `Constrained.Represents`, `Achievable` | fixed-source representability vs. host capacity over a declared family |
| `Constrained.addressable_of_achievable` | the **base square**: every rung, over every family, obeys the bound |
| `Constrained.Rates_bddAbove` | capacity is a **set** first; boundedness follows from the base square |
| `Constrained.vacuity_without_base`, `unit_host_only_zero` | why base feasibility is compulsory, on one host, both directions |
| `Capacity.achievedRate_le` | the bound in rate form, $\lambda=\beta/c\le h_{\mathrm{cap}}$ |
| `Capacity.efficiency_le_one` | the efficiency bound $\eta=\beta/(c\,h_{\mathrm{pack}})\le 1$ |
| `Chart.curvature_at_least_floor`, `Chart.saturated_curvature_eq_floor` | the **curvature floor** under a space-form identification (optional chart) |
| `Chart.normalized_curvature_scale_invariant`, `Chart.process_time_gauge` | gauge invariance of $\bar\kappa=c^2\kappa$ |
| `Chart.StateEquation.normalized_state_equation` | the **state equation** as the *saturated + isotropic* equality case |
| `Chart.StateEquation.rateMismatchSq_zero_iff` | the mismatch is positive-definite with a unique zero — a gap diagnostic, **not** a Lyapunov theorem |
| `Measurability.*` | the growth-class gate's finite-sample refusal rule — an *instrument*, not a theorem of the paper |

A host does not have one capacity but a **profile**, one entry per class of
structural obligation a code must honour. `Constrained` makes that profile
expressible and bounds every entry by $c\,h_{\mathrm{pack}}$; it computes no
entry beyond the block rung, and proves no separation between two rungs.
Everything space-form lives behind the optional `Chart` namespace.

`CapacitySaturated` and `Chart.hcap_eq_spaceForm` are **separate predicates**:
the Lean *derives* the state equation from them; it never assumes them. Build details and
declaration notes: [`theory/lean/README.md`](theory/lean/README.md).

### What the Lean does *not* check (paper-level results)

- The paper's full *limsup* addressability bound (Lean checks the convergent-rate corollary).
- Achievability at any rung above the block one; no profile entry beyond
  $C_{\mathrm{block}}$ is computed, and no separation between rungs is proved.
- Transformation laws for capacity under quasi-isometry, and therefore whether a
  bare $\theta(M)=C_{\mathcal A}/C_{\mathrm{block}}$ is a licensed notation.
- The relational capacity theorem in $\mathbb{H}^n_\kappa$ (uses Skenderi 2026).
- The Heintze/Schur isotropy under Assumption A3.
- That any system occupies or saturates the host; any alphabet or DNA entropy ceiling.

Isotropy is an asserted premise, never a measurement. $n=2$ is an embeddability
floor for genuinely branching trees, not a fitted constant.

## Scope

This repository is the mathematics only, and no biological claim appears in it.
The biology instantiation — *Evolution as Active Geometry*, the reference
encoder, and the experiment registry — lives in the companion repository
[sentry-bio/active-geometry](https://github.com/sentry-bio/active-geometry),
which imports this paper's bound, ladder, and chart and re-derives none of them.

## License

MIT. See [`LICENSE`](LICENSE).
