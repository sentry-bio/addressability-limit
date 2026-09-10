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

The PDFs' source-reproducibility and numbering status is recorded in
[`paper/README.md`](paper/README.md).

The result is a *limit principle* — an inequality nothing beats, with an
idealized equality case — in the lineage of the second law, Carnot, and Shannon.
A host has at least two capacities: how many histories it can tell apart, and
how many of their relations it can preserve. The Structured Addressability
Limit is

$$\beta \le C_{\mathcal A} \le C_{\mathrm{block}} = c\, h_{\mathrm{pack}},$$

under depthwise recoding at the block rung. The gap between the two capacities
can be total. Read the packing bound as a trichotomy: a process that keeps its
history occupies exponential room, or its address radius outruns any finite
rate, or it forgets.

## The Lean kernel

Lean 4 + Mathlib, zero `sorry`/`admit`; the only trusted axioms are Lean's
standard `propext`, `Classical.choice`, `Quot.sound`.

```bash
cd theory/lean
lake exe cache get
lake build
```

### What the Lean certifies, and where it sits in the paper

| Lean declaration | Certifies |
|---|---|
| `Packing.convergent_rate_addressability_limit` | the **addressability bound** $\beta\le c\,h_{\mathrm{pack}}$ (ordinary-limit case) |
| `Packing.logCard_div_radius_le_packingRate` | the **directly measurable** finite-depth form $\log N(R)/r(R)\le\log P(B(o,r(R)),\varepsilon)/r(R)$ |
| `Packing.exists_optimal_blockCode`, `Packing.card_le_packingCount` | exact **finite-radius** block codes; independent codebooks, no nestedness |
| `Constrained.capacity_block_eq_packing` | constructive **asymptotic** block identity $C_{\mathrm{block}}=c\,h_{\mathrm{pack}}$ under depthwise recoding |
| `Constrained.structured_addressability_limit_self` | the Structured Addressability Limit with that constructed endpoint |
| `Constrained.Source.ULF`, `geometricSource_ulf` | finite-rate generation; the canonical relational source class |
| `Packing.subball_fraction_le_packing_fraction` | the finite sub-ball count behind the **radial-concentration** theorem |
| `Constrained.packingNumberOn` | constrained packing, for **intrinsic host-side** obligations |
| `Constrained.Source`, `Code`, `Obligation` | the three separated objects of the **capacity profile** |
| `Constrained.Represents`, `Achievable` | fixed-source representability vs. host capacity over a declared family |
| `Constrained.addressable_of_achievable` | the **base square**: every rung, over every family, obeys the bound |
| `Constrained.Rates_bddAbove` | capacity is a **set** first; boundedness follows from the base square |
| `Constrained.Rates_isometry_eq` | exact profile transport under isometric host equivalence |
| `Constrained.capacity_eq_packing_of_endpoint_achievable` | converse plus an explicit endpoint construction gives exact capacity |
| `Constrained.unit_separates_block_from_malformed_causal` | a strict profile sanity witness, not the geometric balloon |
| `Constrained.balloon_separates` | geometric block-versus-relational gap on the ULF binary tree of Theorem 5.3's source class |
| `Constrained.vacuity_without_base`, `unit_host_only_zero` | why base feasibility is compulsory, on one host, both directions |
| `Capacity.achievedRate_le` | the bound in rate form, $\lambda=\beta/c\le h_{\mathrm{cap}}$ |
| `Capacity.efficiency_le_one` | the efficiency bound $\eta=\beta/(c\,h_{\mathrm{pack}})\le 1$ |
| `Capacity.minimizer_on_Iic_eq_capacity` | conditional boundary selection under an independently supplied decreasing cost |
| `Chart.curvature_at_least_floor`, `Chart.saturated_curvature_eq_floor` | the **curvature floor** under a space-form identification (optional chart) |
| `Chart.normalized_curvature_scale_invariant`, `Chart.process_time_gauge` | gauge invariance of $\bar\kappa=c^2\kappa$ |
| `Chart.StateEquation.normalized_state_equation` | the **state equation** as the *saturated + isotropic* equality case |
| `Chart.StateEquation.rateMismatchSq_zero_iff` | the mismatch is positive-definite with a unique zero — a gap diagnostic, **not** a Lyapunov theorem |
| `Measurability.*` | the growth-class gate's finite-sample refusal rule — an *instrument*, not a theorem of the paper |

A host, relative to a basepoint, resolution, source family, and radial rate,
has a **profile**, one entry per class of structural obligation a code must
honour. `Constrained` makes that profile
expressible and bounds every entry by $c\,h_{\mathrm{pack}}$; it computes the
block rung by depthwise recoding. `balloon_separates` is a Lean-checked
geometric gap: the same ULF binary tree is block-achievable in the balloon and
not relationally representable there. Everything space-form lives behind the
optional `Chart` namespace.

`CapacitySaturated` and `Chart.hcap_eq_spaceForm` are **separate predicates**:
the Lean *derives* the state equation from them; it never assumes them. Build details and
declaration notes: [`theory/lean/README.md`](theory/lean/README.md). The
claim-by-claim evidence ledger is [`STATUS.md`](STATUS.md).

### What the Lean does *not* check (paper-level results)

- The paper's full *limsup* addressability bound (Lean checks the convergent-rate corollary).
- Achievability at the relational rung of a named homogeneous host; Theorem 5.3
  remains paper-level. The balloon's geometric separation against the ULF
  binary tree is Lean-checked.
- Homogeneous positivity (`C_{\mathrm{rel}}>0`) and homogeneous zero tax.
  Tessera–Cornulier and Kerr support positivity, not equality; Skenderi is the
  rank-one equality case (Theorem 5.3).
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
