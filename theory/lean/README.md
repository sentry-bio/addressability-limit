# Formal proofs in Lean 4

This directory machine-checks the addressability bound, the constrained-capacity
framework that generalises it, and the algebra downstream of both. The complete
statements and proofs are in the manuscript,
[`../../paper/addressability-limit.pdf`](../../paper/addressability-limit.pdf).

Lean 4 + Mathlib, no `sorry` or `admit`, no custom axioms. Every declaration
depends on exactly Lean's `propext`, `Classical.choice`, `Quot.sound` — anything
touching `ℝ` inherits all three from Mathlib's construction of the reals, so
this is the floor rather than a signal.

```bash
cd theory/lean
lake exe cache get
lake build
```

## The statement to cite

`ActiveGeometry.Packing.convergent_rate_addressability_limit` — in every proper
metric host, a finite source census with an injective, fixed-resolution
separated address map, radii tending to infinity, and convergent history growth
`β`, radial rate `c`, and packing growth `h_pack`, satisfies

$$\beta \le c\,h_{\mathrm{pack}}.$$

It is the ordinary-limit corollary of the paper's limsup Addressability Limit.

For measurement, cite `Packing.logCard_div_radius_le_packingRate` instead:

$$\frac{\log N(R)}{r(R)} \;\le\; \frac{\log P(B(o,r(R)),\varepsilon)}{r(R)}.$$

This is what a measurement computes. The asymptotic version discards an
additive constant, which is why an achieved rate can exceed `h_pack` at finite
radius without violating anything.

## A host has a profile, not a capacity

The organising idea of `Constrained.lean`. Two hosts can hold the same number of
distinguishable states and differ completely in their ability to preserve
ancestry, refinement, or metric relations. So the scalar question *how much
information fits?* is replaced by

> how much history fits, while retaining a specified amount of its shape?

Three objects are kept apart, because conflating them makes the first of the two
questions below unstatable:

| object | owns |
|---|---|
| `Source` | the growing census of histories, and its own filtration |
| `Code` | addresses and a radial budget, and nothing else |
| `Obligation` | a predicate on a (source, code) **pair** |

which separates:

| | question | who asks it |
|---|---|---|
| `Represents o ε 𝒜 σ c` | can **this** source be held here? | an experiment |
| `Achievable o ε 𝔖 𝒜 β c` | what rates does the host support over a **declared** family `𝔖`? | a theorem |

Obligations form a **product poset**, not a chain. Nothing orders retention
against relational fidelity.

- *metric obligations* — what of the source's shape must survive:
  `Faithful` (cardinality and separation), `Radial` (the rooted budget),
  `Relational` (pairwise distances to distortion `(D,K)`).
- *online obligations* — how the code is presented in time: `Stable` (the past
  is not rewritten), `Causal` (per-step motion is bounded).
- *retention* is **not** an obligation. Whether a census accretes is settled by
  the source; no address map changes it. It is `Source.Retentive`, and it
  enters a capacity claim by restricting `𝔖`.

## Base feasibility is compulsory

`Code.radius` is a free field, unrelated to where `addr` actually puts anything.
Without base feasibility a code may map every history to a single point and
still declare radii growing at rate `c`. Two theorems on the same one-point host
pin this down, and both live in the file so neither can rot:

| declaration | says |
|---|---|
| `vacuity_without_base` | the rate conditions **alone** report `log 2` nats per generative step in `Unit` |
| `unit_host_only_zero` | with `Base` in force the same host admits **only** `0`, since faithful addressing into one point forces singleton censuses |

## Declarations

### `Packing.lean` — the metric kernel

| declaration | meaning |
|---|---|
| `card_le_packingCount` | every finite separated subset of a ball is bounded by its exact packing number |
| `exists_optimal_blockCode` | an exact finite packing code exists whenever the ball packing number is finite |
| `hasFinitePacking_of_properSpace` | in any proper metric space, finiteness is a theorem, not a hypothesis |
| `subball_fraction_le_packing_fraction` | the finite sub-ball count behind radial concentration |
| `history_card_le_packingCount` | faithfully addressed histories obey the packing bound at every depth |
| `logCard_div_radius_le_packingRate` | the directly measurable finite-depth form |
| `convergent_rate_addressability_limit` | the bound, with finiteness discharged in a proper host |

### `Constrained.lean` — the capacity profile

| declaration | meaning |
|---|---|
| `packingNumberOn` | Mathlib's `packingNumber` with one further indexed supremum; the primitive for **intrinsic, host-side** obligations only |
| `packingNumberOn_unconstrained` | the unconstrained case is exactly Mathlib's |
| `Source` / `Code` / `Obligation` | the three separated objects |
| `Represents` / `Achievable` | fixed-source representability, and host capacity over a declared family |
| `Achievable.mono_obligation` | more obligation, fewer achievable rates |
| `Achievable.mono_family` | a larger family cannot achieve less |
| `addressable_of_achievable` | **the base square**: every rung, over every family, obeys `β ≤ c·h_pack` |
| `Rates` / `Rates_bddAbove` | capacity as a **set**, and its boundedness from the base square |
| `capacity` | the scalar, derived afterwards, with every dependency explicit |
| `not_achievable_pos_of_hpack_zero` | the trichotomy's third horn, at every rung and any radial rate |
| `Separates` | the **target** of a separation theorem — inhabited nowhere |

Capacity is a set before it is a number. Defining the scalar first invites
`sSup` of an unbounded real set, which silently returns `0`.

### `Capacity.lean` — scalar algebra of the bound

| declaration | meaning |
|---|---|
| `Addressable` | `β ≤ c · h_cap` |
| `achievedRate` | `λ = β / c`; both sides of the bound in the same units, `c` demoted to a gauge |
| `achievedRate_le` | the bound as `λ ≤ h_cap` |
| `not_addressable_of_lt` | the contrapositive — the empirically observable content |
| `efficiency_le_one` | `η = β/(c·h_cap) ≤ 1` |
| `addressability_forces_positive_entropy` | `β>0`, `c>0` imply `h_cap>0` |

### `Chart.lean` — the space-form chart (optional)

`h_pack` is a rate in nats per unit radius. This file converts it into
geometers' units, and that is all it does. If — and only if — one assumes the
host is isotropic and a space form, that rate is `(n-1)√κ`. The conversion
imposes no constraint and discovers nothing about the host; the gauge lemmas are
the unit-consistency conditions of a dictionary entry.

Nothing in `Capacity`, `Packing` or `Constrained` depends on this file.
`hcap_eq_spaceForm` is a **predicate**, assumed where used, never derived.
`Chart.StateEquation` holds the equality-case face and its gap diagnostics,
which are not a Lyapunov theorem and not an evolution law.

### `Measurability.lean` — growth-class instrument

Elementary identities behind the finite-sample growth-class gate:
`midpoint_exponent_eq`, `spanInformation_eq_logGap_logMean`,
`logGapDeriv_logMean`, `spanInformation_pos`. An instrument, not a theory layer.
Hellinger distance, Le Cam's lemma, and the Poisson-increment model are not
formalized.

## Status vocabulary

Used throughout, and worth keeping distinct:

- **defined** — an object exists; nothing is proved about it. `tax`,
  `availability`, `Relational`, `Causal`, `Separates`.
- **Lean-checked** — proved here. `convergent_rate_addressability_limit`,
  `addressable_of_achievable`, `Rates_bddAbove`, the two one-point witnesses.
- **paper-proved** — proved in the manuscript, not here. Theorem 5.3, the
  balloon, Theorem 7.1.
- **open** — neither.

A definition is not a computed capacity. A monotonicity lemma is not an
achievability theory. A paper theorem is not a Lean theorem.

## What this library does not establish

1. the full limsup generalization of the convergent-rate packing theorem;
2. achievability at **any** rung above the block one — no member of the profile
   beyond `C_block` is computed here;
3. whether `Separates` is inhabited at any pair of rungs;
4. transformation laws for `capacity` under quasi-isometry, and therefore
   whether a bare `θ(M)` is a licensed notation at all — exponential growth
   rates at fixed `ε` are not expected to be quasi-isometry invariants;
5. equivalence of packing and volume entropy under bounded geometry;
6. the space-form classification or the hyperbolic volume formula;
7. Theorem 4.4 (Skenderi / weighted relational capacity of ℍⁿ_κ);
8. Theorem 7.1 (Heintze isotropy / axiom A3);
9. the Buneman/Gromov tree-classification theorems, or Sarkar's embedding;
10. a physical dynamics toward capacity saturation;
11. empirical membership of any biological or linguistic system;
12. alphabet or DNA entropy-rate ceilings — substrate constants, not the kernel.

These are respectively paper proofs, classical cited results, open modeling
choices, or empirical questions.

## Tree dimension

The four-point condition classifies exact tree metrics. Minimal smooth ambient
dimension `n = 2` comes from embeddability: a genuinely branching tree cannot
live faithfully in a connected one-dimensional Riemannian manifold, while finite
trees admit arbitrarily low-distortion embeddings in ℍ². The Lean theorem that
normalized curvature decreases with `n` is algebraic monotonicity, not a proof
that an objective selects `n = 2`.
