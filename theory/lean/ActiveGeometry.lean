/-
  Active Geometry: public entry point
  ===================================

  Relative to a basepoint, resolution, source family, and radial rate, a host
  has a PROFILE, one entry per class of structural obligation the code must
  honour:

      C(M) = (C_block, C_relational)

  The Structured Addressability Limit is the chain

      β ≤ C_𝒜 ≤ C_block = c · h_pack

  under depthwise recoding at the block rung. Nested, causal, or relational
  achievability is a strictly stronger demand. The gap between the two
  capacities can be total (the balloon, Lean-checked against a ULF tree) or
  vanish (ℍⁿ_κ, Theorem 5.3).

  Two hosts can hold the same number of distinguishable states and differ
  completely in their ability to preserve ancestry, refinement, or metric
  relations. The scalar question "how much information fits?" is replaced by

      how much history fits, while retaining a specified amount of its shape?

  ## The spine

      Addressable  ->  achievedRate  ->  feasibility  ->  tax

  `Capacity.Addressable β c hcap` is `β ≤ c · hcap`. Dividing by the gauge `c`
  puts both sides in the same units, nats per unit radius:

      Capacity.achievedRate β c = β / c  ≤  hcap.

  `Constrained.packingNumberOn` is the primitive for INTRINSIC, host-side
  obligations: Mathlib's `packingNumber` with one further indexed supremum, so
  only codebooks meeting an admissibility predicate compete. Everything
  previously proved is the unconstrained case. It is *not* the primitive of the
  whole profile - obligations referring to a labelled source (`Relational`,
  `Stable`, `Causal`) live on source-code pairs.

  ## The two orderings

  Obligations are ordered by implication, while source families are ordered by
  inclusion. These orderings are independent: strengthening what a code must
  honour and narrowing which sources compete are different operations.

    metric obligations - what of the source's shape the image must preserve
      `Faithful`    cardinality and separation
      `Radial`      the rooted radial budget
      `Relational`  pairwise distances to distortion (D, K)

    online restrictions - how the code is presented in time
      `Stable`      the past is not rewritten
      `Causal`      per-step motion is bounded

    source restriction
      `Retentive`   the source census does not discard its past
      `ULF`         finite-rate generation; the relational source class

  ## Three objects, kept apart

  `Constrained` separates what an earlier version conflated:

      `Source`      the growing census of histories - owns its filtration
      `Code`        addresses and a radial budget, and nothing else
      `Obligation`  a predicate on a (source, code) PAIR

  and therefore separates two different questions:

      `Represents o ε 𝒜 σ c`     can THIS source be held here? - what an
                                  experiment tests
      `Achievable o ε 𝔖 𝒜 β c`   what rates does the host support over a
                                  DECLARED family `𝔖`? - what a theorem
                                  classifies

  Retention is a property of the SOURCE (`Source.Retentive`), not an obligation
  on the code: no choice of address map makes a census accrete. It enters a
  capacity claim by restricting `𝔖`.

  `Constrained.Base` is compulsory inside both; an obligation argument carries
  only ADDITIONAL requirements. Without it a rate is not a statement about the
  host at all - `Constrained.vacuity_without_base` exhibits a ONE-POINT host
  reporting `log 2` nats per step once base feasibility is dropped, and is kept
  as a regression test.

  `Achievable.mono_obligation` and `Achievable.mono_family` are the ladder's two
  orderings. `Constrained.addressable_of_achievable` is the base square that
  makes them bite - every rung, over every family, whatever it additionally
  honours, obeys the packing converse `β ≤ c · h_pack`. That theorem is what
  connects this module to `Packing` rather than merely importing it.

  Capacity is a SET before it is a number: `Rates` is the achievable-rate set,
  `Rates_bddAbove` is boundedness from the base square, and the scalar
  `capacity` is derived - with every dependency explicit.

  ## Citation

  `Packing.convergent_rate_addressability_limit` - the ordinary-limit corollary
  of the paper's Addressability Limit, in every proper metric host.

  `Packing.logCard_div_radius_le_packingRate` - the directly measurable form,
  `log N(R)/r(R) ≤ log P(B(o,r(R)),ε)/r(R)`. This is what a measurement
  computes; the asymptotic version discards an additive constant, which is why
  an achieved rate may exceed `h_pack` at finite radius without violating
  anything.

  ## What is optional

  `Chart` and `Chart.StateEquation` convert `h_pack` into geometers' units
  under an assumed space-form identification. Nothing in `Capacity`, `Packing`
  or `Constrained` depends on them. `hcap_eq_spaceForm` is a predicate, assumed
  where used, never derived.

  ## Not formalized

  The paper's limsup generalization; Theorem 5.3 (Skenderi / weighted
  relational capacity of `ℍⁿ_κ`); Proposition 6.2 (Heintze isotropy, axiom A3);
  packing entropy = volume entropy under bounded geometry; homogeneous
  positivity/zero-tax; a dynamics toward saturation; occupancy of any host.

  ## Status vocabulary

  Four states, kept distinct everywhere in this library:

    DEFINED       an object exists; nothing is proved about it
                  (`tax`, `availability`, `Relational`, `Causal`)
    LEAN-CHECKED  proved here (`convergent_rate_addressability_limit`,
                  `addressable_of_achievable`,
                  `Achievable.mono_obligation`, `Achievable.mono_family`,
                  `balloon_separates`)
    PAPER-PROVED  proved in the manuscript, not here (Theorem 5.3)
    OPEN          neither (relational achievability of homogeneous hosts;
                  homogeneous positivity vs zero tax; any natural instantiation)

  A definition is not a computed capacity. A monotonicity lemma is not an
  achievability theory. A paper theorem is not a Lean theorem.

  Above all: the block rung is computed asymptotically by depthwise recoding.
  The balloon is Lean-checked against the ULF binary tree of Theorem 5.3's
  source class: block coding fits, lawful quasi-isometric coding does not.
  No relational profile entry for a named homogeneous host is computed here.
  `ℍⁿ_κ` remains a paper theorem; homogeneity is an open program, not a lemma.
-/

import ActiveGeometry.Capacity
import ActiveGeometry.Chart
import ActiveGeometry.Constrained
import ActiveGeometry.Balloon
import ActiveGeometry.ProfileExamples
import ActiveGeometry.Packing
import ActiveGeometry.Structured
import ActiveGeometry.StateEquation
import ActiveGeometry.Measurability

namespace ActiveGeometry

export Packing (convergent_rate_addressability_limit
                logCard_div_radius_le_packingRate)
export Capacity (Addressable achievedRate achievedRate_le not_addressable_of_lt)
export Constrained (packingNumberOn Source Code Obligation Base
                    Represents Achievable Rates capacity Separates
                    addressable_of_achievable tax availability
                    unit_separates_block_from_malformed_causal
                    capacity_block_eq_packing
                    structured_addressability_limit
                    structured_addressability_limit_self
                    balloon_separates
                    binaryTree_block_achievable
                    binaryTree_not_relational)

end ActiveGeometry
