/-
  Active Geometry: public entry point
  ===================================

  A host does not have one capacity. It has a PROFILE, one entry per class of
  structural obligation the code must honour:

      C(M) = (C_block, C_persistent, C_causal, C_relational, ...)

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
  `Persistent`, `Causal`) live on `Constrained.Code`.

  ## The two axes

  Obligations form a PRODUCT POSET, not a chain. Nothing here orders
  persistence against relational fidelity, and the experiments found them
  independent.

    metric obligations - what of the source's shape the image must preserve
      `Faithful`    cardinality and separation
      `Radial`      the rooted radial budget
      `Relational`  pairwise distances to distortion (D, K)

    online restrictions - how the code is presented in time
      `Persistent`  the past is not discarded
      `Stable`      the past is not rewritten
      `Causal`      per-step motion is bounded

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

  The paper's limsup generalization; Theorem 4.4 (Skenderi / weighted
  relational capacity of `ℍⁿ_κ`); Theorem 7.1 (Heintze isotropy, axiom A3);
  packing entropy = volume entropy under bounded geometry; achievability at any
  rung above `block`; a dynamics toward saturation; occupancy of any host.

  ## Status vocabulary

  Four states, kept distinct everywhere in this library:

    DEFINED       an object exists; nothing is proved about it
                  (`tax`, `availability`, `Relational`, `Causal`, `Separates`)
    LEAN-CHECKED  proved here (`convergent_rate_addressability_limit`,
                  `addressable_of_achievable`, `Achievable.mono`)
    PAPER-PROVED  proved in the manuscript, not here (Theorem 5.3, the balloon)
    OPEN          neither (achievability above the block rung; the
                  transformation laws for `θ`; whether `Separates` is inhabited
                  at any pair of rungs; any natural instantiation)

  A definition is not a computed capacity. A monotonicity lemma is not an
  achievability theory. A paper theorem is not a Lean theorem.

  Above all: no member of the profile beyond the block rung is COMPUTED here.
  The definitions make the profile expressible and the base square makes it
  bounded. Filling in the dictionary - the balloon, `ℍⁿ_κ`, and whatever lies
  between - is the mathematics this file is built to receive.
-/

import ActiveGeometry.Capacity
import ActiveGeometry.Chart
import ActiveGeometry.Constrained
import ActiveGeometry.Packing
import ActiveGeometry.StateEquation
import ActiveGeometry.Measurability

namespace ActiveGeometry

export Packing (convergent_rate_addressability_limit
                logCard_div_radius_le_packingRate)
export Capacity (Addressable achievedRate achievedRate_le not_addressable_of_lt)
export Constrained (packingNumberOn Source Code Obligation Base
                    Represents Achievable Rates capacity Separates
                    addressable_of_achievable tax availability)

end ActiveGeometry
