# Theorem and evidence status

This ledger prevents definitions, formal theorems, manuscript proofs, classical
inputs, and empirical claims from being cited as though they had the same
evidential status.

The debut theorem is the Structured Addressability Limit:

```
β ≤ C_𝒜 ≤ C_block = c · h_pack
```

under depthwise recoding at the block rung. The first inequality is the packing
converse. The second is obligation monotonicity. The equality is constructive
asymptotic block coding. The gap between `C_rel` and `C_block` can be total
(the balloon) or vanish (`ℍⁿ_κ`).

## Lean-checked in this repository

- The finite packing converse and exact finite block code:
  `Packing.card_le_packingCount`, `Packing.exists_optimal_blockCode`,
  `Packing.one_le_packingCount`.
- The finite-depth measurable inequality:
  `Packing.logCard_div_radius_le_packingRate`.
- The ordinary-limit addressability bound:
  `Packing.convergent_rate_addressability_limit`.
- Constructive asymptotic block exactness, by depthwise recoding:
  `Constrained.achievable_block_packing`,
  `Constrained.capacity_block_eq_packing`.
- The structured chain with that constructed endpoint:
  `Constrained.structured_addressability_limit`,
  `Constrained.structured_addressability_limit_self`.
- Uniform local finiteness of the source clock, with a geometric example:
  `Source.ULF`, `geometricSource_ulf`, `geometricSource_hasGrowth`.
- The profile base square and rate-set bound:
  `Constrained.addressable_of_achievable`,
  `Constrained.Rates_bddAbove`.
- Non-negative source growth and scalar profile laws:
  `Source.HasGrowth.nonneg`, `capacity_mono_obligation`,
  `capacity_mono_family`, `capacity_le_packing`, `capacity_nonneg`.
- Exact profile transport under isometry:
  `Constrained.Rates_isometry_eq`.
- Zero-tax laws for requirements already supplied by base feasibility:
  `Rates_faithful_eq_block`, `Rates_radial_eq_block` and their scalar forms.
- A strict separation sanity witness:
  `unit_separates_block_from_malformed_causal`. This checks the profile
  machinery; it is not the manuscript's balloon theorem.
- Geometric block-versus-relational separation on the ULF binary tree:
  `balloon_separates`, `binaryTree_block_achievable`,
  `binaryTree_not_relational`, `binaryTreeSource_ulf`. Same source class as
  Theorem 5.3.
- Conditional boundary selection:
  `Capacity.minimizer_on_Iic_eq_capacity`. This does not supply a cost,
  minimization dynamics, or evidence that a natural system saturates.
- The optional space-form chart and its equality-case algebra:
  `Chart.curvature_at_least_floor`,
  `Chart.StateEquation.normalized_state_equation`.

## Paper-proved, not Lean-checked

- The full limsup addressability theorem.
- Weighted relational capacity of real hyperbolic space (Theorem 5.3).
- The isotropic Heintze classification under A3 (Proposition 6.2).
- The radial-concentration asymptotic statement.

## Classical cited inputs

- Packing and covering-number results used through Mathlib.
- Four-point/tree-metric classification.
- Hyperbolic volume entropy and Skenderi's free sub-semigroup of nearly full
  critical exponent.
- Tessera–Cornulier, *Quasi-isometrically embedded free sub-semigroups*,
  Geom. Topol. 12 (2008): QI-embedded free semigroups in connected Lie groups
  and exponential-growth solvable groups. This yields `C_rel > 0`, not
  `C_rel = C_block`.
- Kerr, *Quasi-trees and product set growth* (Oxford DPhil, 2022): uniform
  product-set growth for acylindrical actions on quasi-trees, again positivity
  rather than full exponent.
- Bartal–Linial–Mendel–Naor, *On metric Ramsey-type phenomena*, Ann. of Math.
  162 (2005): large ultrametric subsets of finite metrics. Complementary to
  the balloon, whose obstruction is a uniformly locally finite infinite tree.
- Doku-Amponsah, arXiv:1608.04154: a lossy AEP for tree-indexed processes,
  with no host geometry.
- Heintze classification and Schur-type isotropy.

## Defined but not computed

- `Relational`, `Stable`, and `Causal` obligations.
- Structural tax `tax` and availability `availability`.
- `HomogeneousPositiveRelational` and `HomogeneousZeroTax`: named open
  claims, not theorems.
- The relational capacity of any named infinite host.

## Open mathematical program

- Restate and Lean-check the balloon against the ULF source class. **Done**
  (`balloon_separates`): the canonical binary tree is ULF, block-achievable
  in the balloon, and not relationally representable there. The theorem is
  about that source, not a quantification over every ULF census.
- Relational coding theorem: `C_rel = c · h_rel` for that class.
- Homogeneous positivity: cocompact / Lie / acylindrically hyperbolic hosts
  with `h_pack > 0` have `C_rel > 0`. Tessera, Kerr, and Skenderi are the
  evidence; this is not zero tax.
- Zero tax in rank one, already Theorem 5.3, still not Lean.
- Clock-equivariance of admissible codes, restoring homogeneity in `c`.
- Quasi-isometric comparison laws. Exact numerical `θ(M)` is not licensed.

## Empirical and deliberately outside this repository

- Whether any natural system realizes the source, host, or obligation model.
- Whether a measured relational tax explains a consequential failure on an
  inhomogeneous host that block capacity cannot explain.
- Whether any natural system approaches or saturates a capacity boundary.
- Any inferred dimension, curvature, alphabet ceiling, or evolutionary
  dynamics.

Occupied regions of an otherwise homogeneous ambient model (grid-cell tori,
shape space) are inhomogeneous as hosts. The ambient isometry group is not
the isometry group of the occupied set.

## Public release gates

1. A framework release requires a clean Lean build, exact dependency language,
   citation metadata, and explicit parameters.
2. A structured-limit release requires the block identity (now Lean), the
   balloon restated against ULF trees (now Lean), and Theorem 5.3 as the
   equality case (still paper).
3. A homogeneity-program release requires a proved positivity theorem in a
   named homogeneous class, not a ratio `θ` or a host taxonomy.
4. A cross-substrate claim requires an independently validated measurement
   protocol and a tax-explains-failure instantiation on a host that is not
   homogeneous.

The manuscript sources are currently distributed as PDFs only. A source archive
containing LaTeX and bibliography inputs remains a publication requirement.
