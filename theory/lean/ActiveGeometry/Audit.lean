/-
  Reproducible axiom audit for the public theorem surface.

  CI executes this file directly and rejects `sorryAx`. Mathlib's construction
  of the real numbers contributes the expected `propext`, `Classical.choice`,
  and `Quot.sound`.
-/

import ActiveGeometry

#print axioms ActiveGeometry.Packing.convergent_rate_addressability_limit
#print axioms ActiveGeometry.Packing.logCard_div_radius_le_packingRate
#print axioms ActiveGeometry.Constrained.addressable_of_achievable
#print axioms ActiveGeometry.Constrained.capacity_eq_packing_of_endpoint_achievable
#print axioms ActiveGeometry.Constrained.capacity_block_eq_packing
#print axioms ActiveGeometry.Constrained.structured_addressability_limit_self
#print axioms ActiveGeometry.Constrained.Rates_isometry_eq
#print axioms ActiveGeometry.Constrained.unit_separates_block_from_malformed_causal
#print axioms ActiveGeometry.Constrained.balloon_separates
#print axioms ActiveGeometry.Constrained.binaryTree_block_achievable
#print axioms ActiveGeometry.Constrained.binaryTree_not_relational
#print axioms ActiveGeometry.Capacity.minimizer_on_Iic_eq_capacity
#print axioms ActiveGeometry.Chart.StateEquation.normalized_state_equation
