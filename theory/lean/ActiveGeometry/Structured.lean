/-
  The Structured Addressability Limit
  ===================================

  A host has at least two capacities: how many histories it can tell apart,
  and how many of their relations it can preserve. The second is bounded by
  the first, and the gap can be total:

      β ≤ C_𝒜 ≤ C_block = c · h_pack

  under depthwise recoding at the block rung. Nested, causal, or relational
  achievability is a strictly stronger demand.

  This file supplies the missing block endpoint inside the profile API and
  names the homogeneity program that would connect the balloon to hyperbolic
  space. The balloon's geometric gap is Lean-checked in `Balloon.lean`. This
  file does not prove Theorem 5.3 or quasi-isometric invariance of a bare
  ratio θ(M).
-/

import ActiveGeometry.Constrained

namespace ActiveGeometry.Constrained

open Filter
open scoped NNReal Topology

variable {M : Type*} [MetricSpace M]

/-! ### Depthwise recoding -/

/-- Independent optimal packings at linearly growing radii. Codebooks at
    distinct depths need not share addresses: this is block coding, not
    successive refinement. -/
noncomputable def blockCensus [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : ε ≠ 0) {c : ℝ} (hc : 0 ≤ c) (R : ℕ) : Finset M :=
  Packing.optimalBlockCodebook o ε (c * R)
    (mul_nonneg hc (Nat.cast_nonneg _))
    (Packing.hasFinitePacking_of_properSpace o hε)

theorem blockCensus_card [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : ε ≠ 0) {c : ℝ} (hc : 0 ≤ c) (R : ℕ) :
    (blockCensus o ε hε hc R).card =
      Packing.packingCount o ε (c * R) :=
  Packing.optimalBlockCodebook_card o ε (c * R)
    (mul_nonneg hc (Nat.cast_nonneg _))
    (Packing.hasFinitePacking_of_properSpace o hε)

theorem blockCensus_nonempty [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : ε ≠ 0) {c : ℝ} (hc : 0 ≤ c) (R : ℕ) :
    (blockCensus o ε hε hc R).Nonempty := by
  refine Finset.card_pos.mp ?_
  have hone : 1 ≤ (blockCensus o ε hε hc R).card := by
    rw [blockCensus_card]
    exact Packing.one_le_packingCount o ε (c * R)
      (mul_nonneg hc (Nat.cast_nonneg _))
      (Packing.hasFinitePacking_of_properSpace o hε)
  exact Nat.succ_le_iff.mp hone

/-- The block source whose generation-R census is an optimal packing of the
    radius-`c R` ball. -/
noncomputable def blockSource [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : ε ≠ 0) {c : ℝ} (hc : 0 ≤ c) : Source M where
  census := blockCensus o ε hε hc
  census_nonempty := blockCensus_nonempty o ε hε hc

/-- Identity addressing of a codebook already sitting in the host. -/
def recodingCode (c : ℝ) : Code M M where
  addr _ x := x
  radius R := c * (R : ℝ)

theorem recodingCode_base [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : ε ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    Base o ε (blockSource o ε hε hc) (recodingCode c) := by
  constructor
  · intro R
    constructor
    · exact Set.injOn_id _
    · have himg :
          book (blockSource o ε hε hc) (recodingCode c) R =
            (blockCensus o ε hε hc R : Set M) := by
        simp [book, recodingCode, blockSource]
      rw [himg]
      exact Packing.optimalBlockCodebook_separated o ε (c * R)
        (mul_nonneg hc (Nat.cast_nonneg _))
        (Packing.hasFinitePacking_of_properSpace o hε)
  · intro R
    have himg :
        book (blockSource o ε hε hc) (recodingCode c) R =
          (blockCensus o ε hε hc R : Set M) := by
      simp [book, recodingCode, blockSource]
    have hr : ((recodingCode c : Code M M).radius R) = c * (R : ℝ) := rfl
    rw [himg, hr]
    exact Packing.optimalBlockCodebook_subset o ε (c * R)
      (mul_nonneg hc (Nat.cast_nonneg _))
      (Packing.hasFinitePacking_of_properSpace o hε)

theorem recodingCode_represents [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : 0 < ε) {c : ℝ} (hc : 0 < c) :
    Represents o ε (noExtra : Obligation M M)
      (blockSource o ε hε.ne' hc.le) c := by
  refine ⟨(recodingCode c : Code M M), recodingCode_base o ε hε.ne' hc.le, trivial, ?_, ?_⟩
  · exact tendsto_natCast_atTop_atTop.const_mul_atTop hc
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
    simp [recodingCode, hR']

theorem blockSource_hasGrowth [ProperSpace M] (o : M) (ε : ℝ≥0)
    (hε : 0 < ε) {c hpack : ℝ} (hc : 0 < c)
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack)) :
    (blockSource o ε hε.ne' hc.le).HasGrowth (c * hpack) := by
  have hρ :
      Tendsto (fun R : ℕ => c * (R : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hsampled :
      Tendsto (fun R : ℕ => Packing.packingRate o ε (c * (R : ℝ)))
        atTop (𝓝 hpack) :=
    hpacking.comp hρ
  have hmul :
      Tendsto (fun R : ℕ =>
          c * Packing.packingRate o ε (c * (R : ℝ))) atTop (𝓝 (c * hpack)) :=
    hsampled.const_mul c
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hρpos : 0 < c * (R : ℝ) := mul_pos hc hR'
  have hcard := blockCensus_card o ε hε.ne' hc.le R
  rw [blockSource, hcard, Packing.packingRate]
  have hne : (c * (R : ℝ)) ≠ 0 := hρpos.ne'
  field_simp [hne, hR'.ne']

/-- Constructive asymptotic block exactness: independent optimal packings
    achieve `c · h_pack` in the profile API. This is depthwise recoding, not
    nested retention. -/
theorem achievable_block_packing [ProperSpace M] (o : M) {ε : ℝ≥0}
    (hε : 0 < ε) {c hpack : ℝ} (hc : 0 < c)
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack)) :
    Achievable o ε (allSources : Set (Source M)) (noExtra : Obligation M M)
      (c * hpack) c :=
  ⟨blockSource o ε hε.ne' hc.le, trivial,
    blockSource_hasGrowth o ε hε hc hpacking,
    recodingCode_represents o ε hε hc⟩

/-- Block capacity equals packing capacity over the unrestricted source
    family, at any positive radial rate whose packing growth converges. -/
theorem capacity_block_eq_packing [ProperSpace M] (o : M) {ε : ℝ≥0}
    (hε : 0 < ε) {c hpack : ℝ} (hc : 0 < c)
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack)) :
    capacity o ε (allSources : Set (Source M)) (noExtra : Obligation M M) c =
      c * hpack :=
  capacity_eq_packing_of_endpoint_achievable hε hpacking
    (achievable_block_packing o hε hc hpacking)

/-- The Structured Addressability Limit with a constructed block endpoint,
    over all sources, under depthwise recoding:

      `β ≤ C_𝒜 ≤ C_block = c · h_pack`. -/
theorem structured_addressability_limit_self [ProperSpace M]
    (o : M) {ε : ℝ≥0} (hε : 0 < ε)
    {𝒜 : Obligation M M} {β c hpack : ℝ} (hc : 0 < c)
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack))
    (h : Achievable o ε (allSources : Set (Source M)) 𝒜 β c) :
    β ≤ capacity o ε (allSources : Set (Source M)) 𝒜 c ∧
      capacity o ε (allSources : Set (Source M)) 𝒜 c ≤
        capacity o ε (allSources : Set (Source M))
          (noExtra : Obligation M M) c ∧
      capacity o ε (allSources : Set (Source M))
          (noExtra : Obligation M M) c = c * hpack :=
  structured_addressability_limit hε hpacking h
    (achievable_block_packing o hε hc hpacking)

/-! ### Homogeneity program

Tessera–Cornulier (Geom. Topol. 12, 2008): every connected Lie group, and
every finitely generated solvable group of exponential growth, contains a
quasi-isometrically embedded free sub-semigroup on two generators. That
yields `C_rel > 0`, not `C_rel = C_block`.

Kerr (DPhil, Oxford 2022): groups acting acylindrically on quasi-trees
satisfy uniform product-set growth
`|U^n| ≥ (α |U|)^{⌊(n+1)/2⌋}`, hence again positive relational growth
rather than full exponent.

Skenderi supplies the rank-one upgrade to equality.

Bartal–Linial–Mendel–Naor (Ann. of Math. 162, 2005): every finite metric
has a polynomially large subset embedding into an ultrametric. That is a
finite, unbounded-degree, subset theorem — complementary to the balloon,
whose exponential cliques are ultrametric and whose obstruction is a
uniformly locally finite infinite tree.

Doku-Amponsah (arXiv:1608.04154) is a rate-distortion AEP for tree-indexed
processes with no host geometry.

The safe conjecture is positivity under homogeneity, not zero tax. -/

/-- Open: positive relational capacity. Not a theorem. -/
def HomogeneousPositiveRelational {S : Type*} [PseudoMetricSpace S]
    (o : M) (ε : ℝ≥0) (𝔖 : Set (Source S)) (q : Distortion) (c : ℝ) : Prop :=
  0 < capacity o ε 𝔖 (Relational q) c

/-- Open, and strictly stronger: vanishing relational tax. Not a theorem. -/
def HomogeneousZeroTax {S : Type*} [PseudoMetricSpace S]
    (o : M) (ε : ℝ≥0) (𝔖 : Set (Source S)) (q : Distortion) (c : ℝ) : Prop :=
  capacity o ε 𝔖 (Relational q) c =
    capacity o ε 𝔖 (noExtra : Obligation S M) c

end ActiveGeometry.Constrained
