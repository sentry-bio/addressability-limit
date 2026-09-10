/-
  Small checked witnesses for the capacity profile
  =================================================

  These examples test that the profile API can express both collapse and
  strict separation. They are logical calibration examples, not models of the
  manuscript's balloon or hyperbolic zero-tax theorem.
-/

import ActiveGeometry.Constrained

namespace ActiveGeometry.Constrained

open Filter
open scoped NNReal Topology

/-- The constant one-history source. -/
def singletonNatSource : Source ℕ where
  census _ := {0}
  census_nonempty _ := by simp

theorem singletonNatSource_hasGrowth_zero :
    singletonNatSource.HasGrowth 0 := by
  simp [Source.HasGrowth, singletonNatSource]

/-- A one-point-host code with linearly growing declared radius. -/
def unitLinearCode : Code ℕ Unit where
  addr _ _ := ()
  radius R := R

theorem singletonNatSource_represents_unit :
    Represents () 0 (noExtra : Obligation ℕ Unit) singletonNatSource 1 := by
  refine ⟨unitLinearCode, ?_, trivial, ?_, ?_⟩
  · constructor
    · intro R
      constructor
      · intro a ha b hb _
        simp [singletonNatSource] at ha hb
        exact ha.trans hb.symm
      · exact Metric.isSeparated_zero _
    · intro R
      simp [book, unitLinearCode, singletonNatSource,
        Metric.mem_closedBall]
  · exact tendsto_natCast_atTop_atTop
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
    simp [unitLinearCode, hR']

/-- A deliberately ill-formed ancestry: the represented history `0` names the
    absent history `1` as its parent. -/
def escapingParent : ℕ → Option ℕ
  | 0 => some 1
  | _ => none

theorem singletonNatSource_not_parentClosed :
    ¬ singletonNatSource.ParentClosed escapingParent := by
  intro h
  have hmem := h 0 0 (by simp [singletonNatSource]) 1 (by simp [escapingParent])
  simp [singletonNatSource] at hmem

/-- `Separates` is inhabited: on the declared singleton family, the block rung
    admits rate zero in the one-point host, while the causal rung rejects the
    source's malformed ancestry. This is a strict profile separation sanity
    witness, not the geometric balloon separation. -/
theorem unit_separates_block_from_malformed_causal :
    Separates () 0 {singletonNatSource}
      (noExtra : Obligation ℕ Unit) (Causal escapingParent 0) 1 := by
  intro heq
  have hzero :
      (0 : ℝ) ∈ Rates () 0 {singletonNatSource}
        (noExtra : Obligation ℕ Unit) 1 :=
    ⟨singletonNatSource, by simp, singletonNatSource_hasGrowth_zero,
      singletonNatSource_represents_unit⟩
  rw [heq] at hzero
  obtain ⟨σ, hσ, _, _, _, hcausal, _, _⟩ := hzero
  have hsigma : σ = singletonNatSource := by simpa using hσ
  subst σ
  exact singletonNatSource_not_parentClosed hcausal.1

end ActiveGeometry.Constrained
