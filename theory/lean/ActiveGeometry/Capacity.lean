/-
  Capacity algebra of the addressability bound
  ============================================

  Pure real algebra downstream of

      Addressable β c hcap  :  β ≤ c · h_cap.

  Nothing here mentions a metric space, a packing number, DNA, or an alphabet.
  `Packing.lean` is what *proves* `Addressable` in the convergent-rate case.
  This file records what the inequality implies, and what it does not.

  This file is the scalar algebra of the bound and nothing else:
  `Addressable`, the achieved rate `λ = β/c`, efficiency, and the equality-case
  predicate `CapacitySaturated`.

  Everything requiring a space-form identification of `h_cap` - the curvature
  floor, the gauge, the normalized curvature - lives in `Chart.lean`, behind
  the `ActiveGeometry.Chart` namespace, because it is optional and carries
  assumptions this file does not. The spine reads:

      Addressable  ->  achievedRate  ->  feasibility  ->  tax

  with curvature reachable only by explicitly entering a chart.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ActiveGeometry.Capacity

open Real

lemma log2_pos : log 2 > 0 :=
  log_pos (by norm_num : (1 : ℝ) < 2)

/-- Convert a rate in bits per step to nats per step. -/
noncomputable def bitsToNats (h : ℝ) : ℝ := h * log 2

/-- The coordinate-free addressability condition `β ≤ c · h_cap`.
    Here `h_cap` is any independently established exponential host-capacity
    rate (fixed-resolution packing entropy, or volume entropy under extra
    hypotheses). -/
def Addressable (β c hcap : ℝ) : Prop := β ≤ c * hcap

/-- The equality case of addressability. This is not part of `Addressable`. -/
def CapacitySaturated (β c hcap : ℝ) : Prop := β = c * hcap

/-- The achieved entropy rate `λ = β / c`: retained history per unit
    representational radius. Written this way, both sides of the bound are
    rates in the same units and `c` is revealed as a gauge, not a third
    physical quantity. -/
noncomputable def achievedRate (β c : ℝ) : ℝ := β / c

/-- The bound in rate-comparison form: `λ ≤ h_cap`. -/
theorem achievedRate_le {β c hcap : ℝ} (hc : 0 < c)
    (h : Addressable β c hcap) : achievedRate β c ≤ hcap := by
  rw [achievedRate, div_le_iff₀ hc]
  simpa [Addressable, mul_comm] using h

/-- Contrapositive: a demand rate exceeding host capacity admits no faithful
    representation. This is the empirically observable content of the bound -
    every failure mode measured is an instance of it. -/
theorem not_addressable_of_lt {β c hcap : ℝ} (hc : 0 < c)
    (h : hcap < achievedRate β c) : ¬ Addressable β c hcap :=
  fun hb => absurd (achievedRate_le hc hb) (not_le.mpr h)

/-- Addressability efficiency `η = β / (c · h_cap)`. On the physical domain
    `β ≥ 0`, `c > 0`, `h_cap > 0`, the bound forces `η ≤ 1`. -/
noncomputable def efficiency (β c hcap : ℝ) : ℝ := β / (c * hcap)

/-- A positive bit rate gives a positive information-growth rate in nats. -/
theorem bitsToNats_pos (h : ℝ) (hh : 0 < h) :
    0 < bitsToNats h :=
  mul_pos hh log2_pos

/-- Positive retained-information growth at finite positive radial rate forces
    positive host entropy. -/
theorem addressability_forces_positive_entropy
    (β c hcap : ℝ)
    (hβ : 0 < β) (hc : 0 < c) (hbound : Addressable β c hcap) :
    0 < hcap := by
  unfold Addressable at hbound
  by_contra hnot
  have hh : hcap ≤ 0 := le_of_not_gt hnot
  have hprod : c * hcap ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hh
  linarith

/-- The addressability efficiency cannot exceed one. -/
theorem efficiency_le_one
    (β c hcap : ℝ)
    (hc : 0 < c) (hh : 0 < hcap) (hbound : Addressable β c hcap) :
    efficiency β c hcap ≤ 1 := by
  unfold efficiency
  rw [div_le_iff₀ (mul_pos hc hh)]
  simpa [Addressable] using hbound

/-- Efficiency is the achieved rate measured against the available one. -/
theorem efficiency_eq_achievedRate_div {β c hcap : ℝ} (hc : c ≠ 0) :
    efficiency β c hcap = achievedRate β c / hcap := by
  rw [efficiency, achievedRate]; field_simp

/-- Saturation implies addressability; the converse is not assumed. -/
theorem saturated_is_addressable
    (β c hcap : ℝ) (hsaturated : CapacitySaturated β c hcap) :
    Addressable β c hcap := by
  unfold CapacitySaturated at hsaturated
  unfold Addressable
  exact hsaturated.le

/-! ### Conditional boundary selection

This is the precise content available to the optimization leg. If a feasible
rate set contains every rate up to its ceiling and an independently supplied
cost strictly decreases with rate, then a cost minimizer lies on the capacity
boundary. The theorem supplies neither the cost nor a dynamics that minimizes
it. -/

/-- `x` minimizes `J` over the feasible set `S`. -/
def MinimizesOn (J : ℝ → ℝ) (S : Set ℝ) (x : ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, J x ≤ J y

/-- A strictly rate-decreasing cost selects the endpoint of a full feasible
    interval. This is a conditional variational theorem, not a saturation
    hypothesis and not an evolution law. -/
theorem minimizer_on_Iic_eq_capacity {J : ℝ → ℝ} {C x : ℝ}
    (hJ : StrictAnti J) (hx : MinimizesOn J (Set.Iic C) x) :
    x = C := by
  apply le_antisymm hx.1
  by_contra hCx
  have hxC : x < C := lt_of_not_ge hCx
  exact (not_lt_of_ge (hx.2 C (by simp))) (hJ hxC)

end ActiveGeometry.Capacity
