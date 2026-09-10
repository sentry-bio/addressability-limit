/-
  Growth-class gate identities (instrument, not a theory layer)
  ==============================================

  Elementary real identities behind the finite-sample growth-class test.
  See the `Measurability.lean` section of `theory/lean/README.md`.

  On a radial window of ratio r > 1, the unique exponential and the unique
  polynomial that match at both endpoints have log-occupancy difference

      f(t) = d log t - d (log r)/(r-1) (t-1),    t ∈ [1, r].

  This file proves:

  * the geometric-midpoint identity (Lemma 1.2);
  * the exact maximum-gap formula at the logarithmic mean (Proposition 1.3);
  * positivity of the span information Δ(r,d) for r > 1, d > 0.

  It does not formalize Hellinger distance, Le Cam's lemma, or the
  Poisson-increment testing model. Those remain paper proofs.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace ActiveGeometry.Measurability

open Real

/-- Log-occupancy difference of the endpoint-matched pair, on the scaled
    window t = ρ/ρ_min. -/
noncomputable def logGap (d r t : ℝ) : ℝ :=
  d * log t - d * (log r / (r - 1)) * (t - 1)

/-- Formal t-derivative of `logGap`. -/
noncomputable def logGapDeriv (d r t : ℝ) : ℝ :=
  d / t - d * (log r / (r - 1))

/-- Geometric-midpoint gap exponent (Lemma 1.2). -/
noncomputable def midpointExponent (d r : ℝ) : ℝ :=
  d * log r * (1 / 2 - 1 / (√r + 1))

/-- Exact maximum log-gap (Proposition 1.3). -/
noncomputable def spanInformation (d r : ℝ) : ℝ :=
  d * (log ((r - 1) / log r) - 1 + log r / (r - 1))

/-- Logarithmic mean of 1 and r: the unique critical point of `logGap`. -/
noncomputable def logMean (r : ℝ) : ℝ :=
  (r - 1) / log r

lemma logGap_one (d r : ℝ) (_hr : 1 < r) : logGap d r 1 = 0 := by
  unfold logGap
  simp [log_one]

lemma logGap_right (d r : ℝ) (hr : 1 < r) : logGap d r r = 0 := by
  have hr1 : r - 1 ≠ 0 := by linarith
  unfold logGap
  field_simp [hr1]
  ring

private lemma sqrt_factor (r : ℝ) (hr0 : 0 < r) :
    r - 1 = (√r - 1) * (√r + 1) := by
  nlinarith [sq_sqrt (le_of_lt hr0)]

private lemma midpoint_rate
    (r : ℝ) (hr : 1 < r) :
    log r / (r - 1) * (√r - 1) = log r / (√r + 1) := by
  have hr0 : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1) hr
  have hne : √r + 1 ≠ 0 := by
    have : 0 < √r := sqrt_pos.mpr hr0
    linarith
  have hsm : √r - 1 ≠ 0 := by
    intro h
    have hsqrt : √r = 1 := by linarith
    have : r = 1 := by
      calc
        r = (√r) ^ 2 := (sq_sqrt (le_of_lt hr0)).symm
        _ = 1 := by simp [hsqrt]
    linarith
  rw [sqrt_factor r hr0]
  field_simp [hne, hsm]

/-- Lemma 1.2: the midpoint identity. -/
theorem midpoint_exponent_eq (d r : ℝ) (hr : 1 < r) :
    logGap d r (√r) = midpointExponent d r := by
  have hr0 : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1) hr
  have hlog : log (√r) = log r / 2 := log_sqrt (le_of_lt hr0)
  have hquot := midpoint_rate r hr
  unfold logGap midpointExponent
  rw [hlog]
  calc
    d * (log r / 2) - d * (log r / (r - 1)) * (√r - 1)
      = d * (log r / 2) - d * (log r / (r - 1) * (√r - 1)) := by ring
    _ = d * (log r / 2) - d * (log r / (√r + 1)) := by rw [hquot]
    _ = d * log r * (1 / 2 - 1 / (√r + 1)) := by ring

/-- The formal derivative vanishes at the logarithmic mean. -/
theorem logGapDeriv_logMean (d r : ℝ) (hr : 1 < r) :
    logGapDeriv d r (logMean r) = 0 := by
  have hlog : 0 < log r := log_pos hr
  have hr1 : r - 1 ≠ 0 := by linarith
  unfold logGapDeriv logMean
  field_simp [hr1, ne_of_gt hlog]
  ring

private lemma logMean_shift
    (r : ℝ) (hr : 1 < r) :
    log r / (r - 1) * ((r - 1) / log r - 1) = 1 - log r / (r - 1) := by
  have hlog : 0 < log r := log_pos hr
  have hr1 : r - 1 ≠ 0 := by linarith
  field_simp [hr1, ne_of_gt hlog]

/-- Proposition 1.3: the gap at the logarithmic mean is the span information. -/
theorem spanInformation_eq_logGap_logMean (d r : ℝ) (hr : 1 < r) :
    logGap d r (logMean r) = spanInformation d r := by
  have ht := logMean_shift r hr
  unfold logGap spanInformation logMean
  calc
    d * log ((r - 1) / log r)
        - d * (log r / (r - 1)) * ((r - 1) / log r - 1)
      = d * log ((r - 1) / log r)
        - d * (log r / (r - 1) * ((r - 1) / log r - 1)) := by ring
    _ = d * log ((r - 1) / log r) - d * (1 - log r / (r - 1)) := by rw [ht]
    _ = d * (log ((r - 1) / log r) - 1 + log r / (r - 1)) := by ring

/-- Span information is positive for r > 1 and d > 0. -/
theorem spanInformation_pos (d r : ℝ) (hd : 0 < d) (hr : 1 < r) :
    0 < spanInformation d r := by
  have hlog : 0 < log r := log_pos hr
  have ht : 1 < logMean r := by
    unfold logMean
    exact (one_lt_div hlog).mpr (log_lt_sub_one_of_pos (by linarith) (ne_of_gt hr))
  have htpos : 0 < logMean r := lt_trans (by norm_num : (0 : ℝ) < 1) ht
  have hx : 0 < logMean r - 1 := sub_pos.mpr ht
  have hlogt : 2 * (logMean r - 1) / (logMean r + 1) < log (logMean r) := by
    have h := lt_log_one_add_of_pos hx
    have hden : logMean r - 1 + 2 = logMean r + 1 := by ring
    have harg : 1 + (logMean r - 1) = logMean r := by ring
    rw [hden, harg] at h
    exact h
  have hcmp :
      (logMean r - 1) / logMean r
        < 2 * (logMean r - 1) / (logMean r + 1) := by
    have hsum : 0 < logMean r + 1 := by linarith
    rw [div_lt_div_iff₀ htpos hsum]
    nlinarith [ht]
  have hmain : (logMean r - 1) / logMean r < log (logMean r) :=
    lt_trans hcmp hlogt
  have hrecip : log r / (r - 1) = (logMean r)⁻¹ := by
    unfold logMean
    field_simp [ne_of_gt hlog]
  have hform :
      logGap d r (logMean r)
        = d * (log (logMean r) - (logMean r - 1) / logMean r) := by
    unfold logGap
    rw [hrecip]
    field_simp [ne_of_gt htpos]
  have hdiff : 0 < log (logMean r) - (logMean r - 1) / logMean r :=
    sub_pos.mpr hmain
  have : 0 < d * (log (logMean r) - (logMean r - 1) / logMean r) :=
    mul_pos hd hdiff
  rw [← spanInformation_eq_logGap_logMean d r hr, hform]
  exact this

/-- `logGapDeriv` really is the derivative of `logGap`. Without this, the
    name `logGapDeriv` asserts a relationship the kernel never checks. -/
theorem hasDerivAt_logGap (d r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (logGap d r) (logGapDeriv d r t) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ d * log t) (d * t⁻¹) t :=
    (Real.hasDerivAt_log ht).const_mul d
  have h2 :
      HasDerivAt (fun t : ℝ ↦ d * (log r / (r - 1)) * (t - 1))
        (d * (log r / (r - 1))) t := by
    simpa using ((hasDerivAt_id t).sub_const 1).const_mul (d * (log r / (r - 1)))
  have h3 :
      HasDerivAt (fun t : ℝ ↦ d * log t - d * (log r / (r - 1)) * (t - 1))
        (d * t⁻¹ - d * (log r / (r - 1))) t := h1.sub h2
  have hrw : logGapDeriv d r t = d * t⁻¹ - d * (log r / (r - 1)) := by
    unfold logGapDeriv; rw [div_eq_mul_inv]
  rw [hrw]
  exact h3

/-- The logarithmic mean maximizes `logGap` over all positive `t` — not merely
    on the window `[1, r]`. The content is the elementary inequality
    `log u ≤ u - 1` evaluated at `u = t / logMean r`; the critical-point
    computation is not needed. -/
theorem logGap_le_logGap_logMean (d r t : ℝ)
    (hd : 0 ≤ d) (hr : 1 < r) (ht : 0 < t) :
    logGap d r t ≤ logGap d r (logMean r) := by
  have hlog : 0 < log r := log_pos hr
  have hr1 : 0 < r - 1 := by linarith
  have hmpos : 0 < logMean r := div_pos hr1 hlog
  have hcancel :
      log r / (r - 1) * (t - logMean r) = t / logMean r - 1 := by
    unfold logMean
    field_simp
  have hkey : log (t / logMean r) ≤ t / logMean r - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ht hmpos)
  rw [Real.log_div ht.ne' hmpos.ne', ← hcancel] at hkey
  have hid :
      logGap d r (logMean r) - logGap d r t
        = d * (log r / (r - 1) * (t - logMean r)
            - (log t - log (logMean r))) := by
    unfold logGap; ring
  have hnn :
      0 ≤ d * (log r / (r - 1) * (t - logMean r)
          - (log t - log (logMean r))) :=
    mul_nonneg hd (by linarith)
  linarith

/-- Strict version: the maximizer is unique. -/
theorem logGap_lt_logGap_logMean (d r t : ℝ)
    (hd : 0 < d) (hr : 1 < r) (ht : 0 < t) (hne : t ≠ logMean r) :
    logGap d r t < logGap d r (logMean r) := by
  have hlog : 0 < log r := log_pos hr
  have hr1 : 0 < r - 1 := by linarith
  have hmpos : 0 < logMean r := div_pos hr1 hlog
  have hm0 : logMean r ≠ 0 := hmpos.ne'
  have hune : t / logMean r ≠ 1 := by
    intro h
    apply hne
    field_simp at h
    linarith
  have hcancel :
      log r / (r - 1) * (t - logMean r) = t / logMean r - 1 := by
    unfold logMean
    field_simp
  have hkey : log (t / logMean r) < t / logMean r - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos ht hmpos) hune
  rw [Real.log_div ht.ne' hmpos.ne', ← hcancel] at hkey
  have hid :
      logGap d r (logMean r) - logGap d r t
        = d * (log r / (r - 1) * (t - logMean r)
            - (log t - log (logMean r))) := by
    unfold logGap; ring
  have hpos :
      0 < d * (log r / (r - 1) * (t - logMean r)
          - (log t - log (logMean r))) :=
    mul_pos hd (by linarith)
  linarith

/-- Proposition 1.3, in full: the span information is the *maximum* of the
    log-gap over the window, attained at the logarithmic mean. -/
theorem spanInformation_eq_max (d r : ℝ) (hd : 0 ≤ d) (hr : 1 < r) :
    IsGreatest (logGap d r '' Set.Ioi 0) (spanInformation d r) := by
  have hlog : 0 < log r := log_pos hr
  have hr1 : 0 < r - 1 := by linarith
  have hmpos : 0 < logMean r := div_pos hr1 hlog
  constructor
  · exact ⟨logMean r, hmpos, spanInformation_eq_logGap_logMean d r hr⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [← spanInformation_eq_logGap_logMean d r hr]
    exact logGap_le_logGap_logMean d r t hd hr ht

end ActiveGeometry.Measurability
