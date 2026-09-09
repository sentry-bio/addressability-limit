/-
  Constrained capacity: the profile of a host
  ==========================================

  A host does not have one capacity. It has a profile, one entry per class of
  structural obligation a code must honour. Two hosts can hold the same number
  of distinguishable states and differ completely in their ability to preserve
  ancestry, refinement, or metric relations.

  ## Three objects, kept apart

  An earlier version bundled the census into the code. Quantifying over codes
  then quantified over sources too, so "can this host hold THIS source?" was
  unstatable, and host capacity was conflated with source representability.
  The three objects are now separate:

      SOURCE      the growing census of histories to be retained
      CODE        addresses and a radial budget, and nothing else
      OBLIGATION  a predicate on a (source, code) PAIR

  From these, two genuinely different notions:

      `Represents o ε 𝒜 σ c`     can THIS source be held here?  - what an
                                  experiment tests, one source at a time
      `Achievable o ε 𝔖 𝒜 β c`   what rates does the host support over a
                                  DECLARED family `𝔖`? - what a theorem
                                  classifies

  ## Retention is a property of the source

  An earlier version made `Persistent` an obligation on the code. That was a
  category error: whether the census accretes is settled by the source, and no
  choice of address map changes it. It is now `Source.Retentive`, and it enters
  a capacity claim by restricting `𝔖` - which is the family parameter earning
  its keep rather than decorating the signature.

  ## Capacity is a set before it is a number

  `Rates` is the achievable-rate SET. Boundedness is a theorem
  (`Rates_subset_Iic`, from the packing converse) and the scalar `capacity` is
  derived afterwards. Defining the scalar first invites `sSup` of an unbounded
  real set, which silently returns `0`.

  ## Status vocabulary

  DEFINED, LEAN-CHECKED, PAPER-PROVED, OPEN, as in `ActiveGeometry`. Nothing
  here computes a profile entry for a named host, and no separation between two
  rungs is proved: `Separates` names that target, and the manuscript's balloon
  is intended to supply the first instance. It is PAPER-PROVED, not Lean.
-/

import ActiveGeometry.Capacity
import ActiveGeometry.Packing
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.ProperSpace

namespace ActiveGeometry.Constrained

open Filter
open scoped ENNReal NNReal Topology

variable {M : Type*} [MetricSpace M] {S : Type*}

/-! ### Host-side admissibility

Scoped narrowly: this is the primitive for INTRINSIC obligations, ones an
unlabelled subset `C ⊆ M` can satisfy on its own. Obligations referring to a
labelled source cannot be seen by an unlabelled `C`; those live on pairs. -/

/-- A host-side obligation: a predicate on codebooks sitting in the host. -/
abbrev Admissible (M : Type*) := Set M → Prop

/-- No host-side obligation. -/
def unconstrained : Admissible M := fun _ => True

/-- Host-side constrained packing number: Mathlib's `Metric.packingNumber` with
    one further indexed supremum, so only codebooks satisfying `P` compete. -/
noncomputable def packingNumberOn (P : Admissible M) (ε : ℝ≥0) (A : Set M) : ℕ∞ :=
  ⨆ (C : Set M) (_ : C ⊆ A) (_ : Metric.IsSeparated ε C) (_ : P C), C.encard

theorem packingNumberOn_unconstrained (ε : ℝ≥0) (A : Set M) :
    packingNumberOn (unconstrained : Admissible M) ε A = Metric.packingNumber ε A := by
  simp [packingNumberOn, Metric.packingNumber, unconstrained]

/-- A stronger host-side obligation cannot admit more. -/
theorem packingNumberOn_mono {P Q : Admissible M} (h : ∀ C, P C → Q C)
    (ε : ℝ≥0) (A : Set M) :
    packingNumberOn P ε A ≤ packingNumberOn Q ε A := by
  refine iSup_le fun C => iSup_le fun hC => iSup_le fun hsep => iSup_le fun hP => ?_
  exact le_iSup_of_le C (le_iSup_of_le hC (le_iSup_of_le hsep
    (le_iSup_of_le (h C hP) le_rfl)))

theorem packingNumberOn_le (P : Admissible M) (ε : ℝ≥0) (A : Set M) :
    packingNumberOn P ε A ≤ Metric.packingNumber ε A := by
  rw [← packingNumberOn_unconstrained ε A]
  exact packingNumberOn_mono (fun _ _ => trivial) ε A

/-! ### Sources -/

/-- A source: the growing census of histories to be retained. The source owns
    its filtration; a code does not get to choose it. -/
structure Source (S : Type*) where
  census : ℕ → Finset S
  census_nonempty : ∀ R, (census R).Nonempty

/-- Retention: the past is not discarded. A property of the SOURCE - no choice
    of address map can create or destroy it. -/
def Source.Retentive (σ : Source S) : Prop := ∀ R, σ.census R ⊆ σ.census (R + 1)

/-- The source's own growth rate, in nats per generative step. -/
def Source.HasGrowth (σ : Source S) (β : ℝ) : Prop :=
  Tendsto (fun R : ℕ => Real.log ((σ.census R).card : ℝ) / (R : ℝ)) atTop (𝓝 β)

/-- Declared source families. `𝔖` is never implicit in a capacity claim. -/
def allSources : Set (Source S) := Set.univ

def retentiveSources : Set (Source S) := {σ | σ.Retentive}

theorem retentiveSources_subset_all :
    (retentiveSources : Set (Source S)) ⊆ allSources := fun _ _ => trivial

/-! ### Codes -/

/-- A code: addresses and a radial budget. Nothing else - in particular, not a
    census. -/
structure Code (S M : Type*) [MetricSpace M] where
  addr : ℕ → S → M
  radius : ℕ → ℝ

/-- The codebook at depth `R`: where this code puts this source's census. -/
def book (σ : Source S) (κ : Code S M) (R : ℕ) : Set M :=
  κ.addr R '' (σ.census R : Set S)

/-- An obligation: a predicate on a (source, code) pair. -/
abbrev Obligation (S M : Type*) [MetricSpace M] := Source S → Code S M → Prop

/-- No obligation beyond base feasibility. -/
def noExtra : Obligation S M := fun _ _ => True

/-! ### Metric obligations

What of the source's shape the image must preserve. Ordered by strength, but
there is no jet formalism here; the word would be metaphor. -/

/-- Distinct histories receive distinct, `ε`-separated addresses. -/
def Faithful (ε : ℝ≥0) : Obligation S M := fun σ κ =>
  ∀ R, Set.InjOn (κ.addr R) (σ.census R : Set S) ∧
       Metric.IsSeparated ε (book σ κ R)

/-- Addresses stay inside the declared radial budget. -/
def Radial (o : M) : Obligation S M := fun σ κ =>
  ∀ R, book σ κ R ⊆ Metric.closedBall o (κ.radius R)

/-- The code preserves the source's own metric to distortion `(D, K)`. The
    source distance is supplied explicitly: a generative clock need not be a
    registered instance. -/
def Relational (dS : S → S → ℝ) (D K : ℝ) : Obligation S M := fun σ κ =>
  ∀ R, ∀ u ∈ σ.census R, ∀ v ∈ σ.census R,
    D⁻¹ * dS u v - K ≤ dist (κ.addr R u) (κ.addr R v) ∧
    dist (κ.addr R u) (κ.addr R v) ≤ D * dS u v + K

/-! ### Online obligations

How the code is presented in time. These constrain the CODE - unlike retention,
which constrains the source. -/

/-- The past is not rewritten: an address, once assigned, moves by at most `m`. -/
def Stable (m : ℝ) : Obligation S M := fun σ κ =>
  ∀ R, ∀ s ∈ σ.census R, dist (κ.addr R s) (κ.addr (R + 1) s) ≤ m

/-- Per-step motion is bounded: a child sits within `m` of its parent. -/
def Causal (parent : S → Option S) (m : ℝ) : Obligation S M := fun σ κ =>
  ∀ R, ∀ s ∈ σ.census R, ∀ p ∈ parent s, dist (κ.addr R s) (κ.addr R p) ≤ m

/-! ### Base feasibility

Without these a "rate" is not a statement about the host at all. `Code.radius`
is a free field, unrelated to where `addr` puts anything; see
`vacuity_without_base`. -/

/-- Base feasibility: faithful addressing inside the radial budget. -/
def Base (o : M) (ε : ℝ≥0) : Obligation S M := fun σ κ =>
  Faithful ε σ κ ∧ Radial o σ κ

/-! ### Representability of a fixed source -/

/-- **What an experiment tests.** This source, in this host, under these
    obligations, at radial rate `c`. -/
def Represents (o : M) (ε : ℝ≥0) (𝒜 : Obligation S M) (σ : Source S) (c : ℝ) :
    Prop :=
  ∃ κ : Code S M, Base o ε σ κ ∧ 𝒜 σ κ ∧
    Tendsto κ.radius atTop atTop ∧
    Tendsto (fun R : ℕ => κ.radius R / (R : ℝ)) atTop (𝓝 c)

/-- A stronger obligation cannot make a source representable. -/
theorem Represents.mono {o : M} {ε : ℝ≥0} {𝒜 ℬ : Obligation S M}
    (h : ∀ σ κ, 𝒜 σ κ → ℬ σ κ) {σ : Source S} {c : ℝ} :
    Represents o ε 𝒜 σ c → Represents o ε ℬ σ c := by
  rintro ⟨κ, hb, ha, hdiv, hc⟩
  exact ⟨κ, hb, h σ κ ha, hdiv, hc⟩

/-! ### Host capacity over a declared family -/

/-- **What a theorem classifies.** `β` is achievable in `M` over the source
    family `𝔖`, under obligations `𝒜`, at radial rate `c`. -/
def Achievable (o : M) (ε : ℝ≥0) (𝔖 : Set (Source S)) (𝒜 : Obligation S M)
    (β c : ℝ) : Prop :=
  ∃ σ ∈ 𝔖, σ.HasGrowth β ∧ Represents o ε 𝒜 σ c

/-- **The spine, in the obligation.** More obligation, fewer achievable rates. -/
theorem Achievable.mono_obligation {o : M} {ε : ℝ≥0} {𝔖 : Set (Source S)}
    {𝒜 ℬ : Obligation S M} (h : ∀ σ κ, 𝒜 σ κ → ℬ σ κ) {β c : ℝ} :
    Achievable o ε 𝔖 𝒜 β c → Achievable o ε 𝔖 ℬ β c := by
  rintro ⟨σ, hσ, hg, hr⟩
  exact ⟨σ, hσ, hg, hr.mono h⟩

/-- **The spine, in the family.** A larger family cannot achieve less. -/
theorem Achievable.mono_family {o : M} {ε : ℝ≥0} {𝔖 𝔗 : Set (Source S)}
    (h : 𝔖 ⊆ 𝔗) {𝒜 : Obligation S M} {β c : ℝ} :
    Achievable o ε 𝔖 𝒜 β c → Achievable o ε 𝔗 𝒜 β c := by
  rintro ⟨σ, hσ, hg, hr⟩
  exact ⟨σ, h hσ, hg, hr⟩

/-- Retention is a restriction on the family, so it cannot achieve more. -/
theorem Achievable.retentive_le_all {o : M} {ε : ℝ≥0} {𝒜 : Obligation S M}
    {β c : ℝ} :
    Achievable o ε (retentiveSources : Set (Source S)) 𝒜 β c →
    Achievable o ε allSources 𝒜 β c :=
  Achievable.mono_family retentiveSources_subset_all

/-! ### The base square: every rung meets the packing converse -/

/-- A base-feasible (source, code) pair is a faithful representation. -/
def toFaithful (σ : Source S) (κ : Code S M) {o : M} {ε : ℝ≥0} (hε : 0 < ε)
    (hb : Base o ε σ κ) : Packing.FaithfulRepresentation S o ε where
  histories := σ.census
  address := κ.addr
  radius := κ.radius
  resolution_pos := hε
  histories_nonempty := σ.census_nonempty
  address_injective := fun R => (hb.1 R).1
  separated := fun R => (hb.1 R).2
  contained := hb.2

/-- **The packing converse, at any rung, over any family.** This is what
    connects the profile to `Packing` rather than merely importing it: whatever
    a code additionally honours, its rate obeys `β ≤ c · h_pack`. -/
theorem addressable_of_achievable [ProperSpace M] {o : M} {ε : ℝ≥0} (hε : 0 < ε)
    {𝔖 : Set (Source S)} {𝒜 : Obligation S M} {β c hpack : ℝ}
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack))
    (h : Achievable o ε 𝔖 𝒜 β c) : Capacity.Addressable β c hpack := by
  obtain ⟨σ, _, hg, κ, hb, _, hdiv, hc⟩ := h
  exact Packing.convergent_rate_addressability_limit o ε
    (toFaithful σ κ hε hb) β c hpack hdiv hg hc hpacking

/-! ### Capacity as a set, then as a number -/

/-- The achievable-rate set. Capacity is a set before it is a number. -/
def Rates (o : M) (ε : ℝ≥0) (𝔖 : Set (Source S)) (𝒜 : Obligation S M) (c : ℝ) :
    Set ℝ := {β | Achievable o ε 𝔖 𝒜 β c}

theorem Rates_mono_obligation {o : M} {ε : ℝ≥0} {𝔖 : Set (Source S)}
    {𝒜 ℬ : Obligation S M} (h : ∀ σ κ, 𝒜 σ κ → ℬ σ κ) (c : ℝ) :
    Rates o ε 𝔖 𝒜 c ⊆ Rates o ε 𝔖 ℬ c :=
  fun _ hβ => Achievable.mono_obligation h hβ

theorem Rates_mono_family {o : M} {ε : ℝ≥0} {𝔖 𝔗 : Set (Source S)} (h : 𝔖 ⊆ 𝔗)
    {𝒜 : Obligation S M} (c : ℝ) :
    Rates o ε 𝔖 𝒜 c ⊆ Rates o ε 𝔗 𝒜 c :=
  fun _ hβ => Achievable.mono_family h hβ

/-- **Boundedness is the base square, restated.** Every rate set, at every
    rung, over every family, sits below `c · h_pack`. -/
theorem Rates_subset_Iic [ProperSpace M] {o : M} {ε : ℝ≥0} (hε : 0 < ε)
    {𝔖 : Set (Source S)} {𝒜 : Obligation S M} {c hpack : ℝ}
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack)) :
    Rates o ε 𝔖 𝒜 c ⊆ Set.Iic (c * hpack) :=
  fun _ hβ => addressable_of_achievable hε hpacking hβ

theorem Rates_bddAbove [ProperSpace M] {o : M} {ε : ℝ≥0} (hε : 0 < ε)
    {𝔖 : Set (Source S)} {𝒜 : Obligation S M} {c hpack : ℝ}
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 hpack)) :
    BddAbove (Rates o ε 𝔖 𝒜 c) :=
  ⟨c * hpack, fun _ hβ => Rates_subset_Iic hε hpacking hβ⟩

/-- The scalar capacity, derived from the set. Every dependency is explicit:
    basepoint, resolution, source family, obligation, radial rate. Meaningful
    only where `Rates_bddAbove` applies - a `sSup` of an unbounded real set
    silently returns `0`. -/
noncomputable def capacity (o : M) (ε : ℝ≥0) (𝔖 : Set (Source S))
    (𝒜 : Obligation S M) (c : ℝ) : ℝ := sSup (Rates o ε 𝔖 𝒜 c)

/-- An obligation already implied by base feasibility costs nothing: its rung
    coincides with the block rung. -/
theorem Rates_eq_of_implied_by_base {o : M} {ε : ℝ≥0} {𝔖 : Set (Source S)}
    {𝒜 : Obligation S M} (h : ∀ σ κ, Base o ε σ κ → 𝒜 σ κ) (c : ℝ) :
    Rates o ε 𝔖 𝒜 c = Rates o ε 𝔖 (noExtra : Obligation S M) c := by
  refine Set.Subset.antisymm (Rates_mono_obligation (fun _ _ _ => trivial) c) ?_
  rintro β ⟨σ, hσ, hg, κ, hb, _, hdiv, hc⟩
  exact ⟨σ, hσ, hg, κ, hb, h σ κ hb, hdiv, hc⟩

/-- **The target of a separation theorem.** Two rungs are separated when their
    rate sets differ. OPEN in Lean at every pair: the manuscript's balloon is
    intended to separate the block rung from the relational one, and its
    Theorem 5.3 to collapse them in `ℍⁿ_κ`. Both are PAPER-PROVED. -/
def Separates (o : M) (ε : ℝ≥0) (𝔖 : Set (Source S)) (𝒜 ℬ : Obligation S M)
    (c : ℝ) : Prop := Rates o ε 𝔖 𝒜 c ≠ Rates o ε 𝔖 ℬ c

/-- **The trichotomy's third horn, at every rung.** A host of zero packing
    entropy supports no positive rate under any obligation, over any family,
    at any radial rate whatsoever - no positivity of `c` is needed. -/
theorem not_achievable_pos_of_hpack_zero [ProperSpace M] {o : M} {ε : ℝ≥0}
    (hε : 0 < ε) {𝔖 : Set (Source S)} {𝒜 : Obligation S M} {β c : ℝ}
    (hβ : 0 < β)
    (hpacking : Tendsto (Packing.packingRate o ε) atTop (𝓝 0)) :
    ¬ Achievable o ε 𝔖 𝒜 β c := by
  intro h
  have hb := addressable_of_achievable hε hpacking h
  unfold Capacity.Addressable at hb
  nlinarith

/-! ### Instruments -/

/- The achieved rate `λ = β/c` and the bound in rate form live in `Capacity`:
   they are scalar algebra, not part of the profile. Re-exported for citation. -/
export Capacity (achievedRate achievedRate_le not_addressable_of_lt)

/-- The capacity tax `Γ`: block capacity lost to a structural obligation. -/
noncomputable def tax (Cblock Cclass : ℝ) : ℝ := Cblock - Cclass

/-- Structural availability `θ = C_𝒜 / C_block`.

    DEPENDENCIES. `θ` inherits every argument of `capacity`: basepoint,
    resolution, source family, obligation, radial rate. Whether any may legally
    be suppressed is OPEN - it needs transformation laws under quasi-isometry,
    which are not proved here, and exponential growth rates at FIXED `ε` are
    not expected to be quasi-isometry invariants. A bare `θ(M)` is not yet a
    licensed notation.

    STATUS. Nothing here computes `θ` for a named host. The balloon is intended
    to give `θ = 0` and Theorem 5.3 `θ = 1` for `ℍⁿ_κ`; both are PAPER-PROVED,
    neither is Lean, and `Separates` is inhabited nowhere in this file. -/
noncomputable def availability (Cclass Cblock : ℝ) : ℝ := Cclass / Cblock

theorem tax_nonneg {Cb Cc : ℝ} (h : Cc ≤ Cb) : 0 ≤ tax Cb Cc := sub_nonneg.mpr h

theorem availability_le_one {Cb Cc : ℝ} (hb : 0 < Cb) (h : Cc ≤ Cb) :
    availability Cc Cb ≤ 1 := by
  rw [availability, div_le_one hb]; exact h

theorem availability_nonneg {Cb Cc : ℝ} (hb : 0 < Cb) (hc : 0 ≤ Cc) :
    0 ≤ availability Cc Cb := div_nonneg hc hb.le

theorem tax_eq_of_availability {Cb Cc : ℝ} (hb : 0 < Cb) :
    tax Cb Cc = Cb * (1 - availability Cc Cb) := by
  rw [tax, availability]; field_simp

/-! ### Regression test: why `Base` is compulsory

`Code.radius` is a free field, unrelated to where `addr` puts anything. Without
base feasibility a code may map every history to a single point and still
declare radii growing at rate `c`. Below, `Unit` is a ONE-POINT metric space -
nothing in it is distinguishable from anything else - and the rate conditions
alone report `log 2` nats of retained history per generative step, at any radial
rate whatsoever.

An earlier version of this file omitted `Base` from the achievability
definition, and this example typechecked against it. It is kept so that the
mistake cannot recur silently. -/

/-- The rate conditions in isolation, with no base feasibility. -/
private def RatesOnly (σ : Source ℕ) (κ : Code ℕ Unit) (β c : ℝ) : Prop :=
  σ.HasGrowth β ∧
  Tendsto (fun R : ℕ => κ.radius R / (R : ℝ)) atTop (𝓝 c)

/-- A one-point host "achieves" `log 2` nats per step once base feasibility is
    dropped. This is the failure `Base` exists to exclude. -/
theorem vacuity_without_base (c : ℝ) :
    ∃ (σ : Source ℕ) (κ : Code ℕ Unit), RatesOnly σ κ (Real.log 2) c := by
  refine ⟨⟨fun R => Finset.range (2 ^ R), fun R => ⟨0, Finset.mem_range.mpr ?_⟩⟩,
          ⟨fun _ _ => (), fun R => c * R⟩, ?_, ?_⟩
  · positivity
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (0:ℝ) < R := by exact_mod_cast hR
    simp only [Finset.card_range]
    rw [show (((2:ℕ) ^ R : ℕ) : ℝ) = (2:ℝ) ^ R by push_cast; ring, Real.log_pow]
    field_simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hR' : (0:ℝ) < R := by exact_mod_cast hR
    field_simp

/-- **The repair, verified.** With `Base` in force, the same one-point host
    admits only the rate `0`: faithful addressing into a single point forces
    every census to be a singleton. The contrast with `vacuity_without_base`,
    which reports `log 2` on the very same host, is the whole content of the
    fix. -/
theorem unit_host_only_zero (o : Unit) (ε : ℝ≥0) (𝔖 : Set (Source ℕ))
    (𝒜 : Obligation ℕ Unit) (β c : ℝ)
    (h : Achievable o ε 𝔖 𝒜 β c) : β = 0 := by
  obtain ⟨σ, _, hg, κ, hb, _, _, _⟩ := h
  have hcard : ∀ R, (σ.census R).card = 1 := by
    intro R
    have hinj : Set.InjOn (κ.addr R) (σ.census R : Set ℕ) := (hb.1 R).1
    have hsub : (σ.census R : Set ℕ).Subsingleton := fun a ha b hb' =>
      hinj ha hb' (by rfl)
    obtain ⟨x, hx⟩ := σ.census_nonempty R
    have hone : σ.census R = {x} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hx, fun y hy => hsub (by exact_mod_cast hy) (by exact_mod_cast hx)⟩
    rw [hone, Finset.card_singleton]
  have hzero : Tendsto (fun R : ℕ => Real.log ((σ.census R).card : ℝ) / (R : ℝ))
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with R
    rw [hcard R]; simp
  exact tendsto_nhds_unique hg hzero

end ActiveGeometry.Constrained
