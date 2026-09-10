/-
  The balloon, against the ULF tree class
  ======================================

  Exponential room, no quasi-isometric copy of a uniformly locally finite
  binary tree. Block codes still fit. The source is the same class as the
  paper's Theorem 5.3: finite-rate generation on a bounded-valence unit-edge
  tree.
-/

import ActiveGeometry.Constrained
import Mathlib.Data.Nat.Dist

namespace ActiveGeometry.Constrained

open Filter
open scoped ENNReal NNReal Topology

/-! ### Host: a ray of hubs, each carrying an exponential star -/

inductive Balloon where
  | hub : ℕ → Balloon
  | leaf : (n : ℕ) → Fin (2 ^ n) → Balloon
deriving DecidableEq

open Balloon

/-- Graph distance on a ray of stars. Leaves at one hub are compared by
    `Fin.val`, so the two `Fin` types need not be definitionally equal. -/
def balloonNDist : Balloon → Balloon → ℕ
  | hub i, hub j => Nat.dist i j
  | hub i, leaf j _ => Nat.dist i j + 1
  | leaf i _, hub j => Nat.dist i j + 1
  | leaf i a, leaf j b =>
      if i = j then (if a.val = b.val then 0 else 2) else Nat.dist i j + 2

theorem balloonNDist_comm (x y : Balloon) :
    balloonNDist x y = balloonNDist y x := by
  cases x with
  | hub i =>
      cases y with
      | hub j => simp [balloonNDist, Nat.dist_comm]
      | leaf n a => simp [balloonNDist, Nat.dist_comm]
  | leaf n a =>
      cases y with
      | hub j => simp [balloonNDist, Nat.dist_comm]
      | leaf m b =>
          simp only [balloonNDist, Nat.dist_comm]
          split_ifs <;> simp_all [eq_comm]

theorem balloonNDist_self (x : Balloon) : balloonNDist x x = 0 := by
  cases x with
  | hub i => simp [balloonNDist]
  | leaf n a => simp [balloonNDist]

theorem balloonNDist_triangle (x y z : Balloon) :
    balloonNDist x z ≤ balloonNDist x y + balloonNDist y z := by
  cases x <;> cases y <;> cases z
  all_goals
    simp [balloonNDist]
    unfold Nat.dist
    first | (split_ifs <;> omega) | omega

noncomputable instance : MetricSpace Balloon where
  dist x y := balloonNDist x y
  dist_self x := by exact_mod_cast balloonNDist_self x
  dist_comm x y := by exact_mod_cast balloonNDist_comm x y
  dist_triangle x y z := by exact_mod_cast balloonNDist_triangle x y z
  eq_of_dist_eq_zero {x y} h := by
    have hz : balloonNDist x y = 0 := by exact_mod_cast h
    cases x with
    | hub i =>
        cases y with
        | hub j =>
            simp [balloonNDist] at hz
            exact congrArg hub (Nat.eq_of_dist_eq_zero hz)
        | leaf n a =>
            simp [balloonNDist] at hz
    | leaf n a =>
        cases y with
        | hub j =>
            simp [balloonNDist] at hz
        | leaf m b =>
            simp [balloonNDist] at hz
            by_cases hi : n = m
            · subst hi
              by_cases hv : a.val = b.val
              · exact congrArg (leaf n) (Fin.ext hv)
              · simp [hv] at hz
            · simp [hi] at hz

def hubIndex : Balloon → ℕ
  | hub n => n
  | leaf n _ => n

theorem balloonNDist_le_two_of_hubIndex_eq {x y : Balloon}
    (h : hubIndex x = hubIndex y) : balloonNDist x y ≤ 2 := by
  cases x with
  | hub i =>
      cases y with
      | hub j => simp [balloonNDist, hubIndex] at h ⊢; simp [h]
      | leaf n a => simp [balloonNDist, hubIndex] at h ⊢; simp [h]
  | leaf n a =>
      cases y with
      | hub j => simp [balloonNDist, hubIndex] at h ⊢; simp [h]
      | leaf m b =>
          simp [balloonNDist, hubIndex] at h ⊢
          subst h
          split_ifs <;> omega

theorem balloonNDist_hub0_hub (n : ℕ) : balloonNDist (hub 0) (hub n) = n := by
  simp [balloonNDist, Nat.dist_zero_left]

theorem balloonNDist_hub0_leaf (n : ℕ) (a : Fin (2 ^ n)) :
    balloonNDist (hub 0) (leaf n a) = n + 1 := by
  simp [balloonNDist, Nat.dist_zero_left]

theorem hubIndex_le_dist_hub0 (x : Balloon) :
    hubIndex x ≤ balloonNDist (hub 0) x := by
  cases x with
  | hub n => simp [hubIndex, balloonNDist_hub0_hub]
  | leaf n a => simp [hubIndex, balloonNDist_hub0_leaf]

/-- Pairwise distance `> 2` forces distinct hubs, so a ball of radius `ρ`
    holds at most `⌊ρ⌋₊ + 1` such points. -/
theorem card_pairwise_gt_two_le_floor {ρ : ℝ} {s : Finset Balloon}
    (hsub : (s : Set Balloon) ⊆ Metric.closedBall (hub 0) ρ)
    (hfar : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 2 < balloonNDist a b) :
    s.card ≤ ⌊ρ⌋₊ + 1 := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨x0, hx0⟩ := hs
    have hρ : 0 ≤ ρ := by
      have hmem := hsub (by exact_mod_cast hx0)
      have hle : dist (hub 0) x0 ≤ ρ := by
        simpa [Metric.mem_closedBall, dist_comm] using hmem
      exact dist_nonneg.trans hle
    have hinj : Set.InjOn hubIndex (s : Set Balloon) := by
      intro a ha b hb hidx
      by_contra hne
      exact (not_lt_of_ge (balloonNDist_le_two_of_hubIndex_eq hidx))
        (hfar a (by exact_mod_cast ha) b (by exact_mod_cast hb) hne)
    have hidx : ∀ a ∈ s, hubIndex a < ⌊ρ⌋₊ + 1 := by
      intro a ha
      have hmem := hsub (by exact_mod_cast ha)
      have hle : (balloonNDist (hub 0) a : ℝ) ≤ ρ := by
        simpa [Metric.mem_closedBall, dist, balloonNDist_comm (hub 0) a] using hmem
      have : (hubIndex a : ℝ) ≤ ρ :=
        (Nat.cast_le.mpr (hubIndex_le_dist_hub0 a)).trans hle
      exact Nat.lt_succ_of_le ((Nat.le_floor_iff hρ).mpr this)
    have hf : (s.image hubIndex).card = s.card :=
      Finset.card_image_of_injOn (fun a ha b hb h =>
        hinj (by exact_mod_cast ha) (by exact_mod_cast hb) h)
    have hsubI : s.image hubIndex ⊆ Finset.range (⌊ρ⌋₊ + 1) := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
      exact Finset.mem_range.mpr (hidx a ha)
    simpa [hf, Finset.card_range] using Finset.card_le_card hsubI
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [this]

/-! ### ULF unit-edge binary tree -/

def lcp : List Bool → List Bool → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys => if x = y then lcp xs ys + 1 else 0

theorem lcp_comm (u v : List Bool) : lcp u v = lcp v u := by
  induction u generalizing v with
  | nil => cases v <;> simp [lcp]
  | cons x xs ih =>
      cases v with
      | nil => simp [lcp]
      | cons y ys =>
          by_cases h : x = y
          · simp [lcp, h, ih]
          · have : ¬ y = x := fun h' => h h'.symm
            simp [lcp, h, this]

theorem lcp_le_length_left (u v : List Bool) : lcp u v ≤ u.length := by
  induction u generalizing v with
  | nil => simp [lcp]
  | cons x xs ih =>
      cases v with
      | nil => simp [lcp]
      | cons y ys =>
          by_cases h : x = y
          · simp [lcp, h]; exact ih ys
          · simp [lcp, h]

theorem lcp_le_length_right (u v : List Bool) : lcp u v ≤ v.length := by
  rw [lcp_comm]; exact lcp_le_length_left _ _

def treeNDist (u v : List Bool) : ℕ :=
  u.length + v.length - 2 * lcp u v

theorem lcp_self (u : List Bool) : lcp u u = u.length := by
  induction u with
  | nil => simp [lcp]
  | cons x xs ih => simp [lcp, ih]

theorem treeNDist_self (u : List Bool) : treeNDist u u = 0 := by
  simp [treeNDist, lcp_self, two_mul]

theorem treeNDist_comm (u v : List Bool) : treeNDist u v = treeNDist v u := by
  simp [treeNDist, lcp_comm, add_comm]

theorem lcp_triangle (u w v : List Bool) :
    lcp u w + lcp w v ≤ w.length + lcp u v := by
  induction w generalizing u v with
  | nil =>
      cases u <;> simp [lcp]
  | cons x xs ih =>
      cases u with
      | nil =>
          simpa [lcp] using lcp_le_length_left (x :: xs) v
      | cons a as =>
          cases v with
          | nil =>
              have := lcp_le_length_left (x :: xs) (a :: as)
              simp [lcp, eq_comm, lcp_comm] at this ⊢
              exact this
          | cons b bs =>
              by_cases hax : a = x
              · by_cases hbx : b = x
                · have hab : a = b := hax.trans hbx.symm
                  have := ih as bs
                  simp [lcp, hax, hbx]
                  linarith
                · have hxb : ¬ x = b := mt Eq.symm hbx
                  have hab : ¬ a = b := fun h => hbx (h ▸ hax)
                  simp [lcp, hax, hxb]
                  exact lcp_le_length_right as xs
              · by_cases hbx : b = x
                · have hab : ¬ a = b := fun h => hax (h.trans hbx)
                  simp [lcp, hax, hbx]
                  exact lcp_le_length_left xs bs
                · have hxb : ¬ x = b := mt Eq.symm hbx
                  simp [lcp, hax, hxb]

theorem treeNDist_triangle (u w v : List Bool) :
    treeNDist u v ≤ treeNDist u w + treeNDist w v := by
  have htri := lcp_triangle u w v
  have := lcp_le_length_left u v
  have := lcp_le_length_left u w
  have := lcp_le_length_left w v
  have := lcp_le_length_right u v
  have := lcp_le_length_right u w
  have := lcp_le_length_right w v
  simp only [treeNDist]
  omega

theorem eq_of_lcp_eq_length {u v : List Bool}
    (hlcp : lcp u v = u.length) (hlen : u.length = v.length) : u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons => simp at hlen
  | cons a as ih =>
      cases v with
      | nil => simp at hlen
      | cons b bs =>
          by_cases hab : a = b
          · subst hab
            simp [lcp] at hlcp
            have hl : lcp as bs = as.length := by omega
            have hs : as.length = bs.length := by simp at hlen; omega
            exact congrArg (List.cons a) (ih hl hs)
          · simp [lcp, hab] at hlcp

theorem eq_of_treeNDist_eq_zero {u v : List Bool} (h : treeNDist u v = 0) :
    u = v := by
  have hle : 2 * lcp u v ≤ u.length + v.length := by
    have := lcp_le_length_left u v
    have := lcp_le_length_right u v
    omega
  have hsum : u.length + v.length = 2 * lcp u v := by
    simp [treeNDist] at h
    omega
  have hlen : u.length = v.length := by
    have := lcp_le_length_left u v
    have := lcp_le_length_right u v
    omega
  have hlcp : lcp u v = u.length := by omega
  exact eq_of_lcp_eq_length hlcp hlen

noncomputable instance : MetricSpace (List Bool) where
  dist u v := treeNDist u v
  dist_self u := by exact_mod_cast treeNDist_self u
  dist_comm u v := by exact_mod_cast treeNDist_comm u v
  dist_triangle u v w := by exact_mod_cast treeNDist_triangle u v w
  eq_of_dist_eq_zero {u v} h :=
    eq_of_treeNDist_eq_zero (by exact_mod_cast h)

def wordsOfLength : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 =>
      (wordsOfLength n).image (fun w => false :: w) ∪
        (wordsOfLength n).image (fun w => true :: w)

theorem mem_wordsOfLength {n : ℕ} {w : List Bool} :
    w ∈ wordsOfLength n ↔ w.length = n := by
  induction n generalizing w with
  | zero =>
      constructor
      · intro h; simp [wordsOfLength] at h; simp [h]
      · intro h
        simp [wordsOfLength, List.length_eq_zero_iff.mp h]
  | succ n ih =>
      constructor
      · intro h
        simp only [wordsOfLength, Finset.mem_union, Finset.mem_image] at h
        rcases h with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
        · simp [ih.mp hu]
        · simp [ih.mp hu]
      · intro hlen
        match w with
        | [] => simp at hlen
        | b :: rest =>
            have hr : rest.length = n := by simp at hlen; omega
            have hr' := ih.mpr hr
            simp only [wordsOfLength, Finset.mem_union, Finset.mem_image]
            cases b
            · exact Or.inl ⟨rest, hr', rfl⟩
            · exact Or.inr ⟨rest, hr', rfl⟩

theorem card_wordsOfLength (n : ℕ) : (wordsOfLength n).card = 2 ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
      have hdis :
          Disjoint ((wordsOfLength n).image (fun w => false :: w))
            ((wordsOfLength n).image (fun w => true :: w)) := by
        refine Finset.disjoint_iff_ne.mpr ?_
        intro x hx y hy hxy
        subst hxy
        simp only [Finset.mem_image] at hx hy
        rcases hx with ⟨_, _, rfl⟩
        rcases hy with ⟨_, _, h⟩
        cases h
      have hf : Function.Injective fun w : List Bool => false :: w :=
        fun _ _ h => (List.cons_inj_right false).mp h
      have ht : Function.Injective fun w : List Bool => true :: w :=
        fun _ _ h => (List.cons_inj_right true).mp h
      rw [wordsOfLength, Finset.card_union_of_disjoint hdis,
        Finset.card_image_of_injective _ hf,
        Finset.card_image_of_injective _ ht, ih]
      ring

/-- Generation-`R` vertices of the rooted unit-edge binary tree. This is a
    uniformly locally finite tree source: the same class Theorem 5.3 uses. -/
def binaryTreeSource : Source (List Bool) where
  census := wordsOfLength
  census_nonempty n :=
    ⟨List.replicate n false, mem_wordsOfLength.mpr (by simp)⟩

theorem binaryTreeSource_ulf : binaryTreeSource.ULF :=
  ⟨2, by norm_num, fun R => by
    simp [binaryTreeSource, card_wordsOfLength, pow_succ, mul_comm]⟩

theorem binaryTreeSource_mem_ulf : binaryTreeSource ∈ ulfSources :=
  binaryTreeSource_ulf

theorem binaryTreeSource_hasGrowth :
    binaryTreeSource.HasGrowth (Real.log 2) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hR)
  simp only [binaryTreeSource, card_wordsOfLength]
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  exact (mul_div_cancel_left₀ (Real.log 2) hR').symm

/-! ### Block achievability by depthwise recoding onto stars -/

noncomputable def wordToLeaf {R : ℕ} (w : List Bool)
    (hw : w ∈ wordsOfLength R) : Balloon :=
  leaf R <|
    Fin.cast (card_wordsOfLength R)
      ((wordsOfLength R).equivFin ⟨w, hw⟩)

noncomputable def balloonBlockCode : Code (List Bool) Balloon where
  addr R w :=
    if hw : w ∈ wordsOfLength R then wordToLeaf w hw else hub 0
  radius R := (R : ℝ) + 1

theorem wordToLeaf_injective {R : ℕ} {u v : List Bool}
    (hu : u ∈ wordsOfLength R) (hv : v ∈ wordsOfLength R)
    (h : wordToLeaf u hu = wordToLeaf v hv) : u = v := by
  unfold wordToLeaf at h
  have hfin : Fin.cast (card_wordsOfLength R)
      ((wordsOfLength R).equivFin ⟨u, hu⟩) =
      Fin.cast (card_wordsOfLength R)
        ((wordsOfLength R).equivFin ⟨v, hv⟩) := by
    simpa using Balloon.leaf.inj h
  have := (Fin.cast_injective (card_wordsOfLength R)) hfin
  have : (⟨u, hu⟩ : { x // x ∈ wordsOfLength R }) = ⟨v, hv⟩ :=
    (wordsOfLength R).equivFin.injective this
  simpa using this

theorem balloonNDist_wordToLeaf {R : ℕ} {u v : List Bool}
    (hu : u ∈ wordsOfLength R) (hv : v ∈ wordsOfLength R) (hne : u ≠ v) :
    balloonNDist (wordToLeaf u hu) (wordToLeaf v hv) = 2 := by
  have hval_ne :
      ((wordsOfLength R).equivFin ⟨u, hu⟩).val ≠
        ((wordsOfLength R).equivFin ⟨v, hv⟩).val := by
    intro h
    have := (wordsOfLength R).equivFin.injective (Fin.ext h)
    exact hne (by simpa using this)
  simp [wordToLeaf, balloonNDist, hval_ne]

theorem balloonBlockCode_base :
    Base (hub 0) 1 binaryTreeSource balloonBlockCode := by
  constructor
  · intro R
    constructor
    · intro u hu v hv haddr
      have hu' : u ∈ wordsOfLength R := by simpa [binaryTreeSource] using hu
      have hv' : v ∈ wordsOfLength R := by simpa [binaryTreeSource] using hv
      simp [balloonBlockCode, hu', hv'] at haddr
      exact wordToLeaf_injective hu' hv' haddr
    · intro x hx y hy hne
      rcases (Set.mem_image _ _ _).1 hx with ⟨u, hu, rfl⟩
      rcases (Set.mem_image _ _ _).1 hy with ⟨v, hv, rfl⟩
      have hu' : u ∈ wordsOfLength R := by simpa [binaryTreeSource] using hu
      have hv' : v ∈ wordsOfLength R := by simpa [binaryTreeSource] using hv
      have hne' : u ≠ v := by
        intro rfl
        exact hne rfl
      have huaddr : balloonBlockCode.addr R u = wordToLeaf u hu' := by
        simp [balloonBlockCode, hu']
      have hvaddr : balloonBlockCode.addr R v = wordToLeaf v hv' := by
        simp [balloonBlockCode, hv']
      have hd : balloonNDist (wordToLeaf u hu') (wordToLeaf v hv') = 2 :=
        balloonNDist_wordToLeaf hu' hv' hne'
      have : (1 : ℝ≥0∞) < edist (balloonBlockCode.addr R u)
          (balloonBlockCode.addr R v) := by
        rw [huaddr, hvaddr, edist_dist]
        have hdR : dist (wordToLeaf u hu') (wordToLeaf v hv') = 2 := by
          change (balloonNDist (wordToLeaf u hu') (wordToLeaf v hv') : ℝ) = 2
          exact_mod_cast hd
        simp [hdR]
      simpa [book] using this
  · intro R x hx
    rcases (Set.mem_image _ _ _).1 hx with ⟨w, hw, rfl⟩
    have hw' : w ∈ wordsOfLength R := by simpa [binaryTreeSource] using hw
    simp [balloonBlockCode, hw', Metric.mem_closedBall, dist, wordToLeaf]
    rw [balloonNDist_comm, balloonNDist_hub0_leaf]
    exact_mod_cast le_rfl

theorem balloonBlockCode_represents :
    Represents (hub 0) 1 (noExtra : Obligation (List Bool) Balloon)
      binaryTreeSource 1 := by
  refine ⟨balloonBlockCode, balloonBlockCode_base, trivial, ?_, ?_⟩
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · have hfun :
        (fun R : ℕ => balloonBlockCode.radius R / (R : ℝ)) =ᶠ[atTop]
          fun R => (1 : ℝ) + (R : ℝ)⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with R hR
      have hR' : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hR)
      simp [balloonBlockCode]
      field_simp
    exact Tendsto.congr' hfun.symm <| by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
          (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)

theorem binaryTree_block_achievable :
    Achievable (hub 0) 1 {binaryTreeSource}
      (noExtra : Obligation (List Bool) Balloon) (Real.log 2) 1 :=
  ⟨binaryTreeSource, by simp, binaryTreeSource_hasGrowth, balloonBlockCode_represents⟩

/-- The same block code, read over the ULF class rather than the singleton. -/
theorem binaryTree_block_achievable_ulf :
    Achievable (hub 0) 1 (ulfSources : Set (Source (List Bool)))
      (noExtra : Obligation (List Bool) Balloon) (Real.log 2) 1 :=
  binaryTree_block_achievable.mono_family (by
    intro σ hσ
    simp only [Set.mem_singleton_iff] at hσ
    subst σ
    exact binaryTreeSource_mem_ulf)

/-! ### Relational obstruction -/

theorem lcp_lt_length_of_ne {u v : List Bool}
    (hlen : u.length = v.length) (huv : u ≠ v) : lcp u v < u.length := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => exact (huv rfl).elim
      | cons => simp at hlen
  | cons a as ih =>
      cases v with
      | nil => simp at hlen
      | cons b bs =>
          simp only [lcp]
          by_cases hab : a = b
          · subst hab
            have hne : as ≠ bs := fun h => huv (by simp [h])
            have hs : as.length = bs.length := by simp at hlen; omega
            have := ih hs hne
            simp; omega
          · simp [hab]

theorem lcp_append_replicate_of_ne {u v : List Bool} {L : ℕ}
    (huv : u ≠ v) (hlen : u.length = v.length) :
    lcp (u ++ List.replicate L false) (v ++ List.replicate L false) =
      lcp u v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => exact (huv rfl).elim
      | cons => simp at hlen
  | cons a as ih =>
      cases v with
      | nil => simp at hlen
      | cons b bs =>
          have hlen' : as.length = bs.length := by simp at hlen; omega
          simp only [List.cons_append, lcp]
          by_cases hab : a = b
          · subst hab
            have hne : as ≠ bs := fun h => huv (congrArg (List.cons a) h)
            simp [ih hne hlen']
          · simp [hab]

/-- Distinct equal-length words, padded by a common tail, remain at least
    `2(L+1)` apart in the tree. -/
theorem treeNDist_append_false {u v : List Bool} {L : ℕ}
    (huv : u ≠ v) (hlen : u.length = v.length) :
    2 * (L + 1) ≤
      treeNDist (u ++ List.replicate L false)
        (v ++ List.replicate L false) := by
  have hlcp := lcp_append_replicate_of_ne (L := L) huv hlen
  have hlt := lcp_lt_length_of_ne hlen huv
  have := lcp_le_length_left u v
  have := lcp_le_length_right u v
  simp [treeNDist, hlcp, List.length_append, List.length_replicate, hlen]
  omega

def paddedWords (k L : ℕ) : Finset (List Bool) :=
  (wordsOfLength k).image (fun w => w ++ List.replicate L false)

theorem paddedWords_injOn (k L : ℕ) :
    Set.InjOn (fun w : List Bool => w ++ List.replicate L false)
      (wordsOfLength k) := by
  intro a ha b hb h
  exact List.append_left_injective (List.replicate L false) h

theorem paddedWords_card (k L : ℕ) : (paddedWords k L).card = 2 ^ k := by
  simpa [paddedWords, card_wordsOfLength] using
    Finset.card_image_of_injOn (paddedWords_injOn k L)

theorem paddedWords_mem_census {k L : ℕ} {w : List Bool}
    (hw : w ∈ paddedWords k L) :
    w ∈ binaryTreeSource.census (k + L) := by
  simp only [paddedWords, Finset.mem_image] at hw
  rcases hw with ⟨u, hu, rfl⟩
  have : (u ++ List.replicate L false).length = k + L := by
    simp [mem_wordsOfLength.mp hu]
  exact mem_wordsOfLength.mpr this

theorem two_pow_linear_lt (n L : ℕ) :
    2 * n + 4 * L + 11 < 2 ^ (n + L + 5) := by
  induction n generalizing L with
  | zero =>
      induction L with
      | zero => decide
      | succ L ih =>
          have hpow : 2 ^ (0 + (L + 1) + 5) = 2 * 2 ^ (0 + L + 5) := by
            rw [show 0 + (L + 1) + 5 = (0 + L + 5) + 1 by omega, pow_succ, mul_comm]
          rw [hpow]
          omega
  | succ n ih =>
      have := ih L
      have hpow : 2 ^ (n + 1 + L + 5) = 2 * 2 ^ (n + L + 5) := by
        rw [show n + 1 + L + 5 = (n + L + 5) + 1 by omega, pow_succ, mul_comm]
      rw [hpow]
      omega

/-- Exponential prefixes outgrow the linear number of hubs in a ball. -/
theorem two_pow_gt_hub_bound (n0 L : ℕ) :
    2 * ((n0 + L + 5) + L) + 1 < 2 ^ (n0 + L + 5) := by
  have heq : 2 * ((n0 + L + 5) + L) + 1 = 2 * n0 + 4 * L + 11 := by ring
  rw [heq]
  exact two_pow_linear_lt n0 L

/-- No lawful quasi-isometric coding of the ULF binary tree into the balloon
    at radial rate `1`. Block coding of the same source still works. -/
theorem binaryTree_not_relational (q : Distortion) :
    ¬ Achievable (hub 0) 1 {binaryTreeSource}
      (Relational q : Obligation (List Bool) Balloon) (Real.log 2) 1 := by
  rintro ⟨σ, hσ, _, κ, hb, hrel, hdiv, hc⟩
  have hsigma : σ = binaryTreeSource := by simpa using hσ
  subst σ
  have hDpos : 0 < q.multiplicative :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) q.one_le_multiplicative
  have hDinv : 0 < q.multiplicative⁻¹ := inv_pos.mpr hDpos
  -- Choose a padding long enough that tree-distance `2(L+1)` forces host
  -- distance strictly greater than 2, after lawful distortion `(D, K)`.
  let L : ℕ := Nat.ceil (q.multiplicative * (q.additive + 3)) + 1
  have hLreal : q.multiplicative * (q.additive + 3) ≤ L := by
    have hceil : q.multiplicative * (q.additive + 3) ≤
        Nat.ceil (q.multiplicative * (q.additive + 3)) := Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast Nat.le_add_right _ 1)
  have hcancel :
      q.multiplicative⁻¹ * (2 * (q.multiplicative * (q.additive + 3))) =
        2 * (q.additive + 3) := by
    calc
      q.multiplicative⁻¹ * (2 * (q.multiplicative * (q.additive + 3)))
          = (q.multiplicative⁻¹ * q.multiplicative) * (2 * (q.additive + 3)) := by
            ring
      _ = 1 * (2 * (q.additive + 3)) := by
            rw [inv_mul_cancel₀ (ne_of_gt hDpos)]
      _ = 2 * (q.additive + 3) := by ring
  have hfar : q.multiplicative⁻¹ * (2 * (L + 1 : ℝ)) - q.additive > 2 := by
    have hmono : q.multiplicative⁻¹ * (2 * (q.multiplicative * (q.additive + 3))) ≤
        q.multiplicative⁻¹ * (2 * (L : ℝ)) := by
      nlinarith [hDinv, hLreal]
    nlinarith [hcancel, hmono, hDinv, q.additive_nonneg]
  have hEv : ∀ᶠ R in atTop, κ.radius R < 2 * (R : ℝ) ∧ 0 < R ∧ 0 ≤ κ.radius R := by
    have hball := hc.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hball, eventually_gt_atTop 0,
      hdiv.eventually (Ioi_mem_atTop (0 : ℝ))] with R hmem hR hpos
    have habs : |κ.radius R / (R : ℝ) - 1| < 1 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hmem
    have hlt : κ.radius R / (R : ℝ) < 2 := by
      have := abs_lt.mp habs
      linarith
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    exact ⟨(div_lt_iff₀ hRpos).mp hlt, hR, le_of_lt hpos⟩
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hEv
  let k := n0 + L + 5
  let R := k + L
  have hRge : n0 ≤ R := by omega
  have hEvR := hn0 R hRge
  have hcard : 2 * R + 1 < 2 ^ k := by
    simpa [k, R] using two_pow_gt_hub_bound n0 L
  have hpads : paddedWords k L ⊆ binaryTreeSource.census R := by
    intro w hw
    simpa [R] using paddedWords_mem_census hw
  have hinj : Set.InjOn (κ.addr R) (paddedWords k L : Set (List Bool)) :=
    ((hb.1 R).1).mono (by exact_mod_cast hpads)
  let s : Finset Balloon := (paddedWords k L).image (κ.addr R)
  have hscard : s.card = 2 ^ k := by
    rw [show s = (paddedWords k L).image (κ.addr R) from rfl,
      Finset.card_image_of_injOn (fun a ha b hb h =>
        hinj (by exact_mod_cast ha) (by exact_mod_cast hb) h),
      paddedWords_card]
  have hsub : (s : Set Balloon) ⊆ Metric.closedBall (hub 0) (κ.radius R) := by
    intro x hx
    have hx' : x ∈ (paddedWords k L).image (κ.addr R) := by simpa [s] using hx
    rcases Finset.mem_image.mp hx' with ⟨w, hw, rfl⟩
    exact hb.2 R (Set.mem_image_of_mem _ (hpads hw))
  have hfarS : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 2 < balloonNDist a b := by
    intro a ha b hb hne
    have ha' : a ∈ (paddedWords k L).image (κ.addr R) := by simpa [s] using ha
    have hb' : b ∈ (paddedWords k L).image (κ.addr R) := by simpa [s] using hb
    rcases Finset.mem_image.mp ha' with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hb' with ⟨v, hv, rfl⟩
    have hne' : u ≠ v := by
      intro rfl
      exact hne rfl
    have hu' := hpads hu
    have hv' := hpads hv
    obtain ⟨u0, hu0, rfl⟩ := Finset.mem_image.mp (show u ∈ paddedWords k L from hu)
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.mp (show v ∈ paddedWords k L from hv)
    have hlen0 : u0.length = v0.length :=
      (mem_wordsOfLength.mp hu0).trans (mem_wordsOfLength.mp hv0).symm
    have hne0 : u0 ≠ v0 := fun h => hne' (by simp [h])
    have htree : 2 * (L + 1) ≤
        treeNDist (u0 ++ List.replicate L false)
          (v0 ++ List.replicate L false) :=
      treeNDist_append_false hne0 hlen0
    have hreluv := hrel R _ hu' _ hv'
    have hdist :
        (2 * (L + 1) : ℝ) ≤
          dist (u0 ++ List.replicate L false)
            (v0 ++ List.replicate L false) := by
      change (2 * (L + 1) : ℝ) ≤
        (treeNDist (u0 ++ List.replicate L false)
          (v0 ++ List.replicate L false) : ℝ)
      exact_mod_cast htree
    have hhost :
        2 < dist (κ.addr R (u0 ++ List.replicate L false))
          (κ.addr R (v0 ++ List.replicate L false)) := by
      have := hreluv.1
      nlinarith [hDinv, hfar, hdist, q.additive_nonneg]
    have : 2 < balloonNDist (κ.addr R (u0 ++ List.replicate L false))
        (κ.addr R (v0 ++ List.replicate L false)) := by
      have hR : (2 : ℝ) <
          (balloonNDist (κ.addr R (u0 ++ List.replicate L false))
            (κ.addr R (v0 ++ List.replicate L false)) : ℝ) := by
        simpa [dist] using hhost
      exact Nat.cast_lt.mp hR
    simpa using this
  have hle := card_pairwise_gt_two_le_floor (ρ := κ.radius R) hsub hfarS
  have hfloor : (⌊κ.radius R⌋₊ : ℝ) ≤ κ.radius R := Nat.floor_le hEvR.2.2
  have hscardR : (s.card : ℝ) ≤ κ.radius R + 1 := by
    have : (s.card : ℝ) ≤ (⌊κ.radius R⌋₊ + 1 : ℝ) := by exact_mod_cast hle
    linarith
  have : (2 ^ k : ℝ) < 2 * (R : ℝ) + 1 := by
    have hk : (2 ^ k : ℝ) = (s.card : ℝ) := by simp [hscard]
    linarith [hEvR.1]
  have hnat : 2 ^ k < 2 * R + 1 := by exact_mod_cast this
  exact (lt_irrefl _ (hnat.trans hcard))

/-- **Geometric profile separation, on the ULF tree class of Theorem 5.3.**
    The balloon admits the binary tree at the block rung and rejects every
    lawful quasi-isometric coding of the same source. -/
theorem balloon_separates (q : Distortion) :
    Separates (hub 0) 1 {binaryTreeSource}
      (noExtra : Obligation (List Bool) Balloon)
      (Relational q) 1 := by
  intro heq
  have hblock :
      (Real.log 2) ∈ Rates (hub 0) 1 {binaryTreeSource}
        (noExtra : Obligation (List Bool) Balloon) 1 :=
    binaryTree_block_achievable
  rw [heq] at hblock
  exact binaryTree_not_relational q hblock

end ActiveGeometry.Constrained
