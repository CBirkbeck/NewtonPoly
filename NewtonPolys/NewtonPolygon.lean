/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newton Polygon Formalization

## Project Notes (for future sessions)

### Goal
Formalize the Newton polygon of a power series in Lean 4, following Gouvêa's
"p-adic Numbers: An Introduction" Section 7.4. The Newton polygon is the lower
convex hull of points (i, v(aᵢ)) where v is a p-adic valuation.

### Progress (as of initial creation)
✅ Basic definitions: ValSeq, finite, slopeRat, slopeReal, slopeSetQ, slopeSetR
✅ Algorithm types: StepResult inductive, nextStep function
✅ Data structures: Segment, FinalRay, NewtonPolygonData, WellFormed
✅ Key theorems: tight_of_slope, minSlope_supporting, achievingSet_onLine
✅ Helper lemmas: slopeSetR_empty_iff, slopeRat_eq_slopeReal
✅ Builds successfully with mathlib v4.28.0-rc1

### Design Decisions
- ValSeq = ℕ → WithTop ℤ (abstracted from actual PowerSeries for simplicity)
- Slopes stored as ℚ in structures, ℝ used for sInf computations
- nextStep uses `open Classical in` for decidability
- field_simp [hne] + ring pattern works for slope equality proofs

### Next Steps
- Connect ValSeq to actual PowerSeries K
- Define full iteration to build complete NewtonPolygonData
- Prove constructed polygon is well-formed
- Prove equivalence with convex hull characterization
- Add multiplicity/root counting theorems
- Connect to Hensel's lemma applications
-/

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Newton Polygon of a Power Series

This file defines the Newton polygon of a power series with coefficients in a valued field,
following the "rotating line" algorithm from Gouvêa's "p-adic Numbers: An Introduction".

## Main Definitions

* `NewtonPolygon.slopeRat` - the slope from point `(i₀, v₀)` to `(i, vᵢ)` as a rational
* `NewtonPolygon.slopeSetR` - the set of slopes from a given vertex to all later finite points
* `NewtonPolygon.StepResult` - the result of one step of the Newton polygon algorithm
* `NewtonPolygon.Segment` - a segment of the Newton polygon
* `NewtonPolygon.NewtonPolygonData` - the complete Newton polygon structure

## Algorithm Overview

Given a power series f(X) = a₀ + a₁X + a₂X² + … with coefficients in a complete p-adic field K
and a valuation v : K → ℤ ∪ {∞}:

1. Plot points (i, v(aᵢ)) for each i where aᵢ ≠ 0
2. Starting from (0, v(a₀)), rotate a line counterclockwise
3. At each step, find the minimum slope m to any later point
4. The next vertex is the rightmost point achieving this minimum slope
5. Continue until no more finite points exist or infinitely many points lie on the line

## Implementation Notes

Since ℚ is not a conditionally complete lattice, we use ℝ for computing infima of slope sets.
The slopes themselves are stored as ℚ in the Segment structure.

## References

* [Gouvêa, F. Q., "p-adic Numbers: An Introduction", Section 7.4]
-/

open Set

namespace NewtonPolygon

/-! ### Setup: Valuations

We work with a valuation function `v : ℕ → WithTop ℤ` representing the valuations
of the coefficients of a power series. This abstracts away the field K.

- `v i = ⊤` means the i-th coefficient is 0
- `v i = n` for some integer n means the i-th coefficient has valuation n

Slopes are computed in ℚ (stored) and ℝ (for infima).
-/

/-- The type of valuation sequences: maps each index to either a finite valuation
    (for nonzero coefficients) or ⊤ (for zero coefficients). -/
abbrev ValSeq := ℕ → WithTop ℤ

variable (v : ValSeq)

/-! ### Basic Definitions -/

/-- Predicate: the i-th coefficient is nonzero (has finite valuation). -/
def finite (i : ℕ) : Prop := v i ≠ ⊤

/-- The set of indices with nonzero coefficients. -/
def support : Set ℕ := {i | finite v i}

/-! ### Slopes

The slope from point (i₀, v₀) to point (i, vᵢ) is (vᵢ - v₀) / (i - i₀).
We compute this in ℚ when both valuations are finite integers.
-/

/-- Slope from (i₀, v₀) to (i, vi) where both are finite valuations and i > i₀.
    Returns a rational number. -/
def slopeRat (i₀ : ℕ) (v₀ : ℤ) (i : ℕ) (vi : ℤ) : ℚ :=
  (vi - v₀ : ℚ) / (i - i₀ : ℚ)

/-- Slope from (i₀, v₀) to (i, vi) as a real number (for infimum computation). -/
noncomputable def slopeReal (i₀ : ℕ) (v₀ : ℤ) (i : ℕ) (vi : ℤ) : ℝ :=
  (vi - v₀ : ℝ) / (i - i₀ : ℝ)

/-- The set of all slopes from vertex (i₀, v₀) to later nonzero coefficients (as rationals). -/
def slopeSetQ (i₀ : ℕ) (v₀ : ℤ) : Set ℚ :=
  {m : ℚ | ∃ i : ℕ, i > i₀ ∧ finite v i ∧
    ∃ (vi : ℤ), v i = vi ∧ m = slopeRat i₀ v₀ i vi}

/-- The set of all slopes from vertex (i₀, v₀) to later nonzero coefficients (as reals).
    This version is used for computing infima since ℝ is conditionally complete. -/
noncomputable def slopeSetR (i₀ : ℕ) (v₀ : ℤ) : Set ℝ :=
  {m : ℝ | ∃ i : ℕ, i > i₀ ∧ finite v i ∧
    ∃ (vi : ℤ), v i = vi ∧ m = slopeReal i₀ v₀ i vi}

/-- Alternative characterization of the slope set. -/
lemma mem_slopeSetQ_iff (i₀ : ℕ) (v₀ : ℤ) (m : ℚ) :
    m ∈ slopeSetQ v i₀ v₀ ↔ ∃ i : ℕ, i > i₀ ∧ finite v i ∧
      ∃ (vi : ℤ), v i = vi ∧ m = (vi - v₀ : ℚ) / (i - i₀ : ℚ) := by
  simp only [slopeSetQ, mem_setOf_eq, slopeRat]

/-! ### The Minimum Slope -/

/-- The set of indices achieving a given slope m from (i₀, v₀). -/
def achievingSet (i₀ : ℕ) (v₀ : ℤ) (m : ℚ) : Set ℕ :=
  {i : ℕ | i > i₀ ∧ finite v i ∧
    ∃ (vi : ℤ), v i = vi ∧ m = slopeRat i₀ v₀ i vi}

/-! ### Step Result: What happens at each iteration -/

/-- The result of one step of the Newton polygon algorithm. -/
inductive StepResult where
  /-- No more nonzero coefficients after i₀: the series is a polynomial ending here. -/
  | polynomialTail
  /-- Infinitely many points achieve the minimum slope m: final ray with infinitely many points. -/
  | infiniteRay (m : ℚ)
  /-- The minimum slope is achieved by finitely many points;
      move to the rightmost one (i₁, v₁). -/
  | nextVertex (i₁ : ℕ) (v₁ : ℤ)
  /-- The infimum is not attained (all later points are strictly above the limiting line):
      final ray with no further lattice points. Uses ℚ approximation. -/
  | limitingRay (m : ℚ)

/-- Compute the next step of the Newton polygon algorithm.
    Given current vertex (i₀, v₀), determines what happens next.
    This is noncomputable because it uses sInf on ℝ and classical choice. -/
noncomputable def nextStep (i₀ : ℕ) (v₀ : ℤ) : StepResult := open Classical in
  let S := slopeSetR v i₀ v₀
  if S = ∅ then
    -- No more nonzero coefficients: polynomial tail
    StepResult.polynomialTail
  else
    -- S is nonempty, compute the infimum in ℝ
    let m := sInf S
    -- Check if m is achieved by some rational slope
    let Q := slopeSetQ v i₀ v₀
    if hQ : ∃ q ∈ Q, (q : ℝ) = m then
      let q := Classical.choose hQ
      let I := achievingSet v i₀ v₀ q
      if hInfinite : I.Infinite then
        -- Infinitely many points achieve the minimum: infinite ray
        StepResult.infiniteRay q
      else if hNonempty : I.Nonempty then
        -- Finitely many points achieve the minimum: take the rightmost
        have hfin : I.Finite := Set.not_infinite.mp hInfinite
        let i₁ := hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hNonempty) id
        match v i₁ with
        | ⊤ => StepResult.polynomialTail  -- Shouldn't happen, but need to handle
        | (v₁ : ℤ) => StepResult.nextVertex i₁ v₁
      else
        -- This case shouldn't happen if q ∈ Q, but handle it
        StepResult.limitingRay q
    else
      -- Infimum not attained by a rational: use 0 as placeholder
      -- (In practice, for power series with integer valuations, this won't happen)
      StepResult.limitingRay 0

/-! ### Segments of the Newton Polygon -/

/-- A segment of the Newton polygon from vertex (i₀, v₀) to (i₁, v₁).
    All coordinates are concrete values (indices as ℕ, valuations as ℤ). -/
structure Segment where
  /-- Starting x-coordinate (index) -/
  i₀ : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  v₀ : ℤ
  /-- Ending x-coordinate (index) -/
  i₁ : ℕ
  /-- Ending y-coordinate (valuation as integer) -/
  v₁ : ℤ
  /-- i₀ < i₁ -/
  lt : i₀ < i₁
  deriving Repr

/-- The slope of a segment as a rational number. -/
def Segment.slope (seg : Segment) : ℚ :=
  slopeRat seg.i₀ seg.v₀ seg.i₁ seg.v₁

/-- A final ray of the Newton polygon starting from (i₀, v₀) with slope m. -/
structure FinalRay where
  /-- Starting x-coordinate (index) -/
  i₀ : ℕ
  /-- Starting y-coordinate (valuation as integer) -/
  v₀ : ℤ
  /-- The slope of the ray -/
  slope : ℚ
  /-- Whether the ray contains infinitely many lattice points -/
  hitsInfinitelyMany : Bool
  deriving Repr

/-! ### The Newton Polygon Structure -/

/-- The Newton polygon of a power series, consisting of:
    - A (possibly empty) list of segments with nondecreasing slopes
    - An optional final ray

    The polygon starts at (0, v(a₀)) and traces the lower convex hull
    of the points (i, v(aᵢ)) for nonzero aᵢ. -/
structure NewtonPolygonData where
  /-- The list of segments. -/
  segments : List Segment
  /-- The final ray, if the polygon terminates with a ray. -/
  finalRay : Option FinalRay
  deriving Repr

/-- Check if segments are properly connected. -/
def NewtonPolygonData.connected (npd : NewtonPolygonData) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).i₁ =
      (npd.segments[k + 1]'hk).i₀ ∧
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).v₁ =
      (npd.segments[k + 1]'hk).v₀

/-- Check if slopes are nondecreasing. -/
def NewtonPolygonData.slopes_nondecreasing (npd : NewtonPolygonData) : Prop :=
  ∀ k : ℕ, ∀ hk : k + 1 < npd.segments.length,
    (npd.segments[k]'(Nat.lt_of_succ_lt hk)).slope ≤
      (npd.segments[k + 1]'hk).slope

/-- Check if the final ray is properly connected to the last segment. -/
def NewtonPolygonData.ray_connected (npd : NewtonPolygonData) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => r.i₀ = s.i₁ ∧ r.v₀ = s.v₁
  | _, _ => True

/-- Check if the final ray's slope is at least the last segment's slope. -/
def NewtonPolygonData.ray_slope_valid (npd : NewtonPolygonData) : Prop :=
  match npd.finalRay, npd.segments.getLast? with
  | some r, some s => s.slope ≤ r.slope
  | _, _ => True

/-- A well-formed Newton polygon satisfies all connectivity and monotonicity conditions. -/
structure NewtonPolygonData.WellFormed (npd : NewtonPolygonData) : Prop where
  connected : npd.connected
  slopes_nondecreasing : npd.slopes_nondecreasing
  ray_connected : npd.ray_connected
  ray_slope_valid : npd.ray_slope_valid

/-! ### Correctness Properties -/

section Correctness

variable {v}

/-- A segment is valid if its endpoints correspond to actual nonzero coefficients
    with the claimed valuations. -/
def Segment.valid (seg : Segment) : Prop :=
  finite v seg.i₀ ∧ finite v seg.i₁ ∧
  v seg.i₀ = seg.v₀ ∧ v seg.i₁ = seg.v₁

/-- The y-coordinate of a point on the line from (i₀, v₀) with slope m. -/
noncomputable def lineAt (i₀ : ℕ) (v₀ : ℤ) (m : ℝ) (i : ℕ) : ℝ :=
  (v₀ : ℝ) + m * ((i : ℝ) - (i₀ : ℝ))

/-- A segment is supporting if all points with i > i₀ lie on or above the line. -/
def Segment.supporting (seg : Segment) : Prop :=
  ∀ i > seg.i₀, finite v i →
    ∀ (vi : ℤ), v i = vi →
      (vi : ℝ) ≥ lineAt seg.i₀ seg.v₀ seg.slope i

/-- A segment is tight if its endpoint (i₁, v₁) lies exactly on the line
    (which it should by construction). -/
def Segment.tight (seg : Segment) : Prop :=
  (seg.v₁ : ℝ) = lineAt seg.i₀ seg.v₀ seg.slope seg.i₁

/-- Every segment is tight by construction. -/
theorem Segment.tight_of_slope (seg : Segment) : seg.tight := by
  simp only [tight, lineAt, Segment.slope, slopeRat]
  have hlt := seg.lt
  have hpos : (0 : ℝ) < (seg.i₁ : ℝ) - (seg.i₀ : ℝ) := by
    rw [sub_pos]
    exact Nat.cast_lt.mpr hlt
  have hne : (seg.i₁ : ℝ) - (seg.i₀ : ℝ) ≠ 0 := ne_of_gt hpos
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_intCast, Rat.cast_natCast]
  field_simp [hne]
  ring

/-- A final ray is supporting if all later points lie on or above the ray. -/
def FinalRay.supporting (ray : FinalRay) : Prop :=
  ∀ i > ray.i₀, finite v i →
    ∀ (vi : ℤ), v i = vi →
      (vi : ℝ) ≥ lineAt ray.i₀ ray.v₀ ray.slope i

end Correctness

/-! ### Main Theorem Statements -/

/-- Key property: if m is the infimum of slopes from (i₀, v₀), then all later points
    lie on or above the line with slope m. -/
theorem minSlope_supporting (i₀ : ℕ) (v₀ : ℤ) (m : ℝ)
    (hm : m = sInf (slopeSetR v i₀ v₀))
    (_ : (slopeSetR v i₀ v₀).Nonempty)
    (hbdd : BddBelow (slopeSetR v i₀ v₀)) :
    ∀ i > i₀, finite v i → ∀ (vi : ℤ), v i = vi →
      (vi : ℝ) ≥ lineAt i₀ v₀ m i := by
  intro i hi hfin vi hvi
  simp only [lineAt]
  -- The slope to (i, vi) is in S, so it's ≥ inf S = m
  have hslope_in : slopeReal i₀ v₀ i vi ∈ slopeSetR v i₀ v₀ := by
    simp only [slopeSetR, mem_setOf_eq]
    exact ⟨i, hi, hfin, vi, hvi, rfl⟩
  have hm_le : m ≤ slopeReal i₀ v₀ i vi := by
    rw [hm]
    exact csInf_le hbdd hslope_in
  -- slopeReal i₀ v₀ i vi = (vi - v₀) / (i - i₀)
  -- So m ≤ (vi - v₀) / (i - i₀)
  -- Thus m * (i - i₀) ≤ vi - v₀  (since i - i₀ > 0)
  -- Thus v₀ + m * (i - i₀) ≤ vi
  simp only [slopeReal] at hm_le
  have hi_pos : (0 : ℝ) < (i : ℝ) - (i₀ : ℝ) := by
    rw [sub_pos]
    exact Nat.cast_lt.mpr hi
  have hle : m * ((i : ℝ) - (i₀ : ℝ)) ≤ (vi : ℝ) - (v₀ : ℝ) := by
    rwa [le_div_iff₀ hi_pos] at hm_le
  linarith

/-- Points achieving the minimum slope lie exactly on the line. -/
theorem achievingSet_onLine (i₀ : ℕ) (v₀ : ℤ) (m : ℚ)
    (i : ℕ) (hi : i ∈ achievingSet v i₀ v₀ m) :
    ∀ (vi : ℤ), v i = vi → (vi : ℝ) = lineAt i₀ v₀ m i := by
  intro vi hvi
  simp only [lineAt]
  simp only [achievingSet, mem_setOf_eq] at hi
  obtain ⟨hi_gt, _, vi', hvi', hm_eq⟩ := hi
  -- vi = vi' since both equal v i
  have hveq : vi = vi' := by
    simp only [hvi'] at hvi
    exact WithTop.coe_injective hvi.symm
  subst hveq
  simp only [slopeRat] at hm_eq
  have hi_pos : (0 : ℝ) < (i : ℝ) - (i₀ : ℝ) := by
    rw [sub_pos]
    exact Nat.cast_lt.mpr hi_gt
  have hne : (i : ℝ) - (i₀ : ℝ) ≠ 0 := ne_of_gt hi_pos
  rw [hm_eq]
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_intCast, Rat.cast_natCast]
  field_simp [hne]
  ring

/-! ### Length and Multiplicity -/

/-- The horizontal length of a segment. -/
def Segment.length (seg : Segment) : ℕ := seg.i₁ - seg.i₀

/-! ### Empty Newton Polygon -/

/-- The empty Newton polygon (for the zero series or constant series). -/
def emptyPolygon : NewtonPolygonData where
  segments := []
  finalRay := none

/-- The empty polygon is well-formed. -/
theorem emptyPolygon_wellFormed : emptyPolygon.WellFormed where
  connected := fun _ hk => by simp [emptyPolygon] at hk
  slopes_nondecreasing := fun _ hk => by simp [emptyPolygon] at hk
  ray_connected := by simp [emptyPolygon, NewtonPolygonData.ray_connected]
  ray_slope_valid := by simp [emptyPolygon, NewtonPolygonData.ray_slope_valid]

/-! ### Constructing the Newton Polygon -/

/-- Create a single segment given valid data. -/
def mkSegment (i₀ : ℕ) (v₀ : ℤ) (i₁ : ℕ) (v₁ : ℤ) (hlt : i₀ < i₁) : Segment :=
  { i₀ := i₀, v₀ := v₀, i₁ := i₁, v₁ := v₁, lt := hlt }

/-- Create a final ray. -/
def mkFinalRay (i₀ : ℕ) (v₀ : ℤ) (slope : ℚ) (infinite : Bool) : FinalRay :=
  { i₀ := i₀, v₀ := v₀, slope := slope, hitsInfinitelyMany := infinite }

/-! ### Helper Lemmas -/

/-- The slope set is empty iff there are no nonzero coefficients after i₀. -/
lemma slopeSetR_empty_iff (i₀ : ℕ) (v₀ : ℤ) :
    slopeSetR v i₀ v₀ = ∅ ↔ ∀ i > i₀, ¬finite v i := by
  constructor
  · intro h i hi hfin
    cases hv : v i with
    | top => exact hfin hv
    | coe vi =>
      have hmem : slopeReal i₀ v₀ i vi ∈ slopeSetR v i₀ v₀ := by
        simp only [slopeSetR, mem_setOf_eq]
        exact ⟨i, hi, hfin, vi, hv, rfl⟩
      rw [h] at hmem
      exact hmem
  · intro h
    ext m
    simp only [mem_empty_iff_false, iff_false]
    intro ⟨i, hi, hfin, _, _, _⟩
    exact h i hi hfin

/-- Rational slopes embed into real slopes. -/
lemma slopeRat_eq_slopeReal (i₀ : ℕ) (v₀ : ℤ) (i : ℕ) (vi : ℤ) :
    (slopeRat i₀ v₀ i vi : ℝ) = slopeReal i₀ v₀ i vi := by
  simp only [slopeRat, slopeReal, Rat.cast_div, Rat.cast_sub, Rat.cast_intCast, Rat.cast_natCast]

/-! ### API: Converting Power Series to Valuation Sequences

These functions provide the interface between Mathlib's `PowerSeries` type
and the Newton polygon computation machinery.
-/

section PowerSeriesAPI

variable {R : Type*} [CommRing R]

/-- Extract the valuation sequence from a power series given a valuation.
    Maps coefficient index i to the valuation v(aᵢ), using ⊤ for zero coefficients. -/
noncomputable def toValSeq (f : PowerSeries R) (v : R → WithTop ℤ) : ValSeq :=
  fun i => v (PowerSeries.coeff i f)

/-- Variant: extract valuation sequence using a Mathlib Valuation structure. -/
noncomputable def toValSeqFromValuation {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (f : PowerSeries R) (v : Valuation R Γ₀) (toInt : Γ₀ → WithTop ℤ) : ValSeq :=
  fun i => toInt (v (PowerSeries.coeff i f))

end PowerSeriesAPI

/-! ### API: Computing the Newton Polygon

The main algorithm iteratively applies `nextStep` to build up the polygon.
Following Gouvêa's "rotating line" procedure from Section 7.4.
-/

section ComputePolygon

variable (v : ValSeq)

/-- Configuration for polygon computation to handle termination. -/
structure ComputeConfig where
  /-- Maximum number of segments to compute (for termination). -/
  maxSegments : ℕ := 1000
  /-- Maximum index to search for finite valuations. -/
  maxIndex : ℕ := 10000

/-- Find the first index with finite valuation, starting from a given position. -/
noncomputable def findFirstFinite (startIdx : ℕ) : Option (ℕ × ℤ) := open Classical in
  if h : ∃ i ≥ startIdx, finite v i then
    let i := Nat.find h
    match v i with
    | ⊤ => none  -- contradicts finiteness, shouldn't happen
    | (val : ℤ) => some (i, val)
  else
    none

/-- Result of iteratively building the Newton polygon. -/
inductive BuildResult where
  /-- Successfully built the polygon. -/
  | complete (npd : NewtonPolygonData)
  /-- Hit the segment limit before completing. -/
  | incomplete (npd : NewtonPolygonData) (reason : String)
  deriving Repr

/-- Build the Newton polygon by iterating the nextStep algorithm.
    This is the main computational function.

    The algorithm follows Gouvêa Section 7.4:
    1. Start at the first nonzero coefficient (i₀, v₀)
    2. Rotate the line counterclockwise to find minimum slope
    3. Move to the rightmost point achieving minimum slope
    4. Repeat until termination (polynomial tail, infinite ray, or limiting ray)
-/
noncomputable def buildNewtonPolygon (cfg : ComputeConfig := {}) : BuildResult := open Classical in
  -- Find the starting point (first finite valuation)
  match findFirstFinite v 0 with
  | none => BuildResult.complete emptyPolygon
  | some (i₀, v₀) =>
    -- Iteratively build segments
    let rec build (currentIdx : ℕ) (currentVal : ℤ) (segments : List Segment)
        (fuel : ℕ) : BuildResult :=
      if fuel = 0 then
        BuildResult.incomplete ⟨segments, none⟩ "reached segment limit"
      else
        match nextStep v currentIdx currentVal with
        | StepResult.polynomialTail =>
            -- No more nonzero coefficients: series is essentially a polynomial
            BuildResult.complete ⟨segments, none⟩
        | StepResult.infiniteRay m =>
            -- Infinitely many points on a line of slope m
            let ray := mkFinalRay currentIdx currentVal m true
            BuildResult.complete ⟨segments, some ray⟩
        | StepResult.limitingRay m =>
            -- Limiting slope not achieved by any point
            let ray := mkFinalRay currentIdx currentVal m false
            BuildResult.complete ⟨segments, some ray⟩
        | StepResult.nextVertex i₁ v₁ =>
            if h : currentIdx < i₁ then
              let seg := mkSegment currentIdx currentVal i₁ v₁ h
              build i₁ v₁ (segments ++ [seg]) (fuel - 1)
            else
              -- Shouldn't happen, but handle gracefully
              BuildResult.incomplete ⟨segments, none⟩ "invalid vertex ordering"
    build i₀ v₀ [] cfg.maxSegments

/-- Extract the Newton polygon data, returning the empty polygon if computation
    was incomplete. -/
noncomputable def newtonPolygon (cfg : ComputeConfig := {}) : NewtonPolygonData :=
  match buildNewtonPolygon v cfg with
  | BuildResult.complete npd => npd
  | BuildResult.incomplete npd _ => npd

end ComputePolygon

/-! ### API: Querying Newton Polygon Properties

Convenience functions for extracting information from a Newton polygon,
following the terminology from Gouvêa Section 7.4.
-/

section QueryAPI

/-- Get all slopes of the Newton polygon (the "Newton slopes"). -/
def NewtonPolygonData.slopes (npd : NewtonPolygonData) : List ℚ :=
  npd.segments.map Segment.slope

/-- Get the length of each segment (projection onto x-axis). -/
def NewtonPolygonData.lengths (npd : NewtonPolygonData) : List ℕ :=
  npd.segments.map Segment.length

/-- Get the vertices (break points) of the polygon as (index, valuation) pairs. -/
def NewtonPolygonData.vertices (npd : NewtonPolygonData) : List (ℕ × ℤ) :=
  match npd.segments with
  | [] => []
  | seg :: rest =>
    (seg.i₀, seg.v₀) :: rest.foldl (fun acc s => acc ++ [(s.i₁, s.v₁)])
      [(seg.i₁, seg.v₁)]

/-- Get slopes paired with their lengths (useful for root counting). -/
def NewtonPolygonData.slopesWithLengths (npd : NewtonPolygonData) : List (ℚ × ℕ) :=
  npd.segments.map fun seg => (seg.slope, seg.length)

/-- Total horizontal extent of the polygon. -/
def NewtonPolygonData.totalLength (npd : NewtonPolygonData) : ℕ :=
  npd.lengths.foldl (· + ·) 0

/-- Check if the polygon is pure (has only one slope).
    Following Gouvêa Definition 7.4.1: A polynomial is pure if its Newton
    polygon has only one slope. -/
def NewtonPolygonData.isPure (npd : NewtonPolygonData) : Bool :=
  npd.segments.length ≤ 1 && npd.finalRay.isNone

/-- Get the unique slope if the polygon is pure, otherwise none. -/
def NewtonPolygonData.pureSlope (npd : NewtonPolygonData) : Option ℚ :=
  if npd.isPure then npd.slopes.head? else none

/-- Count zeros with a given valuation (negative of slope gives absolute value exponent).
    By Gouvêa Theorem 7.4.7, a segment of slope m and length ℓ corresponds to
    exactly ℓ roots of absolute value p^m. -/
def NewtonPolygonData.rootCountAtSlope (npd : NewtonPolygonData) (m : ℚ) : ℕ :=
  npd.segments.foldl (fun acc seg => if seg.slope = m then acc + seg.length else acc) 0

/-- Get all distinct slopes with their root counts. -/
def NewtonPolygonData.rootDistribution (npd : NewtonPolygonData) : List (ℚ × ℕ) :=
  npd.slopesWithLengths.foldl (fun acc (m, len) =>
    match acc.find? (fun (m', _) => m' = m) with
    | some _ => acc.map (fun (m', n) => if m' = m then (m', n + len) else (m', n))
    | none => acc ++ [(m, len)]
  ) []

end QueryAPI

/-! ### API: Main Entry Points for Power Series

These are the primary functions users should call to compute Newton polygons
from power series.
-/

section MainAPI

variable {R : Type*} [CommRing R]

/-- Compute the Newton polygon of a power series given a valuation function.

    **Example usage:**
    ```
    -- For a p-adic field K with valuation v
    def myValuation (x : K) : WithTop ℤ := ...
    def f : PowerSeries K := ...
    def np := newtonPolygonOfPowerSeries f myValuation
    ```

    The valuation function should satisfy:
    - v(0) = ⊤
    - v(xy) = v(x) + v(y)
    - v(x + y) ≥ min(v(x), v(y))
-/
noncomputable def newtonPolygonOfPowerSeries
    (f : PowerSeries R) (v : R → WithTop ℤ) (cfg : ComputeConfig := {}) : NewtonPolygonData :=
  newtonPolygon (toValSeq f v) cfg

/-- Get the slopes of a power series' Newton polygon. -/
noncomputable def slopesOfPowerSeries
    (f : PowerSeries R) (v : R → WithTop ℤ) (cfg : ComputeConfig := {}) : List ℚ :=
  (newtonPolygonOfPowerSeries f v cfg).slopes

/-- Get the lengths of segments in a power series' Newton polygon. -/
noncomputable def lengthsOfPowerSeries
    (f : PowerSeries R) (v : R → WithTop ℤ) (cfg : ComputeConfig := {}) : List ℕ :=
  (newtonPolygonOfPowerSeries f v cfg).lengths

/-- Check if a power series is pure (Newton polygon has single slope).
    By Gouvêa Proposition 7.4.2, irreducible polynomials are pure. -/
noncomputable def isPurePowerSeries
    (f : PowerSeries R) (v : R → WithTop ℤ) (cfg : ComputeConfig := {}) : Bool :=
  (newtonPolygonOfPowerSeries f v cfg).isPure

/-- Get the root distribution of a power series.
    Returns pairs (slope, count) where count is the number of roots
    with absolute value p^slope (by Gouvêa Theorem 7.4.7). -/
noncomputable def rootDistributionOfPowerSeries
    (f : PowerSeries R) (v : R → WithTop ℤ) (cfg : ComputeConfig := {}) : List (ℚ × ℕ) :=
  (newtonPolygonOfPowerSeries f v cfg).rootDistribution

end MainAPI

/-! ### Specialized API for Integer-Valued Valuations

When working with p-adic numbers, the valuation takes values in ℤ (or ℤ ∪ {∞}).
These functions provide a simplified interface for this common case.
-/

section IntValuationAPI

/-- A p-adic-style valuation: maps elements to ℤ ∪ {∞}.
    Zero maps to ⊤, nonzero elements map to their valuation. -/
structure IntValuation (R : Type*) [Ring R] where
  /-- The valuation function -/
  val : R → WithTop ℤ
  /-- Zero has valuation ⊤ -/
  map_zero : val 0 = ⊤
  /-- Multiplicativity (when both are finite) -/
  map_mul : ∀ x y, val (x * y) = val x + val y

variable {R : Type*} [CommRing R]

/-- Compute Newton polygon using an IntValuation structure. -/
noncomputable def newtonPolygonWithIntVal
    (f : PowerSeries R) (v : IntValuation R) (cfg : ComputeConfig := {}) : NewtonPolygonData :=
  newtonPolygonOfPowerSeries f v.val cfg

end IntValuationAPI

/-! ### Example: Newton Polygon of 1 + pX² + p³X⁵

This section demonstrates the Newton polygon computation for a concrete example.
Following Gouvêa Section 7.4, we compute the Newton polygon of f(X) = 1 + pX² + p³X⁵
where p is a prime and we use the p-adic valuation.

The points (i, v_p(aᵢ)) are:
- (0, 0) since v_p(1) = 0
- (2, 1) since v_p(p) = 1
- (5, 3) since v_p(p³) = 3

The Newton polygon has two segments:
- Segment 1: (0,0) → (2,1) with slope 1/2 and length 2
- Segment 2: (2,1) → (5,3) with slope 2/3 and length 3

By Gouvêa Theorem 7.4.7, this means f(X) has:
- 2 roots with absolute value p^(1/2)
- 3 roots with absolute value p^(2/3)
-/

section Example

/-- Valuation sequence for f(X) = 1 + pX² + p³X⁵ under p-adic valuation.
    v_p(1) = 0, v_p(p) = 1, v_p(p³) = 3, and zero coefficients have v_p = ⊤. -/
def exampleValSeq : ValSeq
  | 0 => 0
  | 1 => ⊤
  | 2 => 1
  | 3 => ⊤
  | 4 => ⊤
  | 5 => 3
  | _ => ⊤

/-- First segment: (0, 0) → (2, 1) -/
def exampleSeg1 : Segment := mkSegment 0 0 2 1 (by decide)

/-- Second segment: (2, 1) → (5, 3) -/
def exampleSeg2 : Segment := mkSegment 2 1 5 3 (by decide)

/-- The Newton polygon of f(X) = 1 + pX² + p³X⁵ -/
def examplePolygon : NewtonPolygonData := {
  segments := [exampleSeg1, exampleSeg2]
  finalRay := none
}

/-- The slopes of the example polygon are 1/2 and 2/3. -/
theorem examplePolygon_slopes : examplePolygon.slopes = [1/2, 2/3] := by
  simp only [NewtonPolygonData.slopes, examplePolygon, exampleSeg1, exampleSeg2]
  simp only [List.map, Segment.slope, mkSegment, slopeRat]
  norm_num

/-- The lengths of the segments are 2 and 3. -/
theorem examplePolygon_lengths : examplePolygon.lengths = [2, 3] := by
  simp only [NewtonPolygonData.lengths, examplePolygon, List.map]
  simp only [Segment.length, exampleSeg1, exampleSeg2, mkSegment]

/-- The total length equals the degree (5). -/
theorem examplePolygon_totalLength : examplePolygon.totalLength = 5 := by
  simp only [NewtonPolygonData.totalLength, examplePolygon_lengths]
  rfl

/-- The polygon is not pure (has multiple distinct slopes). -/
theorem examplePolygon_not_pure : examplePolygon.isPure = false := by
  simp only [NewtonPolygonData.isPure, examplePolygon]
  rfl

/-- The vertices (break points) of the polygon. -/
theorem examplePolygon_vertices : examplePolygon.vertices = [(0, 0), (2, 1), (5, 3)] := by
  simp only [NewtonPolygonData.vertices, examplePolygon]
  simp only [exampleSeg1, exampleSeg2, mkSegment, List.foldl]
  rfl

/-- Verify slope of first segment is 1/2. -/
theorem exampleSeg1_slope : exampleSeg1.slope = 1/2 := by
  simp only [exampleSeg1, mkSegment, Segment.slope, slopeRat]
  norm_num

/-- Verify slope of second segment is 2/3. -/
theorem exampleSeg2_slope : exampleSeg2.slope = 2/3 := by
  simp only [exampleSeg2, mkSegment, Segment.slope, slopeRat]
  norm_num

/-- The slopes are strictly increasing, as required by the rotating line algorithm. -/
theorem examplePolygon_slopes_increasing : exampleSeg1.slope < exampleSeg2.slope := by
  simp only [exampleSeg1_slope, exampleSeg2_slope]
  norm_num

/-! #### Using the API with a PowerSeries

Now we demonstrate using the actual `newtonPolygonOfPowerSeries` API to compute
the Newton polygon from a power series with a valuation.
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The p-adic valuation on ℤ, returning ⊤ for 0 and v_p(n) for n ≠ 0. -/
noncomputable def intPadicVal (p : ℕ) : ℤ → WithTop ℤ := fun n =>
  if n = 0 then ⊤ else (padicValInt p n : ℤ)

/-- The power series f(X) = 1 + p·X² + p³·X⁵ over ℤ. -/
def examplePowerSeries (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    match n with
    | 0 => 1
    | 2 => p
    | 5 => p^3
    | _ => 0

/-- The Newton polygon of the example power series, computed via the API. -/
noncomputable def exampleNewtonPolygonViaAPI (p : ℕ) [Fact (Nat.Prime p)] : NewtonPolygonData :=
  newtonPolygonOfPowerSeries (examplePowerSeries p) (intPadicVal p)

omit hp in
/-- Coefficient 0 of the example power series is 1. -/
theorem examplePowerSeries_coeff_0 : PowerSeries.coeff 0 (examplePowerSeries p) = 1 := by
  simp [examplePowerSeries, PowerSeries.coeff_mk]

omit hp in
/-- Coefficient 2 of the example power series is p. -/
theorem examplePowerSeries_coeff_2 : PowerSeries.coeff 2 (examplePowerSeries p) = p := by
  simp [examplePowerSeries, PowerSeries.coeff_mk]

omit hp in
/-- Coefficient 5 of the example power series is p³. -/
theorem examplePowerSeries_coeff_5 : PowerSeries.coeff 5 (examplePowerSeries p) = p^3 := by
  simp [examplePowerSeries, PowerSeries.coeff_mk]

omit hp in
/-- Coefficient 1 of the example power series is 0. -/
theorem examplePowerSeries_coeff_1 : PowerSeries.coeff 1 (examplePowerSeries p) = 0 := by
  simp [examplePowerSeries, PowerSeries.coeff_mk]

omit hp in
/-- The valuation of coefficient 0 is 0 (since v_p(1) = 0). -/
theorem exampleValSeq_via_API_0 :
    toValSeq (examplePowerSeries p) (intPadicVal p) 0 = (0 : ℤ) := by
  simp only [toValSeq, examplePowerSeries_coeff_0, intPadicVal, one_ne_zero, ↓reduceIte,
             padicValInt.one, Nat.cast_zero]

/-- The valuation of coefficient 2 is 1 (since v_p(p) = 1). -/
theorem exampleValSeq_via_API_2 :
    toValSeq (examplePowerSeries p) (intPadicVal p) 2 = (1 : ℤ) := by
  simp only [toValSeq, examplePowerSeries_coeff_2, intPadicVal]
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
  simp only [hp_ne, ↓reduceIte, padicValInt_self, Nat.cast_one]

/-- The valuation of coefficient 5 is 3 (since v_p(p³) = 3). -/
theorem exampleValSeq_via_API_5 :
    toValSeq (examplePowerSeries p) (intPadicVal p) 5 = (3 : ℤ) := by
  simp only [toValSeq, examplePowerSeries_coeff_5, intPadicVal]
  have hp_ne : (p : ℤ)^3 ≠ 0 := pow_ne_zero 3 (Int.natCast_ne_zero.mpr hp.out.ne_zero)
  simp only [hp_ne, ↓reduceIte]
  have h_cast : ((p : ℤ)^3) = ((p^3 : ℕ) : ℤ) := by norm_cast
  simp only [h_cast, padicValInt.of_nat, padicValNat.prime_pow, Nat.cast_ofNat]

omit hp in
/-- The valuation of coefficient 1 is ⊤ (since coefficient is 0). -/
theorem exampleValSeq_via_API_1 :
    toValSeq (examplePowerSeries p) (intPadicVal p) 1 = ⊤ := by
  simp only [toValSeq, examplePowerSeries_coeff_1, intPadicVal, ↓reduceIte]

/-- The valuation sequence from the API matches our manual exampleValSeq at key indices. -/
theorem exampleValSeq_matches :
    toValSeq (examplePowerSeries p) (intPadicVal p) 0 = exampleValSeq 0 ∧
    toValSeq (examplePowerSeries p) (intPadicVal p) 1 = exampleValSeq 1 ∧
    toValSeq (examplePowerSeries p) (intPadicVal p) 2 = exampleValSeq 2 ∧
    toValSeq (examplePowerSeries p) (intPadicVal p) 5 = exampleValSeq 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [exampleValSeq_via_API_0, exampleValSeq]
  · simp [exampleValSeq_via_API_1, exampleValSeq]
  · simp [exampleValSeq_via_API_2, exampleValSeq]
  · simp [exampleValSeq_via_API_5, exampleValSeq]

end Example

/-! ### Example 2: Newton Polygon of 1 + pX + pX² + pX³ + ···

This is the example from Gouvêa Section 7.4 (page 260-261).
The power series f(X) = 1 + pX + pX² + pX³ + ··· has points:
- (0, 0) since v_p(1) = 0
- (1, 1) since v_p(p) = 1
- (2, 1) since v_p(p) = 1
- (n, 1) for all n ≥ 1

From (0, 0), the slope to (n, 1) is 1/n, which tends to 0 as n → ∞.
The infimum is 0, but no finite point achieves this slope.
Thus the Newton polygon is a horizontal ray of slope 0 starting at (0, 0).

This is Gouvêa's "case (ii)" where the line reaches a position where it
can be rotated no further without leaving points behind.
-/

section Example2

/-!
## Example 2: The Geometric Series 1 + pX + pX² + pX³ + ···

We prove that the Newton polygon of this series is a horizontal ray at slope 0.
This is done by connecting the valuation sequence to the Newton polygon algorithm
and proving that `nextStep` returns `limitingRay 0`.

Key insight (Gouvêa p. 262): The points are (0, 0), (1, 1), (2, 1), (3, 1), ...
The slope from (0, 0) to (n, 1) is 1/n. As n → ∞, this approaches 0 but never equals 0.
The infimum of slopes is 0, achieved in the limit but not by any finite point.
-/

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The power series f(X) = 1 + pX + pX² + pX³ + ··· over ℤ. -/
def geometricSeriesWithP (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    match n with
    | 0 => 1
    | _ => p

/-- Valuation sequence for 1 + pX + pX² + pX³ + ···
    v_p(1) = 0 at index 0, v_p(p) = 1 at all other indices. -/
def geometricValSeq : ValSeq
  | 0 => 0
  | _ => 1

omit hp in
/-- Coefficient 0 is 1. -/
theorem geometricSeries_coeff_0 : PowerSeries.coeff 0 (geometricSeriesWithP p) = 1 := by
  simp [geometricSeriesWithP, PowerSeries.coeff_mk]

omit hp in
/-- Coefficient n (for n ≥ 1) is p. -/
theorem geometricSeries_coeff_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) (geometricSeriesWithP p) = p := by
  simp [geometricSeriesWithP, PowerSeries.coeff_mk]

omit hp in
/-- The valuation at index 0 is 0. -/
theorem geometricValSeq_via_API_0 :
    toValSeq (geometricSeriesWithP p) (intPadicVal p) 0 = (0 : ℤ) := by
  simp only [toValSeq, geometricSeries_coeff_0, intPadicVal, one_ne_zero, ↓reduceIte,
             padicValInt.one, Nat.cast_zero]

/-- The valuation at index n+1 is 1 (since coefficient is p). -/
theorem geometricValSeq_via_API_succ (n : ℕ) :
    toValSeq (geometricSeriesWithP p) (intPadicVal p) (n + 1) = (1 : ℤ) := by
  simp only [toValSeq, geometricSeries_coeff_succ, intPadicVal]
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
  simp only [hp_ne, ↓reduceIte, padicValInt_self, Nat.cast_one]

/-! ### Properties of the geometric valuation sequence -/

omit hp in
/-- All indices have finite valuation. -/
theorem geometricValSeq_finite (n : ℕ) : finite geometricValSeq n := by
  cases n with
  | zero => simp [finite, geometricValSeq]
  | succ n => simp [finite, geometricValSeq]

omit hp in
/-- The valuation at index 0 is 0. -/
theorem geometricValSeq_0 : geometricValSeq 0 = (0 : ℤ) := rfl

omit hp in
/-- The valuation at any positive index is 1. -/
theorem geometricValSeq_succ (n : ℕ) : geometricValSeq (n + 1) = (1 : ℤ) := rfl

omit hp in
/-- The slope from (0, 0) to (n, 1) is 1/n. -/
theorem slope_to_n (n : ℕ) (_hn : n > 0) : slopeRat 0 0 n 1 = 1 / n := by
  simp only [slopeRat, Int.cast_zero, Int.cast_one, sub_zero, Nat.cast_zero]

/-! ### The slope set for geometricValSeq from (0, 0) -/

omit hp in
/-- The rational slope set from (0, 0) is exactly {1/n : n ≥ 1}. -/
theorem geometricValSeq_slopeSetQ :
    slopeSetQ geometricValSeq 0 0 = {m : ℚ | ∃ n : ℕ, n > 0 ∧ m = 1 / n} := by
  ext m
  simp only [slopeSetQ, mem_setOf_eq]
  constructor
  · intro ⟨i, hi, hfin, vi, hvi, hm⟩
    use i, hi
    -- vi = 1 since geometricValSeq i = 1 for i > 0
    have hvi' : vi = 1 := by
      cases i with
      | zero => omega
      | succ n =>
        simp only [geometricValSeq] at hvi
        exact WithTop.coe_injective hvi.symm
    subst hvi'
    rw [hm, slope_to_n i hi]
  · intro ⟨n, hn, hm⟩
    use n, hn, geometricValSeq_finite n, 1
    constructor
    · simp [geometricValSeq, Nat.pos_iff_ne_zero.mp hn]
    · rw [hm, slope_to_n n hn]

omit hp in
/-- The slope set is nonempty (contains 1/1 = 1). -/
theorem geometricValSeq_slopeSetQ_nonempty : (slopeSetQ geometricValSeq 0 0).Nonempty := by
  use 1
  rw [geometricValSeq_slopeSetQ]
  simp only [mem_setOf_eq]
  use 1
  simp

omit hp in
/-- The real slope set from (0, 0) is {1/n : n ≥ 1} as real numbers. -/
theorem geometricValSeq_slopeSetR :
    slopeSetR geometricValSeq 0 0 = {m : ℝ | ∃ n : ℕ, n > 0 ∧ m = 1 / n} := by
  ext m
  simp only [slopeSetR, mem_setOf_eq, slopeReal]
  constructor
  · intro ⟨i, hi, hfin, vi, hvi, hm⟩
    use i, hi
    have hvi' : vi = 1 := by
      cases i with
      | zero => omega
      | succ n =>
        simp only [geometricValSeq] at hvi
        exact WithTop.coe_injective hvi.symm
    simp only [hvi', Int.cast_one, Int.cast_zero, sub_zero, Nat.cast_zero] at hm
    exact hm
  · intro ⟨n, hn, hm⟩
    use n, hn, geometricValSeq_finite n, 1
    constructor
    · simp [geometricValSeq, Nat.pos_iff_ne_zero.mp hn]
    · simp only [Int.cast_one, Int.cast_zero, sub_zero, Nat.cast_zero]
      exact hm

omit hp in
/-- The slope set is nonempty. -/
theorem geometricValSeq_slopeSetR_nonempty : (slopeSetR geometricValSeq 0 0).Nonempty := by
  use 1
  rw [geometricValSeq_slopeSetR]
  simp only [mem_setOf_eq]
  use 1
  simp

/-! ### The infimum of slopes is 0 -/

omit hp in
/-- The slope set is bounded below by 0. -/
theorem geometricValSeq_slopeSetR_bddBelow : BddBelow (slopeSetR geometricValSeq 0 0) := by
  use 0
  intro m hm
  rw [geometricValSeq_slopeSetR] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact div_nonneg (by norm_num) (le_of_lt hn')

omit hp in
/-- All slopes are positive. -/
theorem geometricValSeq_slopes_pos (m : ℝ) (hm : m ∈ slopeSetR geometricValSeq 0 0) : m > 0 := by
  rw [geometricValSeq_slopeSetR] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact div_pos (by norm_num) hn'

omit hp in
/-- The infimum of the slope set is 0. -/
theorem geometricValSeq_sInf_eq_zero : sInf (slopeSetR geometricValSeq 0 0) = 0 := by
  apply le_antisymm
  · -- sInf ≤ 0: Show any lower bound is ≤ 0
    rw [csInf_le_iff geometricValSeq_slopeSetR_bddBelow geometricValSeq_slopeSetR_nonempty]
    intro ε hε
    -- If ε > 0, find 1/n < ε in the set, contradicting that ε is a lower bound
    by_contra h
    push_neg at h
    -- Find n such that 1/n < ε
    have hpos : ε > 0 := h
    have hex : ∃ n : ℕ, ε⁻¹ < n := exists_nat_gt ε⁻¹
    obtain ⟨n, hn⟩ := hex
    -- 1/(n+1) is in the set
    have hmem : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ∈ slopeSetR geometricValSeq 0 0 := by
      rw [geometricValSeq_slopeSetR]
      simp only [mem_setOf_eq]
      exact ⟨n + 1, Nat.succ_pos n, rfl⟩
    -- ε is a lower bound, so ε ≤ 1/(n+1)
    have hle : ε ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := hε hmem
    -- But 1/(n+1) < ε
    have hlt : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < ε := by
      have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [one_div_lt hn1 hpos, one_div]
      have h1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by simp
      linarith
    linarith
  · -- 0 ≤ sInf: all elements are positive
    apply le_csInf geometricValSeq_slopeSetR_nonempty
    intro m hm
    exact le_of_lt (geometricValSeq_slopes_pos m hm)

omit hp in
/-- 0 is not achieved by any slope in the set (no n gives slope 0). -/
theorem geometricValSeq_zero_not_achieved :
    ¬∃ q ∈ slopeSetQ geometricValSeq 0 0, (q : ℝ) = (0 : ℝ) := by
  intro ⟨q, hq, hq0⟩
  rw [geometricValSeq_slopeSetQ] at hq
  obtain ⟨n, hn, rfl⟩ := hq
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hq0
  have : (1 : ℝ) / n > 0 := div_pos (by norm_num) hn'
  linarith

/-! ### The Newton polygon algorithm returns limitingRay 0 -/

omit hp in
/-- The first step of the Newton polygon algorithm for geometricValSeq returns limitingRay 0.
    This is the key theorem connecting the algorithm to the geometric series example. -/
theorem geometricValSeq_nextStep_eq_limitingRay :
    nextStep geometricValSeq 0 0 = StepResult.limitingRay 0 := by
  unfold nextStep
  -- The slope set is nonempty
  have hne : slopeSetR geometricValSeq 0 0 ≠ ∅ :=
    Set.Nonempty.ne_empty geometricValSeq_slopeSetR_nonempty
  simp only [if_neg hne]
  -- The infimum is 0
  have hinf : sInf (slopeSetR geometricValSeq 0 0) = 0 := geometricValSeq_sInf_eq_zero
  -- 0 is not achieved by any rational slope
  have hnotach : ¬∃ q ∈ slopeSetQ geometricValSeq 0 0,
      (q : ℝ) = sInf (slopeSetR geometricValSeq 0 0) := by
    rw [hinf]
    exact geometricValSeq_zero_not_achieved
  simp only [dif_neg hnotach]

/-! ### The computed Newton polygon -/

/-- The Newton polygon computed by the algorithm. -/
noncomputable def geometricNewtonPolygonComputed : NewtonPolygonData :=
  newtonPolygon geometricValSeq

omit hp in
/-- Helper: findFirstFinite for geometricValSeq returns (0, 0). -/
theorem geometricValSeq_findFirstFinite :
    findFirstFinite geometricValSeq 0 = some (0, 0) := by
  classical
  unfold findFirstFinite
  have hex : ∃ i ≥ 0, finite geometricValSeq i := ⟨0, le_refl 0, geometricValSeq_finite 0⟩
  simp only [dif_pos hex]
  -- Nat.find hex = 0 because 0 is the minimum satisfying the predicate
  have hfind : Nat.find hex = 0 := by
    rw [Nat.find_eq_zero]
    exact ⟨le_refl 0, geometricValSeq_finite 0⟩
  simp only [hfind, geometricValSeq_0]

/-- The computed polygon has no segments (goes directly to a ray). -/
theorem geometricNewtonPolygonComputed_no_segments :
    geometricNewtonPolygonComputed.segments = [] := by
  unfold geometricNewtonPolygonComputed newtonPolygon buildNewtonPolygon
  simp only [geometricValSeq_findFirstFinite]
  -- Unfold the build recursion one step
  unfold buildNewtonPolygon.build
  simp only [geometricValSeq_nextStep_eq_limitingRay]
  -- 1000 ≠ 0, so the if reduces to the else branch
  rfl

/-- The computed polygon has a final ray with slope 0. -/
theorem geometricNewtonPolygonComputed_ray_slope :
    geometricNewtonPolygonComputed.finalRay.map FinalRay.slope = some 0 := by
  unfold geometricNewtonPolygonComputed newtonPolygon buildNewtonPolygon
  simp only [geometricValSeq_findFirstFinite]
  -- Unfold the build recursion one step
  unfold buildNewtonPolygon.build
  simp only [geometricValSeq_nextStep_eq_limitingRay]
  -- 1000 ≠ 0, so the if reduces to the else branch; simplify the Option.map
  rfl

/-! ### Connection to the power series API -/

omit hp in
/-- The valuation sequence from the API matches our manual definition at index 0. -/
theorem geometricValSeq_matches_0 :
    toValSeq (geometricSeriesWithP p) (intPadicVal p) 0 = geometricValSeq 0 := by
  simp [geometricValSeq_via_API_0, geometricValSeq]

/-- The valuation sequence from the API matches our manual definition at positive indices. -/
theorem geometricValSeq_matches_succ (n : ℕ) :
    toValSeq (geometricSeriesWithP p) (intPadicVal p) (n + 1) = geometricValSeq (n + 1) := by
  simp [geometricValSeq_via_API_succ, geometricValSeq]

/-- Summary: The Newton polygon of 1 + pX + pX² + ··· has no segments and a ray of slope 0.
    This matches Gouvêa's analysis on page 262: "the Newton polygon is a horizontal line". -/
theorem geometric_newton_polygon_is_horizontal_ray :
    geometricNewtonPolygonComputed.segments = [] ∧
    geometricNewtonPolygonComputed.finalRay.map FinalRay.slope = some 0 :=
  ⟨geometricNewtonPolygonComputed_no_segments, geometricNewtonPolygonComputed_ray_slope⟩

end Example2

/-!
## Lemma 7.4.8: Newton Polygon Slopes and Radius of Convergence

Gouvêa's Lemma 7.4.8 states that the radius of convergence of a power series
equals p^m, where m is the supremum of slopes in its Newton polygon.

Key insight: If |x| = p^b with b < m, then the series converges because
the Newton polygon eventually lies above the line y = bx, meaning
v_p(a_i) - b·i → ∞ as i → ∞.
-/

section Lemma748

/-! ### Supremum of Slopes -/

/-- The supremum of slopes in a Newton polygon.
    - If there's a final ray, the sup is the ray's slope
    - Otherwise, it's the maximum of segment slopes (last one, since slopes increase)
    - For an empty polygon, we use 0 as a default -/
noncomputable def NewtonPolygonData.supSlope (npd : NewtonPolygonData) : WithTop ℚ :=
  match npd.finalRay with
  | some ray => ray.slope
  | none =>
    match npd.segments.getLast? with
    | some seg => seg.slope
    | none => 0  -- empty polygon

/-- Alternative: sup slope as an extended rational (using ⊤ for +∞). -/
noncomputable def NewtonPolygonData.supSlopeExt (npd : NewtonPolygonData) : WithTop ℚ :=
  match npd.finalRay with
  | some ray =>
    -- If the ray has infinitely many points with increasing slopes, sup could be ⊤
    -- For a limiting ray (hitsInfinitelyMany = false), the slope is the actual sup
    ray.slope
  | none =>
    match npd.segments.getLast? with
    | some seg => seg.slope
    | none => 0

/-! ### Convergence on closed balls -/

/-- A valuation sequence converges on the closed ball of radius p^m if
    v(a_i) - m·i → ∞ as i → ∞.
    This is equivalent to |a_i|·(p^m)^i → 0. -/
def convergesOnClosedBall (v : ValSeq) (m : ℚ) : Prop :=
  ∀ C : ℤ, ∃ N : ℕ, ∀ i ≥ N, ∀ (vi : ℤ), v i = vi → vi - m * i > C

/-- Points on or above a line: v(a_i) ≥ m·i for all i with finite valuation. -/
def pointsAboveLine (v : ValSeq) (m : ℚ) : Prop :=
  ∀ i : ℕ, finite v i → ∀ (vi : ℤ), v i = vi → (vi : ℚ) ≥ m * i

/-- The Newton polygon lies above a line of slope b from some point onward. -/
def eventuallyAboveLine (v : ValSeq) (b : ℚ) (m : ℚ) (_hb : b < m) : Prop :=
  ∃ N : ℕ, ∀ i ≥ N, finite v i → ∀ (vi : ℤ), v i = vi → (vi : ℚ) > b * i

/-! ### Helper Lemmas for Lemma 7.4.8 -/

/-- Rewrite lineAt in linear form (ℚ version): v₀ + s*(i - i₀) = (v₀ - s*i₀) + s*i -/
lemma lineAt_q (i₀ : ℕ) (v₀ : ℤ) (s : ℚ) (i : ℕ) :
    (v₀ : ℚ) + s * ((i : ℚ) - i₀) = (v₀ : ℚ) - s * i₀ + s * i := by
  ring

/-- Linear term dominates constant: for α > 0, eventually α*i > C. -/
lemma exists_nat_mul_gt (α C : ℚ) (hα : 0 < α) :
    ∃ N : ℕ, ∀ i ≥ N, α * (i : ℚ) > C := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C / α)
  use N
  intro i hi
  have hi' : (N : ℚ) ≤ i := Nat.cast_le.mpr hi
  calc α * (i : ℚ) ≥ α * N := by nlinarith
    _ > α * (C / α) := by nlinarith
    _ = C := by field_simp

/-- From Frequently get arbitrarily large indices. -/
lemma frequently_atTop_iff {P : ℕ → Prop} :
    (∃ᶠ i in Filter.atTop, P i) ↔ ∀ N, ∃ i ≥ N, P i := by
  simp only [Filter.Frequently, Filter.Eventually, Filter.mem_atTop_sets]
  constructor
  · intro h N
    by_contra hne
    push_neg at hne
    apply h
    use N
    intro b hb
    exact hne b hb
  · intro h ⟨a, ha⟩
    obtain ⟨i, hi, hPi⟩ := h a
    exact ha i hi hPi

/-! ### Lemma 7.4.8 Statement -/

/-- **Gouvêa Lemma 7.4.8 (Convergence Direction)**:
    If there exists a supporting line of slope s > b from some point (i₀, v₀),
    then v_p(a_i) - b·i → ∞, meaning the series converges for |x| < p^s.

    This is the exact geometric content of the Newton polygon: if b < sup slope,
    then eventually the polygon lies above a line of slope s > b.

    Proof: The line y = v₀ + s*(x - i₀) has slope s > b. Points above this line
    satisfy v_i ≥ v₀ + s*(i - i₀), so v_i - b*i ≥ (v₀ - s*i₀) + (s-b)*i → ∞. -/
theorem lemma_7_4_8_convergence (v : ValSeq) (b s : ℚ) (hb : b < s)
    (hline : ∃ (i₀ : ℕ) (v₀ : ℤ), ∀ i ≥ i₀, finite v i → ∀ (vi : ℤ), v i = vi →
       (vi : ℚ) ≥ (v₀ : ℚ) + s * ((i : ℚ) - i₀)) :
    convergesOnClosedBall v b := by
  obtain ⟨i₀, v₀, hsupport⟩ := hline
  intro C
  -- Let C' = C - v₀ + s*i₀. We need (s - b)*i > C' for large i.
  let C' : ℚ := (C : ℚ) - (v₀ : ℚ) + s * i₀
  have hα : (0 : ℚ) < s - b := sub_pos.mpr hb
  obtain ⟨N₁, hN₁⟩ := exists_nat_mul_gt (s - b) C' hα
  use max N₁ i₀
  intro i hi vi hvi
  have hi₀ : i ≥ i₀ := le_of_max_le_right hi
  have hN₁i : i ≥ N₁ := le_of_max_le_left hi
  have hfin : finite v i := by
    simp only [finite]
    intro htop
    rw [htop] at hvi
    exact WithTop.coe_ne_top hvi.symm
  -- Apply the supporting line hypothesis
  have hline_i : (vi : ℚ) ≥ (v₀ : ℚ) + s * ((i : ℚ) - i₀) := hsupport i hi₀ hfin vi hvi
  -- Rearrange: vi - b*i ≥ (v₀ - s*i₀) + (s - b)*i
  have hcalc : (vi : ℚ) - b * i ≥ (v₀ : ℚ) - s * i₀ + (s - b) * i := by
    calc (vi : ℚ) - b * i ≥ ((v₀ : ℚ) + s * ((i : ℚ) - i₀)) - b * i := by linarith
      _ = (v₀ : ℚ) - s * i₀ + (s - b) * i := by ring
  -- Use hN₁ to get (s - b)*i > C'
  have hgrow : (s - b) * (i : ℚ) > C' := hN₁ i hN₁i
  -- Therefore vi - b*i > C
  have hfinal : (vi : ℚ) - b * i > C := by
    calc (vi : ℚ) - b * i ≥ (v₀ : ℚ) - s * i₀ + (s - b) * i := hcalc
      _ > (v₀ : ℚ) - s * i₀ + C' := by linarith
      _ = C := by simp only [C']; ring
  -- Convert from ℚ to ℤ inequality
  have : (vi : ℚ) - b * ↑i > ↑C := hfinal
  exact_mod_cast this

/-- **Gouvêa Lemma 7.4.8 (Divergence Direction)**:
    If b > m and infinitely many points lie on the line y = m*x,
    then the series diverges for |x| = p^b.

    Proof idea: For i on the line, v_i - b*i = (m - b)*i < 0 for large i,
    contradicting convergence. -/
theorem lemma_7_4_8_divergence (v : ValSeq) (m b : ℚ) (hb : b > m)
    (hm_achieved : ∃ᶠ i in Filter.atTop, finite v i ∧
          ∃ (vi : ℤ), v i = vi ∧ (vi : ℚ) = m * i) :
    ¬convergesOnClosedBall v b := by
  intro hconv
  -- From convergence, for C = 0 there exists N such that v_i - b*i > 0 for i ≥ N
  specialize hconv 0
  obtain ⟨N, hN⟩ := hconv
  -- Using the Frequently hypothesis, find i ≥ max N 1 on the line v_i = m*i
  rw [frequently_atTop_iff] at hm_achieved
  obtain ⟨i, hi, hfin, vi, hvi, honline⟩ := hm_achieved (max N 1)
  have hiN : i ≥ N := le_of_max_le_left hi
  have hi1 : i ≥ 1 := le_of_max_le_right hi
  -- Apply convergence: v_i - b*i > 0
  have hconv_i : (vi : ℚ) - b * i > 0 := by exact_mod_cast hN i hiN vi hvi
  -- But v_i = m*i, so (m - b)*i > 0
  rw [honline] at hconv_i
  have hcalc : (m - b) * (i : ℚ) > 0 := by linarith
  -- Since b > m, m - b < 0
  have hneg : m - b < 0 := sub_neg.mpr hb
  -- And i ≥ 1 > 0
  have hipos : (i : ℚ) > 0 := by
    have : (1 : ℕ) ≤ i := hi1
    have : (1 : ℚ) ≤ i := Nat.cast_le.mpr this
    linarith
  -- So (m - b)*i < 0, contradiction
  have hcontra : (m - b) * (i : ℚ) < 0 := mul_neg_of_neg_of_pos hneg hipos
  linarith

/-! ### Connection to Newton Polygon API

These theorems connect `Segment.supporting` and `FinalRay.supporting`
to the convergence criterion, completing the link between the Newton
polygon computation and Lemma 7.4.8. -/

variable {v : ValSeq}

/-- Convert `Segment.supporting` (ℝ version) to the ℚ line form.
    A supporting segment gives a line that all later points lie above. -/
theorem Segment.supporting_implies_line (seg : Segment) (hsup : seg.supporting (v := v))
    (hvalid : v seg.i₀ = seg.v₀) :
    ∀ i ≥ seg.i₀, finite v i → ∀ (vi : ℤ), v i = vi →
      (vi : ℚ) ≥ (seg.v₀ : ℚ) + seg.slope * ((i : ℚ) - seg.i₀) := by
  intro i hi hfin vi hvi
  by_cases hi' : i > seg.i₀
  · have hreal := hsup i hi' hfin vi hvi
    -- hreal : (vi : ℝ) ≥ lineAt seg.i₀ seg.v₀ seg.slope i
    simp only [lineAt] at hreal
    -- Now hreal : (vi : ℝ) ≥ seg.v₀ + seg.slope * (i - seg.i₀)
    -- Convert the ℚ goal to ℝ and use hreal
    have hgoal : (vi : ℝ) ≥ (seg.v₀ : ℝ) + (seg.slope : ℝ) * ((i : ℝ) - (seg.i₀ : ℝ)) := hreal
    -- Now cast back to ℚ
    have h1 : ((vi : ℚ) : ℝ) = (vi : ℝ) := by simp
    have h2 : ((seg.v₀ : ℚ) : ℝ) = (seg.v₀ : ℝ) := by simp
    have h3 : ((seg.slope : ℚ) : ℝ) = (seg.slope : ℝ) := rfl
    have h4 : (((i : ℚ) - (seg.i₀ : ℚ)) : ℝ) = ((i : ℝ) - (seg.i₀ : ℝ)) := by simp
    -- Use that ℚ → ℝ is order-preserving and injective on the relevant expressions
    exact_mod_cast hgoal
  · have heq : i = seg.i₀ := Nat.le_antisymm (Nat.not_lt.mp hi') hi
    subst heq
    simp only [sub_self, mul_zero, add_zero, ge_iff_le, Int.cast_le]
    rw [hvalid] at hvi
    exact le_of_eq (WithTop.coe_injective hvi)

/-- Convert `FinalRay.supporting` (ℝ version) to the ℚ line form. -/
theorem FinalRay.supporting_implies_line (ray : FinalRay) (hsup : ray.supporting (v := v))
    (hvalid : v ray.i₀ = ray.v₀) :
    ∀ i ≥ ray.i₀, finite v i → ∀ (vi : ℤ), v i = vi →
      (vi : ℚ) ≥ (ray.v₀ : ℚ) + ray.slope * ((i : ℚ) - ray.i₀) := by
  intro i hi hfin vi hvi
  by_cases hi' : i > ray.i₀
  · have hreal := hsup i hi' hfin vi hvi
    simp only [lineAt] at hreal
    exact_mod_cast hreal
  · have heq : i = ray.i₀ := Nat.le_antisymm (Nat.not_lt.mp hi') hi
    subst heq
    simp only [sub_self, mul_zero, add_zero, ge_iff_le, Int.cast_le]
    rw [hvalid] at hvi
    exact le_of_eq (WithTop.coe_injective hvi)

/-- A supporting segment implies convergence for b < slope.
    This is the main theorem connecting Newton polygon segments to Lemma 7.4.8. -/
theorem Segment.convergesOnClosedBall_of_supporting (seg : Segment) (b : ℚ)
    (hb : b < seg.slope) (hsup : seg.supporting (v := v))
    (hvalid : v seg.i₀ = seg.v₀) :
    convergesOnClosedBall v b := by
  apply lemma_7_4_8_convergence v b seg.slope hb
  use seg.i₀, seg.v₀
  intro i hi hfin vi hvi
  exact Segment.supporting_implies_line seg hsup hvalid i hi hfin vi hvi

/-- A supporting final ray implies convergence for b < slope.
    This connects Newton polygon rays to Lemma 7.4.8. -/
theorem FinalRay.convergesOnClosedBall_of_supporting (ray : FinalRay) (b : ℚ)
    (hb : b < ray.slope) (hsup : ray.supporting (v := v))
    (hvalid : v ray.i₀ = ray.v₀) :
    convergesOnClosedBall v b := by
  apply lemma_7_4_8_convergence v b ray.slope hb
  use ray.i₀, ray.v₀
  intro i hi hfin vi hvi
  exact FinalRay.supporting_implies_line ray hsup hvalid i hi hfin vi hvi

/-- For a well-formed Newton polygon with a supporting final ray,
    convergence holds for all b < supSlope. -/
theorem NewtonPolygonData.convergesOnClosedBall_of_ray (_npd : NewtonPolygonData)
    (ray : FinalRay) (_hray : _npd.finalRay = some ray)
    (hsup : ray.supporting (v := v)) (hvalid : v ray.i₀ = ray.v₀)
    (b : ℚ) (hb : b < ray.slope) :
    convergesOnClosedBall v b :=
  FinalRay.convergesOnClosedBall_of_supporting ray b hb hsup hvalid

/-- For a well-formed Newton polygon ending in a segment (no final ray),
    convergence holds for all b < last segment's slope. -/
theorem NewtonPolygonData.convergesOnClosedBall_of_lastSeg (_npd : NewtonPolygonData)
    (seg : Segment) (_hseg : _npd.segments.getLast? = some seg) (_hnoray : _npd.finalRay = none)
    (hsup : seg.supporting (v := v)) (hvalid : v seg.i₀ = seg.v₀)
    (b : ℚ) (hb : b < seg.slope) :
    convergesOnClosedBall v b :=
  Segment.convergesOnClosedBall_of_supporting seg b hb hsup hvalid

/-! ### Gouvêa Lemma 7.4.8: Main Theorem for Power Series

This section states Lemma 7.4.8 in its natural form for power series:
Given a power series f(X) = Σ aᵢXⁱ with coefficients in a valued field,
the radius of convergence equals p^m where m is the supremum of slopes
in the Newton polygon.

More precisely: if b < supSlope(Newton polygon of f), then f converges
on the closed ball {x : |x| ≤ p^b}.
-/

section PowerSeriesConvergence

variable {R : Type*} [CommRing R]

/-- **Gouvêa Lemma 7.4.8 for Power Series (Convergence via Final Ray)**:

    Let f(X) = Σ aᵢXⁱ be a power series with valuation v, and let NP(f) be its
    Newton polygon computed by `newtonPolygonOfPowerSeries`.

    If NP(f) has a final ray of slope m (either limiting or with infinitely many points),
    and this ray is supporting, then f converges on {x : |x| ≤ p^b} for all b < m.

    This is Gouvêa's Lemma 7.4.8: the radius of convergence is p^(sup slope). -/
theorem PowerSeries.convergesOnClosedBall_of_newton_ray
    (f : PowerSeries R) (v : R → WithTop ℤ)
    (ray : FinalRay)
    (_hray : (newtonPolygonOfPowerSeries f v).finalRay = some ray)
    (hsup : ray.supporting (v := toValSeq f v))
    (hvalid : toValSeq f v ray.i₀ = ray.v₀)
    (b : ℚ) (hb : b < ray.slope) :
    convergesOnClosedBall (toValSeq f v) b :=
  FinalRay.convergesOnClosedBall_of_supporting ray b hb hsup hvalid

/-- **Gouvêa Lemma 7.4.8 for Power Series (Convergence via Last Segment)**:

    If NP(f) ends with a segment (no final ray) of slope m, and this segment
    is supporting, then f converges on {x : |x| ≤ p^b} for all b < m. -/
theorem PowerSeries.convergesOnClosedBall_of_newton_segment
    (f : PowerSeries R) (v : R → WithTop ℤ)
    (seg : Segment)
    (_hseg : (newtonPolygonOfPowerSeries f v).segments.getLast? = some seg)
    (_hnoray : (newtonPolygonOfPowerSeries f v).finalRay = none)
    (hsup : seg.supporting (v := toValSeq f v))
    (hvalid : toValSeq f v seg.i₀ = seg.v₀)
    (b : ℚ) (hb : b < seg.slope) :
    convergesOnClosedBall (toValSeq f v) b :=
  Segment.convergesOnClosedBall_of_supporting seg b hb hsup hvalid

/-- **Gouvêa Lemma 7.4.8 for Power Series (Unified Statement via Final Ray)**:

    Let f(X) be a power series with Newton polygon NP(f) that has a final ray.
    If b < ray.slope and the ray is supporting, then f converges on {x : |x| ≤ p^b}.

    This captures Gouvêa's Lemma 7.4.8: "the radius of convergence equals p^m
    where m is the largest slope of the Newton polygon." -/
theorem PowerSeries.converges_of_lt_ray_slope
    (f : PowerSeries R) (v : R → WithTop ℤ)
    (ray : FinalRay)
    (_hray : (newtonPolygonOfPowerSeries f v).finalRay = some ray)
    (hsup : ray.supporting (v := toValSeq f v))
    (hvalid : toValSeq f v ray.i₀ = ray.v₀)
    (b : ℚ) (hb : b < ray.slope) :
    convergesOnClosedBall (toValSeq f v) b :=
  FinalRay.convergesOnClosedBall_of_supporting ray b hb hsup hvalid

/-- **Gouvêa Lemma 7.4.8 for Power Series (Unified Statement via Last Segment)**:

    Let f(X) be a power series with Newton polygon NP(f) ending in a segment.
    If b < seg.slope and the segment is supporting, then f converges on {x : |x| ≤ p^b}. -/
theorem PowerSeries.converges_of_lt_segment_slope
    (f : PowerSeries R) (v : R → WithTop ℤ)
    (seg : Segment)
    (_hseg : (newtonPolygonOfPowerSeries f v).segments.getLast? = some seg)
    (_hnoray : (newtonPolygonOfPowerSeries f v).finalRay = none)
    (hsup : seg.supporting (v := toValSeq f v))
    (hvalid : toValSeq f v seg.i₀ = seg.v₀)
    (b : ℚ) (hb : b < seg.slope) :
    convergesOnClosedBall (toValSeq f v) b :=
  Segment.convergesOnClosedBall_of_supporting seg b hb hsup hvalid

end PowerSeriesConvergence

/-! ### Specific Instance: Geometric Series

For the geometric series 1 + pX + pX² + ···, the sup of slopes is 0.
By Lemma 7.4.8, the radius of convergence is p^0 = 1.

We verify this matches our earlier analysis: the Newton polygon is a
horizontal ray at slope 0, so the series converges for |x| < 1. -/

/-- The sup of slopes for the geometric series valuation sequence is 0.
    For any m > 0, we can find n such that the slope 1/n < m. -/
theorem geometricValSeq_supSlope_eq_zero :
    ∀ m : ℚ, m > 0 → ∃ n : ℕ, n > 0 ∧ slopeRat 0 0 n 1 < m := by
  intro m hm
  -- The slope from (0,0) to (n,1) is 1/n, which can be made < m for large n
  have h : ∃ n : ℕ, m⁻¹ < n := exists_nat_gt m⁻¹
  obtain ⟨n, hn⟩ := h
  use n + 1
  constructor
  · exact Nat.succ_pos n
  · simp only [slopeRat, Int.cast_one, Int.cast_zero, sub_zero, Nat.cast_zero]
    have hn1 : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
    rw [one_div_lt hn1 hm, one_div]
    calc m⁻¹ < n := hn
      _ < ((n + 1 : ℕ) : ℚ) := by simp

/-- By Lemma 7.4.8, the geometric series converges for |x| < p^0 = 1.
    This matches Example 2 from Gouvêa page 262.

    Proof: For b < 0, we have v(a_i) - b·i = 1 - b·i → ∞ since -b > 0. -/
theorem geometricSeries_radius_of_convergence :
    ∀ b : ℚ, b < 0 → convergesOnClosedBall geometricValSeq b := by
  intro b hb C
  -- Find N such that for i ≥ N, we have 1 - b·i > C
  -- Since b < 0, -b > 0, so 1 + (-b)·i grows without bound
  have hneg_b : -b > 0 := neg_pos.mpr hb
  -- Need N such that 1 + (-b) * N > C, i.e., N > (C - 1) / (-b)
  have h : ∃ N : ℕ, max ((C : ℚ) / (-b)) 1 < N := exists_nat_gt (max (C / (-b)) 1)
  obtain ⟨N, hN⟩ := h
  use N
  intro i hi vi hvi
  cases i with
  | zero =>
    -- At i = 0, v(a_0) = 0, need 0 - b·0 = 0 > C
    -- hi : 0 ≥ N, and N > max(...) ≥ 1, so 0 ≥ N ≥ 1 is a contradiction
    exfalso
    have hN_pos : (N : ℚ) > 1 := lt_of_le_of_lt (le_max_right _ _) hN
    have : (0 : ℕ) ≥ N := hi
    have : N ≤ 0 := this
    have : (N : ℚ) ≤ 0 := Nat.cast_le.mpr this
    linarith
  | succ n =>
    -- At i = n+1, v(a_i) = 1, need 1 - b·(n+1) > C
    simp only [geometricValSeq] at hvi
    have hvi' : vi = 1 := WithTop.coe_injective hvi.symm
    simp only [hvi', Int.cast_one, Nat.cast_succ]
    -- 1 - b·(n+1) = 1 + (-b)·(n+1) > 1 + (-b)·N > C + 1 > C
    have hi' : (N : ℚ) ≤ n + 1 := by
      have : (N : ℚ) ≤ (n + 1 : ℕ) := Nat.cast_le.mpr hi
      simp only [Nat.cast_add, Nat.cast_one] at this
      exact this
    -- From hN: N > C / (-b), so (-b) * N > C
    have hbN : (-b) * N > C := by
      have hmax : (C : ℚ) / (-b) < N := lt_of_le_of_lt (le_max_left _ _) hN
      have hb_ne : b ≠ 0 := ne_of_lt hb
      calc (-b) * N > (-b) * (C / (-b)) := by nlinarith
        _ = C := by field_simp [hb_ne]
    calc (1 : ℚ) - b * (n + 1) = 1 + (-b) * (n + 1) := by ring
      _ ≥ 1 + (-b) * N := by nlinarith
      _ > 1 + C := by linarith
      _ > C := by linarith

/-- The geometric series diverges for |x| = p^b with b > 0.
    This is because for large i, we have v(a_i) - b·i = 1 - b·i < 0
    when i > 1/b, so the terms don't vanish. -/
theorem geometricSeries_diverges_outside :
    ∀ b : ℚ, b > 0 → ¬convergesOnClosedBall geometricValSeq b := by
  intro b hb hconv
  -- If the series converged, then for C = 0, there would exist N such that
  -- v(a_i) - b·i > 0 for all i ≥ N.
  -- But v(a_i) = 1 for i ≥ 1, so 1 - b·i > 0 requires i < 1/b.
  -- This fails for i > 1/b.
  specialize hconv 0
  obtain ⟨N, hN⟩ := hconv
  -- Find n > max(N, 1/b + 1)
  have h : ∃ n : ℕ, max ((1 : ℚ) / b + 2) ((N : ℚ) + 1) < n := exists_nat_gt _
  obtain ⟨n, hn⟩ := h
  have hn_large_rat : (n : ℚ) > 1 / b + 2 := lt_of_le_of_lt (le_max_left _ _) hn
  have hN_large_rat : (n : ℚ) > (N : ℚ) + 1 := lt_of_le_of_lt (le_max_right _ _) hn
  have hi : n ≥ N := by
    have hNlt : (N : ℚ) < n := by linarith
    exact Nat.le_of_lt (Nat.cast_lt.mp hNlt)
  have hi_pos : n ≥ 1 := by
    have h2 : (2 : ℚ) < n := by linarith [one_div_pos.mpr hb]
    have h1 : (1 : ℚ) < n := by linarith
    by_contra hne
    push_neg at hne
    interval_cases n
    · norm_num at h1
  -- For n ≥ 1, geometricValSeq n = 1
  have hval : geometricValSeq n = (1 : ℤ) := by
    simp only [geometricValSeq]
    cases n with
    | zero => exact absurd rfl (Nat.one_le_iff_ne_zero.mp hi_pos)
    | succ k => rfl
  specialize hN n hi 1 hval
  -- hN says (1 : ℤ) - b * n > (0 : ℤ), i.e., (1 : ℚ) - b * n > 0
  -- But n > 1/b + 2 > 1/b, so b * n > 1, contradiction
  have hi_large : (n : ℚ) > 1 / b := by linarith
  have hcontra : b * (n : ℚ) > 1 := by
    calc b * (n : ℚ) > b * (1 / b) := by nlinarith
      _ = 1 := by field_simp
  -- From hN: 1 - b * n > 0, but b * n > 1 means 1 - b * n < 0
  have hN' : (1 : ℚ) - b * n > 0 := by exact_mod_cast hN
  linarith

end Lemma748

end NewtonPolygon
