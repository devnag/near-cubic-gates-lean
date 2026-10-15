import Mathlib
import Proof.Foundations.Semantics
import Proof.Foundations.ThresholdCompiler

/-!
# Constructive strict-layer adapters

This file kernel-checks the convention changes used before the lower-bound
transfer.  The statements are deliberately independent of a particular circuit
encoding: existing bottom-gate contributions are left abstract, while every
direct input-to-top occurrence is replaced by one identity threshold gate and
one gate-to-top occurrence.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.StrictLayerAdapters

open NearCubicWires.ThresholdCompiler

/-- The one-input threshold `[x ≥ 1]` used to eliminate skip-layer wires. -/
def identityBottom (value : Bool) : Bool :=
  if 1 ≤ bitInt value then true else false

theorem identityBottom_eq (value : Bool) : identityBottom value = value := by
  cases value <;> decide

/-- The same identity as an actual retained-support threshold gate.  The
support proof prevents a resource argument from silently charging a zero
coefficient or omitting the input incidence. -/
def identityGate {n : ℕ} (index : Fin n) : RealThresholdGate n where
  weight := fun candidate => if candidate = index then 1 else 0
  threshold := 1
  support := {index}
  mem_support_iff := by
    intro candidate
    simp [eq_comm]

theorem identityGate_eval {n : ℕ} (index : Fin n) (input : BitInput n) :
    (identityGate index).eval input = input index := by
  classical
  change decide (1 ≤ ∑ candidate,
    (if candidate = index then (1 : ℝ) else 0) *
      bitAsReal (input candidate)) = input index
  have hsum :
      (∑ candidate,
        (if candidate = index then (1 : ℝ) else 0) *
          bitAsReal (input candidate)) =
        bitAsReal (input index) := by
    calc
      _ = ∑ candidate, if candidate = index
          then bitAsReal (input candidate) else 0 := by
            apply Finset.sum_congr rfl
            intro candidate _
            by_cases hcandidate : candidate = index <;> simp [hcandidate]
      _ = bitAsReal (input index) := by simp
  rw [hsum]
  cases input index <;> norm_num [bitAsReal]

theorem identityGate_supportCard {n : ℕ} (index : Fin n) :
    (identityGate index).support.card = 1 := by
  simp [identityGate]

/-- Replacing every weighted direct input by its identity-bottom output leaves
the integer score at a threshold top unchanged. -/
theorem thresholdSkipLayerScore
    {Bottom Input : Type} [Fintype Bottom] [Fintype Input]
    (bottomValue : Bottom → Bool) (bottomWeight : Bottom → ℤ)
    (inputValue : Input → Bool) (directWeight : Input → ℤ) :
    (∑ gate, bottomWeight gate * bitInt (bottomValue gate)) +
        (∑ input, directWeight input * bitInt (inputValue input)) =
      (∑ gate, bottomWeight gate * bitInt (bottomValue gate)) +
        (∑ input, directWeight input *
          bitInt (identityBottom (inputValue input))) := by
  simp only [identityBottom_eq]

theorem thresholdSkipLayerSemantics
    {Bottom Input : Type} [Fintype Bottom] [Fintype Input]
    (bottomValue : Bottom → Bool) (bottomWeight : Bottom → ℤ)
    (inputValue : Input → Bool) (directWeight : Input → ℤ)
    (threshold : ℤ) :
    ((∑ gate, bottomWeight gate * bitInt (bottomValue gate)) +
          (∑ input, directWeight input * bitInt (inputValue input)) ≥ threshold) ↔
      ((∑ gate, bottomWeight gate * bitInt (bottomValue gate)) +
          (∑ input, directWeight input *
            bitInt (identityBottom (inputValue input))) ≥ threshold) := by
  rw [thresholdSkipLayerScore]

/-- Real-valued threshold tops use the same adapter; this version connects the
integer compiler seam above to the concrete circuit semantics in
`Proof/Foundations/Semantics.lean`. -/
theorem realThresholdSkipLayerScore
    {Bottom Direct : Type} [Fintype Bottom] [Fintype Direct]
    (bottomValue : Bottom → Bool) (bottomWeight : Bottom → ℝ)
    (directValue : Direct → Bool) (directWeight : Direct → ℝ) :
    (∑ gate, bottomWeight gate * bitAsReal (bottomValue gate)) +
        (∑ direct, directWeight direct * bitAsReal (directValue direct)) =
      (∑ gate, bottomWeight gate * bitAsReal (bottomValue gate)) +
        (∑ direct, directWeight direct *
          bitAsReal (identityBottom (directValue direct))) := by
  simp only [identityBottom_eq]

theorem realThresholdSkipLayerSemantics
    {Bottom Direct : Type} [Fintype Bottom] [Fintype Direct]
    (bottomValue : Bottom → Bool) (bottomWeight : Bottom → ℝ)
    (directValue : Direct → Bool) (directWeight : Direct → ℝ)
    (threshold : ℝ) :
    (threshold ≤
        (∑ gate, bottomWeight gate * bitAsReal (bottomValue gate)) +
          (∑ direct, directWeight direct * bitAsReal (directValue direct))) ↔
      (threshold ≤
        (∑ gate, bottomWeight gate * bitAsReal (bottomValue gate)) +
          (∑ direct, directWeight direct *
            bitAsReal (identityBottom (directValue direct)))) := by
  rw [realThresholdSkipLayerScore]

/-- Symmetric tops see the same Hamming-count index after the strict-layer
translation, so an arbitrary lookup table returns the same output. -/
theorem symmetricSkipLayerCount
    {Bottom Input : Type} [Fintype Bottom] [Fintype Input]
    (bottomValue : Bottom → Bool) (inputValue : Input → Bool) :
    (∑ gate, bitInt (bottomValue gate)) +
        (∑ input, bitInt (inputValue input)) =
      (∑ gate, bitInt (bottomValue gate)) +
        (∑ input, bitInt (identityBottom (inputValue input))) := by
  simp only [identityBottom_eq]

theorem symmetricSkipLayerSemantics
    {Bottom Input : Type} [Fintype Bottom] [Fintype Input]
    (bottomValue : Bottom → Bool) (inputValue : Input → Bool)
    (lookup : ℤ → Bool) :
    lookup ((∑ gate, bitInt (bottomValue gate)) +
        (∑ input, bitInt (inputValue input))) =
      lookup ((∑ gate, bitInt (bottomValue gate)) +
        (∑ input, bitInt (identityBottom (inputValue input)))) := by
  rw [symmetricSkipLayerCount]

/-- Physical wires before and after replacing `direct` skip-layer occurrences.
`existing` already includes both incidences of every retained bottom gate. -/
def skipLayerWires (existing direct : ℕ) : ℕ := existing + direct

def strictLayerWires (existing direct : ℕ) : ℕ := existing + 2 * direct

theorem strictLayerWireIdentity (existing direct : ℕ) :
    strictLayerWires existing direct =
      skipLayerWires existing direct + direct := by
  simp [strictLayerWires, skipLayerWires]
  omega

theorem directWires_le_skipLayerWires (existing direct : ℕ) :
    direct ≤ skipLayerWires existing direct := by
  simp [skipLayerWires]

theorem strictLayerWireFactorTwo (existing direct : ℕ) :
    strictLayerWires existing direct ≤ 2 * skipLayerWires existing direct := by
  simp [strictLayerWires, skipLayerWires]
  omega

/-- Halving a positive cap coefficient exactly pays for the worst-case
factor-two strict-layer translation. -/
theorem halfCoefficientPaysTranslation
    (oldWires newWires : ℕ) (coefficient scale : ℚ)
    (htranslation : (newWires : ℚ) ≤ 2 * oldWires)
    (hold : (oldWires : ℚ) ≤ coefficient * scale / 2) :
    (newWires : ℚ) ≤ coefficient * scale := by
  calc
    (newWires : ℚ) ≤ 2 * oldWires := htranslation
    _ ≤ 2 * (coefficient * scale / 2) :=
      mul_le_mul_of_nonneg_left hold (by norm_num)
    _ = coefficient * scale := by ring

/-- A restriction fixes the right summand of a disjoint input type. -/
def restrictFunction
    {Live Frozen : Type}
    (function : (Live ⊕ Frozen → Bool) → Bool)
    (frozen : Frozen → Bool) :
    (Live → Bool) → Bool :=
  fun live => function (Sum.elim live frozen)

/-- Padding adds ignored variables without changing the original function. -/
def padFunction
    {Input Padding : Type}
    (function : (Input → Bool) → Bool) :
    (Input ⊕ Padding → Bool) → Bool :=
  fun padded => function (fun input => padded (.inl input))

theorem padFunction_ignores
    {Input Padding : Type}
    (function : (Input → Bool) → Bool)
    (input : Input → Bool) (left right : Padding → Bool) :
    padFunction function (Sum.elim input left) =
      padFunction function (Sum.elim input right) := by
  rfl

theorem restrict_pad_roundTrip
    {Input Padding : Type}
    (function : (Input → Bool) → Bool)
    (padding : Padding → Bool) :
    restrictFunction (padFunction function) padding = function := by
  funext input
  rfl

/-- Output negation is semantic complementation and introduces no new input
coordinate; circuit-specific wire preservation is supplied by the typed
normalization contract. -/
def negateFunction
    {Input : Type} (function : (Input → Bool) → Bool) :
    (Input → Bool) → Bool :=
  fun input => !(function input)

theorem negateFunction_involutive
    {Input : Type} (function : (Input → Bool) → Bool) :
    negateFunction (negateFunction function) = function := by
  funext input
  simp [negateFunction]

end NearCubicWires.StrictLayerAdapters
