import Proof.Supplier.SelectiveClausesZeroGuard

/-!
# The clauses guard request certificate

This module freezes the exact input tuple parsed by the arity guard and the
four component-width facts needed by its bounded writes.  It introduces no new
wire format: `totalSelectiveClausesRequest_eq_private` identifies the tuple
definitionally with the existing private clauses ABI.
-/

namespace NearCubicWires.TotalSelectiveClausesGuardedProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.PolynomialClock

open private selectiveClausesInput
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

def selectiveClausesGuardTailThree
    (literalArity decisionCode : ℕ) : ℕ :=
  Nat.pair literalArity decisionCode

def selectiveClausesGuardTailTwo
    (valuesCode literalArity decisionCode : ℕ) : ℕ :=
  Nat.pair valuesCode
    (selectiveClausesGuardTailThree literalArity decisionCode)

def selectiveClausesGuardTailOne
    (inputArity valuesCode literalArity decisionCode : ℕ) : ℕ :=
  Nat.pair inputArity
    (selectiveClausesGuardTailTwo valuesCode literalArity decisionCode)

def totalSelectiveClausesRequest
    (stateCode inputArity valuesCode literalArity decisionCode : ℕ) : ℕ :=
  Nat.pair stateCode
    (selectiveClausesGuardTailOne inputArity valuesCode literalArity decisionCode)

theorem totalSelectiveClausesRequest_eq_private
    (stateCode inputArity valuesCode literalArity decisionCode : ℕ) :
    totalSelectiveClausesRequest stateCode inputArity valuesCode literalArity
        decisionCode =
      selectiveClausesInput stateCode inputArity valuesCode literalArity
        decisionCode := by
  rfl

@[simp] theorem totalSelectiveClausesRequest_right
    (stateCode inputArity valuesCode literalArity decisionCode : ℕ) :
    (Nat.unpair
      (totalSelectiveClausesRequest stateCode inputArity valuesCode
        literalArity decisionCode)).2 =
      selectiveClausesGuardTailOne inputArity valuesCode literalArity
        decisionCode := by
  simp [totalSelectiveClausesRequest]

@[simp] theorem selectiveClausesGuardTailOne_right
    (inputArity valuesCode literalArity decisionCode : ℕ) :
    (Nat.unpair
      (selectiveClausesGuardTailOne inputArity valuesCode literalArity
        decisionCode)).2 =
      selectiveClausesGuardTailTwo valuesCode literalArity decisionCode := by
  simp [selectiveClausesGuardTailOne]

@[simp] theorem selectiveClausesGuardTailTwo_right
    (valuesCode literalArity decisionCode : ℕ) :
    (Nat.unpair
      (selectiveClausesGuardTailTwo valuesCode literalArity decisionCode)).2 =
      selectiveClausesGuardTailThree literalArity decisionCode := by
  simp [selectiveClausesGuardTailTwo]

@[simp] theorem selectiveClausesGuardTailThree_left
    (literalArity decisionCode : ℕ) :
    (Nat.unpair
      (selectiveClausesGuardTailThree literalArity decisionCode)).1 =
      literalArity := by
  simp [selectiveClausesGuardTailThree]

theorem selectiveClausesGuardTailOne_bits
    (stateCode inputArity valuesCode literalArity decisionCode maximumBits : ℕ)
    (hrequest :
      natBitLength
          (totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode) ≤ maximumBits) :
    natBitLength
        (selectiveClausesGuardTailOne inputArity valuesCode literalArity
          decisionCode) ≤ maximumBits :=
  by
    simpa only [totalSelectiveClausesRequest_right] using
      (natBitLength_mono
        (Nat.unpair_right_le
          (totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode))).trans hrequest

theorem selectiveClausesGuardTailTwo_bits
    (stateCode inputArity valuesCode literalArity decisionCode maximumBits : ℕ)
    (hrequest :
      natBitLength
          (totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode) ≤ maximumBits) :
    natBitLength
        (selectiveClausesGuardTailTwo valuesCode literalArity decisionCode) ≤
      maximumBits :=
  by
    simpa only [selectiveClausesGuardTailOne_right] using
      (natBitLength_mono
        (Nat.unpair_right_le
          (selectiveClausesGuardTailOne inputArity valuesCode literalArity
            decisionCode))).trans
        (selectiveClausesGuardTailOne_bits stateCode inputArity valuesCode
          literalArity decisionCode maximumBits hrequest)

theorem selectiveClausesGuardTailThree_bits
    (stateCode inputArity valuesCode literalArity decisionCode maximumBits : ℕ)
    (hrequest :
      natBitLength
          (totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode) ≤ maximumBits) :
    natBitLength
        (selectiveClausesGuardTailThree literalArity decisionCode) ≤
      maximumBits :=
  by
    simpa only [selectiveClausesGuardTailTwo_right] using
      (natBitLength_mono
        (Nat.unpair_right_le
          (selectiveClausesGuardTailTwo valuesCode literalArity
            decisionCode))).trans
        (selectiveClausesGuardTailTwo_bits stateCode inputArity valuesCode
          literalArity decisionCode maximumBits hrequest)

theorem selectiveClausesGuardArity_bits
    (stateCode inputArity valuesCode literalArity decisionCode maximumBits : ℕ)
    (hrequest :
      natBitLength
          (totalSelectiveClausesRequest stateCode inputArity valuesCode
            literalArity decisionCode) ≤ maximumBits) :
    natBitLength literalArity ≤ maximumBits :=
  by
    simpa only [selectiveClausesGuardTailThree_left] using
      (natBitLength_mono
        (Nat.unpair_left_le
          (selectiveClausesGuardTailThree literalArity decisionCode))).trans
        (selectiveClausesGuardTailThree_bits stateCode inputArity valuesCode
          literalArity decisionCode maximumBits hrequest)

end NearCubicWires.TotalSelectiveClausesGuardedProgram
