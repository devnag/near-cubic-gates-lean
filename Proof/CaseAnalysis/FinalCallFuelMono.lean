import Proof.CaseAnalysis.FinalSupplierCall

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CallFuelMono

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage (CallsReady)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1  `CallsReady` is monotone in its fuel -/

theorem callsReady_enlarge {extra cs : ℕ} {calls : Machine (218 + (60 + extra)) cs}
    {fuel fuel' entryWidth callCount : ℕ} {stream input witness : List Bool}
    (h : CallsReady extra calls fuel entryWidth callCount stream input witness)
    (hfuel : fuel ≤ fuel') :
    CallsReady extra calls fuel' entryWidth callCount stream input witness := by
  obtain ⟨mid, hstep, hbank⟩ := h
  exact ⟨mid, hstep.enlarge hfuel, hbank⟩

/-! ## §2  `callFuel` is monotone in `clauseBits` -/

/-- **`callFuel` is monotone in the clause-address width.**  `callFuel preFuel
clauseBits cost = 2*(preFuel + 1 + (2^clauseBits*(cost+3) + 3)) + 2`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`): the loop pays `cost+3` per
clause address and there are `2^clauseBits` of them, so widening the address
space can only widen the budget.  This is the Lean form of "every
branch-specific power-of-two clause list is repeated to this fixed envelope"
(`paper.tex:1642`) -- the branch-specific `M_0 = 2^clauseBits` is charged at the
branch-independent `M = 2^envelopeBits`. -/
theorem callFuel_mono_clauseBits (preFuel cost : ℕ) {clauseBits envelopeBits : ℕ}
    (hfit : clauseBits ≤ envelopeBits) :
    callFuel preFuel clauseBits cost ≤ callFuel preFuel envelopeBits cost := by
  have hpow : (2 : ℕ) ^ clauseBits ≤ 2 ^ envelopeBits := Nat.pow_le_pow_right (by omega) hfit
  have hmul := Nat.mul_le_mul hpow (Nat.le_refl (cost + 3))
  unfold callFuel
  omega

/-! ## §3  The consequence that discharges `hcalls` -/

/-- **The lift, at `callFuel`.**  A `CallsReady` held at the branch-specific
clause width is a `CallsReady` at any envelope above it.  This is the composite
`hcalls` needs: `live_clause_fit` (`Proof/CaseAnalysis/CommonCutoff.lean`) supplies
`hfit`, and `envelopeBits := clauseWidth clauseDegree q` is a function of the
LENGTH alone, so the resulting fuel has the shape
`Parts.callFuel : Phase → ℕ → ℕ` (`Proof/CaseAnalysis/FinalStageSeamBridge.lean`)
requires. -/
theorem callsReady_at_envelope {extra cs : ℕ} {calls : Machine (218 + (60 + extra)) cs}
    {preFuel clauseBits envelopeBits cost entryWidth callCount : ℕ}
    {stream input witness : List Bool}
    (h : CallsReady extra calls (callFuel preFuel clauseBits cost)
      entryWidth callCount stream input witness)
    (hfit : clauseBits ≤ envelopeBits) :
    CallsReady extra calls (callFuel preFuel envelopeBits cost)
      entryWidth callCount stream input witness :=
  callsReady_enlarge h (callFuel_mono_clauseBits preFuel cost hfit)

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

theorem callsReady_of_call_envelope (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost envelopeBits : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ pcpp.clauseBits))))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1)))
    (hfit : pcpp.clauseBits ≤ envelopeBits) :
    CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel envelopeBits cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness :=
  callsReady_at_envelope
    (callsReady_of_call extra pre body answer denominator phase pcpp coordinate systematicAtom
      entryWidth callCount preFuel cost input witness heads scratch hlen hpre hsite) hfit

end NearCubicWires.RepairSource.CloseoutFinal.C10CallFuelMono
