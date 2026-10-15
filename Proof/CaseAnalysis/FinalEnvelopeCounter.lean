import Proof.CaseAnalysis.FinalSupplierCall
import Proof.CaseAnalysis.Language

namespace NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1  The record prefixes saturate at the branch's own address count -/

/-- **Past the branch's address count a round emits nothing.**  `addressRecords`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) is a `drop k` of the address
list `univ.toList : List (Fin (2 ^ pcpp.clauseBits))`, which is empty once `k`
reaches that list's length.  This is the Lean form of "the extra rounds of the
branch-independent envelope add no calls". -/
theorem addressRecords_past_end (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {k : ℕ}
    (hk : 2 ^ pcpp.clauseBits ≤ k) :
    addressRecords answer denominator phase pcpp coordinate systematicAtom k = [] := by
  have hcard : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length
      = 2 ^ pcpp.clauseBits := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  have hle : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length ≤ k := by omega
  unfold addressRecords
  rw [List.drop_eq_nil_of_le hle]
  rfl

/-- **The accumulated stream saturates.**  At ANY round count at or above the
branch's own address count the loop's tape `81` already carries the whole phase
`phaseRecords` (`Proof/CaseAnalysis/FinalWorkerDockSeam.lean`).
`prefixRecords_full` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) is the
special case `k = 2 ^ pcpp.clauseBits`; this is the inequality the envelope
needs. -/
theorem prefixRecords_saturate (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) {k : ℕ}
    (hk : 2 ^ pcpp.clauseBits ≤ k) :
    prefixRecords answer denominator phase pcpp coordinate systematicAtom k
      = phaseRecords answer denominator phase pcpp coordinate systematicAtom := by
  have hcard : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length
      = 2 ^ pcpp.clauseBits := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  have hle : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length ≤ k := by omega
  unfold prefixRecords CloseoutFinalC10WorkerDockSeam.phaseRecords
  rw [List.take_of_length_le hle]

/-- **The loop bank past the branch's address count.**  Every tape of the
`278`-tape prefix is already at its final value; only the scratch still moves. -/
theorem loopBank_saturate (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) {k : ℕ} (hk : 2 ^ pcpp.clauseBits ≤ k) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k
      = bank
        (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
        (CompareMachine.word
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
        (List.replicate entryWidth true) input witness (scratch k) := by
  rw [loopBank_eq,
    prefixRecords_saturate answer denominator phase pcpp coordinate systematicAtom hk]

/-- **The envelope's extra rounds are bank-preserving.**  This is the whole of
the new obligation the envelope creates: at a round past the branch's own
address count the emitter is asked for a step whose `278`-tape prefix does not
move.  It is the machine-checked form of "every branch-specific power-of-two
clause list is repeated to this fixed envelope" (`paper.tex:1642`) read on the
call stream: the repetition contributes no further calls. -/
theorem loopBank_idle_eq (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) {k : ℕ} (hk : 2 ^ pcpp.clauseBits ≤ k)
    (hscratch : scratch (k + 1) = scratch k) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch (k + 1)
      = loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k := by
  rw [loopBank_saturate extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness scratch (by omega : 2 ^ pcpp.clauseBits ≤ k + 1),
    loopBank_saturate extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness scratch hk, hscratch]

/-! ## §2  The call loop at a FREE round count -/

theorem call_run_rounds (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth preFuel cost rounds : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hrounds : 2 ^ pcpp.clauseBits ≤ rounds)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word rounds)))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1)))
    (hidle : ∀ address, 2 ^ pcpp.clauseBits ≤ address → address < rounds →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1))) :
    ∃ scratchOut : ℕ → List Bool,
      Step (callMachine extra pre body)
        (2 * (preFuel + 1 + (rounds * (cost + 3) + 3)) + 2) (fun _ => 0)
        (C10TailCompose.entryOf (C10TailCompose.wflag (60 + (extra + 2))) input witness)
        (fun _ => 0)
        (bank
          (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
            (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
          (CompareMachine.word
            (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
          (List.replicate entryWidth true) input witness scratchOut) := by
  have hall : ∀ j, j < rounds →
      Step body cost (heads j)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch j)
        (heads (j + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (j + 1)) := by
    intro j hj
    rcases Nat.lt_or_ge j (2 ^ pcpp.clauseBits) with h | h
    · exact hsite j h
    · exact hidle j h hj
  have hloop := CloseoutRowsOriginalClauseLoop.run body rounds cost heads
    (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness scratch) hall
  obtain ⟨counter, hrew⟩ := C10TailCompose.step_reset (hpre.seq hloop)
  refine ⟨finalScratch extra (scratch rounds) (CompareMachine.word rounds) counter, ?_⟩
  have hfull := prefixRecords_saturate answer denominator phase pcpp coordinate systematicAtom
    hrounds
  rw [← hfull]
  refine Step.congr (Step.congr_in hrew rfl ?_) rfl ?_
  · exact (bank_succ (t := 218 + (60 + extra) + 1) (by omega) [] [] [] input witness []
      (fun _ => []) (fun _ => []) (fun _ _ => rfl) rfl).trans
      (bank_entryOf (60 + (extra + 2)) input witness)
  · have e2 : Fin.addCases (motive := fun _ => List Bool)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch rounds)
        (fun _ : Fin 1 => CompareMachine.word rounds)
        = bank
          (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
            (prefixRecords answer denominator phase pcpp coordinate systematicAtom rounds))
          (CompareMachine.word
            (prefixRecords answer denominator phase pcpp coordinate systematicAtom rounds).length)
          (List.replicate entryWidth true) input witness
          (outerScratch extra (scratch rounds) (CompareMachine.word rounds)) := by
      rw [loopBank_eq]
      exact bank_succ (t := 218 + (60 + extra)) (by omega) _ _ _ input witness _
        (scratch rounds)
        (outerScratch extra (scratch rounds) (CompareMachine.word rounds))
        (fun j hj => (if_neg (by omega)).symm) (if_pos rfl)
    have e3 := bank_succ (t := 218 + (60 + extra) + 1) (by omega)
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom rounds))
      (CompareMachine.word
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom rounds).length)
      (List.replicate entryWidth true) input witness counter
      (outerScratch extra (scratch rounds) (CompareMachine.word rounds))
      (finalScratch extra (scratch rounds) (CompareMachine.word rounds) counter)
      (fun j hj => (if_neg (by omega)).symm) (if_pos rfl)
    exact (congrArg
      (fun f => Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin 1 => counter)) e2).trans
      e3

/-! ## §3  The same, as S0's `CallsReady` -/

/-- **`callsReady_of_call` at a free round count.**  Same repack as
`callsReady_of_call` (`Proof/CaseAnalysis/FinalSupplierCall.lean`); the stream
delivered is the branch's own `phaseRecords`, exactly as `CallsReady`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`) demands, because the envelope's
extra rounds append nothing. -/
theorem callsReady_of_call_rounds (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost rounds : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hrounds : 2 ^ pcpp.clauseBits ≤ rounds)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word rounds)))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1)))
    (hidle : ∀ address, 2 ^ pcpp.clauseBits ≤ address → address < rounds →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1))) :
    C10SupplierStage.CallsReady (extra + 2) (callMachine extra pre body)
      (2 * (preFuel + 1 + (rounds * (cost + 3) + 3)) + 2) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness := by
  obtain ⟨scratchOut, hstep⟩ := call_run_rounds extra pre body answer denominator phase pcpp
    coordinate systematicAtom entryWidth preFuel cost rounds input witness heads scratch
    hrounds hpre hsite hidle
  refine ⟨_, hstep, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [wordsBank_bank]
    show CompareMachine.word
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = CompareMachine.word callCount
    rw [hlen]
  · intro j h2 h81 h90 h216 h218
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    have hlt := j.isLt
    rw [wordsBank_bank]
    unfold bankAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## §4  The deliverable: the counter at the paper's envelope -/

/-- **The counter is a function of the LENGTH alone.**  `rounds` instantiated at
the paper's branch-independent address count `M = 2 ^ r(N)`, `r(N) =
clauseWidth clauseDegree q` (`Proof/CaseAnalysis/Language.lean`), which
`paper.tex:4516` names as "exactly `log_2 M` for `M = 2^(ceil (d_G log_2 (q+2)))`".

Read the binders: the address counter the prologue must write is
`CompareMachine.word (2 ^ clauseWidth clauseDegree q)` and the budget is
`callFuel preFuel (clauseWidth clauseDegree q) cost`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`).  Neither mentions `pcpp`.  The
decoded branch enters only through `hfit` -- the paper's `M_0 <= M`, which
`live_clause_fit` (`Proof/CaseAnalysis/CommonCutoff.lean`) proves with `q` the
native width at the selected scale, a function of the length -- and through the
record stream the loop delivers, which is and must remain the branch's own
`phaseRecords`.

This is what dissolves the prologue's PCPP decode: a machine meeting `hpre` has
to count out `2 ^ clauseWidth clauseDegree q` unary cells from `q`, and `q`
never depended on the witness. -/
theorem callsReady_at_clauseWidth (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q))))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1)))
    (hidle : ∀ address, 2 ^ pcpp.clauseBits ≤ address →
        address < 2 ^ clauseWidth clauseDegree q →
      Step body cost (heads address)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch address)
        (heads (address + 1))
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (address + 1))) :
    C10SupplierStage.CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness :=
  callsReady_of_call_rounds extra pre body answer denominator phase pcpp coordinate
    systematicAtom entryWidth callCount preFuel cost (2 ^ clauseWidth clauseDegree q)
    input witness heads scratch hlen (Nat.pow_le_pow_right (by omega) hfit) hpre hsite hidle

/-- **Exactly what is left of `hpre`'s counter half, measured.**  The word the
prologue must lay down on tape `218 + (60 + extra)` is
`2 ^ clauseWidth clauseDegree q + 1` cells long -- `CompareMachine.word`
(`Proof/PCP/VerifierDecodingCompare.lean`) is `false :: List.replicate n true`.
Every quantity on the right is a function of `clauseDegree` and `q`; the decoded
`pcpp` does not appear.  That is the residual obligation: a unary exponentiator
driven from the length, not a PCPP decoder. -/
theorem counter_length (clauseDegree q : ℕ) :
    (CompareMachine.word (2 ^ clauseWidth clauseDegree q)).length
      = 2 ^ clauseWidth clauseDegree q + 1 := by
  unfold CompareMachine.word
  rw [List.length_cons, List.length_replicate]

end NearCubicWires.RepairSource.CloseoutFinal.C10EnvelopeCounter
