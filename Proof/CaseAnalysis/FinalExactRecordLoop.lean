import Proof.CaseAnalysis.FinalExactFraction
import Proof.CaseAnalysis.FinalRoundCursor

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactRecordLoop

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionRecords
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (callEntry siteCalls
  siteRecords CoefficientsFit)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth
  joinScalarWidth_eq flag result inputTape port)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader (emitLoader)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold (foldWidth)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry
  contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other
  install_existing)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes (Realizes)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam (stagedBody stagedFuel)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (worker workerBudget)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform (roundBank)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage (Rounds)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.SupplierEstimator
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 The per-address record list, at an arbitrary per-call denominator -/

/-- **The records emitted at one PCPP clause address**, at a record function that
is an arbitrary function of the address AND the monomial.  Same shape as
`siteRecords` (`Proof/CaseAnalysis/FinalSupplierCalls.lean`); the difference is
that `callEntry` (`Proof/CaseAnalysis/FinalSupplierCalls.lean`) threads ONE
`denominator : ℕ` through every record, and `record address` need not. -/
noncomputable def siteRecords' (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (address : Fin (2 ^ pcpp.clauseBits)) : List Entry :=
  (siteCalls phase pcpp coordinate systematicAtom address).monomials.map (record address)

/-- EXACTFRAC's `phaseRecords'` (`Proof/CaseAnalysis/FinalExactFraction.lean`)
is the flatten of §1's per-address lists, exactly as `phaseRecords`
(`Proof/CaseAnalysis/FinalWorkerDockSeam.lean`) is the flatten of `siteRecords`. -/
theorem phaseRecords'_flatMap (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) :
    phaseRecords' phase pcpp coordinate systematicAtom record
      = (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
        (siteRecords' phase pcpp coordinate systematicAtom record) := rfl

/-- **The scalar route is the constant record function.**  Compiled, so the claim
that this file generalises rather than forks is not a reading. -/
theorem siteRecords'_scalar (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    siteRecords' phase pcpp coordinate systematicAtom (fun _ => callEntry answer denominator)
      = siteRecords answer denominator phase pcpp coordinate systematicAtom := rfl

/-- **The records of the first `k` clause addresses** -- the content of tape `81`
after `k` rounds.  `prefixRecords` (`Proof/CaseAnalysis/FinalSupplierCall.lean`)
at the per-call record. -/
noncomputable def prefixRecords' (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (k : ℕ) : List Entry :=
  ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.take k).flatMap
    (siteRecords' phase pcpp coordinate systematicAtom record)

/-- **The records of clause address number `k`**: what round `k` must append.
`addressRecords` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) at the per-call
record. -/
noncomputable def addressRecords' (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (k : ℕ) : List Entry :=
  (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1).flatMap
    (siteRecords' phase pcpp coordinate systematicAtom record)

/-- The scalar prefix family is the constant record function's. -/
theorem prefixRecords'_scalar (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ) :
    prefixRecords' phase pcpp coordinate systematicAtom
        (fun _ => callEntry answer denominator) k
      = prefixRecords answer denominator phase pcpp coordinate systematicAtom k := rfl

theorem prefixRecords'_zero (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) :
    prefixRecords' phase pcpp coordinate systematicAtom record 0 = [] := rfl

/-- **One round, one clause address.**  `prefixRecords_succ`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) at the per-call record. -/
theorem prefixRecords'_succ (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (k : ℕ) :
    prefixRecords' phase pcpp coordinate systematicAtom record (k + 1)
      = prefixRecords' phase pcpp coordinate systematicAtom record k
        ++ addressRecords' phase pcpp coordinate systematicAtom record k := by
  unfold prefixRecords' addressRecords'
  rw [List.take_add, List.flatMap_append]

/-- **Round `k` emits one clause address's calls**, for `k` below the address
count.  `addressRecords_site` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) at
the per-call record. -/
theorem addressRecords'_site (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) (k : ℕ)
    (hk : k < 2 ^ pcpp.clauseBits) :
    ∃ address : Fin (2 ^ pcpp.clauseBits),
      addressRecords' phase pcpp coordinate systematicAtom record k
        = siteRecords' phase pcpp coordinate systematicAtom record address := by
  have hlen : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).length
      = 2 ^ pcpp.clauseBits - k := by
    rw [List.length_drop, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  cases hd : (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k with
  | nil =>
      rw [hd] at hlen
      simp only [List.length_nil] at hlen
      omega
  | cons address rest =>
      refine ⟨address, ?_⟩
      unfold addressRecords'
      rw [hd]
      simp

/-- **Past the branch's address count a round emits nothing.**
`addressRecords_past_end` (`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`) at the
per-call record. -/
theorem addressRecords'_past_end (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) {k : ℕ}
    (hk : 2 ^ pcpp.clauseBits ≤ k) :
    addressRecords' phase pcpp coordinate systematicAtom record k = [] := by
  have hcard : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length
      = 2 ^ pcpp.clauseBits := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  have hle : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length ≤ k := by omega
  unfold addressRecords'
  rw [List.drop_eq_nil_of_le hle]
  rfl

theorem prefixRecords'_saturate (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) {k : ℕ}
    (hk : 2 ^ pcpp.clauseBits ≤ k) :
    prefixRecords' phase pcpp coordinate systematicAtom record k
      = phaseRecords' phase pcpp coordinate systematicAtom record := by
  have hcard : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length
      = 2 ^ pcpp.clauseBits := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  have hle : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length ≤ k := by omega
  unfold prefixRecords'
  rw [List.take_of_length_le hle]
  rfl

/-- **The whole loop is the whole phase.**  `prefixRecords_full`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) at the per-call record. -/
theorem prefixRecords'_full (phase : CloseoutRowsOriginalSchedule.Phase)
    (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry) :
    prefixRecords' phase pcpp coordinate systematicAtom record (2 ^ pcpp.clauseBits)
      = phaseRecords' phase pcpp coordinate systematicAtom record :=
  prefixRecords'_saturate phase pcpp coordinate systematicAtom record le_rfl

/-! ## §2 The loop bank, at an abstract record prefix -/

/-- **The loop bank at one record prefix.**  `loopBank`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) with the six binders
`answer denominator phase pcpp coordinate systematicAtom` replaced by the ONE list
they were only ever used to name. -/
noncomputable def prefixBank (extra entryWidth : ℕ) (xs : List Entry)
    (input witness : List Bool) (s : ℕ → List Bool) : Fin (218 + (60 + extra)) → List Bool :=
  bank
    (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth xs)
    (CompareMachine.word xs.length)
    (List.replicate entryWidth true) input witness s

theorem loopBank_prefixBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k
      = prefixBank extra entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom k)
        input witness (scratch k) := rfl

theorem roundBank_prefixBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s k
      = prefixBank extra entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom k)
        input witness s := rfl

/-- **Round zero is branch-free** -- the empty stream and `CompareMachine.word 0`.
`roundBank_zero` (`Proof/CaseAnalysis/FinalSiteBodyUniform.lean`) at the abstract
prefix. -/
theorem prefixBank_nil (extra entryWidth : ℕ) (input witness : List Bool)
    (s : ℕ → List Bool) :
    prefixBank extra entryWidth [] input witness s
      = bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness s := rfl

/-! ## §3 The clause-address loop, at an abstract record prefix family -/

/-- **`call_run_rounds` (`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`) at an
abstract prefix family.**  Binder for binder the same statement with the six record
binders replaced by `pfx : ℕ → List Entry`, and with the active and idle ranges
merged into the one hypothesis `hround` the envelope already gives at every round
below `rounds` (`call_run_rounds` splits them only to name the residual).

The exit list is `pfx rounds`; `hfull` names it, which is where
`prefixRecords'_saturate` enters at the instantiation. -/
theorem call_run_prefix (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (entryWidth preFuel cost rounds : ℕ)
    (pfx : ℕ → List Entry) (full : List Entry) (hfull : pfx rounds = full)
    (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (prefixBank extra entryWidth (pfx 0) input witness (scratch 0))
        (fun _ : Fin 1 => CompareMachine.word rounds)))
    (hround : ∀ address, address < rounds →
      Step body cost (heads address)
        (prefixBank extra entryWidth (pfx address) input witness (scratch address))
        (heads (address + 1))
        (prefixBank extra entryWidth (pfx (address + 1)) input witness (scratch (address + 1)))) :
    ∃ scratchOut : ℕ → List Bool,
      Step (callMachine extra pre body)
        (2 * (preFuel + 1 + (rounds * (cost + 3) + 3)) + 2) (fun _ => 0)
        (entryOf (wflag (60 + (extra + 2))) input witness)
        (fun _ => 0)
        (bank
          (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth full)
          (CompareMachine.word full.length)
          (List.replicate entryWidth true) input witness scratchOut) := by
  subst hfull
  have hloop := CloseoutRowsOriginalClauseLoop.run body rounds cost heads
    (fun k => prefixBank extra entryWidth (pfx k) input witness (scratch k)) hround
  obtain ⟨counter, hrew⟩ := step_reset (hpre.seq hloop)
  refine ⟨finalScratch extra (scratch rounds) (CompareMachine.word rounds) counter, ?_⟩
  refine Step.congr (Step.congr_in hrew rfl ?_) rfl ?_
  · exact (bank_succ (t := 218 + (60 + extra) + 1) (by omega) [] [] [] input witness []
      (fun _ => []) (fun _ => []) (fun _ _ => rfl) rfl).trans
      (bank_entryOf (60 + (extra + 2)) input witness)
  · have e2 : Fin.addCases (motive := fun _ => List Bool)
        (prefixBank extra entryWidth (pfx rounds) input witness (scratch rounds))
        (fun _ : Fin 1 => CompareMachine.word rounds)
        = bank
          (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth (pfx rounds))
          (CompareMachine.word (pfx rounds).length)
          (List.replicate entryWidth true) input witness
          (outerScratch extra (scratch rounds) (CompareMachine.word rounds)) :=
      bank_succ (t := 218 + (60 + extra)) (by omega) _ _ _ input witness _
        (scratch rounds)
        (outerScratch extra (scratch rounds) (CompareMachine.word rounds))
        (fun j hj => (if_neg (by omega)).symm) (if_pos rfl)
    have e3 := bank_succ (t := 218 + (60 + extra) + 1) (by omega)
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth (pfx rounds))
      (CompareMachine.word (pfx rounds).length)
      (List.replicate entryWidth true) input witness counter
      (outerScratch extra (scratch rounds) (CompareMachine.word rounds))
      (finalScratch extra (scratch rounds) (CompareMachine.word rounds) counter)
      (fun j hj => (if_neg (by omega)).symm) (if_pos rfl)
    exact (congrArg
      (fun f => Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin 1 => counter)) e2).trans
      e3

theorem callsReady_of_prefix (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (entryWidth callCount preFuel cost rounds : ℕ)
    (pfx : ℕ → List Entry) (full : List Entry) (hfull : pfx rounds = full)
    (hlen : full.length = callCount) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (prefixBank extra entryWidth (pfx 0) input witness (scratch 0))
        (fun _ : Fin 1 => CompareMachine.word rounds)))
    (hround : ∀ address, address < rounds →
      Step body cost (heads address)
        (prefixBank extra entryWidth (pfx address) input witness (scratch address))
        (heads (address + 1))
        (prefixBank extra entryWidth (pfx (address + 1)) input witness (scratch (address + 1)))) :
    CallsReady (extra + 2) (callMachine extra pre body)
      (2 * (preFuel + 1 + (rounds * (cost + 3) + 3)) + 2) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth full) input witness := by
  obtain ⟨scratchOut, hstep⟩ := call_run_prefix extra pre body entryWidth preFuel cost rounds
    pfx full hfull input witness heads scratch hpre hround
  refine ⟨_, hstep, rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [wordsBank_bank]
    show CompareMachine.word full.length = CompareMachine.word callCount
    rw [hlen]
  · intro j h2 h81 h90 h216 h218
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    have hlt := j.isLt
    rw [wordsBank_bank]
    unfold bankAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem callsReady_at_clauseWidth' (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (entryWidth callCount preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hlen : (phaseRecords' phase pcpp coordinate systematicAtom record).length = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hpre : Step pre preFuel (fun _ => 0)
      (bank [] [] [] input witness (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record 0) input witness (scratch 0))
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q))))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step body cost (heads address)
        (prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record address)
          input witness (scratch address))
        (heads (address + 1))
        (prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record (address + 1))
          input witness (scratch (address + 1))))
    (hidle : ∀ address, 2 ^ pcpp.clauseBits ≤ address →
        address < 2 ^ clauseWidth clauseDegree q →
      Step body cost (heads address)
        (prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record address)
          input witness (scratch address))
        (heads (address + 1))
        (prefixBank extra entryWidth
          (prefixRecords' phase pcpp coordinate systematicAtom record (address + 1))
          input witness (scratch (address + 1)))) :
    CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords' phase pcpp coordinate systematicAtom record))
      input witness := by
  have henv : 2 ^ pcpp.clauseBits ≤ 2 ^ clauseWidth clauseDegree q :=
    Nat.pow_le_pow_right (by omega) hfit
  refine callsReady_of_prefix extra pre body entryWidth callCount preFuel cost
    (2 ^ clauseWidth clauseDegree q)
    (prefixRecords' phase pcpp coordinate systematicAtom record)
    (phaseRecords' phase pcpp coordinate systematicAtom record)
    (prefixRecords'_saturate phase pcpp coordinate systematicAtom record henv) hlen
    input witness heads scratch hpre ?_
  intro address haddress
  rcases Nat.lt_or_ge address (2 ^ pcpp.clauseBits) with h | h
  · exact hsite address h
  · exact hidle address h haddress

/-! ## §4 `Rounds` at an abstract record prefix family -/

def Rounds' (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (pfx : ℕ → List Entry) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop) : Prop :=
  ∀ (k : ℕ) (s : ℕ → List Bool), Inv k s →
    ∃ s' : ℕ → List Bool, Inv (k + 1) s' ∧
      Step body cost (fun _ => 0)
        (prefixBank extra entryWidth (pfx k) input witness s)
        (fun _ => 0)
        (prefixBank extra entryWidth (pfx (k + 1)) input witness s')

theorem rounds_iff_rounds' (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop) :
    Rounds' extra body cost entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom)
        input witness Inv
      ↔ Rounds extra body cost entryWidth answer denominator phase pcpp
        coordinate systematicAtom input witness Inv := Iff.rfl

/-- **The per-round choices, chained with the invariant carried along.**  The
generic core of `chain_of_rounds`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`): it mentions no bank, so the
same lemma serves both routes.  This is the only place a choice principle enters
this module. -/
theorem chain_with_inv {α : Type} (Inv : ℕ → α → Prop) (P : ℕ → α → α → Prop)
    (hstep : ∀ (k : ℕ) (a : α), Inv k a → ∃ b : α, Inv (k + 1) b ∧ P k a b)
    (a₀ : α) (h0 : Inv 0 a₀) :
    ∃ f : ℕ → α, f 0 = a₀ ∧ ∀ k, P k (f k) (f (k + 1)) := by
  classical
  have hchoice : ∀ (k : ℕ) (a : α), ∃ b : α, Inv k a → Inv (k + 1) b ∧ P k a b := by
    intro k a
    by_cases hk : Inv k a
    · obtain ⟨b, hb, hp⟩ := hstep k a hk
      exact ⟨b, fun _ => ⟨hb, hp⟩⟩
    · exact ⟨a, fun hc => absurd hc hk⟩
  choose g hg using hchoice
  refine ⟨fun k => Nat.rec (motive := fun _ => α) a₀ (fun j b => g j b) k, rfl, ?_⟩
  have hinv : ∀ k : ℕ,
      Inv k (Nat.rec (motive := fun _ => α) a₀ (fun j b => g j b) k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => exact ((hg k _) ih).1
  intro k
  exact ((hg k _) (hinv k)).2

/-- **`chain_of_rounds` (`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) at an
abstract prefix family.** -/
theorem chain_of_rounds' (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth : ℕ) (pfx : ℕ → List Entry) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (hrounds : Rounds' extra body cost entryWidth pfx input witness Inv)
    (w : ℕ → List Bool) (hw : Inv 0 w) :
    ∃ scratch : ℕ → ℕ → List Bool, scratch 0 = w ∧
      ∀ k : ℕ, Step body cost (fun _ => 0)
        (prefixBank extra entryWidth (pfx k) input witness (scratch k))
        (fun _ => 0)
        (prefixBank extra entryWidth (pfx (k + 1)) input witness (scratch (k + 1))) :=
  chain_with_inv Inv
    (fun k a b => Step body cost (fun _ => 0)
      (prefixBank extra entryWidth (pfx k) input witness a) (fun _ => 0)
      (prefixBank extra entryWidth (pfx (k + 1)) input witness b))
    hrounds w hw

theorem callsReady_of_rounds' (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (entryWidth callCount preFuel cost clauseDegree q : ℕ) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (hlen : (phaseRecords' phase pcpp coordinate systematicAtom record).length = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hrounds : Rounds' extra body cost entryWidth
      (prefixRecords' phase pcpp coordinate systematicAtom record) input witness Inv)
    (hpre : ∃ w : ℕ → List Bool, Inv 0 w ∧
      Step pre preFuel (fun _ => 0)
        (bank [] [] [] input witness (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))) :
    CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords' phase pcpp coordinate systematicAtom record))
      input witness := by
  obtain ⟨w, hw, hstep⟩ := hpre
  obtain ⟨scratch, hs0, hchain⟩ :=
    chain_of_rounds' extra body cost entryWidth
      (prefixRecords' phase pcpp coordinate systematicAtom record) input witness Inv hrounds w hw
  refine callsReady_at_clauseWidth' extra pre body phase pcpp coordinate systematicAtom record
    entryWidth callCount preFuel cost clauseDegree q input witness
    (fun _ => fun _ => 0) scratch hlen hfit ?_ ?_ ?_
  · rw [hs0]
    exact hstep
  · intro address _
    exact hchain address
  · intro address _ _
    exact hchain address

/-! ## §5 The supplier stage, at an abstract record list -/

theorem stage_run' (extra : ℕ) {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (ph : CloseoutRowsOriginalSchedule.Phase)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (records : List Entry)
    (hlen : records.length = callCount len)
    (hcalls : CallsReady extra (calls ph) (callFuel ph len) (entryWidth len)
      (callCount len)
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len) records)
      (List.ofFn x) bits)
    {sp : ℕ} (p : Machine (218 + (60 + extra)) sp) (ht : 2 ≤ 218 + (60 + extra)) :
    ∃ (bankTapes : Fin 218 → List Bool) (scratchTapes : Fin (60 + extra) → List Bool),
      Step (stage extra calls ph)
        (stageFuel callFuel entryWidth callCount ph len) (fun _ => 0)
        (exitTapes (Fin.castAdd (60 + extra) flag)
          ((UAcceptanceCarrier.verifier p ht (Fin.castAdd (60 + extra) result)).inputTapes
            (List.ofFn x) bits) 0 true)
        (fun _ => 0) (Fin.addCases bankTapes scratchTapes) ∧
      bankTapes 81 = CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len) records ∧
      bankTapes 90 = CompareMachine.word records.length ∧
      DockReady (entryWidth len) records bankTapes ∧
      EmitEntry (joinScalarWidth (entryWidth len) records.length) bankTapes ∧
      bankTapes 0 = frame (List.ofFn x) ∧ bankTapes 1 = frame bits ∧ bankTapes 216 = [true] ∧
      scratchTapes ⟨56, by omega⟩ =
        List.replicate (joinScalarWidth (entryWidth len) records.length) true ∧
      scratchTapes ⟨57, by omega⟩ =
        List.replicate (CompetitorRationalDecision.width
          (joinScalarWidth (entryWidth len) records.length)) true := by
  classical
  obtain ⟨mid, hstep, m81, m90, m218, m0, m1, m216, mblank⟩ := hcalls
  obtain ⟨Hw, Aw, hws, hwh, w83, w84, w85, w86, w90, w98, w176, w182, w186, w187,
    w213, w214, w274, w275, wfr⟩ :=
    CloseoutFinalC10WordsStage.words_step (entryWidth len) (callCount len)
      (fun _ => 0) (wordsBank extra mid) (fun _ => rfl) m218 m90
      (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        refine mblank i ?_ ?_ ?_ ?_ ?_ <;> omega)
      (by
        intro i hi
        refine mblank i ?_ ?_ ?_ ?_ ?_ <;> omega)
  have hHw : Hw = fun _ => 0 := funext hwh
  subst hHw
  have hfocus := hws.focus (wslot extra) (wslot_inj extra)
    (fun _ => 0) mid
  rw [dockH_zero, install_existing (wslot extra) mid
    (wordsBank extra mid) (fun _ => rfl)] at hfocus
  have hentry := entry_eq p ht (Fin.castAdd (60 + extra) result)
    (wflag (60 + extra)) (by simp) (by simp) (List.ofFn x) bits
  have hrun : Step (stage extra calls ph)
      (stageFuel callFuel entryWidth callCount ph len) (fun _ => 0)
      (exitTapes (Fin.castAdd (60 + extra) flag)
        ((UAcceptanceCarrier.verifier p ht (Fin.castAdd (60 + extra) result)).inputTapes
          (List.ofFn x) bits) 0 true)
      (fun _ => 0) (install (wslot extra) mid Aw) :=
    (hstep.seq hfocus).congr_in rfl hentry.symm
  have hb : ∀ (k : Fin 218) (j : Fin (219 + CloseoutFinalC10WordsStage.s)), k.val = j.val →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k) = Aw j := by
    intro k j hkj
    rw [castAdd_eq_wslot extra k j hkj]
    exact install_slot (wslot extra) (wslot_inj extra) mid Aw j
  have hsc : ∀ (k : Fin (60 + extra)) (j : Fin (219 + CloseoutFinalC10WordsStage.s)),
      218 + k.val = j.val →
      install (wslot extra) mid Aw (Fin.natAdd 218 k) = Aw j := by
    intro k j hkj
    rw [natAdd_eq_wslot extra k j hkj]
    exact install_slot (wslot extra) (wslot_inj extra) mid Aw j
  have hkeep : ∀ (k : Fin 218) (j : Fin (219 + CloseoutFinalC10WordsStage.s)), k.val = j.val →
      j.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} : Finset ℕ) →
      j.val < 219 →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k)
        = wordsBank extra mid j :=
    fun k j h hm hl => (hb k j h).trans (wfr j hm hl)
  have b81 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (81 : Fin 218)) =
      CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len) records :=
    (hkeep 81 81 rfl (by decide) (by decide)).trans m81
  have b83 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (83 : Fin 218)) =
      List.replicate (CompetitorRationalDecision.width (entryWidth len)) true :=
    (hb 83 83 rfl).trans w83
  have b84 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (84 : Fin 218)) =
      List.replicate (CompetitorRationalDecision.width
        (joinScalarWidth (entryWidth len) records.length)) true := by
    rw [hlen]; exact (hb 84 84 rfl).trans w84
  have b85 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (85 : Fin 218)) =
      List.replicate (joinScalarWidth (entryWidth len) records.length) true := by
    rw [hlen]; exact (hb 85 85 rfl).trans w85
  have b86 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (86 : Fin 218)) =
      List.replicate (CompetitorReusableDecision.capacity
        (joinScalarWidth (entryWidth len) records.length)) true := by
    rw [hlen]; exact (hb 86 86 rfl).trans w86
  have b90 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (90 : Fin 218)) =
      CompareMachine.word records.length := by
    rw [hlen]; exact (hb 90 90 rfl).trans w90
  have b98 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (98 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (84 : Fin 218)) :=
    ((hb 98 98 rfl).trans w98).trans (hb 84 84 rfl).symm
  have b176 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (176 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (85 : Fin 218)) :=
    ((hb 176 176 rfl).trans w176).trans (hb 85 85 rfl).symm
  have b182 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (182 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (86 : Fin 218)) :=
    ((hb 182 182 rfl).trans w182).trans (hb 86 86 rfl).symm
  have b186 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (186 : Fin 218)) =
      CompareMachine.word records.length := by
    rw [hlen]; exact (hb 186 186 rfl).trans w186
  have b187 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (187 : Fin 218)) =
      List.replicate (joinScalarWidth (entryWidth len) records.length) true := by
    rw [hlen]; exact (hb 187 187 rfl).trans w187
  have b213 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (213 : Fin 218)) =
      frame (SignedSortKey.binary
        (joinScalarWidth (entryWidth len) records.length) 1) := by
    rw [hlen]; exact (hb 213 213 rfl).trans w213
  have b214 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (214 : Fin 218)) =
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) (213 : Fin 218)) :=
    ((hb 214 214 rfl).trans w214).trans (hb 213 213 rfl).symm
  have bblank : ∀ i : Fin 218, 2 ≤ i.val → i.val < 187 →
      i.val ≠ 81 → i.val ≠ 83 → i.val ≠ 84 → i.val ≠ 85 → i.val ≠ 86 → i.val ≠ 90 →
      i.val ≠ 98 → i.val ≠ 176 → i.val ≠ 182 → i.val ≠ 186 →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) i) = [] := by
    intro i h2 hlt c81 c83 c84 c85 c86 c90 c98 c176 c182 c186
    have hi := i.isLt
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    refine (hkeep i ⟨i.val, by omega⟩ rfl ?_ ?_).trans ?_
    · show i.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · show i.val < 219
      omega
    · refine mblank _ ?_ ?_ ?_ ?_ ?_
      · show 2 ≤ i.val
        omega
      · show i.val ≠ 81
        omega
      · show i.val ≠ 90
        omega
      · show i.val ≠ 216
        omega
      · show i.val ≠ 218
        omega
  have banswer : ∀ i : Fin 218, 187 < i.val → i.val < 216 → i.val ≠ 213 → i.val ≠ 214 →
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) i) = [] := by
    intro i hlt hlt' c213 c214
    have hi := i.isLt
    have hs : CloseoutFinalC10WordsStage.s = 59 := rfl
    refine (hkeep i ⟨i.val, by omega⟩ rfl ?_ ?_).trans ?_
    · show i.val ∉ ({83, 84, 85, 86, 90, 98, 176, 182, 186, 187, 213, 214, 218} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · show i.val < 219
      omega
    · refine mblank _ ?_ ?_ ?_ ?_ ?_
      · show 2 ≤ i.val
        omega
      · show i.val ≠ 81
        omega
      · show i.val ≠ 90
        omega
      · show i.val ≠ 216
        omega
      · show i.val ≠ 218
        omega
  have bready := CloseoutFinalC10WordsStage.ready_of_words (entryWidth len) records
    (fun k : Fin 218 =>
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k))
    b81 ⟨b83, b84, b85, b86, b90, b98, b176, b182, b186, b187, b213, b214⟩ bblank banswer
  have b0 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (0 : Fin 218)) =
      frame (List.ofFn x) := (hkeep 0 0 rfl (by decide) (by decide)).trans m0
  have b1 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (1 : Fin 218)) =
      frame bits := (hkeep 1 1 rfl (by decide) (by decide)).trans m1
  have b216 : install (wslot extra) mid Aw
      (Fin.castAdd (60 + extra) (216 : Fin 218)) =
      [true] := (hkeep 216 216 rfl (by decide) (by decide)).trans m216
  have s274 : install (wslot extra) mid Aw
      (Fin.natAdd 218 (⟨56, by omega⟩ : Fin (60 + extra))) =
      List.replicate (joinScalarWidth (entryWidth len) records.length) true := by
    rw [hlen]
    exact ((hsc ⟨56, by omega⟩ ⟨274, by decide⟩ rfl).trans w274).trans w85
  have s275 : install (wslot extra) mid Aw
      (Fin.natAdd 218 (⟨57, by omega⟩ : Fin (60 + extra))) =
      List.replicate (CompetitorRationalDecision.width
        (joinScalarWidth (entryWidth len) records.length)) true := by
    rw [hlen]
    exact ((hsc ⟨57, by omega⟩ ⟨275, by decide⟩ rfl).trans w275).trans w84
  exact ⟨fun k : Fin 218 =>
      install (wslot extra) mid Aw (Fin.castAdd (60 + extra) k),
    fun k : Fin (60 + extra) =>
      install (wslot extra) mid Aw (Fin.natAdd 218 k),
    (addCases_restrict
      (install (wslot extra) mid Aw)).symm ▸ hrun,
    b81, b90, bready.1, bready.2, b0, b1, b216, s274, s275⟩

/-! ## §6 The two objects the tail consumes, at A.13.9's own per-call fraction -/

/-- The two retained width words, read off the stage's own scratch.  This is
`width_of_scratch` (`Proof/CaseAnalysis/FinalStageSeamBridge.lean`) re-proved here
rather than imported, because `StageSeamBridge` is not in this file's import cone
and the lemma is eighteen lines of `Fin` arithmetic with no record content. -/
theorem width_of_scratch' {e : ℕ} (he : 58 ≤ e) (b : ℕ)
    (bankTapes : Fin 218 → List Bool) (scratchTapes : Fin e → List Bool)
    (h56 : scratchTapes ⟨56, by omega⟩ = List.replicate b true)
    (h57 : scratchTapes ⟨57, by omega⟩ =
      List.replicate (CompetitorRationalDecision.width b) true) :
    ∀ j, Fin.addCases bankTapes scratchTapes
        (retained e he j)
      = widthWord b j := by
  have key : ∀ (m : ℕ) (hm : m < 2) (hjv : 56 + m < e),
      Fin.addCases bankTapes scratchTapes
          (retained e he ⟨m, hm⟩)
        = scratchTapes ⟨56 + m, hjv⟩ := by
    intro m hm hjv
    have hi : retained e he ⟨m, hm⟩
        = (⟨56 + m, hjv⟩ : Fin e).natAdd 218 := by
      apply Fin.ext
      show 274 + m = 218 + (56 + m)
      omega
    rw [hi, Fin.addCases_right]
  rintro ⟨m, hm⟩
  interval_cases m
  · exact (key 0 (by omega) (by omega)).trans h56
  · exact (key 1 (by omega) (by omega)).trans h57

/-- `foldWidth (width entryWidth) entries = joinScalarWidth entryWidth entries.length`, over
`joinScalarWidth_eq` (`Proof/CaseAnalysis/FinalWorkerDock.lean`).  The same three lines as
`foldWidth_eq_joinScalarWidth` (`Proof/CaseAnalysis/FinalStageContracts.lean`), re-proved here
because `StageContracts` is not in this file's import cone. -/
theorem foldWidth_eq_joinScalarWidth' (entryWidth : ℕ) (entries : List Entry) :
    foldWidth (CompetitorRationalDecision.width entryWidth) entries
      = joinScalarWidth entryWidth entries.length :=
  (joinScalarWidth_eq entryWidth entries).symm

/-- **`StageReady`'s content, at the paper's own per-call fraction.**  Every field
of `StageReady` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at
`records := phaseRecords' … (exactFractionRecord …)`: the stage `Step`, the docked
bank, the emit entry, the two gate tapes and the two retained width words.
`hrecords` pins the list to A.13.9's own numerator/denominator pair
(`paper.tex:3161`), so nothing here is satisfiable by a stream that carries a
common denominator only. -/
theorem exactRecord_stageReady (extra : ℕ) (he : 58 ≤ 60 + extra)
    {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (num den : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → ℕ)
    (records : List Entry)
    (hrecords : records = phaseRecords' phase pcpp coordinate systematicAtom
      (exactFractionRecord (2 ^ pcpp.clauseBits) num den))
    (onset len : ℕ) (x : BitInput len) (bits : List Bool)
    (hlen : records.length = callCount len)
    (hcalls : CallsReady extra (calls phase) (callFuel phase len)
      (entryWidth len) (callCount len)
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len) records)
      (List.ofFn x) bits) :
    ∃ (bankTapes : Fin 218 → List Bool) (scratchTapes : Fin (60 + extra) → List Bool),
      Step (stage extra calls phase)
        (stageFuel callFuel entryWidth callCount phase len) (fun _ => 0)
        (exitTapes (Fin.castAdd (60 + extra) flag)
          ((UAcceptanceCarrier.verifier
            (worker onset (Fin.castAdd (60 + extra) inputTape)
              (Fin.castAdd (60 + extra) flag) (Fin.castAdd (60 + extra) result)
              (stagedBody (stage extra calls phase) emitLoader))
            (by omega) (Fin.castAdd (60 + extra) result)).inputTapes
            (List.ofFn x) bits) 0 true)
        (fun _ => 0) (Fin.addCases bankTapes scratchTapes) ∧
      DockReady (entryWidth len) records bankTapes ∧
      EmitEntry (joinScalarWidth (entryWidth len) records.length) bankTapes ∧
      bankTapes 0 = frame (List.ofFn x) ∧ bankTapes 1 = frame bits ∧
      (∀ j, Fin.addCases bankTapes scratchTapes
          (retained (60 + extra) he j)
        = widthWord
          (joinScalarWidth (entryWidth len) records.length) j) := by
  subst hrecords
  obtain ⟨bankTapes, scratchTapes, hstep, _h81, _h90, hready, hentry, h0, h1, _h216, w56, w57⟩ :=
    stage_run' extra calls callFuel entryWidth callCount phase len x bits _ hlen hcalls
      (worker onset (Fin.castAdd (60 + extra) inputTape) (Fin.castAdd (60 + extra) flag)
        (Fin.castAdd (60 + extra) result)
        (stagedBody (stage extra calls phase) emitLoader))
      (by omega)
  exact ⟨bankTapes, scratchTapes, hstep, hready, hentry, h0, h1,
    width_of_scratch' he _ bankTapes scratchTapes w56 w57⟩

/-- **Consumer 3, reached from the loop.**  `BlockRunsWidths`
(`Proof/CaseAnalysis/FinalBodyWidths.lean`) -- the object `blocks_run`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`) hands the verdict composer --
at the per-call record stream, from `CallsReady` alone.  EXACTFRAC's
`exactFraction_widths` is the semantic half; `stage_run'` is the physical half;
this is the two joined, so the attachment is machine-checked and not read. -/
theorem exactRecord_widths (extra : ℕ) (he : 58 ≤ 60 + extra)
    {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (num den : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → ℕ)
    (onset len : ℕ) (x : BitInput len) (bits : List Bool)
    (hnum : ∀ address monomial, num address monomial < 2 ^ entryWidth len)
    (hden : ∀ address monomial, den address monomial < 2 ^ entryWidth len)
    (hdenPos : ∀ address monomial, 0 < den address monomial)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit (entryWidth len) (siteCalls phase pcpp coordinate systematicAtom address))
    (records : List Entry)
    (hrecords : records = phaseRecords' phase pcpp coordinate systematicAtom
      (exactFractionRecord (2 ^ pcpp.clauseBits) num den))
    (hlen : records.length = callCount len)
    (hcalls : CallsReady extra (calls phase) (callFuel phase len)
      (entryWidth len) (callCount len)
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len) records)
      (List.ofFn x) bits) :
    BlockRunsWidths (60 + extra) he
      (stagedBody (stage extra calls phase) emitLoader)
      (stagedFuel (stageFuel callFuel entryWidth callCount phase)
        (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
          (joinScalarWidth (entryWidth len) records.length))
        (entryWidth len) records.length len)
      (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth (CompetitorRationalDecision.width (entryWidth len)) records)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions records)) 1 1)
      (foldWidth (CompetitorRationalDecision.width (entryWidth len)) records) := by
  obtain ⟨bankTapes, scratchTapes, hstep, h81, h90, hready, hentry, h0, h1, h216, w56, w57⟩ :=
    stage_run' extra calls callFuel entryWidth callCount phase len x bits records hlen hcalls
      (worker onset (Fin.castAdd (60 + extra) inputTape) (Fin.castAdd (60 + extra) flag)
        (Fin.castAdd (60 + extra) result)
        (stagedBody (stage extra calls phase) emitLoader))
      (by omega)
  subst hrecords
  exact exactFraction_widths he phase pcpp coordinate systematicAtom (entryWidth len)
    num den (fun a m _ => hnum a m) (fun a m _ => hden a m) hdenPos hcoefficients onset
    (stage extra calls phase)
    (stageFuel callFuel entryWidth callCount phase)
    (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
      (joinScalarWidth (entryWidth len)
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length))
    len x bits bankTapes scratchTapes hready hentry h0 h1 rfl hstep
    (fun j => by
      rw [foldWidth_eq_joinScalarWidth' (entryWidth len)
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den))]
      exact width_of_scratch' he _ bankTapes scratchTapes w56 w57 j)

theorem exactRecord_realizes {source : PointwisePCPPAlgorithm} (extra : ℕ)
    {cs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (calls : (ph : CloseoutRowsOriginalSchedule.Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (entryWidth callCount : ℕ → ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit) (evaluate : Atom → BitInput arity → Bool)
    (proofValue : BitInput arity → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input = parityOn (pcpp.systematicSupport index) input)
    (supplier : List Atom → ℚ)
    (num den : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → ℕ)
    (onset len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (hratio : ∀ (address : Fin (2 ^ pcpp.clauseBits)) (monomial : CircuitMonomial Atom 4),
      ((num address monomial : ℚ) / (den address monomial : ℚ)) = supplier monomial.factors)
    (hnum : ∀ address monomial, num address monomial < 2 ^ entryWidth len)
    (hden : ∀ address monomial, den address monomial < 2 ^ entryWidth len)
    (hdenPos : ∀ address monomial, 0 < den address monomial)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit (entryWidth len) (siteCalls phase pcpp coordinate systematicAtom address))
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass : ℚ) : ℝ)
      ≤ mass)
    (hbudget : failure * mass ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (records : List Entry)
    (hrecords : records = phaseRecords' phase pcpp coordinate systematicAtom
      (exactFractionRecord (2 ^ pcpp.clauseBits) num den))
    (hlen : records.length = callCount len)
    (hcalls : CallsReady extra (calls phase) (callFuel phase len)
      (entryWidth len) (callCount len)
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len) records)
      (List.ofFn x) bits) :
    Nonempty (Realizes phase constants pcpp proofValue evaluate
      (worker onset (Fin.castAdd (60 + extra) inputTape) (Fin.castAdd (60 + extra) flag)
        (Fin.castAdd (60 + extra) result)
        (stagedBody (stage extra calls phase) emitLoader))
      (workerBudget onset
        (stagedFuel (stageFuel callFuel entryWidth callCount phase)
          (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
            (joinScalarWidth (entryWidth len) records.length))
          (entryWidth len) records.length) len)
      (fun _ => 0)
      ((UAcceptanceCarrier.verifier
        (worker onset (Fin.castAdd (60 + extra) inputTape) (Fin.castAdd (60 + extra) flag)
          (Fin.castAdd (60 + extra) result)
          (stagedBody (stage extra calls phase) emitLoader))
        (by omega) (Fin.castAdd (60 + extra) result)).inputTapes (List.ofFn x) bits)
      (Fin.castAdd (60 + extra) port)
      (foldWidth (CompetitorRationalDecision.width (entryWidth len)) records)) := by
  obtain ⟨bankTapes, scratchTapes, hstep, h81, h90, hready, hentry, h0, h1, h216, w56, w57⟩ :=
    stage_run' extra calls callFuel entryWidth callCount phase len x bits records hlen hcalls
      (worker onset (Fin.castAdd (60 + extra) inputTape) (Fin.castAdd (60 + extra) flag)
        (Fin.castAdd (60 + extra) result)
        (stagedBody (stage extra calls phase) emitLoader))
      (by omega)
  subst hrecords
  exact ⟨exactFraction_realizes phase constants pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic supplier (entryWidth len) num den hratio (fun a m _ => hnum a m) (fun a m _ => hden a m) hdenPos
    hcoefficients failure hfailure hpoint mass hmass hbudget onset
    (stage extra calls phase)
    (stageFuel callFuel entryWidth callCount phase)
    (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
      (joinScalarWidth (entryWidth len)
        (phaseRecords' phase pcpp coordinate systematicAtom
          (exactFractionRecord (2 ^ pcpp.clauseBits) num den)).length))
    len x bits honset bankTapes scratchTapes hready hentry rfl hstep⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactRecordLoop
