import Proof.CaseAnalysis.FinalSupplierStage

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The bank `CallsReady` describes, written once -/

/-- **The prologue's exit bank, as a function of the tape NUMBER.**  Every
clause of `C10SupplierStage.CallsReady` is one branch of this `if`-chain, and
nothing else of the `278`-tape prefix is written. -/
def bankAt (stream count driver input witness : List Bool) (scratch : ℕ → List Bool)
    (v : ℕ) : List Bool :=
  if v = 0 then frame input
  else if v = 1 then frame witness
  else if v = 81 then stream
  else if v = 90 then count
  else if v = 216 then [true]
  else if v = 218 then driver
  else if 278 ≤ v then scratch v
  else []

/-- The same, at any bank width. -/
def bank {t : ℕ} (stream count driver input witness : List Bool) (scratch : ℕ → List Bool)
    (i : Fin t) : List Bool :=
  bankAt stream count driver input witness scratch i.val

/-- The gate's exit tapes, by tape number: `wflag` is `216`. -/
theorem entryOf_apply (e : ℕ) (input witness : List Bool) (i : Fin (218 + e)) :
    C10TailCompose.entryOf (C10TailCompose.wflag e) input witness i =
      if i.val = 216 then [true]
      else if i.val = 0 then frame input
      else if i.val = 1 then frame witness else [] := by
  by_cases h : i.val = 216
  · have hi : i = C10TailCompose.wflag e :=
      Fin.ext (by rw [h, C10TailCompose.wflag_val])
    simp [C10TailCompose.entryOf, hi]
  · have hi : i ≠ C10TailCompose.wflag e := by
      intro hh
      exact h (by rw [hh, C10TailCompose.wflag_val])
    simp [C10TailCompose.entryOf, hi, h]

/-- **The entry bank IS the gate's exit bank.**  The empty stream, the empty
counter, the empty driver word and empty scratch. -/
theorem bank_entryOf (e : ℕ) (input witness : List Bool) :
    (bank [] [] [] input witness (fun _ => []) : Fin (218 + e) → List Bool)
      = C10TailCompose.entryOf (C10TailCompose.wflag e) input witness := by
  funext i
  rw [entryOf_apply]
  show bankAt [] [] [] input witness (fun _ => []) i.val = _
  unfold bankAt
  split_ifs <;> first | rfl | omega

/-- **One more tape.**  Both the loop's address counter and the head reset's
mark tape land at index `>= 278`, i.e. in the scratch region, so the bank
expression is unchanged. -/
theorem bank_succ {t : ℕ} (ht : 278 ≤ t) (stream count driver input witness top : List Bool)
    (sc1 sc2 : ℕ → List Bool) (h : ∀ j, j < t → sc1 j = sc2 j) (htop : sc2 t = top) :
    Fin.addCases (motive := fun _ => List Bool)
        (bank stream count driver input witness sc1 : Fin t → List Bool)
        (fun _ : Fin 1 => top)
      = (bank stream count driver input witness sc2 : Fin (t + 1) → List Bool) := by
  funext i
  refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    show bankAt stream count driver input witness sc1 j.val
        = bankAt stream count driver input witness sc2 j.val
    unfold bankAt
    split_ifs <;> first | rfl | exact h j.val j.isLt
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd t j : Fin (t + 1)).val = t := by
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      show t + j.val = t
      omega
    show (fun _ : Fin 1 => top) j
        = bankAt stream count driver input witness sc2 (Fin.natAdd t j : Fin (t + 1)).val
    rw [hv]
    show top = bankAt stream count driver input witness sc2 t
    unfold bankAt
    rw [if_neg (by omega : ¬ (t = 0)), if_neg (by omega : ¬ (t = 1)),
      if_neg (by omega : ¬ (t = 81)), if_neg (by omega : ¬ (t = 90)),
      if_neg (by omega : ¬ (t = 216)), if_neg (by omega : ¬ (t = 218)), if_pos ht]
    exact htop.symm

theorem bank_scratch_congr {t : ℕ} (stream count driver input witness : List Bool)
    (sc1 sc2 : ℕ → List Bool) (h : ∀ j, j < t → sc1 j = sc2 j) :
    (bank stream count driver input witness sc1 : Fin t → List Bool)
      = bank stream count driver input witness sc2 := by
  funext i
  show bankAt stream count driver input witness sc1 i.val
      = bankAt stream count driver input witness sc2 i.val
  unfold bankAt
  split_ifs <;> first | rfl | exact h i.val i.isLt

/-- `C10SupplierStage.wordsBank` reads this bank by tape number. -/
theorem wordsBank_bank (extra : ℕ) (stream count driver input witness : List Bool)
    (scratch : ℕ → List Bool) (j : Fin (219 + CloseoutFinalC10WordsStage.s)) :
    C10SupplierStage.wordsBank (extra + 2)
        (bank stream count driver input witness scratch) j
      = bankAt stream count driver input witness scratch j.val := rfl

/-! ## §2 The clause-address prefixes of the phase's record stream -/

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-- **The records of the first `k` clause addresses.**  `phaseRecords` is
`univ.toList.flatMap (siteRecords ...)`; this is the same `flatMap` over the
first `k` entries of that address list, i.e. the content of tape `81` after `k`
rounds of the loop. -/
noncomputable def prefixRecords (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ) : List Entry :=
  ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.take k).flatMap
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)

/-- **The records of clause address number `k`**: what round `k` of the loop
must append. -/
noncomputable def addressRecords (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ) : List Entry :=
  (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1).flatMap
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)

theorem prefixRecords_zero (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    prefixRecords answer denominator phase pcpp coordinate systematicAtom 0 = [] := rfl

/-- **One round, one clause address.** -/
theorem prefixRecords_succ (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ) :
    prefixRecords answer denominator phase pcpp coordinate systematicAtom (k + 1)
      = prefixRecords answer denominator phase pcpp coordinate systematicAtom k
        ++ addressRecords answer denominator phase pcpp coordinate systematicAtom k := by
  unfold prefixRecords addressRecords
  rw [List.take_add, List.flatMap_append]

/-- **Round `k` emits one clause address's calls**, for `k` below the address
count: `addressRecords` is `siteRecords` at a real `Fin (2 ^ clauseBits)`. -/
theorem addressRecords_site (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ)
    (hk : k < 2 ^ pcpp.clauseBits) :
    ∃ address : Fin (2 ^ pcpp.clauseBits),
      addressRecords answer denominator phase pcpp coordinate systematicAtom k
        = siteRecords answer denominator phase pcpp coordinate systematicAtom address := by
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
      unfold addressRecords
      rw [hd]
      simp

/-- **The whole loop is the whole phase.**  At `k = 2 ^ pcpp.clauseBits` the
prefix is `phaseRecords` itself -- the list `stage_run` names. -/
theorem prefixRecords_full (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    prefixRecords answer denominator phase pcpp coordinate systematicAtom (2 ^ pcpp.clauseBits)
      = phaseRecords answer denominator phase pcpp coordinate systematicAtom := by
  have hcard : ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList).length
      = 2 ^ pcpp.clauseBits := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  unfold prefixRecords CloseoutFinalC10WorkerDockSeam.phaseRecords
  rw [List.take_of_length_le (le_of_eq hcard)]

/-- The encoded stream splits along the address list exactly as the record list
does: appending a clause address's records appends its words. -/
theorem words_append (b : ℕ) (xs ys : List Entry) :
    CloseoutRowsEstimatorCoefficients.Stream.words b (xs ++ ys)
      = CloseoutRowsEstimatorCoefficients.Stream.words b xs
        ++ CloseoutRowsEstimatorCoefficients.Stream.words b ys := by
  unfold CloseoutRowsEstimatorCoefficients.Stream.words
  rw [List.flatMap_append]

/-! ## §3 The loop's bank family -/

/-- **The bank after `k` rounds**: the first `k` clause addresses' calls encoded
on tape `81`, their count on tape `90`, the driver word on `218`, the gate's
tapes `0`/`1`/`216` untouched, the rest of `0 .. 277` blank. -/
noncomputable def loopBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) : Fin (218 + (60 + extra)) → List Bool :=
  bank
    (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k))
    (CompareMachine.word
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length)
    (List.replicate entryWidth true) input witness (scratch k)

theorem loopBank_eq (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k
      = bank
        (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k))
        (CompareMachine.word
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length)
        (List.replicate entryWidth true) input witness (scratch k) := rfl

noncomputable def callMachine (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs) :=
  Rewind.machine (Composition.machine pre (RepeatMachine.machine body (fun _ _ => true)))

/-- **The budget.**  `Rewind`'s `2*n+2` over `Step.seq`'s one bridge step over
`CloseoutRowsOriginalClauseLoop.run`'s `N*(cost+3)+3`. -/
def callFuel (preFuel clauseBits cost : ℕ) : ℕ :=
  2 * (preFuel + 1 + (2 ^ clauseBits * (cost + 3) + 3)) + 2

def rowFuel (preFuel cost : ℕ) : ℕ := 2 * cost + 2 * preFuel + 18

/-- **S0's `hcall`.**  `callFuel <= rowCount * rowFuel` at
`rowCount := 2 ^ clauseBits` -- the clause-address count -- because the loop's
constant residues and the prologue are each charged once and there is at least
one address. -/
theorem callFuel_le_row (preFuel clauseBits cost : ℕ) :
    callFuel preFuel clauseBits cost ≤ 2 ^ clauseBits * rowFuel preFuel cost := by
  have hN : 1 ≤ 2 ^ clauseBits := Nat.one_le_pow _ 2 (by norm_num)
  have key : ∀ N : ℕ, 1 ≤ N →
      2 * (preFuel + 1 + (N * (cost + 3) + 3)) + 2 ≤ N * (2 * cost + 2 * preFuel + 18) := by
    intro N hNpos
    have e1 : N * (2 * cost + 2 * preFuel + 18)
        = N * (2 * cost) + N * (2 * preFuel) + N * 18 := by ring
    have e2 : 2 * (preFuel + 1 + (N * (cost + 3) + 3)) + 2
        = N * (2 * cost) + N * 6 + 2 * preFuel + 10 := by ring
    have b1 : 2 * preFuel ≤ N * (2 * preFuel) := by
      calc 2 * preFuel = 1 * (2 * preFuel) := by ring
        _ ≤ N * (2 * preFuel) := Nat.mul_le_mul hNpos (le_refl _)
    have b2 : N * 6 + 10 ≤ N * 18 := by
      have hb : 12 ≤ N * 12 := by
        calc (12 : ℕ) = 1 * 12 := by ring
          _ ≤ N * 12 := Nat.mul_le_mul hNpos (le_refl _)
      have hsplit : N * 18 = N * 6 + N * 12 := by ring
      omega
    omega
  exact key _ hN

theorem stageFuel_split_of_call
    (preFuel clauseBits cost : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ)
    (entryWidth callCount : ℕ → ℕ)
    (driver : CloseoutRowsOriginalSchedule.Phase → ℕ → ℕ) (onset : ℕ)
    (hdriver : ∀ ph N, onset ≤ N →
      C10SupplierStage.driverFuel entryWidth callCount N ≤ driver ph N) :
    ∀ ph N, onset ≤ N →
      C10SupplierStage.stageFuel
          (fun ph N => callFuel (preFuel ph N) (clauseBits ph N) (cost ph N))
          entryWidth callCount ph N
        ≤ driver ph N
          + (fun ph N => 2 ^ clauseBits ph N) ph N
            * (fun ph N => rowFuel (preFuel ph N) (cost ph N)) ph N :=
  C10SupplierStage.stageFuel_split _ entryWidth callCount driver
    (fun ph N => 2 ^ clauseBits ph N) (fun ph N => rowFuel (preFuel ph N) (cost ph N)) onset
    (fun _ _ _ => callFuel_le_row _ _ _) hdriver

/-! ## §5 The two scratch extensions -/

/-- The address counter's tape, at index `218 + (60 + extra)`. -/
def outerScratch (extra : ℕ) (base : ℕ → List Bool) (loopWord : List Bool) (j : ℕ) :
    List Bool :=
  if j = 218 + (60 + extra) then loopWord else base j

/-- The head-reset mark tape, at index `218 + (60 + extra) + 1`. -/
def finalScratch (extra : ℕ) (base : ℕ → List Bool) (loopWord counter : List Bool) (j : ℕ) :
    List Bool :=
  if j = 218 + (60 + extra) + 1 then counter else outerScratch extra base loopWord j

/-! ## §6 `call_run` -- the clause-address loop, run -/

/-- **S1.**  One run of the call loop, from the gate's own exit tapes at heads
zero, ending at heads zero with the WHOLE phase's call-record stream
`Stream.words entryWidth (phaseRecords ...)` on bank tape `81`, its length on
tape `90`, the driver word on `218`, tapes `0`/`1`/`216` as received and every
other tape of `0 .. 277` blank.

Paper C.10.1 (`paper.tex:4133-4142`): the machine estimates
`mu = E_{i,u} F_i(u)` "by expanding it into AND-four supplier calls"; the `i` is
the clause address and this is the loop over it.  The two physical hypotheses
are the prologue `pre` (the driver word, the empty counter and the address
counter) and the per-address emitter `body`, both at the FIXED bank family
`loopBank`, so the loop and its budget are not assumed. -/
theorem call_run (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth preFuel cost : ℕ) (input witness : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
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
          input witness scratch (address + 1))) :
    ∃ scratchOut : ℕ → List Bool,
      Step (callMachine extra pre body) (callFuel preFuel pcpp.clauseBits cost) (fun _ => 0)
        (C10TailCompose.entryOf (C10TailCompose.wflag (60 + (extra + 2))) input witness)
        (fun _ => 0)
        (bank
          (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
            (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
          (CompareMachine.word
            (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
          (List.replicate entryWidth true) input witness scratchOut) := by
  have hloop := CloseoutFinalC10WorkerChain.clauseAddress_loop body pcpp cost heads
    (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
      input witness scratch) hsite
  obtain ⟨counter, hrew⟩ := C10TailCompose.step_reset (hpre.seq hloop)
  refine ⟨finalScratch extra (scratch (2 ^ pcpp.clauseBits))
    (CompareMachine.word (2 ^ pcpp.clauseBits)) counter, ?_⟩
  have hfull := prefixRecords_full answer denominator phase pcpp coordinate systematicAtom
  rw [← hfull]
  refine Step.congr (Step.congr_in hrew rfl ?_) rfl ?_
  · exact (bank_succ (t := 218 + (60 + extra) + 1) (by omega) [] [] [] input witness []
      (fun _ => []) (fun _ => []) (fun _ _ => rfl) rfl).trans
      (bank_entryOf (60 + (extra + 2)) input witness)
  · have e2 : Fin.addCases (motive := fun _ => List Bool)
        (loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
          input witness scratch (2 ^ pcpp.clauseBits))
        (fun _ : Fin 1 => CompareMachine.word (2 ^ pcpp.clauseBits))
        = bank
          (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
            (prefixRecords answer denominator phase pcpp coordinate systematicAtom
              (2 ^ pcpp.clauseBits)))
          (CompareMachine.word
            (prefixRecords answer denominator phase pcpp coordinate systematicAtom
              (2 ^ pcpp.clauseBits)).length)
          (List.replicate entryWidth true) input witness
          (outerScratch extra (scratch (2 ^ pcpp.clauseBits))
            (CompareMachine.word (2 ^ pcpp.clauseBits))) := by
      rw [loopBank_eq]
      exact bank_succ (t := 218 + (60 + extra)) (by omega) _ _ _ input witness _
        (scratch (2 ^ pcpp.clauseBits))
        (outerScratch extra (scratch (2 ^ pcpp.clauseBits))
          (CompareMachine.word (2 ^ pcpp.clauseBits)))
        (fun j hj => (if_neg (by omega)).symm) (if_pos rfl)
    have e3 := bank_succ (t := 218 + (60 + extra) + 1) (by omega)
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom
          (2 ^ pcpp.clauseBits)))
      (CompareMachine.word
        (prefixRecords answer denominator phase pcpp coordinate systematicAtom
          (2 ^ pcpp.clauseBits)).length)
      (List.replicate entryWidth true) input witness counter
      (outerScratch extra (scratch (2 ^ pcpp.clauseBits))
        (CompareMachine.word (2 ^ pcpp.clauseBits)))
      (finalScratch extra (scratch (2 ^ pcpp.clauseBits))
        (CompareMachine.word (2 ^ pcpp.clauseBits)) counter)
      (fun j hj => (if_neg (by omega)).symm) (if_pos rfl)
    exact (congrArg
      (fun f => Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin 1 => counter)) e2).trans
      e3

/-! ## §7 `callsReady_of_call` -- literally S0's `CallsReady` -/

/-- **The deliverable.**  `call_run`, read as the prologue obligation of
`C10SupplierStage.stage_run`: this IS
`C10SupplierStage.CallsReady` (`Proof/CaseAnalysis/FinalSupplierStage.lean`)
at `stream := Stream.words entryWidth (phaseRecords ...)`, the argument
`stage_run` supplies it at. -/
theorem callsReady_of_call (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost : ℕ) (input witness : List Bool)
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
          input witness scratch (address + 1))) :
    C10SupplierStage.CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel pcpp.clauseBits cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      input witness := by
  obtain ⟨scratchOut, hstep⟩ := call_run extra pre body answer denominator phase pcpp
    coordinate systematicAtom entryWidth preFuel cost input witness heads scratch hpre hsite
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

/-! ## §8 The consumer-side check -/

/-- **`C10SupplierStage.stage_run` applied to `callsReady_of_call`.**  The type
is deliberately NOT restated: it is whatever
`stage_run` (`Proof/CaseAnalysis/FinalSupplierStage.lean`) concludes, so this
term cannot elaborate unless the `Prop` §7 proves IS that theorem's `hcalls`
binder -- at `callFuel ph n := callFuel (preFuel n) pcpp.clauseBits (cost n)`,
`stream := Stream.words (entryWidth len) (phaseRecords ...)`,
`input := List.ofFn x`, `witness := bits`.  That is the machine-checked form of
"S1 closes the last open hypothesis of the supplier stage". -/
theorem stageRun_of_call (extra : ℕ)
    {ps bs : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (pre : (q : CloseoutRowsOriginalSchedule.Phase) →
      Machine (218 + (60 + extra) + 1) (ps q))
    (body : (q : CloseoutRowsOriginalSchedule.Phase) →
      Machine (218 + (60 + extra)) (bs q))
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth callCount preFuel cost : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount len)
    (hpre : Step (pre phase) (preFuel len) (fun _ => 0)
      (bank [] [] [] (List.ofFn x) bits (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate systematicAtom
          (List.ofFn x) bits scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ pcpp.clauseBits))))
    (hsite : ∀ address, address < 2 ^ pcpp.clauseBits →
      Step (body phase) (cost len) (heads address)
        (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate systematicAtom
          (List.ofFn x) bits scratch address)
        (heads (address + 1))
        (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate systematicAtom
          (List.ofFn x) bits scratch (address + 1)))
    {sp : ℕ} (p : Machine (218 + (60 + (extra + 2))) sp)
    (ht : 2 ≤ 218 + (60 + (extra + 2))) :
    ∃ (bnk : Fin 218 → List Bool) (scr : Fin (60 + (extra + 2)) → List Bool),
      Step (C10SupplierStage.stage (extra + 2)
          (fun q => callMachine extra (pre q) (body q)) phase)
        (C10SupplierStage.stageFuel
          (fun _ n => callFuel (preFuel n) pcpp.clauseBits (cost n)) entryWidth callCount
          phase len) (fun _ => 0)
        (C10LengthGate.exitTapes
          (Fin.castAdd (60 + (extra + 2)) CloseoutFinalC10WorkerDock.flag)
          ((UAcceptanceCarrier.verifier p ht
            (Fin.castAdd (60 + (extra + 2)) CloseoutFinalC10WorkerDock.result)).inputTapes
            (List.ofFn x) bits) 0 true)
        (fun _ => 0) (Fin.addCases bnk scr) ∧
      bnk 81 = CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom) ∧
      bnk 90 = CompareMachine.word
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length ∧
      CloseoutFinalC10WorkerDock.DockReady (entryWidth len)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom) bnk ∧
      CloseoutFinalC10WorkerEmitShape.EmitEntry
        (CloseoutFinalC10WorkerDock.joinScalarWidth (entryWidth len)
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length) bnk ∧
      bnk 0 = frame (List.ofFn x) ∧ bnk 1 = frame bits ∧ bnk 216 = [true] ∧
      scr ⟨56, by omega⟩ = List.replicate
        (CloseoutFinalC10WorkerDock.joinScalarWidth (entryWidth len)
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length) true ∧
      scr ⟨57, by omega⟩ = List.replicate (CompetitorRationalDecision.width
        (CloseoutFinalC10WorkerDock.joinScalarWidth (entryWidth len)
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)) true :=
  C10SupplierStage.stage_run (extra + 2) (fun q => callMachine extra (pre q) (body q))
    (fun _ n => callFuel (preFuel n) pcpp.clauseBits (cost n)) entryWidth callCount
    answer denominator phase pcpp coordinate systematicAtom len x bits hlen
    (callsReady_of_call extra (pre phase) (body phase) answer denominator phase pcpp
      coordinate systematicAtom (entryWidth len) (callCount len) (preFuel len) (cost len)
      (List.ofFn x) bits heads scratch hlen hpre hsite) p ht

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
