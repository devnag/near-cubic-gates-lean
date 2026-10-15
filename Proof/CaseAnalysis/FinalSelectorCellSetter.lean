import Proof.CaseAnalysis.FinalSelectorPorts
import Proof.PCP.VerifierLookupFieldReaders

namespace NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- One paid step: write `true` at the head. The mirror of `LookupReadBit.clear`. -/
def setOne : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>some true,fun _=>.stay⟩ else none

theorem set_ready (bit : Bool):ReadyRun setOne 1 (fun _=>[bit]) (fun _=>[true]):=by
  let input : Configuration 1 2:=⟨0,fun _=>0,fun _=>[bit]⟩
  let output : Configuration 1 2:=⟨1,fun _=>0,fun _=>[true]⟩
  have hs:step setOne input=some output:=by rfl
  obtain ⟨r,hr,hrf,hrs⟩:=(Timed.single (by rfl : setOne.halted input.control=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hrf],by intro i;rw [hrf],hrs⟩

theorem set_blank (m : ℕ):
    ReadyRun setOne 1 (fun _=>List.replicate (m+1) false) (fun _=>true::List.replicate m false):=by
  let input : Configuration 1 2:=⟨0,fun _=>0,fun _=>List.replicate (m+1) false⟩
  let output : Configuration 1 2:=⟨1,fun _=>0,fun _=>true::List.replicate m false⟩
  have hs:step setOne input=some output:=by rfl
  obtain ⟨r,hr,hrf,hrs⟩:=(Timed.single (by rfl : setOne.halted input.control=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hrf],by intro i;rw [hrf],hrs⟩

/-- The port-2 producer: from the all-blank word of length `q`, one step
yields the exact `current` marker of the selector's entry bank. -/
theorem set_one_hot (q : ℕ) (hq:0<q):
    ReadyRun setOne 1 (fun _=>List.replicate q false)
      (fun _=>List.ofFn (fun i : Fin q=>decide (i.val=0))):=by
  obtain ⟨m,rfl⟩:∃ m,q=m+1:=⟨q-1,by omega⟩
  rw [head_marker (m+1) (by omega)]
  exact set_blank m

/-- The same word, named as the width-`q` binary one. -/
theorem set_binary_one (q : ℕ) (hq:0<q):
    ReadyRun setOne 1 (fun _=>List.replicate q false) (fun _=>binary q 1):=by
  have h:=set_one_hot q hq
  rwa [head_marker_binary q hq] at h

/-- As a `Step` receipt, ready to be docked by an injective slot map. -/
theorem set_one_hot_step (q : ℕ) (hq:0<q):
    Step setOne 1 (fun _=>0) (fun _=>List.replicate q false) (fun _=>0)
      (fun _=>List.ofFn (fun i : Fin q=>decide (i.val=0))):=
  Step.of_ready (set_one_hot q hq)

/-! ### The other bare cells the port chart needs

`LookupReadBit.clear` is already accepted; these are the two instances the
selector's entry bank asks for and that nothing had stated before. -/

/-- Ports 29 and 32: the single physical flag / carry cell, from a blank tape. -/
theorem clear_blank:ReadyRun LookupReadBit.clear 1 (fun _=>([] : List Bool)) (fun _=>[false]):=by
  let input : Configuration 1 2:=⟨0,fun _=>0,fun _=>([] : List Bool)⟩
  let output : Configuration 1 2:=⟨1,fun _=>0,fun _=>[false]⟩
  have hs:step LookupReadBit.clear input=some output:=by rfl
  obtain ⟨r,hr,hrf,hrs⟩:=(Timed.single
    (by rfl : LookupReadBit.clear.halted input.control=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hrf],by intro i;rw [hrf],hrs⟩

theorem clear_replicate (m : ℕ):
    ReadyRun LookupReadBit.clear 1 (fun _=>List.replicate (m+1) true)
      (fun _=>CompareMachine.word m):=by
  let input : Configuration 1 2:=⟨0,fun _=>0,fun _=>List.replicate (m+1) true⟩
  let output : Configuration 1 2:=⟨1,fun _=>0,fun _=>CompareMachine.word m⟩
  have hs:step LookupReadBit.clear input=some output:=by rfl
  obtain ⟨r,hr,hrf,hrs⟩:=(Timed.single
    (by rfl : LookupReadBit.clear.halted input.control=false) hs).run (by rfl)
  exact ⟨r,hr,by rw [hrf],by intro i;rw [hrf],hrs⟩

/-- Port 3: the `remaining` mask, one paid step from the raw unary q driver. -/
theorem set_remaining (q : ℕ) (hq:0<q):
    ReadyRun LookupReadBit.clear 1 (fun _=>List.replicate q true)
      (fun _=>List.ofFn (fun i : Fin q=>decide (0 < i.val))):=by
  obtain ⟨m,rfl⟩:∃ m,q=m+1:=⟨q-1,by omega⟩
  rw [tail_marker_word (m+1) (by omega)]
  exact clear_replicate m

theorem clear_blank_step:
    Step LookupReadBit.clear 1 (fun _=>0) (fun _=>([] : List Bool)) (fun _=>0) (fun _=>[false]):=
  Step.of_ready clear_blank

theorem set_remaining_step (q : ℕ) (hq:0<q):
    Step LookupReadBit.clear 1 (fun _=>0) (fun _=>List.replicate q true) (fun _=>0)
      (fun _=>List.ofFn (fun i : Fin q=>decide (0 < i.val))):=
  Step.of_ready (set_remaining q hq)

end NearCubicWires.RepairOrdinary.CloseoutFinalSelector
