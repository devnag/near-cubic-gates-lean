import Proof.MachineModel.BankZero
import Proof.CaseAnalysis.WitnessHeaderSwitch

/-! Inspect the existing raw stream marker without moving its cursor. Exactly
one existing incidence/bank worker runs, including the paid empty clear. -/
namespace NearCubicWires.ExtIncidence.BankBranch
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def idle : Machine 116 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none

def dispatch {s t : ℕ} (positive : Machine 116 s) (zero : Machine 116 t):=
  CloseoutWitness.HeaderSwitch.machine idle positive zero (fun _=>true) (fun cells=>cells 113)

theorem dispatch_run {s t : ℕ} (positive : Machine 116 s) (zero : Machine 116 t)
    (j : Fin 3) (hj:j=1 ∨ j=2) (fuel : ℕ) (H : Fin 116→ℕ) (A : Fin 116→List Bool)
    (base : ExecutionReceipt 116 (CloseoutWitness.HeaderSwitch.sizes 1 s t j))
    (hbit:j=if readTapeBit (A 113) (H 113) then 1 else 2)
    (hr:runFrom (CloseoutWitness.HeaderSwitch.programs idle positive zero j) fuel
      ⟨(CloseoutWitness.HeaderSwitch.programs idle positive zero j).start,H,A⟩=some base) :
    ∃ actual,runFrom (dispatch positive zero) (fuel+2)
      ⟨(dispatch positive zero).start,H,A⟩=some actual ∧
      actual.steps ≤ fuel+2 ∧ actual.final.heads=base.final.heads ∧
      actual.final.tapes=base.final.tapes:=by
  let prior : ExecutionReceipt 116 1:=⟨⟨0,H,A⟩,0,(⟨0,H,A⟩ : Configuration 116 1).tapeCells⟩
  have hp:runFrom idle 0 ⟨idle.start,H,A⟩=some prior:=rfl
  simpa only [dispatch,Nat.zero_add,Nat.add_comm 1 fuel,Nat.add_assoc,Nat.reduceAdd] using
    CloseoutWitness.HeaderSwitch.accepted idle positive zero (fun _=>true) (fun cells=>cells 113)
      j hj 0 fuel H A prior base hp hr rfl hbit

def machine:=dispatch BankConsumer.machine BankZero.machine

theorem stream_marker (ms : List (List ℕ)) (pre tail : List Bool) :
    readTapeBit (pre++stream ms++tail) pre.length=decide (0 < ms.length):=by
  cases ms with
  | nil=>simpa only [stream_nil,List.append_assoc,List.singleton_append,List.length_nil,
      Nat.lt_irrefl,decide_false] using
      Streaming.read_append pre tail false
  | cons m ms=>
    simpa only [stream_cons,monomialWord,List.cons_append,List.append_assoc,
      List.length_cons,Nat.zero_lt_succ,decide_true] using
      Streaming.read_append pre ((m.flatMap block++[false])++stream ms++tail) true

end
end NearCubicWires.ExtIncidence.BankBranch
