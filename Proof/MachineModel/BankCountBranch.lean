import Proof.MachineModel.BankCountPositive
import Proof.MachineModel.BankCountZero

/-! Dispatch on the original raw stream marker in the same count bank. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def idle : Machine 128 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def dispatch {s t : ℕ} (yes : Machine 128 s) (no : Machine 128 t):=
  CloseoutWitness.HeaderSwitch.machine idle yes no (fun _=>true) (fun cells=>cells 113)
def optional:=dispatch positive zero

theorem dispatch_run {s t : ℕ} (yes : Machine 128 s) (no : Machine 128 t)
    (j : Fin 3) (hj : j=1 ∨ j=2) (fuel : ℕ) (H : Fin 128→ℕ) (A : Fin 128→List Bool)
    (base : ExecutionReceipt 128 (CloseoutWitness.HeaderSwitch.sizes 1 s t j))
    (hbit : j=if readTapeBit (A 113) (H 113) then 1 else 2)
    (hr : runFrom (CloseoutWitness.HeaderSwitch.programs idle yes no j) fuel
      ⟨(CloseoutWitness.HeaderSwitch.programs idle yes no j).start,H,A⟩=some base) :
    ∃ actual,runFrom (dispatch yes no) (fuel+2)
      ⟨(dispatch yes no).start,H,A⟩=some actual ∧
      actual.steps≤fuel+2 ∧ actual.final.heads=base.final.heads ∧
      actual.final.tapes=base.final.tapes:=by
  let prior : ExecutionReceipt 128 1:=⟨⟨0,H,A⟩,0,(⟨0,H,A⟩ : Configuration 128 1).tapeCells⟩
  have hp : runFrom idle 0 ⟨idle.start,H,A⟩=some prior:=rfl
  simpa only [dispatch,Nat.zero_add,Nat.add_comm 1 fuel,Nat.add_assoc,Nat.reduceAdd] using
    CloseoutWitness.HeaderSwitch.accepted idle yes no (fun _=>true) (fun cells=>cells 113)
      j hj 0 fuel H A prior base hp hr rfl hbit

end
end NearCubicWires.ExtIncidence.BankCount
