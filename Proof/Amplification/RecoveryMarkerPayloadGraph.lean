import Proof.Amplification.RecoveryMarkerPayloadCalls

/-! Actual three-node compact payload controller: perform the three paid
metadata copies, read the saved polarity, then execute the selected table
checker. Both branches return on the same physical answer tape107. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerHandoff
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : Nat} (_ : Machine t s) := s
noncomputable def sizes : Fin 3→Nat :=
  ![stateCount RecoveryMarkerHandoff.machine,stateCount flatMachine,stateCount nestedMachine]
noncomputable def programs : (j : Fin 3)→Machine 212 (sizes j)
  | ⟨0,_⟩=>RecoveryMarkerHandoff.machine
  | ⟨1,_⟩=>flatMachine
  | ⟨2,_⟩=>nestedMachine
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 212→Bool) : Option (Fin 3) :=
  ![some (if bits 56 then 1 else 2),none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def answer (marker : MarkerState) (x : CheckState) (word innerBits outerBits : List Bool) :=
  if marker.outer.result then RecoveryRowRoot.wholeAnswer (flatState x) word innerBits
  else RecoveryNestedTable.answer x word innerBits outerBits
def budget (width : Nat) := 24*width+28+payloadBudget width

theorem polarity (marker : MarkerState) (x : CheckState) {s : Nat} (q : Fin s) :
    (cfg marker x q).scanned 56=marker.outer.result := by
  change readTapeBit [marker.outer.result] 0=marker.outer.result
  rfl

theorem budget_le (width : Nat) : budget width ≤ 268435456*(width+1)^3 := by
  have h : width+1 ≤ (width+1)^3 := Nat.le_self_pow (by decide) _
  unfold budget payloadBudget
  nlinarith only [h]

end NearCubicWires.RepairOrdinary.RecoveryMarkerPayload
