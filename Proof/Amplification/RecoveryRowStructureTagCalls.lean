import Proof.Amplification.RecoveryRowStructureCode

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compareTapes (left right : List Bool) (flags : Fin 2→Bool) (capacity padding : Nat) : Fin 5→List Bool :=
  ![ZeroPadding.pad padding (frame left),frame right,[flags 0],[flags 1],List.replicate capacity false]

theorem tag_compare_ready (left right : List Bool) (flags : Fin 2→Bool) (capacity padding : Nat)
    (hw : left.length=right.length) :
    ReadyRun RecoveryRowComparison.machine (8*left.length+20) (compareTapes left right flags capacity padding)
      (compareTapes left right ![decide (value left=value right),decide (value right≤value left)]
        (max capacity (2*left.length+3)) padding) := by
  have h := RecoveryChildSelection.ReadyRun.pad (RecoveryRowComparison.equal_ready left right flags capacity hw)
    ![padding,0,0,0,0]
  have hin : (fun i : Fin 5=>ZeroPadding.pad (![padding,0,0,0,0] i)
      (RecoveryRowComparison.tapes left right flags capacity i))=compareTapes left right flags capacity padding := by
    funext i
    fin_cases i <;> simp [RecoveryRowComparison.tapes,compareTapes]
  have hout : (fun i : Fin 5=>ZeroPadding.pad (![padding,0,0,0,0] i)
      (RecoveryRowComparison.tapes left right ![decide (value left=value right),decide (value right≤value left)]
        (max capacity (2*left.length+3)) i))=
      compareTapes left right ![decide (value left=value right),decide (value right≤value left)]
        (max capacity (2*left.length+3)) padding := by
    funext i
    fin_cases i <;> simp [RecoveryRowComparison.tapes,compareTapes]
  rw [hin,hout] at h
  exact h

def kindTapes (bits : List Bool) (flags : Fin 3→Bool) (capacity padding : Nat) : Fin 5→List Bool :=
  ![ZeroPadding.pad padding (frame bits),[flags 0],[flags 1],[flags 2],List.replicate capacity false]

theorem tag_kind_ready (bits : List Bool) (flags : Fin 3→Bool) (capacity padding : Nat) :
    ReadyRun RecoveryRowKind.machine (RecoveryRowKind.time bits) (kindTapes bits flags capacity padding)
      (kindTapes (RecoveryRowKind.after bits) (fun i=>decide (value bits=i.val))
        (max capacity (2*bits.length+1)) padding) := by
  have h := RecoveryChildSelection.ReadyRun.pad (RecoveryRowKind.kind_ready bits flags capacity)
    ![padding,0,0,0,0]
  have hin : (fun i : Fin 5=>ZeroPadding.pad (![padding,0,0,0,0] i)
      (RecoveryRowKind.tapes bits flags capacity i))=kindTapes bits flags capacity padding := by
    funext i
    fin_cases i <;> simp [RecoveryRowKind.tapes,kindTapes]
  have hout : (fun i : Fin 5=>ZeroPadding.pad (![padding,0,0,0,0] i)
      (RecoveryRowKind.tapes (RecoveryRowKind.after bits) (fun j=>decide (value bits=j.val))
        (max capacity (2*bits.length+1)) i))=
      kindTapes (RecoveryRowKind.after bits) (fun j=>decide (value bits=j.val))
        (max capacity (2*bits.length+1)) padding := by
    funext i
    fin_cases i <;> simp [RecoveryRowKind.tapes,kindTapes]
  rw [hin,hout] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
