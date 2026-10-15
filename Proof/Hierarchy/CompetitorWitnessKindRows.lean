import Proof.Hierarchy.CompetitorWitnessKindFields
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessKind
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics RecoveryLiteralTag
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
theorem row_install (bits outBits : List Bool) (fs : Fin 3 → Bool) (cap : ℕ) :
    install rowSlots (tapes bits (fun _=>false) 0) (RecoveryRowKind.tapes outBits fs cap)=
      tapes outBits ![fs 0,fs 1,fs 2,false] cap := by
  funext i;fin_cases i
  · exact install_slot rowSlots (by decide) _ _ 0
  · exact install_slot rowSlots (by decide) _ _ 1
  · exact install_slot rowSlots (by decide) _ _ 2
  · exact install_slot rowSlots (by decide) _ _ 3
  · exact install_slot rowSlots (by decide) _ _ 4
  · exact install_other rowSlots _ _ 5 (by intro j;fin_cases j <;> decide)

theorem row_ready (bits : List Bool) : ReadyRun row (RecoveryRowKind.time bits)
    (tapes bits (fun _=>false) 0) (tapes (RecoveryRowKind.after bits) (rowFlags bits) (2*bits.length+1)) := by
  have h := (RecoveryRowKind.kind_ready bits (fun _=>false) 0).focus rowSlots (by decide)
    (tapes bits (fun _=>false) 0) (by intro i;fin_cases i <;> rfl)
  rw [row_install,Nat.zero_max] at h
  exact h

theorem pred_install (bits outBits : List Bool) (fs : Fin 4 → Bool) (b : Bool) (cap outCap : ℕ) :
    install predSlots (tapes bits fs cap)
      ![frame outBits,[b],List.replicate outCap false]=tapes outBits ![fs 0,fs 1,fs 2,b] outCap := by
  funext i;fin_cases i
  · exact install_slot predSlots (by decide) _ _ 0
  · exact install_other predSlots _ _ 1 (by intro j;fin_cases j <;> decide)
  · exact install_other predSlots _ _ 2 (by intro j;fin_cases j <;> decide)
  · exact install_other predSlots _ _ 3 (by intro j;fin_cases j <;> decide)
  · exact install_slot predSlots (by decide) _ _ 2
  · exact install_slot predSlots (by decide) _ _ 1

theorem pred_generic (bits : List Bool) (fs : Fin 4 → Bool) (cap : ℕ) :
    ReadyRun predecessor (4*bits.length+4) (tapes bits fs cap)
      (tapes (predWord bits) ![fs 0,fs 1,fs 2,nonzero bits] (max cap (2*bits.length+1))) := by
  have h := (RecoveryListPredecessor.predecessor_ready bits (fs 3) cap).focus
    predSlots (by decide) (tapes bits fs cap) (by intro i;fin_cases i <;> rfl)
  rw [pred_install] at h
  exact h

theorem predecessor_ready (bits : List Bool) : ReadyRun predecessor (4*bits.length+4)
    (tapes (RecoveryRowKind.after bits) (rowFlags bits) (2*bits.length+1))
    (tapes (after bits) (predFlags bits) (2*bits.length+1)) := by
  have h := pred_generic (RecoveryRowKind.after bits) (rowFlags bits) (2*bits.length+1)
  rw [after_row_length,max_self] at h
  exact h

end NearCubicWires.RepairOrdinary.CompetitorWitnessKind
