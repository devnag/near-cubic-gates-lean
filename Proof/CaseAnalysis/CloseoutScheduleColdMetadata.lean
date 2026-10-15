import Proof.CaseAnalysis.ScheduleClear
import Proof.CaseAnalysis.CloseoutScheduleMetadata

/-! Actual cold metadata is installed directly in its final schedule ports;
the actual C driver and blank work bank are retained. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Cold
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def metadataProgram (w : Nat) := RecoveryFocus.machine (metadataSlots w) Metadata.machine

theorem metadata_port_ne (w : Nat) (i : Fin 6)
    (hi : i.val=2 ∨ i.val=3 ∨ i.val=4) (j : Fin 8) : metadataSlots w j ≠ port w i := by
  intro h
  have hv := congrArg Fin.val h
  fin_cases j <;> simp [metadataSlots,port,core,extra] at hv <;> omega

theorem metadata_run (w : Nat) (bits : List Bool) (ambient : Fin (tapes w) → List Bool)
    (hx : ambient (extra w 0) = frame bits)
    (hc : ∀ i : Fin (w+6), i.val ≠ w+3 → ambient (core w i) = [])
    (he : ∀ i : Fin 30, 26 ≤ i.val → ambient (extra w i) = []) : ∃ out,
    ClockJoin.ReadyRun (metadataProgram w) (8*bits.length+30) ambient out ∧
    (∀ i, out (metadataSlots w i) = Metadata.output bits (UnaryTemplate.tape 1) i) ∧
    (∀ i : Fin w, out (core w (i.castAdd 6)) = []) ∧
    (∀ i : Fin 6, i.val=2 ∨ i.val=3 ∨ i.val=4 → out (port w i) = ambient (port w i)) := by
  have h := (Metadata.metadata_run bits).focus (metadataSlots w) (metadata_injective w) ambient (by
    intro i
    fin_cases i
    · exact hx
    · exact hc ((5 : Fin 6).natAdd w) (by change w+5 ≠ w+3; omega)
    · exact he 26 (by decide)
    · exact he 27 (by decide)
    · exact hc ((1 : Fin 6).natAdd w) (by change w+1 ≠ w+3; omega)
    · exact he 28 (by decide)
    · exact hc ((0 : Fin 6).natAdd w) (by change w+0 ≠ w+3; omega)
    · exact he 29 (by decide))
  refine ⟨_,h,?_,?_,?_⟩
  · intro i
    exact install_slot _ (metadata_injective w) _ _ i
  · intro i
    rw [install_other _ _ _ _ (work_metadata w i)]
    exact hc (i.castAdd 6) (by have := i.isLt; change i.val ≠ w+3; omega)
  · intro i hi
    exact install_other _ _ _ _ (metadata_port_ne w i hi)

end
end NearCubicWires.RepairSource.CloseoutSchedule.Cold
