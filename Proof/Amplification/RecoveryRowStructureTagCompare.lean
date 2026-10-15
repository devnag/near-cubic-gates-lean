import Proof.Amplification.RecoveryRowStructureFlags

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagCompareSlots : Fin 5→Fin 52 := ![17,42,43,44,22]
theorem tagCompareSlots_injective : Function.Injective tagCompareSlots := by decide
noncomputable def tagCompareMachine := RecoveryFocus.machine tagCompareSlots RecoveryRowComparison.machine

def tagCompared (d : Data) (tag : List Bool) : Data :=
  setFlag (setFlag d 1 (decide (value d.kind≤value tag))) 0 (decide (value tag=value d.kind))

theorem tagCompared_tapes (d : Data) (capacity : Nat) (tag : List Bool) :
    (cfg (tagCompared d tag) capacity (0 : Fin 1)).tapes=
      Function.update (Function.update (cfg d capacity (0 : Fin 1)).tapes 44 [decide (value d.kind≤value tag)])
        43 [decide (value tag=value d.kind)] := by
  unfold tagCompared
  rw [cfg_flag,cfg_flag]
  rfl

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem compare_output (ambient : Fin 52→List Bool) (left right : List Bool) (capacity padding : Nat)
    (hl : ambient 17=ZeroPadding.pad padding (frame left)) (hr : ambient 42=frame right)
    (hreset : ambient 22=List.replicate capacity false) :
    install tagCompareSlots ambient
      (compareTapes left right ![decide (value left=value right),decide (value right≤value left)] capacity padding)=
      Function.update (Function.update ambient 44 [decide (value right≤value left)])
        43 [decide (value left=value right)] := by
  apply install_eq tagCompareSlots tagCompareSlots_injective
  · intro j
    fin_cases j
    · exact hl.symm
    · exact hr.symm
    · simp [tagCompareSlots,compareTapes]
    · simp [tagCompareSlots,compareTapes]
    · exact hreset.symm
  · intro i hi
    have h43 : i≠43 := by intro he; exact hi 2 he.symm
    have h44 : i≠44 := by intro he; exact hi 3 he.symm
    simp only [Function.update_of_ne h43,Function.update_of_ne h44]

theorem tag_compare_run (d : Data) (capacity padding : Nat) (tag word : List Bool) (hd : d.Valid word)
    (hw : tag.length=d.kind.length) (hreset : 2*tag.length+3≤d.state.capacity)
    (hsource : (cfg d capacity (0 : Fin 1)).tapes 17=ZeroPadding.pad padding (frame tag)) :
    ∃ r,runFrom tagCompareMachine (8*tag.length+20) (cfg d capacity tagCompareMachine.start)=some r ∧
      r.final=cfg (tagCompared d tag) capacity r.final.control ∧ r.steps=8*tag.length+20 ∧
      (tagCompared d tag).Valid word ∧
      (tagCompared d tag).flags 0=decide (value tag=value d.kind) := by
  have h := tag_compare_ready tag d.kind ![d.flags 0,d.flags 1] d.state.capacity padding hw
  rw [Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hheads,htapes,hsteps⟩ := h.focus_at tagCompareSlots tagCompareSlots_injective
    (cfg d capacity tagCompareMachine.start).heads (cfg d capacity tagCompareMachine.start).tapes
    (by intro j; fin_cases j <;> first | exact hsource | rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hsteps,hd,?_⟩
  · apply configuration_ext
    · rfl
    · exact hheads
    · exact htapes.trans ((compare_output (cfg d capacity (0 : Fin 1)).tapes tag d.kind d.state.capacity padding
        hsource (by rfl) (by rfl)).trans (tagCompared_tapes d capacity tag).symm)
  · simp [tagCompared,setFlag]

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
