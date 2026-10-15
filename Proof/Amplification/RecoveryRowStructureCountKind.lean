import Proof.Amplification.RecoveryRowStructureSmallState

/-! Actual classification of a retained row count. The original kind word,
source cursor, payload and previously computed result bit are preserved. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countKindSlots : Fin 5→Fin 52 := ![47,43,44,45,22]
theorem countKindSlots_injective : Function.Injective countKindSlots := by decide
noncomputable def countKindMachine := RecoveryFocus.machine countKindSlots RecoveryRowKind.machine

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem count_kind_output (ambient : Fin 52→List Bool) (count : List Bool) (capacity : Nat)
    (hreset : ambient 22=List.replicate capacity false) :
    install countKindSlots ambient (RecoveryRowKind.tapes (RecoveryRowKind.after count)
      (fun i=>decide (value count=i.val)) capacity)=
      Function.update (Function.update (Function.update (Function.update ambient
        47 (frame (RecoveryRowKind.after count))) 43 [decide (value count=0)])
          44 [decide (value count=1)]) 45 [decide (value count=2)] := by
  apply install_eq countKindSlots countKindSlots_injective
  · intro j
    fin_cases j
    · simp [countKindSlots,RecoveryRowKind.tapes]
    · simp [countKindSlots,RecoveryRowKind.tapes]
    · simp [countKindSlots,RecoveryRowKind.tapes]
    · simp [countKindSlots,RecoveryRowKind.tapes]
    · exact hreset.symm
  · intro i hi
    have h47 : i≠47 := by intro he; exact hi 0 he.symm
    have h43 : i≠43 := by intro he; exact hi 1 he.symm
    have h44 : i≠44 := by intro he; exact hi 2 he.symm
    have h45 : i≠45 := by intro he; exact hi 3 he.symm
    simp only [Function.update_of_ne h47,Function.update_of_ne h43,Function.update_of_ne h44,Function.update_of_ne h45]

theorem count_kind_run (d : Data) (capacity : Nat) (word : List Bool) (hd : d.Valid word) :
    ∃ r,runFrom countKindMachine (RecoveryRowKind.time d.count) (cfg d capacity countKindMachine.start)=some r ∧
      r.final=cfg (countClassified d) capacity r.final.control ∧ r.steps=RecoveryRowKind.time d.count ∧
      (countClassified d).Valid word := by
  have hreset : 2*d.count.length+1≤d.state.capacity := by
    have hwidth := hd.2.2.2.2
    have hcap := hd.2.1.reset
    change 8192*(d.state.bits.length+1)^2+1≤d.state.capacity at hcap
    nlinarith
  have h := RecoveryRowKind.kind_ready d.count d.flags d.state.capacity
  rw [Nat.max_eq_left hreset] at h
  obtain ⟨r,hr,hheads,htapes,hsteps⟩ := h.focus_at countKindSlots countKindSlots_injective
    (cfg d capacity countKindMachine.start).heads (cfg d capacity countKindMachine.start).tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,?_,hsteps,countClassified_valid d word hd⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans ((count_kind_output (cfg d capacity (0 : Fin 1)).tapes d.count d.state.capacity
      (by rfl)).trans (countClassified_tapes d capacity).symm)

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
