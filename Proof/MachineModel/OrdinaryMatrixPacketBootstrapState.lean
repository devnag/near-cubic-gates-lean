import Proof.MachineModel.OrdinaryMatrixPacketSignPair

/-! The first real packet and executed capacity/erase bootstrap supply
the recurrent state. The initial caller has paid the request copy, whose
two short counters are retained outside this body. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketBootstrapState
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) :=
  TapeEmbedding.machine 2 (MatrixPacketBootstrapErase.machine a E C false)
def counters (r : Request) := MatrixPacketRestore.extras (2*(word r).length+1) (4*(word r).length+3)
noncomputable def input (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 2 => 0) (counters r)
    (MatrixPacketBootstrapErase.input a E C r 0 out (physicalInput r))
noncomputable def capacity (E C : ℕ) (r : Request) := C*(r.U+1)^2*(r.d+r.p+1)^E

theorem state_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (out : List Bool)
    (hp : 0<r.p) (hcap : MatrixVariablePacketWorkspace.footprint a r 0 false≤capacity E C r) :
    ∃ st : State a E (capacity E C r) r 0 (out++packet r false 0),∃ actual,
      runFrom (machine a E C) (MatrixPacketBootstrapErase.budget a E C r false 0)
        (input a E C r out)=some actual ∧ actual.final.heads=st.heads ∧ actual.final.tapes=st.tapes ∧
      actual.steps≤MatrixPacketBootstrapErase.budget a E C r false 0 := by
  obtain ⟨base,hb,work,capT,capH,logT,logH,outT,outH,offT,offH,sourceT,sourceH,bs⟩ :=
    MatrixPacketBootstrapErase.erase_run a E C r false 0 out (physicalInput r) hp hcap
  have ha:=TapeEmbedding.run_embed (MatrixPacketBootstrapErase.machine a E C false)
    (fun _ : Fin 2 => 0) (counters r) _ _ base hb
  let actual:=TapeEmbedding.receipt (fun _ : Fin 2 => 0) (counters r) base
  have oldT (i : Fin (MatrixPacketWorkClear.tapes a E)) : actual.final.tapes (i.castAdd 2)=base.final.tapes i :=
    Fin.addCases_left (motive := fun _ => List Bool) (left := base.final.tapes) (right := counters r) i
  have oldH (i : Fin (MatrixPacketWorkClear.tapes a E)) : actual.final.heads (i.castAdd 2)=base.final.heads i :=
    Fin.addCases_left (motive := fun _ => ℕ) (left := base.final.heads) (right := fun _ => 0) i
  have freshT (i : Fin 2) : actual.final.tapes (i.natAdd (MatrixPacketWorkClear.tapes a E))=counters r i :=
    Fin.addCases_right (motive := fun _ => List Bool) (left := base.final.tapes) (right := counters r) i
  have freshH (i : Fin 2) : actual.final.heads (i.natAdd (MatrixPacketWorkClear.tapes a E))=0 :=
    Fin.addCases_right (motive := fun _ => ℕ) (left := base.final.heads) (right := fun _ => 0) i
  have wb (i : Fin (MatrixVariablePacketWorkspace.tapes a)) (hi : MatrixVariablePacketWorkspace.working a i) :
      (actual.final.tapes (MatrixPacketRestoreDock.slots a E i)).length≤capacity E C r ∧
      actual.final.heads (MatrixPacketRestoreDock.slots a E i)=0 := by
    obtain ⟨j,hj⟩:=MatrixPacketRestoreDock.work_witness a E i hi
    have hwt : base.final.tapes (MatrixPacketBootstrapErase.old a E i)=List.replicate (capacity E C r) false :=
      (congrArg base.final.tapes hj).symm.trans (work j).1
    have hwh : base.final.heads (MatrixPacketBootstrapErase.old a E i)=0 :=
      (congrArg base.final.heads hj).symm.trans (work j).2
    refine ⟨?_,(oldH _).trans hwh⟩
    have ht:=(oldT (MatrixPacketBootstrapErase.old a E i)).trans hwt
    exact (congrArg List.length ht).le.trans (by simp)
  have ct (j : Fin 5) : actual.final.tapes (MatrixPacketRestoreControls.controls a E j)=
      MatrixPacketRestoreControls.values (capacity E C r) (word r) j := by
    fin_cases j
    · exact (oldT _).trans capT
    · exact (oldT _).trans logT
    · exact (oldT _).trans sourceT
    · exact freshT 0
    · exact freshT 1
  have ch (j : Fin 5) : actual.final.heads (MatrixPacketRestoreControls.controls a E j)=0 := by
    fin_cases j
    · exact (oldH _).trans capH
    · exact (oldH _).trans logH
    · exact (oldH _).trans sourceH
    · exact freshH 0
    · exact freshH 1
  let st : State a E (capacity E C r) r 0 (out++packet r false 0) :=
    ⟨actual.final.heads,actual.final.tapes,(fun i hi => (wb i hi).1),(fun i hi => (wb i hi).2),
      (oldT _).trans offT,(oldH _).trans offH,(oldT _).trans outT,(oldH _).trans outH,ct,ch⟩
  exact ⟨st,actual,ha,rfl,rfl,bs⟩

end NearCubicWires.RepairOrdinary.MatrixPacketBootstrapState
