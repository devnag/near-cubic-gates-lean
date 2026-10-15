import Proof.MachineModel.OrdinaryMatrixPacketColdDock

/-! The first packet and all reuse controls are produced from the one
original canonical request and blank local work. The p guard is executed
by the enclosing header controller before taking this positive branch. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketColdBootstrap
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) :=
  Composition.machine (MatrixPacketColdPrepare.machine a E) (MatrixPacketBootstrapState.machine a E C)
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :=
  MatrixPacketColdPrepare.budget r+1+MatrixPacketBootstrapErase.budget a E C r false 0

theorem cold_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (hp : 0<r.p)
    (hcap : MatrixVariablePacketWorkspace.footprint a r 0 false≤MatrixPacketBootstrapState.capacity E C r) :
    ∃ st : State a E (MatrixPacketBootstrapState.capacity E C r) r 0 (packet r false 0),∃ actual,
      run (machine a E C) (budget a E C r) (MatrixPacketColdPrepare.cold a E r)=some actual ∧
      actual.final.heads=st.heads ∧ actual.final.tapes=st.tapes ∧ actual.steps≤budget a E C r := by
  obtain ⟨prepared,hp0,pt,ph,ps⟩:=MatrixPacketColdPrepare.prepare_run a E r
  obtain ⟨st,body,hb,bh,bt,bs⟩:=MatrixPacketBootstrapState.state_run a E C r [] hp hcap
  have hi : Composition.restart prepared.final (MatrixPacketBootstrapState.machine a E C).start=
      MatrixPacketBootstrapState.input a E C r [] := by
    apply configuration_ext
    · rfl
    · exact ph.trans (MatrixPacketColdDock.heads_eq a E C r)
    · exact pt.trans (MatrixPacketColdDock.tapes_eq a E C r)
  rw [←hi] at hb
  have whole:=Composition.run_join (MatrixPacketColdPrepare.machine a E) (MatrixPacketBootstrapState.machine a E C)
    _ _ _ prepared body hp0 hb
  refine ⟨st,Composition.joinedReceipt prepared body,whole,bh,bt,?_⟩
  change prepared.steps+1+body.steps≤budget a E C r
  rw [ps]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixPacketColdBootstrap
