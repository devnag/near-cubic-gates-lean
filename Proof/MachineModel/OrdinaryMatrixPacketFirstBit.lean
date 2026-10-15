import Proof.MachineModel.OrdinaryMatrixPacketBootstrap

/-! The complete first sign pair starts from only the canonical source;
the first positive packet pays for the reusable capacity bootstrap. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketFirstBit
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (a : WilliamsAlgorithm) (E C : ℕ) :=
  Composition.machine (MatrixPacketColdBootstrap.machine a E C) (MatrixPacketReuse.machine a E true)
noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) :=
  Composition.machine (first a E C) (MatrixPacketStateAdvance.machine a E)
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :=
  (MatrixPacketColdBootstrap.budget a E C r+1+
    MatrixPacketReuse.budget a r true 0 (MatrixPacketBootstrapState.capacity E C r))+1+MatrixPacketOffset.budget 0

theorem cold_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (hp : 0<r.p)
    (hcap : ∀ negative,MatrixVariablePacketWorkspace.footprint a r 0 negative≤MatrixPacketBootstrapState.capacity E C r) :
    ∃ st : State a E (MatrixPacketBootstrapState.capacity E C r) r 1 (MatrixPacketSignPair.wordPair r 0),∃ actual,
      run (machine a E C) (budget a E C r) (MatrixPacketColdPrepare.cold a E r)=some actual ∧
      actual.final.heads=st.heads ∧ actual.final.tapes=st.tapes ∧ actual.steps≤budget a E C r := by
  obtain ⟨positive,pos,hp0,ph,pt,ps⟩:=MatrixPacketColdBootstrap.cold_run a E C r hp (hcap false)
  obtain ⟨negative,neg,hn,nh,nt,ns⟩:=MatrixPacketState.state_run a E (MatrixPacketBootstrapState.capacity E C r)
    r 0 (packet r false 0) true positive hp (hcap true)
  have hi : Composition.restart pos.final (MatrixPacketReuse.machine a E true).start=
      MatrixPacketState.data a E (MatrixPacketBootstrapState.capacity E C r) r 0 (packet r false 0) true positive := by
    apply configuration_ext
    · rfl
    · exact ph
    · exact pt
  rw [←hi] at hn
  have pair:=Composition.run_join (MatrixPacketColdBootstrap.machine a E C) (MatrixPacketReuse.machine a E true)
    _ _ _ pos neg hp0 hn
  let paired:=Composition.joinedReceipt pos neg
  obtain ⟨advanced,adv,ha,ah,atapes,as⟩:=MatrixPacketStateAdvance.state_run a E (MatrixPacketBootstrapState.capacity E C r)
    r 0 (packet r false 0++packet r true 0) negative
  have ha0 : Composition.restart paired.final (MatrixPacketStateAdvance.machine a E).start=
      MatrixPacketStateAdvance.input a E (MatrixPacketBootstrapState.capacity E C r)
        r 0 (packet r false 0++packet r true 0) negative := by
    apply configuration_ext
    · rfl
    · exact nh
    · exact nt
  rw [←ha0] at ha
  have whole:=Composition.run_join (first a E C) (MatrixPacketStateAdvance.machine a E) _ _ _ paired adv pair ha
  refine ⟨advanced,Composition.joinedReceipt paired adv,whole,ah,atapes,?_⟩
  change (pos.steps+1+neg.steps)+1+adv.steps≤budget a E C r
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixPacketFirstBit
