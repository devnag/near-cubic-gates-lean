import Proof.MachineModel.OrdinarySourceSATLiftReady

/-! The supplied physical cold state executes the entire original source
trace through the corrected-query graph and reaches a fresh-output call. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure OutputReady (p : OrdinaryOracleProgram) (word : List Bool)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool) : Prop where
  head : heads (core p p.base.outputTape)=0
  tape : data (core p p.base.outputTape)=frame word
  fresh : ∀ i,p.base.tapeCount+179 ≤ i.val → heads i=0 ∧ data i=[]

theorem query_start (p : OrdinaryOracleProgram) (heads : Fin (tapes p) → ℕ)
    (data : Fin (tapes p) → List Bool) :
    QueryGraph.atSource (wiring p) p.base.machine.start ⟨p.base.machine.start,heads,data⟩=
      (⟨(QueryGraph.piece (wiring p)).machine.start,heads,data⟩ :
        Configuration (tapes p) (QueryGraph.piece (wiring p)).states) := by
  apply configuration_ext
  · change RecoveryCalls.code (fun j => (QueryGraph.pieces (wiring p) j).states)
      (QueryGraph.sourceNode p p.base.machine.start) _ = _
    apply congrArg (RecoveryCalls.code (fun j => (QueryGraph.pieces (wiring p) j).states)
      (QueryGraph.sourceNode p p.base.machine.start))
    apply Fin.ext
    exact (congrArg (fun (piece : Piece (tapes p)) => piece.machine.start.val)
      (QueryGraph.pieces_source (wiring p) p.base.machine.start)).symm
  · rfl
  · rfl

theorem source_ready (p : OrdinaryOracleProgram) (input word : List Bool) (b cost : ℕ)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool)
    (hcold : ColdReady p input b heads data) (final : p.Config)
    (h : OrdinaryOracleTrace RecoveryOracle.sourceSAT p cost
      (initialConfiguration p.base.machine (p.base.inputTapes input)) final)
    (hbudget : cost ≤ 2*b+2) (hhalt : p.base.machine.halted final.control=true)
    (hheads : ∀ i,final.heads i=0) (houtput : final.tapes p.base.outputTape=frame word) :
    ∃ newHeads newData,Path p 5 6 (10*capacity b*cost+2) heads newHeads data newData ∧
      OutputReady p word newHeads newData := by
  obtain ⟨used,hu,lastPhase,newHeads,newData,_hwork,hkeep,htrace⟩ :=
    QueryGraph.simulate (wiring p) (ports p) rfl b h p.base.machine.start heads data hbudget hcold.workspace
  have hinit : RecoveryFocus.config (core p) heads data
      (initialConfiguration p.base.machine (p.base.inputTapes input))=
      (⟨p.base.machine.start,heads,data⟩ : Configuration (tapes p) p.base.stateCount) := by
    apply (wiring p).focus_existing
    · exact hcold.core_heads
    · exact hcold.core_tapes
  change OrdinaryOracleTrace _ ((ports p).program (QueryGraph.piece (wiring p))) used
    (QueryGraph.atSource (wiring p) p.base.machine.start
      (RecoveryFocus.config (core p) heads data (initialConfiguration p.base.machine (p.base.inputTapes input))))
    (QueryGraph.atSource (wiring p) lastPhase (RecoveryFocus.config (core p) newHeads newData final)) at htrace
  rw [hinit,query_start] at htrace
  let actual := RecoveryFocus.config (core p) newHeads newData final
  have hstop := QueryGraph.source_stop (wiring p) (ports p) lastPhase actual hhalt
  let stopped := RecoveryCalls.stopped (fun j => (QueryGraph.pieces (wiring p) j).states)
    actual.heads actual.tapes
  have hinner := OrdinaryOracleCompose.trans htrace hstop
  have hout := call_trace p 5 6 (used+1) (10*capacity b*cost+1) heads data stopped
    hinner (by
      change (QueryGraph.piece (wiring p)).machine.halted stopped.control=true
      simp [stopped,QueryGraph.piece,graph,RecoveryCalls.machine,RecoveryCalls.stopped])
    (by omega) rfl
  refine ⟨stopped.heads,stopped.tapes,hout,?_,?_,?_⟩
  · change actual.heads (core p p.base.outputTape)=0
    simpa [actual,RecoveryFocus.config,RecoveryFocus.pick_slot (core p) (core_injective p)] using hheads p.base.outputTape
  · change actual.tapes (core p p.base.outputTape)=frame word
    simpa [actual,RecoveryFocus.config,RecoveryFocus.pick_slot (core p) (core_injective p)] using houtput
  · intro i hi
    have hc : ∀ j,(wiring p).core j≠i := fun j => Ne.symm (high_ne_core p i hi j)
    have hk : ∀ j,(wiring p).kernel j≠i := fun j => Ne.symm (high_ne_kernel p i hi j)
    have retained := hkeep i hc hk
    have hp : RecoveryFocus.pick (core p) i=none := by
      classical
      unfold RecoveryFocus.pick
      exact dif_neg (by rintro ⟨j,he⟩; exact hc j he)
    have fresh := hcold.fresh i hi
    change actual.heads i=0 ∧ actual.tapes i=[]
    simp only [actual,RecoveryFocus.config,hp]
    exact ⟨retained.1.trans fresh.1,retained.2.trans fresh.2⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
