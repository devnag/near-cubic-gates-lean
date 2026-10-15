import Proof.MachineModel.OrdinarySourceSATLiftGraph
import Proof.PCP.PCPSerializerCapacityFocus

/-! Exact local and return transport through the fixed query graph. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def atPiece {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (node : Fin (Fintype.card (Phase p))) (a : Piece t) (ha : pieces w node=a)
    (c : Configuration t a.states) : Configuration t (piece w).states :=
  controlConfig (fun q => RecoveryCalls.code (fun j => (pieces w j).states) node
    (Fin.cast (congrArg Piece.states ha.symm) q)) c

noncomputable abbrev atSource {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (q : Fin p.base.stateCount) (c : Configuration t p.base.stateCount) :=
  atPiece w (sourceNode p q) (ordinary (RecoveryFocus.machine w.core (paused p q)))
    (pieces_source w q) c
noncomputable abbrev atKernel {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (q : Fin p.base.stateCount) (c : Configuration t (Fintype.card (RecoveryCalls.Control Kernel.sizes))) :=
  atPiece w (kernelNode p q) (ordinary (RecoveryFocus.machine w.kernel Kernel.machine))
    (pieces_kernel w q) c
noncomputable abbrev atAsk {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (q : Fin p.base.stateCount) (c : Configuration t 3) :=
  atPiece w (askNode p q) (askPiece p t q) (pieces_ask w q) c

theorem trace_piece {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (node : Fin (Fintype.card (Phase p))) (a : Piece t) (ha : pieces w node=a)
    {cost : ℕ} {c d : Configuration t a.states}
    (h : OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program a) cost c d) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) cost
      (atPiece w node a ha c) (atPiece w node a ha d) := by
  subst a
  exact graph_trace ports (pieces w) (sourceNode p p.base.machine.start) (next w) node h

theorem return_piece {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (node target : Fin (Fintype.card (Phase p))) (a z : Piece t)
    (ha : pieces w node=a) (hz : pieces w target=z) (c : Configuration t a.states)
    (hh : a.machine.halted c.control=true)
    (hn : next w node (Fin.cast (congrArg Piece.states ha.symm) c.control) c.scanned=some target) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) 1
      (atPiece w node a ha c)
      (atPiece w target z hz ⟨z.machine.start,c.heads,c.tapes⟩) := by
  subst a
  subst z
  exact graph_return _ ports (pieces w) (sourceNode p p.base.machine.start) (next w)
    node target c hh hn

theorem source_step {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (q : Fin p.base.stateCount) (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (c d : p.Config) (hh : p.base.machine.halted c.control=false)
    (hq : p.query c.control=none) (hs : step p.base.machine c=some d) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) 1
      (atSource w q (RecoveryFocus.config w.core heads tapes c))
      (atSource w q (RecoveryFocus.config w.core heads tapes d)) := by
  apply trace_piece w ports (sourceNode p q) _ (pieces_source w q)
  apply single
  refine .local _ _ ?_ rfl ?_
  · simp [ordinary,RecoveryFocus.machine,paused,RecoveryFocus.config,hh,hq]
  · change step (RecoveryFocus.machine w.core p.base.machine)
      (RecoveryFocus.config w.core heads tapes c)=_
    rw [RecoveryFocus.step_config w.core w.core_injective,hs]
    rfl

theorem source_return {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (q : Fin p.base.stateCount) (c : Configuration t p.base.stateCount)
    (r : OracleReturn p.base.stateCount) (hh : p.base.machine.halted c.control=false)
    (hq : p.query c.control=some r) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) 1
      (atSource w q c) (atKernel w c.control ⟨Kernel.machine.start,c.heads,c.tapes⟩) := by
  apply return_piece w ports (sourceNode p q) (kernelNode p c.control) _ _
    (pieces_source w q) (pieces_kernel w c.control) c
  · simp [ordinary,RecoveryFocus.machine,paused,hh,hq]
  · simp [next,sourceNode,c.control.isLt,hh]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
