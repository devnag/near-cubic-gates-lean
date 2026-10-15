import Proof.MachineModel.OrdinarySourceSATLiftQuery

/-! Every source trace is replaced by an actual corrected-oracle trace.
The common capacity is reused between queries, and inactive data survives. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem simulate {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (hp : ports.queryTape=w.kernel Kernel.outputSlot) (b : ℕ)
    {cost : ℕ} {c d : p.Config} (h : OrdinaryOracleTrace RecoveryOracle.sourceSAT p cost c d)
    (phase : Fin p.base.stateCount) (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (hbudget : cost ≤ 2*b+2) (hw : Workspace w b heads tapes) :
    ∃ used ≤ 10*capacity b*cost,∃ lastPhase newHeads newTapes,
      Workspace w b newHeads newTapes ∧ Retained w heads newHeads tapes newTapes ∧
      OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) used
        (atSource w phase (RecoveryFocus.config w.core heads tapes c))
        (atSource w lastPhase (RecoveryFocus.config w.core newHeads newTapes d)) := by
  induction h generalizing phase heads tapes with
  | refl c => exact ⟨0,by omega,phase,heads,tapes,hw,Retained.refl w heads tapes,.refl _⟩
  | @cons stepCost rest c middle d hs ht ih =>
    cases hs with
    | «local» c middle hh hq hs =>
      obtain ⟨used,hu,lastPhase,newHeads,newTapes,hwork,hkeep,htrace⟩ :=
        ih phase heads tapes (by omega) hw
      have hfirst := source_step w ports phase heads tapes c middle hh hq hs
      have hcap := Kernel.capacity_large b
      refine ⟨1+used,?_,lastPhase,newHeads,newTapes,hwork,hkeep,OrdinaryOracleCompose.trans hfirst htrace⟩
      have hunit : 1 ≤ 10*capacity b := by omega
      calc
        1+used ≤ 10*capacity b+10*capacity b*rest := Nat.add_le_add hunit hu
        _ = 10*capacity b*(1+rest) := by ring
    | ask c bits padding r hh hq hr htape =>
      have hbits : bits.length ≤ b := by
        rw [frame_length] at hbudget
        omega
      obtain ⟨used,hu,nextHeads,nextTapes,hwork,hkeep,hfirst⟩ :=
        replace_query w ports hp b phase heads tapes c bits padding r hw hbits hh hq hr htape
      obtain ⟨last,hl,lastPhase,newHeads,newTapes,hwork',hkeep',htrace⟩ :=
        ih (if RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits) then r.onTrue else r.onFalse)
          nextHeads nextTapes (by omega) hwork
      refine ⟨used+last,?_,lastPhase,newHeads,newTapes,hwork',hkeep.trans hkeep',
        OrdinaryOracleCompose.trans hfirst htrace⟩
      have hcharge : 1 ≤ (frame bits).length+1 := by omega
      have hstepBound : used ≤ 10*capacity b*((frame bits).length+1) :=
        hu.trans (by simpa using Nat.mul_le_mul_left (10*capacity b) hcharge)
      calc
        used+last ≤ 10*capacity b*((frame bits).length+1)+10*capacity b*rest :=
          Nat.add_le_add hstepBound hl
        _ = 10*capacity b*((frame bits).length+1+rest) := by ring

theorem stop_piece {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (node : Fin (Fintype.card (Phase p))) (a : Piece t) (ha : pieces w node=a)
    (c : Configuration t a.states) (hh : a.machine.halted c.control=true)
    (hn : next w node (Fin.cast (congrArg Piece.states ha.symm) c.control) c.scanned=none) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) 1
      (atPiece w node a ha c)
      (RecoveryCalls.stopped (fun j => (pieces w j).states) c.heads c.tapes) := by
  subst a
  exact graph_stop _ ports (pieces w) (sourceNode p p.base.machine.start) (next w) node c hh hn

theorem source_stop {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (q : Fin p.base.stateCount) (c : Configuration t p.base.stateCount)
    (hh : p.base.machine.halted c.control=true) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) 1
      (atSource w q c) (RecoveryCalls.stopped (fun j => (pieces w j).states) c.heads c.tapes) := by
  apply stop_piece w ports (sourceNode p q) _ (pieces_source w q) c
  · simp [ordinary,RecoveryFocus.machine,paused,hh]
  · simp [next,sourceNode,c.control.isLt,hh]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
