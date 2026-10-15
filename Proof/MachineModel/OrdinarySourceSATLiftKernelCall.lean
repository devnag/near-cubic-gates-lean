import Proof.MachineModel.OrdinarySourceSATLiftTransport

/-! A physically executed kernel call in the surrounding source program.
Inactive original cursors survive verbatim, including an output/query alias. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_core {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (ambient : Fin t → List Bool) (out : Fin 156 → List Bool)
    (h0 : out 0=ambient (w.kernel 0)) (i : Fin p.base.tapeCount) :
    install w.kernel ambient out (w.core i)=ambient (w.core i) := by
  cases hp : RecoveryFocus.pick w.kernel (w.core i) with
  | none => simp [install,hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick w.kernel hp
    have hj : j=0 := by
      by_contra hn
      exact w.disjoint i j hn he.symm
    subst j
    simpa only [install,hp] using h0.trans (congrArg ambient he)

theorem kernel_call {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (q : Fin p.base.stateCount) (b log : ℕ) (heads : Fin t → ℕ)
    (ambient : Fin t → List Bool) (bits padding : List Bool)
    (hbits : bits.length ≤ b) (hb : Kernel.Bounded (capacity b) (ambient ∘ w.kernel))
    (hd : ambient (w.kernel 1)=List.replicate (capacity b) true)
    (hl : ambient (w.kernel 2)=List.replicate log false) (hz : log ≤ capacity b+1)
    (hsource : ambient (w.kernel 0)=frame bits++padding)
    (hheads : ∀ i,heads (w.kernel i)=0) :
    ∃ cost ≤ 8*capacity b+1,∃ out : Fin 156 → List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) cost
        (atKernel w q ⟨Kernel.machine.start,heads,ambient⟩)
        (atAsk w q ⟨0,heads,install w.kernel ambient out⟩) ∧
      out Kernel.outputSlot=ZeroPadding.pad (capacity b) (frame (fourth (RadixSemantics.value bits)).bits) ∧
      out 0=ambient (w.kernel 0) ∧ out 1=List.replicate (capacity b) true ∧
      out 2=List.replicate (capacity b+1) false ∧ Kernel.Bounded (capacity b) out := by
  obtain ⟨out,hready,hout,hzero,hdriver,hlog,hbounded⟩ := Kernel.run b log (ambient ∘ w.kernel)
    bits padding hbits hb hd hl hz hsource
  obtain ⟨r,hr,hh,ht,hs⟩ := hready.focus_at w.kernel w.kernel_injective heads ambient
    (by intro i; rfl) hheads
  have hbody := trace_piece w ports (kernelNode p q) _ (pieces_kernel w q)
    (ordinary_trace ports (RecoveryFocus.machine w.kernel Kernel.machine) _ _ r hr)
  have hhalt := (prefix_of_run (RecoveryFocus.machine w.kernel Kernel.machine) _ _ r hr).2
  have hreturn := return_piece w ports (kernelNode p q) (askNode p q) _ _
    (pieces_kernel w q) (pieces_ask w q) r.final hhalt (by simp [next,kernelNode])
  change OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) 1
    (atKernel w q r.final) (atAsk w q ⟨0,r.final.heads,r.final.tapes⟩) at hreturn
  rw [hh,ht] at hreturn
  exact ⟨r.steps+1,by omega,out,OrdinaryOracleCompose.trans hbody hreturn,hout,hzero,hdriver,hlog,hbounded⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
