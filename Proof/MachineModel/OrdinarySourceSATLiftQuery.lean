import Proof.MachineModel.OrdinarySourceSATLiftAsk
import Proof.MachineModel.OrdinarySourceSATLiftWorkspace

/-! One original source query is replaced by actual preparation, arithmetic,
corrected-oracle querying and paid return to the selected source state. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem replace_query {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (ports : Ports t)
    (hp : ports.queryTape=w.kernel Kernel.outputSlot) (b : ℕ)
    (q : Fin p.base.stateCount) (heads : Fin t → ℕ) (tapes : Fin t → List Bool)
    (c : p.Config) (bits padding : List Bool) (r : OracleReturn p.base.stateCount)
    (hw : Workspace w b heads tapes) (hbits : bits.length ≤ b)
    (hh : p.base.machine.halted c.control=false) (hq : p.query c.control=some r)
    (hhead : c.heads p.queryTape=0) (htape : c.tapes p.queryTape=frame bits++padding) :
    ∃ cost ≤ 10*capacity b,∃ newHeads newTapes,
      Workspace w b newHeads newTapes ∧ Retained w heads newHeads tapes newTapes ∧
      OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) cost
        (atSource w q (RecoveryFocus.config w.core heads tapes c))
        (atSource w (if RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits) then r.onTrue else r.onFalse)
          (RecoveryFocus.config w.core newHeads newTapes
            {c with control := if RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits)
              then r.onTrue else r.onFalse})) := by
  let before := RecoveryFocus.config w.core heads tapes c
  have hwork := hw.focus c
  obtain ⟨log,hlog,hlogtape⟩ := hwork.log
  have hzero : ∀ j,before.heads (w.kernel j)=0 := by
    intro j
    by_cases hj : j=0
    · subst j
      rw [w.shared]
      simpa [before,RecoveryFocus.config,RecoveryFocus.pick_slot w.core w.core_injective] using hhead
    · exact hwork.heads_zero j hj
  have hsource : before.tapes (w.kernel 0)=frame bits++padding := by
    rw [w.shared]
    simpa [before,RecoveryFocus.config,RecoveryFocus.pick_slot w.core w.core_injective] using htape
  obtain ⟨kc,hkc,out,hkernel,hout,hout0,hout1,hout2,houtb⟩ := kernel_call w ports c.control b log
    before.heads before.tapes bits padding hbits hwork.bounded hwork.driver hlogtape hlog hsource hzero
  let newTapes := install w.kernel before.tapes out
  have newWork := hwork.install out hout1 hout2 houtb
  have hnewHead : before.heads ports.queryTape=0 := by rw [hp]; exact hzero _
  have hnewTape : newTapes ports.queryTape=ZeroPadding.pad (capacity b)
      (frame (fourth (RadixSemantics.value bits)).bits) := by
    rw [hp]
    exact (install_slot w.kernel w.kernel_injective before.tapes out _).trans hout
  have hask := ask_call w ports c.control r bits (capacity b) before.heads newTapes hq hnewHead hnewTape
  have hret := source_return w ports q before r hh hq
  let answer := RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits)
  let target := if answer then r.onTrue else r.onFalse
  have he : RecoveryFocus.config w.core before.heads newTapes {c with control:=target}=
      (⟨target,before.heads,newTapes⟩ : Configuration t p.base.stateCount) := by
    apply w.focus_existing
    · intro i
      simp [before,RecoveryFocus.config,RecoveryFocus.pick_slot w.core w.core_injective]
    · intro i
      change install w.kernel before.tapes out (w.core i)=c.tapes i
      rw [install_core w before.tapes out hout0]
      simp [before,RecoveryFocus.config,RecoveryFocus.pick_slot w.core w.core_injective]
  have hcost : 1+(kc+((frame (fourth (RadixSemantics.value bits)).bits).length+2)) ≤ 10*capacity b := by
    have hlift := lift_width bits
    have hlarge := Kernel.capacity_large b
    rw [frame_length]
    omega
  refine ⟨_,hcost,before.heads,newTapes,newWork,retained_query w heads tapes c out,?_⟩
  change OrdinaryOracleTrace RecoveryOracle.correctedSat (ports.program (piece w)) _ _ (atSource w target
    (RecoveryFocus.config w.core before.heads newTapes {c with control:=target}))
  rw [he]
  exact OrdinaryOracleCompose.trans hret (OrdinaryOracleCompose.trans hkernel hask)

end NearCubicWires.RepairSource.OrdinarySourceSATLift.QueryGraph
