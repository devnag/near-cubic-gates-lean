import Proof.Amplification.RecoveryPrefixLoopDock

/-! The actual prefix search at the zero-head boundary used by its cold
caller. The caller may allocate a larger fixed polynomial capacity; every
reachable query is proved to fit it. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixSearch
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
open RecoveryPrefixBody RecoveryPrefix RecoveryQuery
open private search_succ from Proof.Amplification.RecoveryPrefixLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev program (flat : Bool) := RecoveryPrefixLoopDock.program (RecoveryPrefixBody.program flat)
def budget (cap total : Nat) := total*(20*cap+3)+8

theorem prepared_ready (cap payload total log : Nat) (flat : Bool) (old : Bool)
    (padding : List Bool) (ambient : Fin 360→List Bool)
    (hi : Inv cap payload log [] old padding ambient) (hz : log≤cap+1)
    (hcap : workspace payload total≤cap) :
    ∃ cost ≤ budget cap total,∃ (out : Fin 360→List Bool) (lastLog : Nat) (last : Bool),
      Ready RecoveryOracle.correctedSat (program flat) cost
        (RecoveryPrefixLoopDock.tapes (RecoveryPrefixBody.program flat) total ambient)
        (RecoveryPrefixLoopDock.tapes (RecoveryPrefixBody.program flat) total out) ∧
      lastLog≤cap+1 ∧ Inv cap payload lastLog (search flat payload total []) last padding out := by
  let I : Nat→(Fin 360→List Bool)→Prop := fun pos input=>
    ∃ log old,log≤cap+1 ∧ Inv cap payload log (search flat payload pos []) old padding input
  have body : ∀ pos<total,∀ input,I pos input →
      ∃ cost≤20*cap,∃ final : (RecoveryPrefixBody.program flat).Config,
        OrdinaryOracleTrace RecoveryOracle.correctedSat (RecoveryPrefixBody.program flat) cost
          (initialConfiguration (RecoveryPrefixBody.program flat).base.machine input) final ∧
        (RecoveryPrefixBody.program flat).base.machine.halted final.control=true ∧
        (∀ i,final.heads i=0) ∧ I (pos+1) final.tapes := by
    intro pos hpos input ⟨log,old,hlog,hin⟩
    have hc := (workspace_covers payload total (search flat payload pos []) (by simpa using hpos.le)).trans hcap
    obtain ⟨cost,hcost,final,htrace,hhalt,hheads,hout⟩ :=
      body_ready cap payload log flat (search flat payload pos []) old padding input hin hc hlog
    refine ⟨cost,hcost,final,htrace,hhalt,hheads,cap+1,
      answer flat payload (search flat payload pos []),Nat.le_refl _,?_⟩
    simpa only [search_succ] using hout
  obtain ⟨out,hrun,lastLog,last,hlog,hout⟩ := RecoveryPrefixLoop.whole RecoveryOracle.correctedSat
    (RecoveryPrefixBody.program flat) total (20*cap) I body ambient ⟨log,old,hz,hi⟩
  obtain ⟨cost,hcost,hready⟩ := RecoveryPrefixLoopDock.ready_of_run RecoveryOracle.correctedSat
    (RecoveryPrefixBody.program flat) total (total*(20*cap+3)+3) ambient out hrun
  exact ⟨cost,by dsimp [budget]; omega,out,lastLog,last,hready,hlog,hout⟩

end NearCubicWires.RepairSource.RecoveryPrefixSearch
