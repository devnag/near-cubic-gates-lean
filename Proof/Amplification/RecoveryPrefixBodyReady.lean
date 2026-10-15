import Proof.Amplification.RecoveryPrefixBodyInvariant

/-! The actual initial/halting boundary for the reusable oracle prefix
body. No encoded input, capacity or clock is inserted by this wrapper. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixBody
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixUpdate RecoveryPrefix RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem query_start_initial {t s : Nat} (p : Machine t s) (slot : Fin t) (input : Fin t→List Bool) :
    RecoveryQueryCall.start p slot input=initialConfiguration (RecoveryQueryCall.piece p slot).machine input := by
  rfl

theorem start_initial (flat : Bool) (ambient : Fin 360→List Bool) :
    start flat ambient=initialConfiguration (program flat).base.machine ambient := by
  have hq : RecoveryQueryStep.start flat (ambient ∘ querySlots)=
      initialConfiguration (RecoveryQueryStep.program flat).base.machine (ambient ∘ querySlots) :=
    query_start_initial _ _ _
  have he := WilliamsSourceCrop.focus_same querySlots
    (initialConfiguration (program flat).base.machine ambient)
    (initialConfiguration (RecoveryQueryStep.program flat).base.machine (ambient ∘ querySlots))
    (by intro i; rfl) (by intro i; rfl)
  unfold start
  rw [hq]
  exact congrArg (controlConfig (RecoveryCalls.code (fun j => (pieces flat j).states) 0)) he

private theorem graph_stopped {t k : Nat} (ports : Ports t) (ps : Fin k→Piece t) (entry : Fin k)
    (next : (j : Fin k)→Fin (ps j).states→(Fin t→Bool)→Option (Fin k))
    (heads : Fin t→Nat) (tapes : Fin t→List Bool) :
    (ports.program (graph ps entry next)).base.machine.halted
      (RecoveryCalls.stopped (fun j=>(ps j).states) heads tapes).control=true := by
  simp [Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]

theorem stopped_halted (flat : Bool) (out : Fin 360→List Bool) :
    (program flat).base.machine.halted (stopped flat out).control=true :=
  graph_stopped ports (pieces flat) 0 (next flat) _ out

theorem body_ready (cap payload log : Nat) (flat : Bool) (xs : List Bool) (old : Bool)
    (padding : List Bool) (ambient : Fin 360→List Bool)
    (hi : Inv cap payload log xs old padding ambient)
    (hc : capacity payload (commitment xs) (queryCount xs) ≤ cap) (hz : log ≤ cap+1) :
    ∃ cost ≤ 20*cap,∃ final : (program flat).Config,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program flat) cost
        (initialConfiguration (program flat).base.machine ambient) final ∧
      (program flat).base.machine.halted final.control=true ∧
      (∀ i,final.heads i=0) ∧
      Inv cap payload (cap+1) (nextPrefix flat payload xs) (answer flat payload xs) padding final.tapes := by
  obtain ⟨cost,hcost,out,htrace,hout⟩ := body_inv cap payload log flat xs old padding ambient hi hc hz
  rw [start_initial] at htrace
  exact ⟨cost,hcost,stopped flat out,htrace,stopped_halted flat out,fun _=>rfl,hout⟩

end NearCubicWires.RepairSource.RecoveryPrefixBody
