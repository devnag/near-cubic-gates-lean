import Proof.MachineModel.OrdinaryOracleComposeGraph

/-! The two actual calls are composed before either state cardinality is
instantiated. The second call receives the first call's unchanged bank. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedColdSearchCompose
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pieces {t s : Nat} (first : Machine t s) (last : Piece t) : Fin 2→Piece t
  | 0=>ordinary first
  | 1=>last
def next {t s : Nat} (first : Machine t s) (last : Piece t) (j : Fin 2)
    (_ : Fin (pieces first last j).states) (_ : Fin t→Bool) : Option (Fin 2):=
  if j=0 then some 1 else none
noncomputable abbrev program {t s : Nat} (ports : Ports t) (first : Machine t s) (last : Piece t):=
  ports.program (graph (pieces first last) 0 (next first last))

theorem run {t s : Nat} (o : Nat→Bool) (ports : Ports t)
    (first : Machine t s) (last : Piece t) (fuel : Nat) (A : Fin t→List Bool)
    (r : ExecutionReceipt t s) (hr : LocalBitMultitape.run first fuel A=some r)
    (cost : Nat) (searched : Configuration t last.states)
    (trace : OrdinaryOracleTrace o (ports.program last) cost
      ⟨last.machine.start,r.final.heads,r.final.tapes⟩ searched)
    (halt : last.machine.halted searched.control=true) :
    ∃ final,
      OrdinaryOracleTrace o (program ports first last) (r.steps+(1+(cost+1)))
        (initialConfiguration (program ports first last).base.machine A) final ∧
      (program ports first last).base.machine.halted final.control=true ∧
      final.heads=searched.heads ∧ final.tapes=searched.tapes := by
  have ordinaryRun:=ordinary_trace (o:=o) ports first fuel _ r hr
  have halted:=(prefix_of_run first fuel _ r hr).2
  have firstBody:=graph_trace ports (pieces first last) 0 (next first last) 0 ordinaryRun
  have handoff:=graph_return o ports (pieces first last) 0 (next first last) 0 1 r.final halted rfl
  have secondBody:=graph_trace ports (pieces first last) 0 (next first last) 1 trace
  have stopped:=graph_stop o ports (pieces first last) 0 (next first last) 1 searched halt rfl
  have whole:=trans firstBody (trans handoff (trans secondBody stopped))
  refine ⟨_,whole,?_,rfl,rfl⟩
  simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]

end NearCubicWires.RepairSource.RecoveryBoundedColdSearchCompose
