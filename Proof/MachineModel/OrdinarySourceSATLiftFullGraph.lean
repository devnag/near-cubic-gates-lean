import Proof.MachineModel.OrdinarySourceSATLiftParseMoves
import Proof.MachineModel.OrdinarySourceSATLiftTrace

/-! The cold wrapper's fixed seven-node controller: two layers of request
parsing, physical capacity production, source-query replacement, and a fresh
exact framed output. All inter-node returns are actual local transitions. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev pieces (p : OrdinaryOracleProgram) (j : Fin 7) : Piece (tapes p) :=
  match j.val with
  | 0 => ordinary (RecoveryFocus.machine (outerSlots p) Streaming.machine)
  | 1 => ordinary (RecoveryFocus.machine (firstSlots p) PCPFieldMoves.advanceMachine)
  | 2 => ordinary (RecoveryFocus.machine (secondSlots p) PCPFieldMoves.advanceMachine)
  | 3 => ordinary (RecoveryFocus.machine (budgetSlots p) Streaming.machine)
  | 4 => ordinary (RecoveryFocus.machine (power p) (PCPSerializerCapacity.Power.machine 2 268435456))
  | 5 => QueryGraph.piece (wiring p)
  | _ => ordinary (RecoveryFocus.machine (finalSlots p) PCPFieldMoves.readyMachine)

def next (p : OrdinaryOracleProgram) (j : Fin 7) (_ : Fin (pieces p j).states)
    (_ : Fin (tapes p) → Bool) : Option (Fin 7) :=
  if j.val=6 then none else some ⟨(j.val+1)%7,Nat.mod_lt _ (by decide)⟩

noncomputable abbrev program (p : OrdinaryOracleProgram) : OrdinaryOracleProgram :=
  (ports p).program (graph (pieces p) 0 (next p))

noncomputable def atCall (p : OrdinaryOracleProgram) (j : Fin 7)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool) : (program p).Config :=
  controlConfig (RecoveryCalls.code (fun j => (pieces p j).states) j)
    ⟨(pieces p j).machine.start,heads,data⟩

def Path (p : OrdinaryOracleProgram) (j k : Fin 7) (budget : ℕ)
    (beforeHeads afterHeads : Fin (tapes p) → ℕ)
    (beforeTapes afterTapes : Fin (tapes p) → List Bool) : Prop :=
  ∃ cost ≤ budget,OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) cost
    (atCall p j beforeHeads beforeTapes) (atCall p k afterHeads afterTapes)

theorem Path.trans {p : OrdinaryOracleProgram} {j k l : Fin 7} {a b : ℕ}
    {h0 h1 h2 : Fin (tapes p) → ℕ} {t0 t1 t2 : Fin (tapes p) → List Bool}
    (h : Path p j k a h0 h1 t0 t1) (g : Path p k l b h1 h2 t1 t2) :
    Path p j l (a+b) h0 h2 t0 t2 := by
  obtain ⟨n,hn,ht⟩ := h
  obtain ⟨m,hm,gt⟩ := g
  exact ⟨n+m,by omega,OrdinaryOracleCompose.trans ht gt⟩

theorem call_trace (p : OrdinaryOracleProgram) (j k : Fin 7) (cost budget : ℕ)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool)
    (final : Configuration (tapes p) (pieces p j).states)
    (h : OrdinaryOracleTrace RecoveryOracle.correctedSat ((ports p).program (pieces p j)) cost
      ⟨(pieces p j).machine.start,heads,data⟩ final)
    (hh : (pieces p j).machine.halted final.control=true) (hc : cost ≤ budget)
    (hn : next p j final.control final.scanned=some k) :
    Path p j k (budget+1) heads final.heads data final.tapes := by
  have ht := graph_trace (ports p) (pieces p) 0 (next p) j h
  have hr := graph_return RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) j k final hh hn
  exact ⟨cost+1,by omega,OrdinaryOracleCompose.trans ht hr⟩

theorem stop_trace (p : OrdinaryOracleProgram) (cost : ℕ)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool)
    (final : Configuration (tapes p) (pieces p 6).states)
    (h : OrdinaryOracleTrace RecoveryOracle.correctedSat ((ports p).program (pieces p 6)) cost
      ⟨(pieces p 6).machine.start,heads,data⟩ final)
    (hh : (pieces p 6).machine.halted final.control=true) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) (cost+1)
      (atCall p 6 heads data)
      (RecoveryCalls.stopped (fun j => (pieces p j).states) final.heads final.tapes) := by
  have ht := graph_trace (ports p) (pieces p) 0 (next p) 6 h
  have hr := graph_stop RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) 6 final hh rfl
  exact OrdinaryOracleCompose.trans ht hr

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
