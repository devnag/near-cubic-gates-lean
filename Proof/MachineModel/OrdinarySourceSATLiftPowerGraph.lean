import Proof.MachineModel.OrdinarySourceSATLiftPowerStart

/-! Keep the full capacity-call transport abstract in its coefficient. Its
specialization is definitionally the existing seven-piece cold controller. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full.PowerGraph
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev pieces (p : OrdinaryOracleProgram) (C : ℕ) (j : Fin 7) : Piece (tapes p) :=
  match j.val with
  | 0 => ordinary (RecoveryFocus.machine (outerSlots p) Streaming.machine)
  | 1 => ordinary (RecoveryFocus.machine (firstSlots p) PCPFieldMoves.advanceMachine)
  | 2 => ordinary (RecoveryFocus.machine (secondSlots p) PCPFieldMoves.advanceMachine)
  | 3 => ordinary (RecoveryFocus.machine (budgetSlots p) Streaming.machine)
  | 4 => ordinary (RecoveryFocus.machine (power p) (PCPSerializerCapacity.Power.machine 2 C))
  | 5 => QueryGraph.piece (wiring p)
  | _ => ordinary (RecoveryFocus.machine (finalSlots p) PCPFieldMoves.readyMachine)

def next (p : OrdinaryOracleProgram) (C : ℕ) (j : Fin 7) (_ : Fin (pieces p C j).states)
    (_ : Fin (tapes p) → Bool) : Option (Fin 7) :=
  if j.val=6 then none else some ⟨(j.val+1)%7,Nat.mod_lt _ (by decide)⟩

noncomputable abbrev program (p : OrdinaryOracleProgram) (C : ℕ) : OrdinaryOracleProgram :=
  (ports p).program (graph (pieces p C) 0 (next p C))

noncomputable def atCall (p : OrdinaryOracleProgram) (C : ℕ) (j : Fin 7)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool) : (program p C).Config :=
  controlConfig (RecoveryCalls.code (fun j => (pieces p C j).states) j)
    ⟨(pieces p C j).machine.start,heads,data⟩

def Path (p : OrdinaryOracleProgram) (C : ℕ) (j k : Fin 7) (budget : ℕ)
    (beforeHeads afterHeads : Fin (tapes p) → ℕ)
    (beforeTapes afterTapes : Fin (tapes p) → List Bool) : Prop :=
  ∃ cost ≤ budget,OrdinaryOracleTrace RecoveryOracle.correctedSat (program p C) cost
    (atCall p C j beforeHeads beforeTapes) (atCall p C k afterHeads afterTapes)

theorem call_trace (p : OrdinaryOracleProgram) (C : ℕ) (j k : Fin 7) (cost budget : ℕ)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool)
    (final : Configuration (tapes p) (pieces p C j).states)
    (h : OrdinaryOracleTrace RecoveryOracle.correctedSat ((ports p).program (pieces p C j)) cost
      ⟨(pieces p C j).machine.start,heads,data⟩ final)
    (hh : (pieces p C j).machine.halted final.control=true) (hc : cost ≤ budget)
    (hn : next p C j final.control final.scanned=some k) :
    Path p C j k (budget+1) heads final.heads data final.tapes := by
  have ht := graph_trace (ports p) (pieces p C) 0 (next p C) j h
  have hr := graph_return RecoveryOracle.correctedSat (ports p) (pieces p C) 0 (next p C) j k final hh hn
  exact ⟨cost+1,by omega,OrdinaryOracleCompose.trans ht hr⟩

theorem power_call (C : ℕ) (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :
    ∃ out,Path p C 4 5 (PCPSerializerCapacity.Power.budget 2 C b+1)
      (parsedHeads p input b) (parsedHeads p input b) (parsed p input b)
      (install (power p) (parsed p input b) out) ∧
      out (PCPSerializerCapacity.Power.outputSlot 2)=List.replicate (C*(b+1)^2) true := by
  obtain ⟨out,r,hr,hh,ht,hs,hcap⟩ := power_focused_run C p input b
  have h := call_trace p C 4 5 _ (PCPSerializerCapacity.Power.budget 2 C b) _ _ r.final
    (quiet_trace (ports p) (pieces p C 4) (fun _ => rfl) _ _ r hr)
    (prefix_of_run _ _ _ r hr).2 hs rfl
  rw [hh,ht] at h
  exact ⟨out,h,hcap⟩

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full.PowerGraph
