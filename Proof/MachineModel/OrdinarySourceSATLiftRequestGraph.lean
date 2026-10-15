import Proof.MachineModel.OrdinarySourceSATLiftRequestLayout

namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev pieces (code : List Bool) (C D : ℕ) (j : Fin 7) : Piece (tapes D) :=
  match j.val with
  | 0 => ordinary (RecoveryFocus.machine (copySlots D) Streaming.machine)
  | 1 => ordinary (RecoveryFocus.machine (powerSlot D) (PCPSerializerCapacity.Power.machine D C))
  | 2 => ordinary (RecoveryFocus.machine (fun _ : Fin 1 => outSlot D) (HierarchyFixedWord.raw (header code)))
  | 3 => ordinary (RecoveryFocus.machine (scaleSlots D false) (RequestScale.machine 8))
  | 4 => ordinary (RecoveryFocus.machine (fun _ : Fin 1 => outSlot D) (HierarchyFixedWord.raw separator))
  | 5 => ordinary (RecoveryFocus.machine (scaleSlots D true) (RequestScale.machine 4))
  | _ => ordinary (RecoveryFocus.machine (fun _ : Fin 1 => outSlot D) (HierarchyFixedWord.raw trailer))

def next (code : List Bool) (C D : ℕ) (j : Fin 7) (_ : Fin (pieces code C D j).states)
    (_ : Fin (tapes D) → Bool) : Option (Fin 7) :=
  if j.val=6 then none else some ⟨(j.val+1)%7,Nat.mod_lt _ (by decide)⟩

noncomputable abbrev program (code : List Bool) (C D : ℕ) : OrdinaryOracleProgram :=
  (ports D).program (graph (pieces code C D) 0 (next code C D))
noncomputable def atCall (code : List Bool) (C D : ℕ) (j : Fin 7)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool) : (program code C D).Config :=
  controlConfig (RecoveryCalls.code (fun j => (pieces code C D j).states) j)
    ⟨(pieces code C D j).machine.start,heads,data⟩

def Path (code : List Bool) (C D : ℕ) (j k : Fin 7) (budget : ℕ)
    (heads afterHeads : Fin (tapes D) → ℕ) (data afterData : Fin (tapes D) → List Bool) : Prop :=
  ∃ cost ≤ budget,OrdinaryOracleTrace RecoveryOracle.correctedSat (program code C D) cost
    (atCall code C D j heads data) (atCall code C D k afterHeads afterData)

theorem Path.trans {code : List Bool} {C D : ℕ} {j k l : Fin 7} {a b : ℕ}
    {h0 h1 h2 : Fin (tapes D) → ℕ} {t0 t1 t2 : Fin (tapes D) → List Bool}
    (h : Path code C D j k a h0 h1 t0 t1) (g : Path code C D k l b h1 h2 t1 t2) :
    Path code C D j l (a+b) h0 h2 t0 t2 := by
  obtain ⟨n,hn,ht⟩ := h
  obtain ⟨m,hm,gt⟩ := g
  exact ⟨n+m,by omega,OrdinaryOracleCompose.trans ht gt⟩

theorem call_run (code : List Bool) (C D : ℕ) (j k : Fin 7) (budget : ℕ)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (r : ExecutionReceipt (tapes D) (pieces code C D j).states)
    (hr : runFrom (pieces code C D j).machine budget
      ⟨(pieces code C D j).machine.start,heads,data⟩=some r)
    (hs : r.steps ≤ budget) (hq : ∀ q,(pieces code C D j).query q=none)
    (hn : next code C D j r.final.control r.final.scanned=some k) :
    Path code C D j k (budget+1) heads r.final.heads data r.final.tapes := by
  have hp := Full.quiet_trace (o := RecoveryOracle.correctedSat) (ports D) (pieces code C D j) hq budget _ r hr
  have ht := graph_trace (ports D) (pieces code C D) 0 (next code C D) j hp
  have hj := graph_return RecoveryOracle.correctedSat (ports D) (pieces code C D) 0
    (next code C D) j k r.final (prefix_of_run _ _ _ r hr).2 hn
  exact ⟨r.steps+1,by omega,OrdinaryOracleCompose.trans ht hj⟩

theorem stop_run (code : List Bool) (C D budget : ℕ)
    (heads : Fin (tapes D) → ℕ) (data : Fin (tapes D) → List Bool)
    (r : ExecutionReceipt (tapes D) (pieces code C D 6).states)
    (hr : runFrom (pieces code C D 6).machine budget
      ⟨(pieces code C D 6).machine.start,heads,data⟩=some r) :
    OrdinaryOracleTrace RecoveryOracle.correctedSat (program code C D) (r.steps+1)
      (atCall code C D 6 heads data)
      (RecoveryCalls.stopped (fun j => (pieces code C D j).states) r.final.heads r.final.tapes) := by
  have hp := Full.quiet_trace (o := RecoveryOracle.correctedSat) (ports D) (pieces code C D 6) (fun _ => rfl) budget _ r hr
  have ht := graph_trace (ports D) (pieces code C D) 0 (next code C D) 6 hp
  have hj := graph_stop RecoveryOracle.correctedSat (ports D) (pieces code C D) 0
    (next code C D) 6 r.final (prefix_of_run _ _ _ r hr).2 rfl
  exact OrdinaryOracleCompose.trans ht hj

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Request
