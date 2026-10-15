import Proof.Supplier.RowTupleTerms

/-! Advance the actual tuple tape after its accepted-candidate consumer has
returned. Only the tuple and continuation flag change; the filter bank stays. -/
namespace NearCubicWires.RepairOrdinary.RowTupleAdvance
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowTupleFilterParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (w k : ℕ) (flag : Bool) : Fin 3→List Bool :=
  ![frame (binary (w*k+1) (2^(w*k)-1)),[flag],List.replicate (2*(w*k)+3) false]
def cfg {s : ℕ} (q : Fin s) (w k : ℕ) (x : Data) (flag : Bool) : Configuration 17 s :=
  TapeEmbedding.config (fun _=>0) (extra w k flag) (RowTupleFilterReusable.cfg q w k x)
def next (w k n : ℕ) (x : Data) : Data := {x with source:=frame (binary (w*k+1) (n+1))}
def slots : Fin 4→Fin 17 := ![0,14,15,16]
theorem injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots RowTupleCounter.machine

theorem pick (i : Fin 17) : RecoveryFocus.pick slots i=
    if i=0 then some 0 else if i=14 then some 1 else if i=15 then some 2 else if i=16 then some 3 else none := by
  fin_cases i
  all_goals
    first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | exact RecoveryFocus.pick_slot slots injective 3
    | decide

theorem next_run (w k n : ℕ) (x : Data) (flag : Bool)
    (hn : n<2^(w*k)) (hx : x.source=frame (binary (w*k+1) n)) :
    ∃ r,runFrom machine (8*(w*k)+17) (cfg machine.start w k x flag)=some r ∧
      r.final.heads=(cfg machine.start w k x flag).heads ∧
      r.final.tapes=(cfg machine.start w k (next w k n x) (decide (n+1<2^(w*k)))).tapes ∧
      r.steps≤8*(w*k)+17 := by
  obtain ⟨base,hbase,bf⟩ := RowTupleCounter.binary_next_run (w*k) n flag hn
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective RowTupleCounter.machine
    (cfg machine.start w k x flag).heads (cfg machine.start w k x flag).tapes _ _ base hbase
  have hi : RecoveryFocus.config slots (cfg machine.start w k x flag).heads
      (cfg machine.start w k x flag).tapes
      (WitnessCounterCheck.config RowTupleCounter.machine.start (w*k+1) n (2^(w*k)-1) (2*(w*k)+3) flag)=
      cfg machine.start w k x flag := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i
      · exact hx
      · rfl
      · rfl
      · rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [rf,bf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick,WitnessCounterCheck.config,cfg,TapeEmbedding.config,
      Fin.addCases,RowTupleFilterReusable.cfg,RowTupleFilterReusable.heads]
  · rw [rf,bf]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,pick,WitnessCounterCheck.config,cfg,TapeEmbedding.config,
      Fin.addCases,RowTupleFilterReusable.cfg,RowTupleFilterReusable.tapes,RowTupleFilterParts.tapes,extra,next]
  · rw [rs]
    exact runFrom_steps_le RowTupleCounter.machine _ _ base hbase

end NearCubicWires.RepairOrdinary.RowTupleAdvance
