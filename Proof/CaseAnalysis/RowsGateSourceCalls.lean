import Proof.CaseAnalysis.RowsGateGuardRun
import Proof.Circuits.DecompositionSourceRealization

/-! The guarded original source call may return its documented output
cursor and templates, rather than restore every head to the caller's entry.
The same two-node controller transports that exact receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSourceCalls
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CloseoutRowsGateColdPair CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem joined {t a b : ℕ} (p : Machine t a) (q : Machine t b) (test : (Fin t → Bool) → Bool)
    (fp fq : ℕ) (heads : Fin t → ℕ) (input middle : Fin t → List Bool)
    (hp : ReadyAt p fp heads input middle) (last : ExecutionReceipt t b)
    (hq : runFrom q fq (RecoveryCalls.restarted q heads middle)=some last)
    (hn : test (fun i => readTapeBit (middle i) (heads i))=true) :
    ∃ r,runFrom (machine p q test) (fp+1+fq+1)
      (RecoveryCalls.restarted (machine p q test) heads input)=some r ∧
      r.final.tapes=last.final.tapes ∧ r.final.heads=last.final.heads ∧ r.steps≤fp+1+fq+1 := by
  obtain ⟨base,hbase,bt,bh,_bs⟩ := hp
  have scan : base.final.scanned=(fun i => readTapeBit (middle i) (heads i)) := by
    funext i;simp only [Configuration.scanned,bt,bh]
  obtain ⟨u,hu,first⟩ := call_receipt (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 0 1 fp _ base hbase (by
      change (if test base.final.scanned then some (1 : Fin 2) else none)=some 1
      rw [scan,hn];rfl)
  rw [bh,bt] at first
  obtain ⟨v,hv,tail⟩ := stop_receipt (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 1 fq _ last hq (by rfl)
  obtain ⟨r,hr,rf,rs⟩ := (first.trans tail).run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  have hb : u+v≤fp+1+fq+1 := by omega
  have more := runFrom_moreFuel (machine p q test) (u+v) (fp+1+fq+1-(u+v)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,by rw [rf];rfl,by rw [rf];rfl,rs.le.trans hb⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSourceCalls
