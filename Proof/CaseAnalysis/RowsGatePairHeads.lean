import Proof.CaseAnalysis.RowsGateRawRun

/-! The existing two-node guard also runs at retained physical heads.
This is required by the public source-domain template at head one; no
head conversion, template copy or additional machine is introduced. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGatePairHeads
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CloseoutRowsGateColdPair
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ReadyAt {t s : ℕ} (p : Machine t s) (fuel : ℕ) (heads : Fin t → ℕ)
    (input output : Fin t → List Bool) : Prop := ∃ r,
  runFrom p fuel (RecoveryCalls.restarted p heads input)=some r ∧
    r.final.tapes=output ∧ r.final.heads=heads ∧ r.steps ≤ fuel

theorem joined {t a b : ℕ} (p : Machine t a) (q : Machine t b) (test : (Fin t → Bool) → Bool)
    (fp fq : ℕ) (heads : Fin t → ℕ) (input middle output : Fin t → List Bool)
    (hp : ReadyAt p fp heads input middle) (hq : ReadyAt q fq heads middle output)
    (hn : test (fun i => readTapeBit (middle i) (heads i))=true) :
    ReadyAt (machine p q test) (fp+1+fq+1) heads input output := by
  obtain ⟨r1,hr1,t1,h1,_s1⟩ := hp
  obtain ⟨r2,hr2,t2,h2,_s2⟩ := hq
  have scan : r1.final.scanned=(fun i => readTapeBit (middle i) (heads i)) := by
    funext i;simp only [Configuration.scanned,t1,h1]
  obtain ⟨u,hu,first⟩ := call_receipt (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 0 1 fp _ r1 hr1 (by
      change (if test r1.final.scanned then some (1 : Fin 2) else none)=some 1
      rw [scan,hn];rfl)
  rw [h1,t1] at first
  obtain ⟨v,hv,last⟩ := stop_receipt (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 1 fq _ r2 hr2 (by rfl)
  obtain ⟨r,hr,rf,rs⟩ := (first.trans last).run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  have hb : u+v ≤ fp+1+fq+1 := by omega
  have more := runFrom_moreFuel (machine p q test) (u+v) (fp+1+fq+1-(u+v)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,by rw [rf];exact t2,by rw [rf];exact h2,rs.le.trans hb⟩

theorem rejected {t a b : ℕ} (p : Machine t a) (q : Machine t b) (test : (Fin t → Bool) → Bool)
    (fp : ℕ) (heads : Fin t → ℕ) (input output : Fin t → List Bool)
    (hp : ReadyAt p fp heads input output) (hn : test (fun i => readTapeBit (output i) (heads i))=false) :
    ReadyAt (machine p q test) (fp+1) heads input output := by
  obtain ⟨base,hbase,bt,bh,_bs⟩ := hp
  have scan : base.final.scanned=(fun i => readTapeBit (output i) (heads i)) := by
    funext i;simp only [Configuration.scanned,bt,bh]
  obtain ⟨u,hu,trace⟩ := stop_receipt (sizes (a := a) (b := b)) (programs p q) 0
    (next test) 0 fp _ base hbase (by
      change (if test base.final.scanned then some (1 : Fin 2) else none)=none
      rw [scan,hn];rfl)
  obtain ⟨r,hr,rf,rs⟩ := trace.run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  have more := runFrom_moreFuel (machine p q test) u (fp+1-u) _ r hr
  rw [Nat.add_sub_of_le hu] at more
  exact ⟨r,more,by rw [rf];exact bt,by rw [rf];exact bh,rs.le.trans hu⟩

theorem enlarge {t s : ℕ} (p : Machine t s) (small large : ℕ) (heads : Fin t → ℕ)
    (input output : Fin t → List Bool) (h : ReadyAt p small heads input output) (hb : small ≤ large) :
    ReadyAt p large heads input output := by
  obtain ⟨r,hr,rt,rh,rs⟩ := h
  have more := runFrom_moreFuel p small (large-small) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rt,rh,rs.trans hb⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGatePairHeads
