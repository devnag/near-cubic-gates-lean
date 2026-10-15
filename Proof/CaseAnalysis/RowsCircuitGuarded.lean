import Proof.CaseAnalysis.RowsCircuitBottomPosition

/-! The existing two-node controller joins circuit stages that retain
changed native/resource cursors. A rejected parser stops immediately. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGuarded
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsGateColdPair
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem accepted {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (test : (Fin t → Bool) → Bool) (fp fq : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (first : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p fp (RecoveryCalls.restarted p H A)=some first)
    (hq : runFrom q fq (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last)
    (yes : test first.final.scanned=true) : ∃ r,
    runFrom (machine p q test) (fp+1+fq+1) (RecoveryCalls.restarted (machine p q test) H A)=some r ∧
      r.steps ≤ fp+1+fq+1 ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes:=by
  obtain ⟨u,hu,one⟩:=call_receipt (sizes (a:=a) (b:=b)) (programs p q) 0 (next test) 0 1 fp _ first hp (by
    change (if test first.final.scanned then some (1 : Fin 2) else none)=some 1
    rw [yes];rfl)
  obtain ⟨v,hv,two⟩:=stop_receipt (sizes (a:=a) (b:=b)) (programs p q) 0 (next test) 1 fq _ last hq (by rfl)
  obtain ⟨r,hr,rf,rs⟩:=(one.trans two).run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  have ht:u+v ≤ fp+1+fq+1:=by omega
  have more:=runFrom_moreFuel (machine p q test) _ (fp+1+fq+1-(u+v)) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨r,more,rs.le.trans ht,by rw [rf];rfl,by rw [rf];rfl⟩

theorem rejected {t a b : ℕ} (p : Machine t a) (q : Machine t b)
    (test : (Fin t → Bool) → Bool) (fp : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (first : ExecutionReceipt t a)
    (hp : runFrom p fp (RecoveryCalls.restarted p H A)=some first)
    (no : test first.final.scanned=false) : ∃ r,
    runFrom (machine p q test) (fp+1) (RecoveryCalls.restarted (machine p q test) H A)=some r ∧
      r.steps ≤ fp+1 ∧ r.final.heads=first.final.heads ∧ r.final.tapes=first.final.tapes:=by
  obtain ⟨u,hu,one⟩:=stop_receipt (sizes (a:=a) (b:=b)) (programs p q) 0 (next test) 0 fp _ first hp (by
    change (if test first.final.scanned then some (1 : Fin 2) else none)=none
    rw [no];rfl)
  obtain ⟨r,hr,rf,rs⟩:=one.run (by
    simp only [RecoveryCalls.machine,RecoveryCalls.stopped,Equiv.symm_apply_apply,Option.isNone_none])
  have more:=runFrom_moreFuel (machine p q test) _ (fp+1-u) _ r hr
  rw [Nat.add_sub_of_le hu] at more
  exact ⟨r,more,rs.le.trans hu,by rw [rf];rfl,by rw [rf];rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitGuarded
