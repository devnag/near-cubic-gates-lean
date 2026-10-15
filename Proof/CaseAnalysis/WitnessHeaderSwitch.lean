import Proof.CaseAnalysis.WitnessHeaderDock

/-! The bounded header either rejects or dispatches its actual mode bit
into exactly one checked cold family. The existing call/stop interpreter
charges both control transitions and preserves the selected receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderSwitch
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {t a b c : ℕ}
def sizes (a b c : ℕ) : Fin 3→ℕ:=![a,b,c]
def programs (p : Machine t a) (q : Machine t b) (r : Machine t c) : (j : Fin 3)→Machine t (sizes a b c j)
  | 0=>p | 1=>q | 2=>r
def next (good mode : (Fin t→Bool)→Bool) (j : Fin 3) (_ : Fin (sizes a b c j))
    (cells : Fin t→Bool) : Option (Fin 3):=
  if j.val=0 then if good cells then some (if mode cells then 1 else 2) else none else none
def machine (p : Machine t a) (q : Machine t b) (r : Machine t c)
    (good mode : (Fin t→Bool)→Bool):=
  RecoveryCalls.machine (sizes a b c) (programs p q r) 0 (next good mode)

theorem accepted (p : Machine t a) (q : Machine t b) (r : Machine t c)
    (good mode : (Fin t→Bool)→Bool) (j : Fin 3) (hj:j=1 ∨ j=2) (pfuel fuel : ℕ)
    (heads : Fin t→ℕ) (data : Fin t→List Bool) (prior : ExecutionReceipt t a)
    (last : ExecutionReceipt t (sizes a b c j))
    (hp:runFrom p pfuel ⟨p.start,heads,data⟩=some prior)
    (hl:runFrom (programs p q r j) fuel
      (RecoveryCalls.restarted (programs p q r j) prior.final.heads prior.final.tapes)=some last)
    (hg:good prior.final.scanned=true) (hm:j=if mode prior.final.scanned then 1 else 2) :
    ∃ actual,runFrom (machine p q r good mode) (pfuel+1+fuel+1)
      ⟨(machine p q r good mode).start,heads,data⟩=some actual ∧
      actual.steps ≤ pfuel+1+fuel+1 ∧ actual.final.heads=last.final.heads ∧ actual.final.tapes=last.final.tapes:=by
  obtain ⟨u,hu,first⟩:=call_receipt (sizes a b c) (programs p q r) 0 (next good mode) 0 j pfuel _ prior hp (by
    change (if good prior.final.scanned then some (if mode prior.final.scanned then (1:Fin 3) else 2) else none)=some j
    rw [hg];exact congrArg some hm.symm)
  obtain ⟨v,hv,tail⟩:=stop_receipt (sizes a b c) (programs p q r) 0 (next good mode) j fuel _ last hl
    (by rcases hj with rfl|rfl <;> rfl)
  obtain ⟨actual,hr,hf,hs⟩:=(first.trans tail).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have bound:u+v ≤ pfuel+1+fuel+1:=by omega
  have more:=runFrom_moreFuel (machine p q r good mode) (u+v) (pfuel+1+fuel+1-(u+v)) _ actual hr
  rw [Nat.add_sub_of_le bound] at more
  exact ⟨actual,more,hs.le.trans bound,by rw [hf];rfl,by rw [hf];rfl⟩

theorem rejected (p : Machine t a) (q : Machine t b) (r : Machine t c)
    (good mode : (Fin t→Bool)→Bool) (fuel : ℕ) (heads : Fin t→ℕ) (data : Fin t→List Bool)
    (prior : ExecutionReceipt t a) (hp:runFrom p fuel ⟨p.start,heads,data⟩=some prior)
    (hg:good prior.final.scanned=false) :
    ∃ actual,runFrom (machine p q r good mode) (fuel+1)
      ⟨(machine p q r good mode).start,heads,data⟩=some actual ∧
      actual.steps ≤ fuel+1 ∧ actual.final.heads=prior.final.heads ∧ actual.final.tapes=prior.final.tapes:=by
  obtain ⟨u,hu,trace⟩:=stop_receipt (sizes a b c) (programs p q r) 0 (next good mode) 0 fuel _ prior hp
    (by change (if good prior.final.scanned then some (if mode prior.final.scanned then (1:Fin 3) else 2) else none)=none;rw [hg];rfl)
  obtain ⟨actual,hr,hf,hs⟩:=trace.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel (machine p q r good mode) u (fuel+1-u) _ actual hr
  rw [Nat.add_sub_of_le hu] at more
  exact ⟨actual,more,hs.le.trans hu,by rw [hf];rfl,by rw [hf];rfl⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderSwitch
