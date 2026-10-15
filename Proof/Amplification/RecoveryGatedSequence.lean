import Proof.Amplification.RecoveryRowRootResult

/-! Two actual calls with a physical result-cell gate. The abstract state
counts keep enclosing table machines from expanding during composition. -/
namespace NearCubicWires.RepairOrdinary.RecoveryGatedSequence
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes (s u : Nat) : Fin 2→Nat := ![s,u]
def programs {t s u : Nat} (p : Machine t s) (q : Machine t u) : (j : Fin 2)→Machine t (sizes s u j)
  | ⟨0,_⟩=>p
  | ⟨1,_⟩=>q
  | ⟨n+2,h⟩=>False.elim (by omega)
def next {t s u : Nat} (slot : Fin t) (j : Fin 2) (_ : Fin (sizes s u j)) (scanned : Fin t→Bool) : Option (Fin 2) :=
  if j.val=0 then if scanned slot then some 1 else none else none
noncomputable def machine {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t) :=
  RecoveryCalls.machine (sizes s u) (programs p q) 0 (next slot)

theorem reject_run {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t)
    (fuel : Nat) (source : Configuration t s) (first : ExecutionReceipt t s)
    (hr : runFrom p fuel source=some first) (hh : first.final.heads slot=0)
    (ht : first.final.tapes slot=[false]) :
    ∃ r,runFrom (machine p q slot) (fuel+1)
        (controlConfig (RecoveryCalls.code (sizes s u) 0) source)=some r ∧
      r.steps ≤ fuel+1 ∧ r.final=RecoveryCalls.stopped (sizes s u) first.final.heads first.final.tapes := by
  have hn : next (s:=s) (u:=u) slot 0 first.final.control first.final.scanned=none := by
    simp [next,Configuration.scanned,hh,ht,readTapeBit]
  obtain ⟨n,hn,h⟩ := stop_receipt (sizes s u) (programs p q) 0 (next slot) 0 fuel source first hr hn
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel (machine p q slot) n (fuel+1-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hs.le.trans hn,hf⟩

theorem accept_run {t s u : Nat} (p : Machine t s) (q : Machine t u) (slot : Fin t)
    (b1 b2 : Nat) (source : Configuration t s) (first : ExecutionReceipt t s) (last : ExecutionReceipt t u)
    (hr : runFrom p b1 source=some first) (hh : first.final.heads slot=0)
    (ht : first.final.tapes slot=[true])
    (hl : runFrom q b2 (RecoveryCalls.restarted q first.final.heads first.final.tapes)=some last) :
    ∃ r,runFrom (machine p q slot) (b1+b2+2)
        (controlConfig (RecoveryCalls.code (sizes s u) 0) source)=some r ∧
      r.steps ≤ b1+b2+2 ∧ r.final=RecoveryCalls.stopped (sizes s u) last.final.heads last.final.tapes := by
  have hn : next (s:=s) (u:=u) slot 0 first.final.control first.final.scanned=some 1 := by
    simp [next,Configuration.scanned,hh,ht,readTapeBit]
  obtain ⟨n0,hn0,h0⟩ := call_receipt (sizes s u) (programs p q) 0 (next slot) 0 1 b1 source first hr hn
  obtain ⟨n1,hn1,h1⟩ := stop_receipt (sizes s u) (programs p q) 0 (next slot) 1 b2 _ last hl (by rfl)
  have h := h0.trans h1
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb : n0+n1 ≤ b1+b2+2 := by omega
  have hm := runFrom_moreFuel (machine p q slot) (n0+n1) (b1+b2+2-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r,hm,hs.le.trans hb,hf⟩

end NearCubicWires.RepairOrdinary.RecoveryGatedSequence
