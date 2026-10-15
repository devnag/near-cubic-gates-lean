import Proof.Amplification.RecoveryCursorCalls

/-! The assignment dispatcher's two finite paths, checked with symbolic worker
state counts so neither branch expands the other branch's machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AssignmentPaths
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {t k : ℕ} (sizes : Fin k → ℕ)
  (programs : (j : Fin k) → Machine t (sizes j))
  (entry : Fin k)
  (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))

theorem finish {n bound : ℕ} {H : Fin t → ℕ} {A : Fin t → List Bool}
    {H' : Fin t → ℕ} {A' : Fin t → List Bool}
    (path : Timed (RecoveryCalls.machine sizes programs entry next) n
      (controlConfig (RecoveryCalls.code sizes entry)
        (RecoveryCalls.restarted (programs entry) H A))
      (RecoveryCalls.stopped sizes H' A')) (hb : n ≤ bound) : ∃ out,
    runFrom (RecoveryCalls.machine sizes programs entry next) bound
      ⟨(RecoveryCalls.machine sizes programs entry next).start,H,A⟩=some out ∧
    out.steps ≤ bound ∧ out.final.heads=H' ∧ out.final.tapes=A':=by
  obtain ⟨out,ho,hf,os⟩:=path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel _ n (bound-n) _ out ho
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨out,more,os.le.trans hb,congrArg Configuration.heads hf,
    congrArg Configuration.tapes hf⟩

theorem two (last : Fin k) (f g : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (p : ExecutionReceipt t (sizes entry)) (q : ExecutionReceipt t (sizes last))
    (hp : runFrom (programs entry) f (RecoveryCalls.restarted (programs entry) H A)=some p)
    (hq : runFrom (programs last) g
      (RecoveryCalls.restarted (programs last) p.final.heads p.final.tapes)=some q)
    (hn : next entry p.final.control p.final.scanned=some last)
    (he : next last q.final.control q.final.scanned=none) : ∃ out,
    runFrom (RecoveryCalls.machine sizes programs entry next) (f+1+(g+1))
      ⟨(RecoveryCalls.machine sizes programs entry next).start,H,A⟩=some out ∧
    out.steps ≤ f+1+(g+1) ∧ out.final.heads=q.final.heads ∧ out.final.tapes=q.final.tapes:=by
  obtain ⟨np,hnp,pp⟩:=call_receipt sizes programs entry next entry last f _ p hp hn
  obtain ⟨nq,hnq,pq⟩:=stop_receipt sizes programs entry next last g _ q hq he
  exact finish sizes programs entry next (pp.trans pq) (by omega)

theorem three (middle last : Fin k) (f g h : ℕ) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (p : ExecutionReceipt t (sizes entry)) (q : ExecutionReceipt t (sizes middle))
    (r : ExecutionReceipt t (sizes last))
    (hp : runFrom (programs entry) f (RecoveryCalls.restarted (programs entry) H A)=some p)
    (hq : runFrom (programs middle) g
      (RecoveryCalls.restarted (programs middle) p.final.heads p.final.tapes)=some q)
    (hr : runFrom (programs last) h
      (RecoveryCalls.restarted (programs last) q.final.heads q.final.tapes)=some r)
    (hn : next entry p.final.control p.final.scanned=some middle)
    (hm : next middle q.final.control q.final.scanned=some last)
    (he : next last r.final.control r.final.scanned=none) : ∃ out,
    runFrom (RecoveryCalls.machine sizes programs entry next) (f+1+(g+1)+(h+1))
      ⟨(RecoveryCalls.machine sizes programs entry next).start,H,A⟩=some out ∧
    out.steps ≤ f+1+(g+1)+(h+1) ∧ out.final.heads=r.final.heads ∧ out.final.tapes=r.final.tapes:=by
  obtain ⟨np,hnp,pp⟩:=call_receipt sizes programs entry next entry middle f _ p hp hn
  obtain ⟨nq,hnq,pq⟩:=call_receipt sizes programs entry next middle last g _ q hq hm
  obtain ⟨nr,hnr,pr⟩:=stop_receipt sizes programs entry next last h _ r hr he
  exact finish sizes programs entry next ((pp.trans pq).trans pr) (by omega)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AssignmentPaths
