import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomialRun

/-! The original tuple stream controls the actual callback loop. Each body
consumes one complete marked tuple and retires its private row workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTupleFold
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsEstimator
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem trace {t s : ℕ} (p : Machine t s) (port : Fin t) (n cost : ℕ)
    (H : ℕ→Fin t→ℕ) (A : ℕ→Fin t→List Bool)
    (marked : ∀ j<n,readTapeBit (A j port) (H j port)=true)
    (ended : readTapeBit (A n port) (H n port)=false)
    (body : ∀ j<n,Step p cost (H j) (A j) (H (j+1)) (A (j+1))) :
    ∃ time≤n*(cost+2)+1,Timed (SubstitutionRepeat.machine p port) time
      (SubstitutionRepeat.entry p 0 (H 0) (A 0))
      (SubstitutionRepeat.final p (H n) (A n)) := by
  induction n generalizing H A with
  | zero=>exact ⟨1,by omega,SubstitutionRepeat.stop p port _ _ ended⟩
  | succ n ih=>
    have first:=SubstitutionRepeat.probe p port (H 0) (A 0) (marked 0 (by omega))
    obtain ⟨used,hused,call⟩:=SubstitutionRepeat.body p port _ _ _ _ (body 0 (by omega))
    obtain ⟨rest,hrest,tail⟩:=ih (fun j=>H (j+1)) (fun j=>A (j+1))
      (fun j hj=>marked (j+1) (by omega)) ended (fun j hj=>body (j+1) (by omega))
    refine ⟨1+(used+rest),?_,first.trans (call.trans tail)⟩
    rw [Nat.succ_mul]
    omega

theorem run {t s : ℕ} (p : Machine t s) (port : Fin t) (n cost : ℕ)
    (H : ℕ→Fin t→ℕ) (A : ℕ→Fin t→List Bool)
    (marked : ∀ j<n,readTapeBit (A j port) (H j port)=true)
    (ended : readTapeBit (A n port) (H n port)=false)
    (body : ∀ j<n,Step p cost (H j) (A j) (H (j+1)) (A (j+1))) :
    Step (SubstitutionRepeat.machine p port) (n*(cost+2)+1) (H 0) (A 0) (H n) (A n) := by
  obtain ⟨time,ht,tr⟩:=trace p port n cost H A marked ended body
  obtain ⟨r,hr,hf,_⟩:=tr.run (by simp [SubstitutionRepeat.machine,SubstitutionRepeat.final,
    RecoveryCalls.machine,RecoveryCalls.stopped])
  rw [SubstitutionMonomial.repeat_entry p port] at hr
  exact (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).enlarge ht

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTupleFold
