import Proof.CaseAnalysis.RowsEstimatorSubstitutionDock

/-! A shared physical delimiter loop serves both factors and monomials. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionRepeat
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle (t : ℕ) : Machine t 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes (s : ℕ) : Fin 2 → ℕ:=![1,s]
def programs {t s : ℕ} (p : Machine t s) : (i : Fin 2) → Machine t (sizes s i)
  | ⟨0,_⟩=>idle t
  | ⟨1,_⟩=>p
  | ⟨n+2,h⟩=>False.elim (by omega)
def next {t s : ℕ} (port : Fin t) (i : Fin 2) (_ : Fin (sizes s i)) (bits : Fin t → Bool) : Option (Fin 2):=
  if i=0 then if bits port then some 1 else none else some 0
noncomputable def machine {t s : ℕ} (p : Machine t s) (port : Fin t):=RecoveryCalls.machine (sizes s) (programs p) 0 (next port)
noncomputable def entry {t s : ℕ} (p : Machine t s) (i : Fin 2) (H : Fin t → ℕ) (A : Fin t → List Bool):=
  controlConfig (RecoveryCalls.code (sizes s) i) (⟨(programs p i).start,H,A⟩ : Configuration t (sizes s i))
noncomputable def final {t s : ℕ} (_p : Machine t s) (H : Fin t → ℕ) (A : Fin t → List Bool):=
  RecoveryCalls.stopped (sizes s) H A

theorem probe {t s : ℕ} (p : Machine t s) (port : Fin t) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : readTapeBit (A port) (H port)=true) :
    Timed (machine p port) 1 (entry p 0 H A) (entry p 1 H A) := by
  refine Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ?_
  exact RecoveryCalls.return_step (sizes s) (programs p) 0 (next port) 0 1
    (⟨(programs p 0).start,H,A⟩ : Configuration t (sizes s 0)) (by rfl)
    (by simp [next,Configuration.scanned,h])

theorem stop {t s : ℕ} (p : Machine t s) (port : Fin t) (H : Fin t → ℕ) (A : Fin t → List Bool)
    (h : readTapeBit (A port) (H port)=false) :
    Timed (machine p port) 1 (entry p 0 H A) (final p H A) := by
  refine Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ?_
  exact RecoveryCalls.stop_step (sizes s) (programs p) 0 (next port) 0
    (⟨(programs p 0).start,H,A⟩ : Configuration t (sizes s 0)) (by rfl)
    (by simp [next,Configuration.scanned,h])

theorem body {t s n : ℕ} (p : Machine t s) (port : Fin t) (H H' : Fin t → ℕ)
    (A A' : Fin t → List Bool) (raw : Step p n H A H' A') :
    ∃ time ≤ n+1,Timed (machine p port) time (entry p 1 H A) (entry p 0 H' A') := by
  obtain ⟨r,hr,rh,rt,_⟩:=raw
  obtain ⟨time,ht,tr⟩:=call_receipt (sizes s) (programs p) 0 (next port) 1 0 _ _ r hr (by rfl)
  have he : RecoveryCalls.restarted (programs p 0) r.final.heads r.final.tapes=
      (⟨(programs p 0).start,H',A'⟩ : Configuration t (sizes s 0)) := by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [he] at tr
  exact ⟨time,ht,tr⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionRepeat
