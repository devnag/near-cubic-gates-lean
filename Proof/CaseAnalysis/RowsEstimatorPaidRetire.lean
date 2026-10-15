import Proof.CaseAnalysis.RowsEstimatorPaidDriverReady
import Proof.CaseAnalysis.RowsEstimatorDriverRetire

/-! Retire both actual D words at their final shared-bank locations. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def retireSlots (a : WilliamsAlgorithm) (p : Program) : Fin 2 → Fin (tapes a p) :=
  ![old a p (WarmPrepare.driver p),(ScannedClean.fresh a 1).natAdd (WarmPrepare.tapes p)]
noncomputable def retire (a : WilliamsAlgorithm) (p : Program):=RecoveryFocus.machine (retireSlots a p) DriverRetire.machine

theorem retire_injective (a : WilliamsAlgorithm) (p : Program) : Function.Injective (retireSlots a p) := by
  intro i j he
  have hv:=congrArg (fun z : Fin (tapes a p)=>z.val) he
  have hd:=(WarmPrepare.driver p).isLt
  fin_cases i <;> fin_cases j <;> simp [retireSlots,old,Fin.val_natAdd] at hv ⊢ <;> omega

theorem retire_heads (a : WilliamsAlgorithm) (p : Program) (out : List Bool) (j : Fin 2) :
    heads a p out (retireSlots a p j)=0 := by
  fin_cases j
  · simp [retireSlots,heads,old,WarmPrepare.heads,WarmPrepared.driver_ne]
  · simp [retireSlots,heads]

theorem retire_input (a : WilliamsAlgorithm) (p : Program) (D : ℕ)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool)
    (hd : A (WarmPrepare.driver p)=List.replicate D true)
    (he : extra (ScannedClean.fresh a 1)=List.replicate D true) (j : Fin 2) :
    Fin.addCases A extra (retireSlots a p j)=List.replicate D true := by
  fin_cases j
  · simpa [retireSlots,old] using hd
  · simpa [retireSlots] using he

def FocusResult {t u s : ℕ} (slot : Fin t → Fin u) (worker : Machine t s) (n : ℕ)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (B : Fin t → List Bool) : Prop := ∃ r,
    runFrom (RecoveryFocus.machine slot worker) n ⟨worker.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=install slot A B ∧ r.steps=n

theorem focus_result {t u s n : ℕ} (worker : Machine t s) (A B : Fin t → List Bool)
    (hr : ReadyRun worker n A B) (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (H : Fin u → ℕ) (ambient : Fin u → List Bool)
    (hin : ∀ j,ambient (slot j)=A j) (hh : ∀ j,H (slot j)=0) :
    FocusResult slot worker n H ambient B := hr.focus_at slot hi H ambient hin hh

theorem retire_focus {u : ℕ} (D : ℕ) (slot : Fin 2 → Fin u) (hi : Function.Injective slot)
    (H : Fin u → ℕ) (ambient : Fin u → List Bool)
    (hin : ∀ j,ambient (slot j)=List.replicate D true) (hh : ∀ j,H (slot j)=0) :
    FocusResult slot DriverRetire.machine (2*D+4) H ambient (fun _=>List.replicate D false) :=
  focus_result DriverRetire.machine _ _ (DriverRetire.ready D) slot hi H ambient hin hh

theorem retire_run (a : WilliamsAlgorithm) (p : Program) (D : ℕ) (out : List Bool)
    (A : Fin (WarmPrepare.tapes p) → List Bool) (extra : Fin (ScannedClean.tapes a) → List Bool)
    (hd : A (WarmPrepare.driver p)=List.replicate D true)
    (he : extra (ScannedClean.fresh a 1)=List.replicate D true) :
    FocusResult (retireSlots a p) DriverRetire.machine (2*D+4) (heads a p out)
      (Fin.addCases A extra) (fun _=>List.replicate D false) := by
  have hin : ∀ j : Fin 2,(fun i : Fin (tapes a p)=>Fin.addCases A extra i) (retireSlots a p j)=
      List.replicate D true := by
    intro j
    fin_cases j
    · simpa [retireSlots,old] using hd
    · simpa [retireSlots] using he
  have result:=retire_focus (u:=tapes a p) D (retireSlots a p) (retire_injective a p) (heads a p out)
    (fun i : Fin (tapes a p)=>Fin.addCases A extra i) hin (retire_heads a p out)
  exact result

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
