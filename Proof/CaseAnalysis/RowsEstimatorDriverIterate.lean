import Proof.CaseAnalysis.RowsEstimatorDriverReturnMany
import Proof.CaseAnalysis.RowsEstimatorDriverSweepRound

/-! A finite, program-constant number of actual cleanup passes. Each
composition handoff is included in the execution receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverIterate
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => states s n+s
def stop (t : ℕ) : Machine t 1 := ⟨0,0,fun _ => true,fun _ _ => none⟩
def machine {t s : ℕ} (p : Machine t s) : (n : ℕ) → Machine t (states s n)
  | 0 => stop t
  | n+1 => Composition.machine (machine p n) p
def cfg {t s : ℕ} (p : Machine t s) (n : ℕ)
    (h : Fin t → ℕ) (w : Fin t → List Bool) : Configuration t (states s n) :=
  ⟨(machine p n).start,h,w⟩

theorem run {t s : ℕ} (p : Machine t s) (fuel : ℕ)
    (h : ℕ → Fin t → ℕ) (w : ℕ → Fin t → List Bool)
    (step : ∀ n,∃ r,runFrom p fuel ⟨p.start,h n,w n⟩=some r ∧
      r.final.heads=h (n+1) ∧ r.final.tapes=w (n+1) ∧ r.steps=fuel) (n : ℕ) :
    ∃ r,runFrom (machine p n) (n*(fuel+1)) (cfg p n (h 0) (w 0))=some r ∧
      r.final.heads=h n ∧ r.final.tapes=w n ∧ r.steps=n*(fuel+1) := by
  induction n with
  | zero =>
    refine ⟨⟨cfg p 0 (h 0) (w 0),0,(cfg p 0 (h 0) (w 0)).tapeCells⟩,?_,rfl,rfl,by simp⟩
    simp [machine,stop,cfg,runFrom]
  | succ n ih =>
    obtain ⟨first,hf,fh,ft,fs⟩ := ih
    obtain ⟨last,hl,lh,lt,ls⟩ := step n
    have he : Composition.restart first.final p.start=⟨p.start,h n,w n⟩ := by
      apply configuration_ext
      · rfl
      · exact fh
      · exact ft
    rw [← he] at hl
    have hj := Composition.run_join (machine p n) p _ _ _ first last hf hl
    have ht : n*(fuel+1)+1+fuel=(n+1)*(fuel+1) := by ring
    rw [ht] at hj
    refine ⟨Composition.joinedReceipt first last,hj,lh,lt,?_⟩
    change first.steps+1+last.steps=(n+1)*(fuel+1)
    rw [fs,ls,ht]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverIterate
