import Proof.CaseAnalysis.RowsEstimatorDriverClean

/-! The actual unary copy already supplies a D+2 false log. Reuse its
allocated cells through the unchanged cleanup program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverClean
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def logCapacity (t L : ℕ) : Fin (t+1+2) → ℕ :=
  Fin.addCases (fun _ : Fin (t+1) => 0) (![0,L] : Fin 2 → ℕ)
def logged {t : ℕ} (D pos L : ℕ) (data : Fin t → List Bool) : Fin (t+1+2) → List Bool :=
  Fin.addCases (RecoveryScratchErase.tapes D pos data)
    (![List.replicate D true,List.replicate L false] : Fin 2 → List Bool)

theorem pad_words {t : ℕ} (D pos L : ℕ) (data : Fin t → List Bool) (hL : D+1≤L) :
    (fun i => ZeroPadding.pad (logCapacity t L i) (DriverSweep.words D pos data i))=
      logged D pos L data := by
  funext i
  refine Fin.addCases (m:=t+1) (n:=2) (fun j => ?_) (fun j => ?_) i
  · simp [logCapacity,DriverSweep.words,logged]
  · fin_cases j
    · simp [logCapacity,DriverSweep.words,DriverSweep.extra,logged]
    · simp only [logCapacity,DriverSweep.words,DriverSweep.extra,logged,Fin.addCases_right]
      change ZeroPadding.pad L (List.replicate (D+1) false)=List.replicate L false
      unfold ZeroPadding.pad
      rw [List.length_replicate,← List.replicate_add]
      congr 1
      omega

theorem logged_run {t : ℕ} (D K L : ℕ) (data : Fin t → List Bool)
    (bound : ∀ i,(data i).length≤K*D) (hL : D+1≤L) :
    ClockJoin.ReadyRun (machine t K) (K*(5*D+10)+1)
      (logged D 0 L data) (logged D (K*D) L (fun _ : Fin t => [])) := by
  obtain ⟨base,hb,bt,bh,bs⟩ := run D K data bound
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config (machine t K) (logCapacity t L)
    _ _ base hb
  have hi : ZeroPadding.config (logCapacity t L)
      (initialConfiguration (machine t K) (DriverSweep.words D 0 data))=
      initialConfiguration (machine t K) (logged D 0 L data) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact pad_words D 0 L data hL
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,by rw [rs,bs]⟩
  · rw [rf]
    change (fun i => ZeroPadding.pad (logCapacity t L i) (base.final.tapes i))=_
    rw [bt]
    exact pad_words D (K*D) L (fun _ : Fin t => []) hL
  · intro i
    rw [rf]
    exact bh i

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverClean
