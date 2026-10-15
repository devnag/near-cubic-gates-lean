import Proof.CaseAnalysis.RowsEstimatorDriverPartialReset

/-! Return every scratch cursor in parallel by D+1 using the retained D.
The worker is the existing zero-tape scratch sweep (a driver scan), focused
into the old bank and wrapped by the existing masked recorded reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverReturnMany
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot (t : ℕ) : Fin 1 → Fin (t+2) := fun _ => (0 : Fin 2).natAdd t
noncomputable def body (t : ℕ) := RecoveryFocus.machine (slot t) (RecoveryScratchErase.machine 0)
noncomputable def machine (t : ℕ) := MaskedReset.machine (body t) (fun _ => true)
def heads (t pos : ℕ) : Fin (t+2) → ℕ := Fin.addCases (fun _ : Fin t => pos) (fun _ : Fin 2 => 0)
def scannedHeads (t D pos : ℕ) : Fin (t+2) → ℕ := Fin.addCases (fun _ : Fin t => pos) (![D,0] : Fin 2 → ℕ)
def words {t : ℕ} (D : ℕ) (data : Fin t → List Bool) : Fin (t+2) → List Bool :=
  Fin.addCases data (fun _ : Fin 2 => List.replicate D true)
def start {t : ℕ} (D pos : ℕ) (data : Fin t → List Bool) : Configuration (t+2) 2 :=
  ⟨0,heads t pos,words D data⟩
def cfg {t : ℕ} (q : Fin 4) (D pos : ℕ) (data : Fin t → List Bool) : Configuration (t+2+1) 4 :=
  Rewind.config q (heads t pos) (words D data) 0 (List.replicate (D+1) false)

theorem avoids (t : ℕ) (j : Fin t) : ∀ i,slot t i≠j.castAdd 2 := by
  intro i he
  have hv := congrArg (fun z : Fin (t+2) => z.val) he
  have hj := j.isLt
  dsimp [slot] at hv
  omega

theorem body_run {t : ℕ} (D pos : ℕ) (data : Fin t → List Bool) : ∃ r,
    runFrom (body t) (D+1) (start D pos data)=some r ∧
      r.final=(⟨1,scannedHeads t D pos,words D data⟩ : Configuration (t+2) 2) ∧ r.steps=D+1 := by
  obtain ⟨base,hb,bf,bs⟩ := DriverSweep.forward D 0 (fun _ : Fin 0 => [])
  obtain ⟨r,hr,rc,rs,rh,rt,keep⟩ := RecoveryFocus.dock (slot t)
    (by intro i j _;exact Subsingleton.elim i j) (RecoveryScratchErase.machine 0) (D+1)
    (heads t pos) (words D data) _
    (by intro i;fin_cases i;simp [heads,slot,DriverSweep.cfg,Fin.addCases])
    (by intro i;fin_cases i;simp [words,slot,DriverSweep.cfg,RecoveryScratchErase.tapes,Fin.addCases]) base hb
  refine ⟨r,hr,?_,rs.trans bs⟩
  apply configuration_ext
  · rw [rc,bf]
    rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=2) (fun j => ?_) (fun j => ?_) i
    · rw [(keep _ (avoids t j)).1]
      simp [heads,scannedHeads]
    · fin_cases j
      · simpa [slot,bf,DriverSweep.cfg,scannedHeads,Fin.addCases] using rh 0
      · rw [(keep _ (by intro j he;have hv:=congrArg Fin.val he;simp [slot] at hv)).1]
        simp [heads,scannedHeads]
  · funext i
    refine Fin.addCases (m:=t) (n:=2) (fun j => ?_) (fun j => ?_) i
    · exact (keep _ (avoids t j)).2
    · fin_cases j
      · simpa [slot,bf,DriverSweep.cfg,words,RecoveryScratchErase.tapes,Fin.addCases] using rt 0
      · exact (keep _ (by intro j he;have hv:=congrArg Fin.val he;simp [slot] at hv)).2

theorem run {t : ℕ} (D pos : ℕ) (data : Fin t → List Bool) : ∃ r,
    runFrom (machine t) (2*D+4) (cfg 0 D pos data)=some r ∧
      r.final=cfg 3 D (pos-(D+1)) data ∧ r.steps=2*D+4 := by
  obtain ⟨base,hb,bf,bs⟩ := body_run D pos data
  obtain ⟨r,hr,rf,rs⟩ := DriverSweep.partial_workspace (body t) (fun _ => true) (D+1) (D+1) _ base hb
  have hin : ZeroPadding.config (Rewind.Workspace.capacities (t+2) (D+1)) (Rewind.recording (start D pos data) 0)=
      cfg 0 D pos data := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m:=t+2) (n:=1) (fun j => ?_) (fun j => ?_) i <;>
        simp [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,start,cfg,ZeroPadding.pad]
  rw [hin,bs] at hr
  have htime : 2*(D+1)+2=2*D+4 := by omega
  rw [htime] at hr
  refine ⟨r,hr,?_,by rw [rs,bs];omega⟩
  rw [rf,bf,bs]
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t+2) (n:=1) (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (m:=t) (n:=2) (fun j => ?_) (fun j => ?_) j
      · simp [SelectiveReset.finished,Rewind.config,cfg,heads,scannedHeads]
      · fin_cases j <;> simp [SelectiveReset.finished,Rewind.config,cfg,heads,scannedHeads]
    · simp [SelectiveReset.finished,Rewind.config,cfg]
  · simp [SelectiveReset.finished,Rewind.config,cfg]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverReturnMany
