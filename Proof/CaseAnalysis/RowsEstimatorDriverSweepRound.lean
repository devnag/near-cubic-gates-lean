import Proof.CaseAnalysis.RowsEstimatorDriverReturn

/-! One actual offset D sweep, followed by return of only its D cursor.
A second retained D word and the D+1 log are reused between fixed passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (D : ℕ) : Fin 2 → List Bool := ![List.replicate D true,List.replicate (D+1) false]
def returnSlots (t : ℕ) : Fin 3 → Fin (t+1+2) :=
  ![(((0 : Fin 1).natAdd t).castAdd 2),((0 : Fin 2).natAdd (t+1)),((1 : Fin 2).natAdd (t+1))]
theorem return_injective (t : ℕ) : Function.Injective (returnSlots t) := by
  intro i j he
  have hv := congrArg (fun z : Fin (t+1+2) => z.val) he
  fin_cases i <;> fin_cases j <;> simp [returnSlots] at hv ⊢ <;> omega
theorem avoids (t : ℕ) (j : Fin t) : ∀ i,returnSlots t i≠(j.castAdd 1).castAdd 2 := by
  intro i he
  have hv := congrArg (fun z : Fin (t+1+2) => z.val) he
  have hj := j.isLt
  fin_cases i <;> simp [returnSlots] at hv <;> omega

def roundFirst (t : ℕ) := TapeEmbedding.machine 2 (RecoveryScratchErase.machine t)
noncomputable def roundLast (t : ℕ) := RecoveryFocus.machine (returnSlots t) CompetitorRecordRewind.machine
noncomputable def round (t : ℕ) := Composition.machine (roundFirst t) (roundLast t)
def heads (t offset : ℕ) : Fin (t+1+2) → ℕ :=
  Fin.addCases (Fin.addCases (fun _ : Fin t => offset) (fun _ : Fin 1 => 0)) (fun _ : Fin 2 => 0)
def words {t : ℕ} (D offset : ℕ) (backing : Fin t → List Bool) : Fin (t+1+2) → List Bool :=
  Fin.addCases (RecoveryScratchErase.tapes D offset backing) (extra D)
noncomputable def entry {t : ℕ} (D offset : ℕ) (backing : Fin t → List Bool) : Configuration (t+1+2) 5 :=
  Composition.leftConfig 3 (TapeEmbedding.config (fun _ : Fin 2 => 0) (extra D) (cfg 0 D offset 0 backing))

theorem round_run {t : ℕ} (D offset : ℕ) (backing : Fin t → List Bool) : ∃ r,
    runFrom (round t) (3*D+4) (entry D offset backing)=some r ∧
      r.final.heads=heads t (offset+D) ∧ r.final.tapes=words D (offset+D) backing ∧ r.steps=3*D+4 := by
  obtain ⟨base,hb,bf,bs⟩ := forward D offset backing
  let before := TapeEmbedding.receipt (fun _ : Fin 2 => 0) (extra D) base
  have hf := TapeEmbedding.run_embed (RecoveryScratchErase.machine t) (fun _ : Fin 2 => 0) (extra D) _ _ base hb
  obtain ⟨ret,hr,rf,rs⟩ := return_padded (List.replicate D true) D D
  obtain ⟨after,ha,_ac,asteps,ah,atapes,keep⟩ := RecoveryFocus.dock (returnSlots t) (return_injective t)
    CompetitorRecordRewind.machine (2*D+2) before.final.heads before.final.tapes _
    (by intro i;fin_cases i <;> simp [before,TapeEmbedding.receipt,TapeEmbedding.config,bf,returnSlots,cfg,CompetitorRecordRewind.cfg])
    (by intro i;fin_cases i <;> simp [before,TapeEmbedding.receipt,TapeEmbedding.config,bf,returnSlots,cfg,CompetitorRecordRewind.cfg,RecoveryScratchErase.tapes,extra])
    ret hr
  have hjoin := Composition.run_join (roundFirst t) (roundLast t) _ _ _ before after hf ha
  have htime : (D+1)+1+(2*D+2)=3*D+4 := by omega
  rw [htime] at hjoin
  refine ⟨Composition.joinedReceipt before after,hjoin,?_,?_,?_⟩
  · change after.final.heads=_
    funext i
    refine Fin.addCases (m:=t+1) (n:=2) (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun j => ?_) (fun j => ?_) j
      · rw [(keep _ (avoids t j)).1]
        simp [heads,before,TapeEmbedding.receipt,TapeEmbedding.config,bf,cfg]
      · fin_cases j
        simpa [returnSlots,heads,rf,CompetitorRecordRewind.cfg] using ah 0
    · fin_cases j
      · simpa [returnSlots,heads,rf,CompetitorRecordRewind.cfg] using ah 1
      · simpa [returnSlots,heads,rf,CompetitorRecordRewind.cfg] using ah 2
  · change after.final.tapes=_
    funext i
    refine Fin.addCases (m:=t+1) (n:=2) (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (m:=t) (n:=1) (fun j => ?_) (fun j => ?_) j
      · rw [(keep _ (avoids t j)).2]
        simp [words,before,TapeEmbedding.receipt,TapeEmbedding.config,bf,cfg]
      · fin_cases j
        simpa [returnSlots,words,RecoveryScratchErase.tapes,rf,CompetitorRecordRewind.cfg] using atapes 0
    · fin_cases j
      · simpa [returnSlots,words,extra,rf,CompetitorRecordRewind.cfg] using atapes 1
      · simpa [returnSlots,words,extra,rf,CompetitorRecordRewind.cfg] using atapes 2
  · change base.steps+1+after.steps=_
    rw [bs,asteps,rs]
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
