import Proof.MachineModel.UMemoryCloseFinish

/-! Whole final verifier pipeline: execute the supplied fixed emitter,
append its sole delimiter, reset only the event cursor once, and physically
branch to false or the existing chronological checker on fresh workspace. -/
namespace NearCubicWires.RepairOrdinary.UMemoryClose
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev finishStates := Fintype.card (RecoveryCalls.Control finishSizes)
noncomputable def machine {t s : ℕ} (p : Machine t s) (event flag : Fin t) :
    Machine ((t+1)+20) (((s+2)+2)+finishStates) :=
  Composition.machine (resetPrefix p event flag) (finishMachine event flag)

def entry {t s : ℕ} (c : Configuration t s) : Configuration ((t+1)+20) (((s+2)+2)+finishStates) :=
  Composition.leftConfig finishStates (resetEntry c)

def inputTapes {t : ℕ} (tapes : Fin t → List Bool) : Fin ((t+1)+20) → List Bool :=
  Fin.addCases (Fin.addCases tapes (fun _ : Fin 1 => [])) (fun _ : Fin 20 => [])

theorem initial_entry {t s : ℕ} (p : Machine t s) (event flag : Fin t) (tapes : Fin t → List Bool) :
    entry (initialConfiguration p tapes)=initialConfiguration (machine p event flag) (inputTapes tapes) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
        simp [entry,resetEntry,TapeEmbedding.config,Rewind.recording,Rewind.config,
          Composition.leftConfig,initialConfiguration]
    · simp [entry,resetEntry,TapeEmbedding.config,Composition.leftConfig,initialConfiguration]
  · rfl

theorem close_run {t s : ℕ} (p : Machine t s) (event flag : Fin t) (hne : event ≠ flag)
    (fuel : ℕ) (c : Configuration t s) (source : ExecutionReceipt t s)
    (hsource : runFrom p fuel c=some source) (hstart : c.heads event=0)
    (answer : Option MemoryChecker.Request) (hflag : source.final.scanned flag=answer.isSome)
    (hstream : ∀ req, answer=some req → source.final.tapes event++[false]=req.input ∧
      source.final.heads event=(source.final.tapes event).length) :
    ∃ r,runFrom (machine p event flag) (2*fuel+answerBudget answer+10) (entry c)=some r ∧
      r.steps≤2*fuel+answerBudget answer+10 ∧
      r.final.tapes (resultSlot t)=[answerValue answer] ∧ r.final.heads (resultSlot t)=0 ∧
      r.final.scanned (resultSlot t)=answerValue answer ∧
      (∀ i : Fin t, i ≠ event → r.final.heads (oldSlot i)=source.final.heads i ∧
        r.final.tapes (oldSlot i)=source.final.tapes i) := by
  obtain ⟨reset,hr,hrf,_⟩ := reset_prefix_run p event flag fuel c source hsource hstart
  obtain ⟨tail,ht,htt,hth,hother⟩ := finish_run event flag hne source.final source.steps answer hflag hstream
  have ht' : runFrom (finishMachine event flag) (answerBudget answer+3)
      (Composition.restart reset.final (finishMachine event flag).start)=some tail := by
    rw [hrf]
    exact ht
  have hjoin := Composition.run_join (resetPrefix p event flag) (finishMachine event flag)
    (2*source.steps+6) (answerBudget answer+3) (resetEntry c) reset tail hr ht'
  have hsteps := runFrom_steps_le p fuel c source hsource
  have hbound : (2*source.steps+6)+1+(answerBudget answer+3) ≤ 2*fuel+answerBudget answer+10 := by omega
  have hmore := runFrom_moreFuel (machine p event flag) ((2*source.steps+6)+1+(answerBudget answer+3))
    ((2*fuel+answerBudget answer+10)-((2*source.steps+6)+1+(answerBudget answer+3))) _ _ hjoin
  rw [Nat.add_sub_of_le hbound] at hmore
  let result := Composition.joinedReceipt reset tail
  have hout : result.final.tapes (resultSlot t)=[answerValue answer] := htt
  have hhead : result.final.heads (resultSlot t)=0 := hth
  refine ⟨result,hmore,runFrom_steps_le (machine p event flag) _ _ result hmore,hout,hhead,?_,hother⟩
  simp only [Configuration.scanned,hhead,hout,readTapeBit,List.getD,List.getElem?_cons_zero,Option.getD_some]

theorem close_initial_run {t s : ℕ} (p : Machine t s) (event flag : Fin t) (hne : event ≠ flag)
    (fuel : ℕ) (tapes : Fin t → List Bool) (source : ExecutionReceipt t s)
    (hsource : run p fuel tapes=some source)
    (answer : Option MemoryChecker.Request) (hflag : source.final.scanned flag=answer.isSome)
    (hstream : ∀ req, answer=some req → source.final.tapes event++[false]=req.input ∧
      source.final.heads event=(source.final.tapes event).length) :
    ∃ r,run (machine p event flag) (2*fuel+answerBudget answer+10) (inputTapes tapes)=some r ∧
      r.steps≤2*fuel+answerBudget answer+10 ∧
      r.final.tapes (resultSlot t)=[answerValue answer] ∧ r.final.heads (resultSlot t)=0 ∧
      r.final.scanned (resultSlot t)=answerValue answer ∧
      (∀ i : Fin t, i ≠ event → r.final.heads (oldSlot i)=source.final.heads i ∧
        r.final.tapes (oldSlot i)=source.final.tapes i) := by
  obtain ⟨r,hr,hsteps,ht,hh,hs,ho⟩ := close_run p event flag hne fuel
    (initialConfiguration p tapes) source hsource rfl answer hflag hstream
  rw [initial_entry p event flag] at hr
  exact ⟨r,hr,hsteps,ht,hh,hs,ho⟩

end NearCubicWires.RepairOrdinary.UMemoryClose
