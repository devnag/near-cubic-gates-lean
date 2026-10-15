import Proof.CaseAnalysis.RowsTupleSeekTupleLayout

/-! A list-indexed receipt for the existing counted loop, kept symbolic in
its ordinary body's finite control. The body run remains an explicit input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek.RepeatList
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word {α : Type} (emit : α → List Bool) (js : List α) := js.flatMap emit

theorem remaining {t s : ℕ} {α β : Type} (p : Machine t s) (cost : ℕ)
    (source : ℕ → List Bool → β → Configuration t s) (emit : α → List Bool) (update : β → α → β)
    (hstart : ∀ ip index out,(source ip index out).control=p.start)
    (supplier : ∀ j pre tail out,∃ r,runFrom p cost (source pre.length (pre++emit j++tail) out)=some r ∧
      r.final.heads=(source (pre.length+(emit j).length) (pre++emit j++tail) (update out j)).heads ∧
      r.final.tapes=(source (pre.length+(emit j).length) (pre++emit j++tail) (update out j)).tapes ∧ r.steps ≤ cost)
    (js : List α) (pre tail : List Bool) (out : β) (total done : ℕ) (hn : done+js.length=total) :
    ∃ time ≤ js.length*(cost+2)+total+3,Timed (RepeatMachine.machine p (fun _ _=>true)) time
      (RepeatMachine.cfg 0 (source pre.length (pre++word emit js++tail) out) total (done+1))
      (RepeatMachine.cfg 3 (source (pre.length+(word emit js).length)
        (pre++word emit js++tail) (js.foldl update out)) total 1) := by
  induction js generalizing pre out done with
  | nil=>
    have hd : done=total := by simpa using hn
    subst done
    refine ⟨total+3,by simp,?_⟩
    simpa only [word,List.flatMap_nil,List.foldl_nil,List.append_nil,List.length_nil,Nat.add_zero] using
      RepeatMachine.exhaust p (fun _ _=>true) (source pre.length (pre++tail) out) total
  | cons j js ih=>
    let index := pre++emit j++(word emit js++tail)
    obtain ⟨r,hr,rh,rt,rs⟩ := supplier j pre (word emit js++tail) out
    have step := RepeatMachine.iteration p (fun _ _=>true) (source pre.length index out) total done r
      (hstart _ _ _) (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at step
    rw [RowOccurrenceLoop.cfg_eq 0 r.final (source (pre.length+(emit j).length) index (update out j))
      total (done+2) rh rt] at step
    obtain ⟨time,ht,tr⟩ := ih (pre++emit j) (update out j) (done+1)
      (by simp only [List.length_cons] at hn;omega)
    have same : (pre++emit j)++word emit js++tail=index := by simp [index,List.append_assoc]
    rw [same] at tr
    simp only [List.length_append,show done+1+1=done+2 by omega] at tr
    have all := step.trans tr
    refine ⟨r.steps+2+time,?_,?_⟩
    · simp only [List.length_cons];nlinarith
    · simpa only [word,List.flatMap_cons,List.foldl_cons,List.length_append,List.append_assoc,Nat.add_assoc,index] using all

theorem run {t s : ℕ} {α β : Type} (p : Machine t s) (cost : ℕ)
    (source : ℕ → List Bool → β → Configuration t s) (emit : α → List Bool) (update : β → α → β)
    (hstart : ∀ ip index out,(source ip index out).control=p.start)
    (supplier : ∀ j pre tail out,∃ r,runFrom p cost (source pre.length (pre++emit j++tail) out)=some r ∧
      r.final.heads=(source (pre.length+(emit j).length) (pre++emit j++tail) (update out j)).heads ∧
      r.final.tapes=(source (pre.length+(emit j).length) (pre++emit j++tail) (update out j)).tapes ∧ r.steps ≤ cost)
    (js : List α) (pre tail : List Bool) (out : β) (hfour : js.length ≤ 4) :
    ∃ r,runFrom (RepeatMachine.machine p (fun _ _=>true)) (4*(cost+3)+3)
      (RepeatMachine.cfg 0 (source pre.length (pre++word emit js++tail) out) js.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (source (pre.length+(word emit js).length)
        (pre++word emit js++tail) (js.foldl update out)) js.length 1 ∧ r.steps ≤ 4*(cost+3)+3 := by
  obtain ⟨time,ht,tr⟩ := remaining p cost source emit update hstart supplier js pre tail out js.length 0 (by omega)
  have bound : time ≤ 4*(cost+3)+3 := by nlinarith
  obtain ⟨r,hr,rf,rs⟩ := tr.run (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel (RepeatMachine.machine p (fun _ _=>true)) time (4*(cost+3)+3-time) _ r hr
  rw [Nat.add_sub_of_le bound] at more
  exact ⟨r,more,rf,rs.le.trans bound⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek.RepeatList
