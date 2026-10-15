import Proof.PCP.ProjectionNormalizationSharedDriverRestore

/-! One fixed three-field copy, used for candidate retention and for the
conditional kept-clause stream. No runtime field-count driver is required. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.ClauseCopy
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailMachine := Composition.machine Field.machine Field.machine
def machine := Composition.machine Field.machine tailMachine
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 s :=
  ⟨q,![pos,out.length],![source,out]⟩
def finalCode : Fin 9 := (2 : Fin 3).natAdd 3 |>.natAdd 3

theorem copy_run (pre : List Bool) (fields : SuffixScan.Clause) (tail out : List Bool) :
    ∃ r,runFrom machine ((ClauseEquality.stream fields).length+2)
      (cfg machine.start (pre++ClauseEquality.stream fields++tail) pre.length out)=some r ∧
      r.final=cfg finalCode (pre++ClauseEquality.stream fields++tail)
        (pre.length+(ClauseEquality.stream fields).length) (out++ClauseEquality.stream fields) ∧
      r.steps=(ClauseEquality.stream fields).length+2 := by
  let source := pre++ClauseEquality.stream fields++tail
  let p₁ := pre++frame (fields 0)
  let p₂ := p₁++frame (fields 1)
  let o₁ := out++frame (fields 0)
  let o₂ := o₁++frame (fields 1)
  obtain ⟨a,ha,haf,hat⟩ := Field.copy_run pre (fields 0) (frame (fields 1)++frame (fields 2)++tail) out
  obtain ⟨b,hb,hbf,hbt⟩ := Field.copy_run p₁ (fields 1) (frame (fields 2)++tail) o₁
  obtain ⟨c,hc,hcf,hct⟩ := Field.copy_run p₂ (fields 2) tail o₂
  have hstart : Field.machine.start=0 := rfl
  have ha' : runFrom Field.machine (2*(fields 0).length+1) (Field.cfg 0 source pre.length out)=some a := by
    simpa only [source,ClauseEquality.stream,List.append_assoc] using ha
  have haf' : a.final=Field.cfg 2 source p₁.length o₁ := by
    simpa [source,ClauseEquality.stream,p₁,o₁,List.append_assoc,frame_length,Nat.add_assoc] using haf
  have hb' : runFrom Field.machine (2*(fields 1).length+1) (Composition.restart a.final Field.machine.start)=some b := by
    rw [haf']
    simpa only [Composition.restart,hstart,source,ClauseEquality.stream,p₁,Field.cfg,List.append_assoc] using hb
  have hbf' : b.final=Field.cfg 2 source p₂.length o₂ := by
    simpa [source,ClauseEquality.stream,p₁,p₂,o₂,List.append_assoc,frame_length,Nat.add_assoc] using hbf
  have hc' : runFrom Field.machine (2*(fields 2).length+1) (Composition.restart b.final Field.machine.start)=some c := by
    rw [hbf']
    simpa only [Composition.restart,hstart,source,ClauseEquality.stream,p₁,p₂,Field.cfg,List.append_assoc] using hc
  have hbc := Composition.run_join Field.machine Field.machine _ _ _ b c hb' hc'
  have he : Composition.leftConfig 3 (Composition.restart a.final Field.machine.start)=
      Composition.restart a.final tailMachine.start := rfl
  rw [he] at hbc
  have hall := Composition.run_join Field.machine tailMachine _ _ _ a (Composition.joinedReceipt b c) ha' hbc
  have ht : (2*(fields 0).length+1)+1+((2*(fields 1).length+1)+1+(2*(fields 2).length+1))=
      (ClauseEquality.stream fields).length+2 := by simp [ClauseEquality.stream,frame_length]; omega
  rw [ht] at hall
  refine ⟨Composition.joinedReceipt a (Composition.joinedReceipt b c),hall,?_,?_⟩
  · change Composition.rightConfig 3 (Composition.rightConfig 3 c.final)=_
    rw [hcf]
    change cfg finalCode _ _ _=_
    simp only [p₂,p₁,o₂,o₁,ClauseEquality.stream,List.append_assoc]
    congr 1; simp [frame_length]; omega
  · change a.steps+1+(b.steps+1+c.steps)=_
    rw [hat,hbt,hct]
    exact ht

theorem forward (i : Fin 2) : CursorRestore.NoLeft machine i := by
  have hf : CursorRestore.NoLeft Field.machine i := by
    intro q bits a ha
    simp only [Field.machine] at ha
    split at ha
    · cases ha; simp
    · split at ha
      · cases ha; simp
      · contradiction
  exact CursorRestore.composition_forward Field.machine tailMachine i hf
    (CursorRestore.composition_forward Field.machine Field.machine i hf hf)

end NearCubicWires.RepairSource.ProjectionNormalization.ClauseCopy
