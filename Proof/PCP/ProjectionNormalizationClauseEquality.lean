import Proof.PCP.ProjectionNormalizationFieldEquality

/-! Three sequential field comparisons for one source clause. All stream
movement is paid, and the equality flag is accumulated on its actual tape. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.ClauseEquality
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev size := Fintype.card FieldEquality.State
noncomputable def tailMachine := Composition.machine FieldEquality.machine FieldEquality.machine
noncomputable def machine := Composition.machine FieldEquality.machine tailMachine
noncomputable def finalCode : Fin (size+(size+size)) :=
  (FieldEquality.finalCode.natAdd size).natAdd size

def cfg {s : ℕ} (q : Fin s) (left right : List Bool) (lp rp : ℕ) (flag : Bool) : Configuration 3 s :=
  ⟨q,![lp,rp,0],![left,right,[flag]]⟩
def stream (a : Fin 3 → List Bool) := frame (a 0)++frame (a 1)++frame (a 2)
def budget (left right : Fin 3 → List Bool) :=
  2*max (left 0).length (right 0).length+1+1+
  (2*max (left 1).length (right 1).length+1+1+
  (2*max (left 2).length (right 2).length+1))

theorem clause_run (left right : Fin 3 → List Bool) (pl pr tl tr : List Bool) (old : Bool) :
    ∃ r, runFrom machine (budget left right)
      (cfg machine.start (pl++stream left++tl) (pr++stream right++tr) pl.length pr.length old)=some r ∧
      r.final=cfg finalCode (pl++stream left++tl) (pr++stream right++tr)
        (pl.length+(stream left).length) (pr.length+(stream right).length)
        (old && decide (left=right)) ∧ r.steps=budget left right := by
  classical
  let ls := pl++stream left++tl
  let rs := pr++stream right++tr
  let lp₁ := pl++frame (left 0)
  let rp₁ := pr++frame (right 0)
  let lp₂ := lp₁++frame (left 1)
  let rp₂ := rp₁++frame (right 1)
  let f₁ := old && decide (left 0=right 0)
  let f₂ := f₁ && decide (left 1=right 1)
  obtain ⟨a,ha,haf,hat⟩ := FieldEquality.equality_run (left 0) (right 0) pl pr
    (frame (left 1)++frame (left 2)++tl) (frame (right 1)++frame (right 2)++tr) old
  obtain ⟨b,hb,hbf,hbt⟩ := FieldEquality.equality_run (left 1) (right 1) lp₁ rp₁
    (frame (left 2)++tl) (frame (right 2)++tr) f₁
  obtain ⟨c,hc,hcf,hct⟩ := FieldEquality.equality_run (left 2) (right 2) lp₂ rp₂ tl tr f₂
  have ha' : runFrom FieldEquality.machine (2*max (left 0).length (right 0).length+1)
      (FieldEquality.cfg FieldEquality.machine.start ls rs pl.length pr.length old)=some a := by
    simpa only [ls,rs,stream,List.append_assoc] using ha
  have haf' : a.final=FieldEquality.cfg FieldEquality.finalCode ls rs lp₁.length rp₁.length f₁ := by
    simpa [ls,rs,stream,lp₁,rp₁,f₁,List.append_assoc,frame_length,Nat.add_assoc] using haf
  have hb' : runFrom FieldEquality.machine (2*max (left 1).length (right 1).length+1)
      (Composition.restart a.final FieldEquality.machine.start)=some b := by
    rw [haf']
    simpa only [Composition.restart,ls,rs,stream,lp₁,rp₁,FieldEquality.cfg,List.append_assoc] using hb
  have hbf' : b.final=FieldEquality.cfg FieldEquality.finalCode ls rs lp₂.length rp₂.length f₂ := by
    simpa [ls,rs,stream,lp₁,rp₁,lp₂,rp₂,f₂,List.append_assoc,frame_length,Nat.add_assoc] using hbf
  have hc' : runFrom FieldEquality.machine (2*max (left 2).length (right 2).length+1)
      (Composition.restart b.final FieldEquality.machine.start)=some c := by
    rw [hbf']
    simpa only [Composition.restart,ls,rs,stream,lp₁,rp₁,lp₂,rp₂,FieldEquality.cfg,List.append_assoc] using hc
  have hbc := Composition.run_join FieldEquality.machine FieldEquality.machine _ _ _ b c hb' hc'
  have hentry : Composition.leftConfig size (Composition.restart a.final FieldEquality.machine.start)=
      Composition.restart a.final tailMachine.start := rfl
  rw [hentry] at hbc
  have hall := Composition.run_join FieldEquality.machine tailMachine _ _ _ a
    (Composition.joinedReceipt b c) ha' hbc
  have heq : (f₂ && decide (left 2=right 2))=(old && decide (left=right)) := by
    have hi : left=right ↔ left 0=right 0 ∧ left 1=right 1 ∧ left 2=right 2 := by
      constructor
      · intro h; subst right; exact ⟨rfl,rfl,rfl⟩
      · rintro ⟨h0,h1,h2⟩; funext i; fin_cases i <;> assumption
    simp [hi,f₂,f₁,Bool.and_assoc]
  refine ⟨Composition.joinedReceipt a (Composition.joinedReceipt b c),hall,?_,?_⟩
  · change Composition.rightConfig size (Composition.rightConfig size c.final)=_
    rw [hcf]
    change cfg finalCode _ _ _ _ (f₂ && decide (left 2=right 2))=_
    rw [heq]
    simp only [stream,lp₁,rp₁,lp₂,rp₂,List.append_assoc]
    congr 1 <;> simp [frame_length] <;> omega
  · change a.steps+1+(b.steps+1+c.steps)=_
    rw [hat,hbt,hct]
    rfl

end NearCubicWires.RepairSource.ProjectionNormalization.ClauseEquality
