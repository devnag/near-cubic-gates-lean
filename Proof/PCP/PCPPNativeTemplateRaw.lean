import Proof.PCP.PCPPNativeNodeRead
import Proof.MachineModel.OrdinaryMatrixTemplateEntries

/-! Convert the actual head-one sentinel supplied by native/projection
readers into raw unary counters. Both cursor shifts and the existing copy
and reset are executed; the source sentinel returns to head one. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeTemplateRaw
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shift (direction : HeadMove) : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=0 then direction else .stay⟩ else none
def moved (direction : HeadMove) (heads : Fin 5 → ℕ) (i : Fin 5) :=
  if i=0 then direction.apply (heads i) else heads i

theorem shift_run (direction : HeadMove) (heads : Fin 5 → ℕ) (data : Fin 5 → List Bool) :
    ∃ r,runFrom (shift direction) 1 (⟨0,heads,data⟩ : Configuration 5 2)=some r ∧
      r.final=⟨1,moved direction heads,data⟩ ∧ r.steps=1 := by
  have hs : step (shift direction) (⟨0,heads,data⟩ : Configuration 5 2)=some ⟨1,moved direction heads,data⟩ := by
    simp only [step,shift,Fin.val_zero,ite_true,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=0 <;> simp only [applyAction,moved,hi,ite_true,ite_false,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def machine := Composition.machine
  (Composition.machine (shift .left) MatrixTemplateCopy.resetMachine) (shift .right)
def heads (i : Fin 5) : ℕ := if i=0 then 1 else 0
noncomputable def entry (n : ℕ) :=
  (⟨machine.start,heads,MatrixTemplateCopy.resetInput n⟩ : Configuration 5 _)

theorem template_run (n : ℕ) :
    ∃ r,runFrom machine (4*n+16) (entry n)=some r ∧ r.steps=4*n+16 ∧
      r.final.tapes 0=UnaryTemplate.tape n ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧ r.final.heads=heads := by
  obtain ⟨a,ha,af,as⟩ := shift_run .left heads (MatrixTemplateCopy.resetInput n)
  obtain ⟨b,hb,b0,b1,b2,b3,bh,bs⟩ := MatrixTemplateCopy.reset_run n
  have hmid : Composition.restart a.final MatrixTemplateCopy.resetMachine.start=
      initialConfiguration MatrixTemplateCopy.resetMachine (MatrixTemplateCopy.resetInput n) := by
    rw [af]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  change runFrom MatrixTemplateCopy.resetMachine _ _=some b at hb
  rw [←hmid] at hb
  have hab := Composition.run_join (shift .left) MatrixTemplateCopy.resetMachine _ _ _ a b ha hb
  obtain ⟨c,hc,cf,cs⟩ := shift_run .right b.final.heads b.final.tapes
  have hlast : Composition.restart (Composition.joinedReceipt a b).final (shift .right).start=
      (⟨0,b.final.heads,b.final.tapes⟩ : Configuration 5 2) := rfl
  rw [←hlast] at hc
  let result := Composition.joinedReceipt (Composition.joinedReceipt a b) c
  have hr := Composition.run_join (Composition.machine (shift .left) MatrixTemplateCopy.resetMachine)
    (shift .right) _ _ _ (Composition.joinedReceipt a b) c hab hc
  have ht : 1+1+(4*n+12)+1+1=4*n+16 := by omega
  rw [ht] at hr
  refine ⟨result,hr,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps=_
    omega
  · change c.final.tapes 0=_
    rw [cf]; exact b0
  · change c.final.tapes 1=_
    rw [cf]; exact b1
  · change c.final.tapes 2=_
    rw [cf]; exact b2
  · change c.final.tapes 3=_
    rw [cf]; exact b3
  · change c.final.heads=_
    rw [cf]
    funext i
    simp only [moved,bh,heads,HeadMove.apply]

end NearCubicWires.RepairOrdinary.PCPPNativeTemplateRaw
