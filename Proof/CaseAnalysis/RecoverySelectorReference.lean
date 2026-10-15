import Proof.CaseAnalysis.RecoverySelectorReset

/-! The guarded AND is the node after the unary condition's output. Execute
both counter increments and save that exact AND address on the outer stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReference
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def incrementSlots : Fin 2→Fin 3:=![0,2]
noncomputable def increment:=RecoveryFocus.machine incrementSlots RepairSource.RecoveryTseitinRawIncrement.machine
noncomputable def machine:=Composition.machine
  (Composition.machine increment PCPUnaryStackPush.machine) increment
def heads (stack : List Bool) : Fin 3→ℕ:=![0,stack.length,0]
def data (acc C : ℕ) (stack : List Bool) : Fin 3→List Bool:=
  ![List.replicate acc true,stack,List.replicate C false]
def pushed (acc : ℕ) (stack : List Bool):=stack++(frame (List.replicate (acc+1) true)).reverse
noncomputable def entry (acc C : ℕ) (stack : List Bool) :=
  (⟨machine.start,heads stack,data acc C stack⟩ : Configuration 3 _)

theorem increment_run (acc C : ℕ) (stack : List Bool) (hC : acc+1 ≤ C) :
    ∃ r,runFrom increment (2*acc+4) ⟨increment.start,heads stack,data acc C stack⟩=some r ∧
      r.final.heads=heads stack ∧ r.final.tapes=data (acc+1) C stack ∧ r.steps=2*acc+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=
    (RepairSource.RecoveryTseitinRawIncrement.increment_ready acc C hC).focus_at incrementSlots
      (by decide) (heads stack) (data acc C stack)
      (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have he : install incrementSlots (data acc C stack)
      ![List.replicate (acc+1) true,List.replicate C false]=data (acc+1) C stack := by
    apply HierarchyWidth.install_eq incrementSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      · exact False.elim (hi 0 rfl)
      · rfl
      · rfl
  rw [he] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem reference_run (acc C : ℕ) (stack : List Bool) (hC : 2*(acc+1)+2 ≤ C) :
    ∃ r,runFrom machine (8*acc+22) (entry acc C stack)=some r ∧
      r.final.heads=heads (pushed acc stack) ∧
      r.final.tapes=data (acc+2) C (pushed acc stack) ∧ r.steps ≤ 8*acc+22 := by
  obtain ⟨a,ha,ah,atapes,as⟩:=increment_run acc C stack (by omega)
  obtain ⟨b,hb,bt,bh,bs⟩:=RecoveryBoundedNativeReference.push_run (acc+1) C stack hC
  have hb' : runFrom PCPUnaryStackPush.machine (4*(acc+1)+6)
      (restart a.final PCPUnaryStackPush.machine.start)=some b := by
    change runFrom _ _ ⟨PCPUnaryStackPush.machine.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact hb
  have hab:=Composition.run_join increment PCPUnaryStackPush.machine _ _ _ a b ha hb'
  have bh' : b.final.heads=heads (pushed acc stack) := by
    rw [bh]
    funext i
    fin_cases i
    · rfl
    · simp only [heads,pushed,List.length_append,List.length_reverse,frame_length,List.length_replicate,
        Nat.add_assoc]
    · rfl
  have bt' : b.final.tapes=data (acc+1) C (pushed acc stack) := bt
  obtain ⟨c,hc,ch,ct,cs⟩:=increment_run (acc+1) C (pushed acc stack) (by omega)
  have hc' : runFrom increment (2*(acc+1)+4)
      (restart (joinedReceipt a b).final increment.start)=some c := by
    change runFrom _ _ ⟨increment.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh',bt']
    exact hc
  have full:=Composition.run_join (Composition.machine increment PCPUnaryStackPush.machine)
    increment _ _ _ (joinedReceipt a b) c hab hc'
  have he : 2*acc+4+1+(4*(acc+1)+6)+1+(2*(acc+1)+4)=8*acc+22 := by omega
  rw [he] at full
  refine ⟨joinedReceipt (joinedReceipt a b) c,full,ch,ct,?_⟩
  change a.steps+1+b.steps+1+c.steps ≤ _
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorReference
