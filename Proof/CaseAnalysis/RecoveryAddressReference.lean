import Proof.CaseAnalysis.RecoveryAddressSchedule

/-! Save the actual plain child output, then advance the graph counter once.
This is the reference handoff needed by the original address-selection OR. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape RepairRepresentation Composition
open RecoveryBoundedSelectorReference
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pushed (acc : ℕ) (stack : List Bool):=stack++(frame (List.replicate acc true)).reverse
noncomputable def reference:=Composition.machine PCPUnaryStackPush.machine increment

theorem reference_run (acc C : ℕ) (stack : List Bool) (hC : 2*acc+2 ≤ C) :
    ∃ r,runFrom reference (6*acc+11)
      ⟨reference.start,heads stack,data acc C stack⟩=some r ∧
      r.final.heads=heads (pushed acc stack) ∧
      r.final.tapes=data (acc+1) C (pushed acc stack) ∧ r.steps ≤ 6*acc+11 := by
  obtain ⟨a,ha,atapes,ah,as⟩:=RecoveryBoundedNativeReference.push_run acc C stack hC
  have ah' : a.final.heads=heads (pushed acc stack) := by
    rw [ah]
    funext i
    fin_cases i
    · rfl
    · simp only [heads,pushed,List.length_append,List.length_reverse,frame_length,List.length_replicate,
        Nat.add_assoc]
    · rfl
  have at' : a.final.tapes=data acc C (pushed acc stack) := atapes
  obtain ⟨b,hb,bh,bt,bs⟩:=increment_run acc C (pushed acc stack) (by omega)
  have hb' : runFrom increment (2*acc+4) (restart a.final increment.start)=some b := by
    change runFrom _ _ ⟨increment.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah',at']
    exact hb
  have full:=Composition.run_join PCPUnaryStackPush.machine increment _ _ _ a b ha hb'
  have he : 4*acc+6+1+(2*acc+4)=6*acc+11 := by omega
  rw [he] at full
  refine ⟨joinedReceipt a b,full,bh,bt,?_⟩
  change a.steps+1+b.steps ≤ _
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
