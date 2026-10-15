import Proof.PCP.PCPPNativeInputFront

/-! Emit the complete two-node projection substitution. A negative
projection negates the actual first-node position, while a positive one
reuses the projected input index. Both counters and scratch are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeInput
open LocalBitMultitape RepairRepresentation PCPPNativeSumBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def targetMachine (negative : Bool) := if negative then rightMachine else valueMachine
def target (negative : Bool) (index position : ℕ) := if negative then position else index
def targetBudget (negative : Bool) (index position C : ℕ) := PCPPNativeSumReusable.budget 0 (target negative index position) C
noncomputable def targetEntry (negative : Bool) (index position C : ℕ) (out : List Bool) :=
  (⟨(targetMachine negative).start,heads out,data 0 index position C out⟩ : Configuration 25 _)

theorem target_run (negative : Bool) (index position C : ℕ) (out : List Bool)
    (hindex : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hposition : PCPPNativeSumAppend.budget 0 position+1 ≤ C) :
    ∃ r,runFrom (targetMachine negative) (targetBudget negative index position C)
      (targetEntry negative index position C out)=some r ∧
      r.steps ≤ targetBudget negative index position C ∧
      r.final.heads=heads (out++natWord (target negative index position)) ∧
      r.final.tapes=data 0 index position C (out++natWord (target negative index position)) := by
  cases negative
  · obtain ⟨raw,hr,rs,rh,rt⟩ := PCPPNativeSumReusable.append_run 0 index C out hindex
    simp only [Nat.zero_add] at rh rt
    let eh : Fin 1 → ℕ := fun _ => 0
    let et : Fin 1 → List Bool := fun _ => List.replicate position true
    have hrun := TapeEmbedding.run_embed PCPPNativeSumReusable.machine eh et _ _ raw hr
    refine ⟨TapeEmbedding.receipt eh et raw,hrun,rs,?_,?_⟩
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) raw.final.heads eh=heads _
      rw [rh]; rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) raw.final.tapes et=data _ _ _ _ _
      rw [rt]; rfl
  · simpa only [Nat.zero_add,targetMachine,targetBudget,targetEntry,target,rightEntry,ite_true]
      using right_run 0 index position C out hposition

def lastBits : List Bool := natWord 0
noncomputable def last := TapeEmbedding.machine 1 (PCPPNativeLiteralAppend.machine lastBits)
noncomputable def machine (negative : Bool) := Composition.machine
  (Composition.machine (front negative) (targetMachine negative)) last
noncomputable def entry (negative : Bool) (index position C : ℕ) (out : List Bool) :=
  (⟨(machine negative).start,heads out,data 0 index position C out⟩ : Configuration 25 _)
def emitted (negative : Bool) (index position : ℕ) :=
  frontEmitted negative index++natWord (target negative index position)++lastBits
def budget (negative : Bool) (index position C : ℕ) := frontBudget negative index C+1+
  targetBudget negative index position C+1+lastBits.length

theorem emitted_nodes (r : ℕ) (negative : Bool) (index : Fin r) (position : ℕ) :
    emitted negative index.val position=PCPPRequestNodeSchema.native (.input index : BooleanNode r)++
      PCPPRequestNodeSchema.native (if negative then (.not position : BooleanNode r) else .input index) := by
  cases negative <;> simp only [emitted,frontEmitted,firstBits,betweenBits,target,lastBits,
    Bool.false_eq_true,ite_false,ite_true,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,
    List.append_assoc] <;> rfl

theorem node_run (negative : Bool) (index position C : ℕ) (out : List Bool)
    (hindex : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hposition : PCPPNativeSumAppend.budget 0 position+1 ≤ C) :
    ∃ r,runFrom (machine negative) (budget negative index position C)
      (entry negative index position C out)=some r ∧
      r.steps ≤ budget negative index position C ∧
      r.final.heads=heads (out++emitted negative index position) ∧
      r.final.tapes=data 0 index position C (out++emitted negative index position) := by
  obtain ⟨a,ha,as,ah,atapes⟩ := front_run negative index position C out hindex
  obtain ⟨b,hb,bs,bh,bt⟩ := target_run negative index position C
    (out++frontEmitted negative index) hindex hposition
  have hmid : Composition.restart a.final (targetMachine negative).start=
      targetEntry negative index position C (out++frontEmitted negative index) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←hmid] at hb
  have hab := Composition.run_join (front negative) (targetMachine negative) _ _ _ a b ha hb
  obtain ⟨c,hc,cs,ch,ct⟩ := PCPPNativeLiteralAppend.append_run lastBits 0 index C
    ((out++frontEmitted negative index)++natWord (target negative index position))
  let eh : Fin 1 → ℕ := fun _ => 0
  let et : Fin 1 → List Bool := fun _ => List.replicate position true
  let cr := TapeEmbedding.receipt eh et c
  have hcr := TapeEmbedding.run_embed (PCPPNativeLiteralAppend.machine lastBits) eh et _ _ c hc
  have hlast : Composition.restart (Composition.joinedReceipt a b).final last.start=
      TapeEmbedding.config eh et (PCPPNativeLiteralAppend.entry lastBits 0 index C
        ((out++frontEmitted negative index)++natWord (target negative index position))) := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  rw [←hlast] at hcr
  let result := Composition.joinedReceipt (Composition.joinedReceipt a b) cr
  have hr := Composition.run_join (Composition.machine (front negative) (targetMachine negative)) last _ _ _
    (Composition.joinedReceipt a b) cr hab hcr
  refine ⟨result,hr,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold budget
    omega
  · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) c.final.heads eh=heads _
    rw [ch]
    simp only [heads,emitted,List.append_assoc]
    rfl
  · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) c.final.tapes et=data _ _ _ _ _
    rw [ct]
    simp only [data,emitted,List.append_assoc]
    rfl

end NearCubicWires.RepairOrdinary.PCPPNativeInput
