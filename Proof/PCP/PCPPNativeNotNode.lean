import Proof.PCP.PCPPNativeLiteralAppend
import Proof.PCP.PCPPRequestNodeSchema

/-! Emit both actual nodes for an original NOT gate: a false placeholder
and the NOT of its physically generated shifted shared-DAG address. The
same bounded scratch and live output layout are restored for the caller. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNotNode
open LocalBitMultitape RepairRepresentation PCPPNativeAddressReusable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstBits : List Bool := PCPPRequestNodeSchema.native (.const false : BooleanNode 0)++natWord 2
def lastBits : List Bool := natWord 0
noncomputable def first := PCPPNativeLiteralAppend.machine firstBits
noncomputable def middle := PCPPNativeAddressReusable.machine
noncomputable def last := PCPPNativeLiteralAppend.machine lastBits
noncomputable def machine := Composition.machine (Composition.machine first middle) last
noncomputable def entry (base index C : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data base index C out⟩ : Configuration 24 _)
def emitted (base index : ℕ) := firstBits++natWord (PCPPSubstitution.address base index)++lastBits
def budget (base index C : ℕ) := firstBits.length+1+PCPPNativeAddressReusable.budget base index C+1+lastBits.length

theorem emitted_nodes (r base index : ℕ) :
    emitted base index=PCPPRequestNodeSchema.native (.const false : BooleanNode r)++
      PCPPRequestNodeSchema.native (.not (PCPPSubstitution.address base index) : BooleanNode r) := by
  simp only [emitted,firstBits,lastBits,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]
  rfl

theorem node_run (base index C : ℕ) (out : List Bool)
    (hC : PCPPNativeAddressAppend.budget base index+1 ≤ C) :
    ∃ r,runFrom machine (budget base index C) (entry base index C out)=some r ∧
      r.steps ≤ budget base index C ∧
      r.final.heads=heads (out++emitted base index) ∧
      r.final.tapes=data base index C (out++emitted base index) := by
  obtain ⟨a,ha,as,ah,atapes⟩ := PCPPNativeLiteralAppend.append_run firstBits base index C out
  obtain ⟨b,hb,bs,bh,bt⟩ := PCPPNativeAddressReusable.append_run base index C (out++firstBits) hC
  have hmid : Composition.restart a.final middle.start=PCPPNativeAddressReusable.entry base index C (out++firstBits) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←hmid] at hb
  have hab := Composition.run_join first middle _ _ _ a b ha hb
  obtain ⟨c,hc,cs,ch,ct⟩ := PCPPNativeLiteralAppend.append_run lastBits base index C
    ((out++firstBits)++natWord (PCPPSubstitution.address base index))
  have hlast : Composition.restart (Composition.joinedReceipt a b).final last.start=
      PCPPNativeLiteralAppend.entry lastBits base index C
        ((out++firstBits)++natWord (PCPPSubstitution.address base index)) := by
    apply configuration_ext
    · rfl
    · exact bh
    · exact bt
  rw [←hlast] at hc
  let result := Composition.joinedReceipt (Composition.joinedReceipt a b) c
  have hr := Composition.run_join (Composition.machine first middle) last _ _ _
    (Composition.joinedReceipt a b) c hab hc
  refine ⟨result,hr,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold budget
    omega
  · change c.final.heads=_
    simpa only [emitted,List.append_assoc] using ch
  · change c.final.tapes=_
    simpa only [emitted,List.append_assoc] using ct

end NearCubicWires.RepairOrdinary.PCPPNativeNotNode
