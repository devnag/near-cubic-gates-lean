import Proof.PCP.PCPPNativeBinaryLayout

/-! Execute the two-node substitution for an original AND or OR node.
Both shifted child addresses use one reusable physical workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeBinary
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstBits (isOr : Bool) : List Bool :=
  PCPPRequestNodeSchema.native (.const false : BooleanNode 0)++natWord (if isOr then 4 else 3)
noncomputable def first (isOr : Bool) := TapeEmbedding.machine 1 (PCPPNativeLiteralAppend.machine (firstBits isOr))
noncomputable def middle := TapeEmbedding.machine 1 PCPPNativeAddressReusable.machine
noncomputable def machine (isOr : Bool) := Composition.machine (Composition.machine (first isOr) middle) rightMachine
noncomputable def entry (isOr : Bool) (base left right C : ℕ) (out : List Bool) :=
  (⟨(machine isOr).start,heads out,data base left right C out⟩ : Configuration 25 _)
def emitted (isOr : Bool) (base left right : ℕ) := firstBits isOr++
  natWord (PCPPSubstitution.address base left)++natWord (PCPPSubstitution.address base right)
def budget (isOr : Bool) (base left right C : ℕ) := (firstBits isOr).length+1+
  PCPPNativeAddressReusable.budget base left C+1+PCPPNativeAddressReusable.budget base right C

theorem emitted_nodes (r : ℕ) (isOr : Bool) (base left right : ℕ) :
    emitted isOr base left right=PCPPRequestNodeSchema.native (.const false : BooleanNode r)++
      PCPPRequestNodeSchema.native (if isOr then
        (.or (PCPPSubstitution.address base left) (PCPPSubstitution.address base right) : BooleanNode r)
        else .and (PCPPSubstitution.address base left) (PCPPSubstitution.address base right)) := by
  cases isOr <;> simp only [emitted,firstBits,Bool.false_eq_true,ite_false,ite_true,
    PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc] <;> rfl

theorem node_run (isOr : Bool) (base left right C : ℕ) (out : List Bool)
    (hleft : PCPPNativeAddressAppend.budget base left+1 ≤ C)
    (hright : PCPPNativeAddressAppend.budget base right+1 ≤ C) :
    ∃ r,runFrom (machine isOr) (budget isOr base left right C)
      (entry isOr base left right C out)=some r ∧
      r.steps ≤ budget isOr base left right C ∧
      r.final.heads=heads (out++emitted isOr base left right) ∧
      r.final.tapes=data base left right C (out++emitted isOr base left right) := by
  obtain ⟨a,ha,as,ah,atapes⟩ := PCPPNativeLiteralAppend.append_run (firstBits isOr) base left C out
  let extraHeads : Fin 1 → ℕ := fun _ => 0
  let extraData : Fin 1 → List Bool := fun _ => List.replicate right true
  let ar := TapeEmbedding.receipt extraHeads extraData a
  have har := TapeEmbedding.run_embed (PCPPNativeLiteralAppend.machine (firstBits isOr))
    extraHeads extraData _ _ a ha
  obtain ⟨b,hb,bs,bh,bt⟩ := PCPPNativeAddressReusable.append_run base left C (out++firstBits isOr) hleft
  let br := TapeEmbedding.receipt extraHeads extraData b
  have hbr := TapeEmbedding.run_embed PCPPNativeAddressReusable.machine extraHeads extraData _ _ b hb
  have hmid : Composition.restart ar.final middle.start= 
      TapeEmbedding.config extraHeads extraData (PCPPNativeAddressReusable.entry base left C (out++firstBits isOr)) := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) a.final.heads extraHeads=Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) (PCPPNativeAddressReusable.heads _) extraHeads
      rw [ah]
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) a.final.tapes extraData=Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) (PCPPNativeAddressReusable.data base left C _) extraData
      rw [atapes]
  rw [←hmid] at hbr
  have hab := Composition.run_join (first isOr) middle _ _ _ ar br har hbr
  obtain ⟨c,hc,cs,ch,ct⟩ := right_run base left right C
    ((out++firstBits isOr)++natWord (PCPPSubstitution.address base left)) hright
  have hlast : Composition.restart (Composition.joinedReceipt ar br).final rightMachine.start=
      rightEntry base left right C ((out++firstBits isOr)++natWord (PCPPSubstitution.address base left)) := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) b.final.heads extraHeads=heads _
      rw [bh]; rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) b.final.tapes extraData=data _ _ _ _ _
      rw [bt]; rfl
  rw [←hlast] at hc
  let result := Composition.joinedReceipt (Composition.joinedReceipt ar br) c
  have hr := Composition.run_join (Composition.machine (first isOr) middle) rightMachine _ _ _
    (Composition.joinedReceipt ar br) c hab hc
  refine ⟨result,hr,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold budget
    omega
  · change c.final.heads=_
    simpa only [emitted,List.append_assoc] using ch
  · change c.final.tapes=_
    simpa only [emitted,List.append_assoc] using ct

end NearCubicWires.RepairOrdinary.PCPPNativeBinary
