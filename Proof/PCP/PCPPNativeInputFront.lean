import Proof.PCP.PCPPNativeSumBinaryLayout

/-! Print the first projected input node and the tag of its second node.
The projected index and current emitted-node position remain physical raw
counters; native fields are computed and appended with cleared workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeInput
open LocalBitMultitape RepairRepresentation PCPPNativeSumBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstBits : List Bool := natWord 1
def betweenBits (negative : Bool) : List Bool := natWord 0++natWord (if negative then 2 else 1)
noncomputable def first := TapeEmbedding.machine 1 (PCPPNativeLiteralAppend.machine firstBits)
noncomputable def valueMachine := TapeEmbedding.machine 1 PCPPNativeSumReusable.machine
noncomputable def between (negative : Bool) :=
  TapeEmbedding.machine 1 (PCPPNativeLiteralAppend.machine (betweenBits negative))
noncomputable def front (negative : Bool) := Composition.machine (Composition.machine first valueMachine) (between negative)
noncomputable def frontEntry (negative : Bool) (index position C : ℕ) (out : List Bool) :=
  (⟨(front negative).start,heads out,data 0 index position C out⟩ : Configuration 25 _)
def frontEmitted (negative : Bool) (index : ℕ) := firstBits++natWord index++betweenBits negative
def frontBudget (negative : Bool) (index C : ℕ) := firstBits.length+1+
  PCPPNativeSumReusable.budget 0 index C+1+(betweenBits negative).length

theorem front_run (negative : Bool) (index position C : ℕ) (out : List Bool)
    (hC : PCPPNativeSumAppend.budget 0 index+1 ≤ C) :
    ∃ r,runFrom (front negative) (frontBudget negative index C)
      (frontEntry negative index position C out)=some r ∧
      r.steps ≤ frontBudget negative index C ∧
      r.final.heads=heads (out++frontEmitted negative index) ∧
      r.final.tapes=data 0 index position C (out++frontEmitted negative index) := by
  obtain ⟨a,ha,as,ah,atapes⟩ := PCPPNativeLiteralAppend.append_run firstBits 0 index C out
  let extraHeads : Fin 1 → ℕ := fun _ => 0
  let extraData : Fin 1 → List Bool := fun _ => List.replicate position true
  let ar := TapeEmbedding.receipt extraHeads extraData a
  have har := TapeEmbedding.run_embed (PCPPNativeLiteralAppend.machine firstBits) extraHeads extraData _ _ a ha
  obtain ⟨b,hb,bs,bh,bt⟩ := PCPPNativeSumReusable.append_run 0 index C (out++firstBits) hC
  simp only [Nat.zero_add] at bh bt
  let br := TapeEmbedding.receipt extraHeads extraData b
  have hbr := TapeEmbedding.run_embed PCPPNativeSumReusable.machine extraHeads extraData _ _ b hb
  have hmid : Composition.restart ar.final valueMachine.start=
      TapeEmbedding.config extraHeads extraData (PCPPNativeSumReusable.entry 0 index C (out++firstBits)) := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) a.final.heads extraHeads=
        Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) (PCPPNativeSumReusable.heads _) extraHeads
      rw [ah]; rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) a.final.tapes extraData=
        Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) (PCPPNativeSumReusable.data 0 index C _) extraData
      rw [atapes]; rfl
  rw [←hmid] at hbr
  have hab := Composition.run_join first valueMachine _ _ _ ar br har hbr
  obtain ⟨c,hc,cs,ch,ct⟩ := PCPPNativeLiteralAppend.append_run (betweenBits negative) 0 index C
    ((out++firstBits)++natWord index)
  let cr := TapeEmbedding.receipt extraHeads extraData c
  have hcr := TapeEmbedding.run_embed (PCPPNativeLiteralAppend.machine (betweenBits negative))
    extraHeads extraData _ _ c hc
  have hlast : Composition.restart (Composition.joinedReceipt ar br).final (between negative).start=
      TapeEmbedding.config extraHeads extraData (PCPPNativeLiteralAppend.entry (betweenBits negative) 0 index C
        ((out++firstBits)++natWord index)) := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) b.final.heads extraHeads=
        Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) (PCPPNativeAddressReusable.heads _) extraHeads
      rw [bh]; rfl
    · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) b.final.tapes extraData=
        Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) (PCPPNativeAddressReusable.data 0 index C _) extraData
      rw [bt]; rfl
  rw [←hlast] at hcr
  let result := Composition.joinedReceipt (Composition.joinedReceipt ar br) cr
  have hr := Composition.run_join (Composition.machine first valueMachine) (between negative) _ _ _
    (Composition.joinedReceipt ar br) cr hab hcr
  refine ⟨result,hr,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold frontBudget
    omega
  · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => ℕ) c.final.heads extraHeads=heads _
    rw [ch]
    simp only [heads,frontEmitted,List.append_assoc]
    rfl
  · change Fin.addCases (m := 24) (n := 1) (motive := fun _ : Fin 25 => List Bool) c.final.tapes extraData=data _ _ _ _ _
    rw [ct]
    simp only [data,frontEmitted,List.append_assoc]
    rfl

end NearCubicWires.RepairOrdinary.PCPPNativeInput
