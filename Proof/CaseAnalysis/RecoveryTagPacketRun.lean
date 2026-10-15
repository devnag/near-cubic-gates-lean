import Proof.CaseAnalysis.RecoveryTagPacketCalls

/-! Execute the fixed five-field original tag packet. The existing counter
supplies input, NOT, AND and OR references and finishes at the next graph count. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacket
open LocalBitMultitape RepairRepresentation Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pair:=Composition.machine next next
noncomputable def four:=Composition.machine pair pair
noncomputable def machine:=Composition.machine (reference true) four
def pairWord (current : ℕ):=frame (List.replicate current true)++frame (List.replicate (current+1) true)
def fourWord (current : ℕ):=pairWord current++pairWord (current+2)
def word (constant current : ℕ):=frame (List.replicate constant true)++fourWord current
def pairBudget (current C : ℕ):=24*current+4*C+59
def fourBudget (current C : ℕ):=48*current+8*C+167
def budget (constant current C : ℕ):=10*constant+48*current+10*C+186

theorem pair_run (current constant C : ℕ) (out : List Bool) (hC : 2*(current+1)+1 ≤ C) :
    ∃ r,runFrom pair (pairBudget current C) ⟨pair.start,heads out,data current constant C out⟩=some r ∧
      r.steps ≤ pairBudget current C ∧ r.final.heads=heads (out++pairWord current) ∧
      r.final.tapes=data (current+2) constant C (out++pairWord current) := by
  obtain ⟨a,ar,asteps,ah,atapes⟩:=next_run current constant C out (by omega)
  obtain ⟨b,br,bsteps,bh,bt⟩:=next_run (current+1) constant C (out++frame (List.replicate current true)) hC
  have br' : runFrom next (nextBudget (current+1) C) (restart a.final next.start)=some b := by
    change runFrom next _ ⟨next.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have full:=Composition.run_join next next _ _ _ a b ar br'
  have he : nextBudget current C+1+nextBudget (current+1) C=pairBudget current C := by unfold nextBudget pairBudget;omega
  rw [he] at full
  refine ⟨joinedReceipt a b,full,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ pairBudget current C
    unfold nextBudget at asteps bsteps
    unfold pairBudget
    omega
  · change b.final.heads=heads (out++pairWord current)
    simpa only [pairWord,List.append_assoc] using bh
  · change b.final.tapes=data (current+2) constant C (out++pairWord current)
    simpa only [pairWord,List.append_assoc] using bt

theorem four_run (current constant C : ℕ) (out : List Bool) (hC : 2*(current+3)+1 ≤ C) :
    ∃ r,runFrom four (fourBudget current C) ⟨four.start,heads out,data current constant C out⟩=some r ∧
      r.steps ≤ fourBudget current C ∧ r.final.heads=heads (out++fourWord current) ∧
      r.final.tapes=data (current+4) constant C (out++fourWord current) := by
  obtain ⟨a,ar,asteps,ah,atapes⟩:=pair_run current constant C out (by omega)
  obtain ⟨b,br,bsteps,bh,bt⟩:=pair_run (current+2) constant C (out++pairWord current) hC
  have br' : runFrom pair (pairBudget (current+2) C) (restart a.final pair.start)=some b := by
    change runFrom pair _ ⟨pair.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have full:=Composition.run_join pair pair _ _ _ a b ar br'
  have he : pairBudget current C+1+pairBudget (current+2) C=fourBudget current C := by unfold pairBudget fourBudget;omega
  rw [he] at full
  refine ⟨joinedReceipt a b,full,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ fourBudget current C
    unfold pairBudget at asteps bsteps
    unfold fourBudget
    omega
  · change b.final.heads=heads (out++fourWord current)
    simpa only [fourWord,List.append_assoc] using bh
  · change b.final.tapes=data (current+4) constant C (out++fourWord current)
    simpa only [fourWord,List.append_assoc] using bt

theorem packet_run (constant current C : ℕ) (out : List Bool)
    (hk : 2*constant+1 ≤ C) (hi : 2*(current+3)+1 ≤ C) :
    ∃ r,runFrom machine (budget constant current C) ⟨machine.start,heads out,data current constant C out⟩=some r ∧
      r.steps ≤ budget constant current C ∧ r.final.heads=heads (out++word constant current) ∧
      r.final.tapes=data (current+4) constant C (out++word constant current) := by
  obtain ⟨a,ar,asteps,ah,atapes⟩:=reference_run true current constant C out hk
  obtain ⟨b,br,bsteps,bh,bt⟩:=four_run current constant C (out++frame (List.replicate constant true)) hi
  have br' : runFrom four (fourBudget current C) (restart a.final four.start)=some b := by
    change runFrom four _ ⟨four.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have full:=Composition.run_join (reference true) four _ _ _ a b ar br'
  have he : RecoveryBoundedTagReferenceAppend.budget (selectedValue true current constant) C+1+fourBudget current C=budget constant current C := by
    change (10*constant+2*C+18)+1+(48*current+8*C+167)=10*constant+48*current+10*C+186
    omega
  rw [he] at full
  refine ⟨joinedReceipt a b,full,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ budget constant current C
    change a.steps ≤ 10*constant+2*C+18 at asteps
    unfold fourBudget at bsteps
    unfold budget
    omega
  · change b.final.heads=heads (out++word constant current)
    simpa only [word,List.append_assoc] using bh
  · change b.final.tapes=data (current+4) constant C (out++word constant current)
    simpa only [word,List.append_assoc] using bt

theorem word_original (constant current : ℕ) :
    word constant current=RecoveryBoundedSelectorLoop.sourceWord [constant,current,current+1,current+2,current+3] := by
  simp only [word,fourWord,pairWord,RecoveryBoundedSelectorLoop.sourceWord,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc]

theorem word_length (constant current : ℕ) : (word constant current).length=2*constant+8*current+17 := by
  simp only [word,fourWord,pairWord,List.length_append,frame_length,List.length_replicate]
  omega

theorem budget_quadratic (constant current W : ℕ) (hk : constant ≤ W) (hi : current ≤ W) :
    budget constant current (RecoveryBoundedSelectorLoop.capacity W) ≤ 1048576*(W+1)^2 := by
  unfold budget RecoveryBoundedSelectorLoop.capacity
  nlinarith [Nat.zero_le (W^2)]

theorem budget_log (constant current W D : ℕ) (hk : constant ≤ W) (hi : current ≤ W)
    (hD : 8388608*(W+1)^3 ≤ D) :
    budget constant current (RecoveryBoundedSelectorLoop.capacity W) ≤ D := by
  have h:=budget_quadratic constant current W hk hi
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagPacket
