import Proof.Amplification.RecoveryBoundedNativeLiteralStepLayout
import Proof.Amplification.RecoveryBoundedNativeAdvance

/-! A reusable literal-compiler step: exact bytes and saved output reference,
then paid base/index advance and actual address-workspace erasure. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStep
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem padded_data (index position C ref : ℕ) (negative : Bool) (out stack : List Bool) :
    (fun i=>ZeroPadding.pad (padding C i)
      (RecoveryBoundedNativeLiteralStack.data index position C negative out stack ref i))=
      data index position C negative out stack ref := by
  funext i
  by_cases hi : i=30
  · subst i; rfl
  · simp only [padding,data,hi,ite_false,ZeroPadding.pad_zero]

theorem first_run (index position C : ℕ) (negative : Bool) (out stack : List Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hp : PCPPNativeSumAppend.budget 0 position+1 ≤ C)
    (hz : PCPPNativeSumAppend.budget 0 0+1 ≤ C)
    (hsum : position+3 ≤ C) (hpush : 2*(position+negative.toNat)+2 ≤ C) :
    ∃ r, runFrom first (RecoveryBoundedNativeLiteralStack.budget index position C negative)
      ⟨first.start,heads out stack,data index position C negative out stack 0⟩=some r ∧
      r.steps ≤ RecoveryBoundedNativeLiteralStack.budget index position C negative ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) ∧
      r.final.tapes=data index position C negative
        (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) (position+negative.toNat) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=RecoveryBoundedNativeLiteralStack.literal_stack_run
    index position C negative out stack hi hp hz hsum hpush
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config first (padding C) _ _ a ha
  have hin : ZeroPadding.config (padding C)
      (RecoveryBoundedNativeLiteralStack.entry index position C negative out stack)=
      (⟨first.start,heads out stack,data index position C negative out stack 0⟩ : Configuration 34 _) := by
    apply configuration_ext
    · rfl
    · rfl
    · exact padded_data index position C 0 negative out stack
  rw [hin] at hr
  refine ⟨r,hr,rs.le.trans as,?_,?_⟩
  · rw [rf]; exact ah
  · rw [rf]
    change (fun i=>ZeroPadding.pad (padding C i) (a.final.tapes i))=_
    rw [atapes]
    exact padded_data _ _ _ _ _ _ _

theorem advance_run (index position C ref : ℕ) (negative : Bool) (out stack : List Bool)
    (hb : position ≤ ref) (hC : ref+1 ≤ C) :
    ∃ r, runFrom advance (2*ref+4)
      ⟨advance.start,heads out stack,data index position C negative out stack ref⟩=some r ∧
      r.final.heads=heads out stack ∧ r.final.tapes=data index (ref+1) C negative out stack (ref+1) ∧
      r.steps=2*ref+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedNativeAdvance.advance_ready ref position C hb hC).focus_at
    advanceSlots (by decide) (heads out stack) (data index position C negative out stack ref)
    (fun j=>(advance_input index position C ref negative out stack j).2)
    (fun j=>(advance_input index position C ref negative out stack j).1)
  rw [advance_tapes] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem increment_run (index position C ref : ℕ) (negative : Bool) (out stack : List Bool)
    (hC : index+1 ≤ C) :
    ∃ r, runFrom increment (2*index+4)
      ⟨increment.start,heads out stack,data index position C negative out stack ref⟩=some r ∧
      r.final.heads=heads out stack ∧ r.final.tapes=data (index+1) position C negative out stack ref ∧
      r.steps=2*index+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RepairSource.RecoveryTseitinRawIncrement.increment_ready index C hC).focus_at
    incrementSlots (by decide) (heads out stack) (data index position C negative out stack ref)
    (fun j=>(increment_input index position C ref negative out stack j).2)
    (fun j=>(increment_input index position C ref negative out stack j).1)
  rw [increment_tapes] at rt
  exact ⟨r,hr,rh,rt,rs⟩

theorem erase_run (index position C ref : ℕ) (negative : Bool) (out stack : List Bool)
    (hC : ref ≤ C) :
    ∃ r, runFrom erase (2*C+4)
      ⟨erase.start,heads out stack,data index position C negative out stack ref⟩=some r ∧
      r.final.heads=heads out stack ∧ r.final.tapes=data index position C negative out stack 0 ∧
      r.steps=2*C+4 := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedNativeAdvance.erase_ready ref C hC).focus_at
    eraseSlots (by decide) (heads out stack) (data index position C negative out stack ref)
    (fun j=>(erase_input index position C ref negative out stack j).2)
    (fun j=>(erase_input index position C ref negative out stack j).1)
  rw [erase_tapes] at rt
  exact ⟨r,hr,rh,rt,rs⟩

def budget (index position C : ℕ) (negative : Bool) :=
  RecoveryBoundedNativeLiteralStack.budget index position C negative+1+
    (2*(position+negative.toNat)+4)+1+(2*index+4)+1+(2*C+4)

theorem step_run (index position C : ℕ) (negative : Bool) (out stack : List Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hp : PCPPNativeSumAppend.budget 0 position+1 ≤ C)
    (hz : PCPPNativeSumAppend.budget 0 0+1 ≤ C)
    (hsum : position+3 ≤ C) (hpush : 2*(position+negative.toNat)+2 ≤ C)
    (hindex : index+1 ≤ C) :
    ∃ r, runFrom machine (budget index position C negative) (entry index position C negative out stack)=some r ∧
      r.steps ≤ budget index position C negative ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) ∧
      r.final.tapes=data (index+1) (position+negative.toNat+1) C negative
        (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) 0 := by
  obtain ⟨a,ha,as,ah,atapes⟩:=first_run index position C negative out stack hi hp hz hsum hpush
  obtain ⟨b,hb,bh,bt,bs⟩:=advance_run index position C (position+negative.toNat) negative
    (out++RecoveryBoundedNativeLiteral.emitted index position negative)
    (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) (by omega) (by omega)
  have hb' : runFrom advance (2*(position+negative.toNat)+4) (restart a.final advance.start)=some b := by
    change runFrom advance _ ⟨advance.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]; exact hb
  have hab:=Composition.run_join first advance _ _ _ a b ha hb'
  obtain ⟨c,hc,ch,ct,cs⟩:=increment_run index (position+negative.toNat+1) C (position+negative.toNat+1) negative
    (out++RecoveryBoundedNativeLiteral.emitted index position negative)
    (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) hindex
  have hc' : runFrom increment (2*index+4) (restart (joinedReceipt a b).final increment.start)=some c := by
    change runFrom increment _ ⟨increment.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]; exact hc
  have habc:=Composition.run_join (Composition.machine first advance) increment _ _ _ (joinedReceipt a b) c hab hc'
  obtain ⟨d,hd,dh,dt,ds⟩:=erase_run (index+1) (position+negative.toNat+1) C (position+negative.toNat+1) negative
    (out++RecoveryBoundedNativeLiteral.emitted index position negative)
    (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) (by omega)
  have hd' : runFrom erase (2*C+4) (restart (joinedReceipt (joinedReceipt a b) c).final erase.start)=some d := by
    change runFrom erase _ ⟨erase.start,c.final.heads,c.final.tapes⟩=some d
    rw [ch,ct]; exact hd
  have full:=Composition.run_join (Composition.machine (Composition.machine first advance) increment) erase _ _ _
    (joinedReceipt (joinedReceipt a b) c) d habc hd'
  refine ⟨joinedReceipt (joinedReceipt (joinedReceipt a b) c) d,full,?_,dh,dt⟩
  change a.steps+1+b.steps+1+c.steps+1+d.steps ≤ budget index position C negative
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStep
