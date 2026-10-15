import Proof.Amplification.RecoveryBoundedNativeLiteralStackLayout

/-! Execute one original grammar literal, compute its actual compiler output
address, and push that address onto the live reverse unary stack. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStack
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (index position C : ℕ) (negative : Bool) :=
  RecoveryBoundedNativeLiteral.budget index position C+1+
    (2*(position+negative.toNat)+6)+1+(4*(position+negative.toNat)+6)

theorem first_run (index position C : ℕ) (negative : Bool) (out stack : List Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hp : PCPPNativeSumAppend.budget 0 position+1 ≤ C)
    (hz : PCPPNativeSumAppend.budget 0 0+1 ≤ C) :
    ∃ r, runFrom first (RecoveryBoundedNativeLiteral.budget index position C)
      ⟨first.start,heads out stack,data index position C negative out stack 0⟩=some r ∧
      r.steps ≤ RecoveryBoundedNativeLiteral.budget index position C ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative) stack ∧
      r.final.tapes=data index position C negative
        (out++RecoveryBoundedNativeLiteral.emitted index position negative) stack 0 := by
  obtain ⟨a,ha,as,ah,atapes⟩:=RecoveryBoundedNativeLiteral.literal_run index position C negative out hi hp hz
  let extraH : Fin 4→ℕ:=![0,stack.length,0,0]
  let extraT : Fin 4→List Bool:=![[],stack,List.replicate C false,List.replicate C false]
  have hr:=TapeEmbedding.run_embed RecoveryBoundedNativeLiteral.machine extraH extraT _ _ a ha
  refine ⟨TapeEmbedding.receipt extraH extraT a,hr,as,?_,?_⟩
  · change (Fin.addCases (m:=30) (n:=4) (motive:=fun _=>ℕ) a.final.heads extraH)=_
    rw [ah]; rfl
  · change (Fin.addCases (m:=30) (n:=4) (motive:=fun _=>List Bool) a.final.tapes extraT)=_
    rw [atapes]; rfl

theorem second_run (index position C : ℕ) (negative : Bool) (out stack : List Bool)
    (hC : position+3 ≤ C) :
    ∃ r, runFrom second (2*(position+negative.toNat)+6)
      ⟨second.start,heads out stack,data index position C negative out stack 0⟩=some r ∧
      r.steps ≤ 2*(position+negative.toNat)+6 ∧ r.final.heads=heads out stack ∧
      r.final.tapes=data index position C negative out stack (position+negative.toNat) := by
  obtain ⟨a,ha,atapes,ah,as⟩:=RecoveryBoundedNativeReference.sum_ready position C negative hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock sumSlots (by decide) ClockUnarySum.machine _
    (heads out stack) (data index position C negative out stack 0)
    (initialConfiguration ClockUnarySum.machine
      ![List.replicate position true,[negative],[],List.replicate C false])
    (fun j=>(sum_input index position C negative out stack j).1)
    (fun j=>(sum_input index position C negative out stack j).2) a ha
  refine ⟨r,hr,rs.le.trans as,?_,?_⟩
  · funext i
    by_cases hs : ∃ j,sumSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      exact (rh j).trans ((ah j).trans (sum_input index position C negative out stack j).1.symm)
    · exact (rkeep i (by simpa using hs)).1
  · have he:=HierarchyWidth.install_eq sumSlots (by decide)
      (data index position C negative out stack 0) r.final.tapes
      ![List.replicate position true,[negative],List.replicate (position+negative.toNat) true,List.replicate C false]
      (by intro j; rw [rt j,atapes]) (by intro i hi; exact (rkeep i hi).2)
    rw [sum_tapes] at he
    exact he.symm

theorem last_run (index position C ref : ℕ) (negative : Bool) (out stack : List Bool)
    (hC : 2*ref+2 ≤ C) :
    ∃ r, runFrom last (4*ref+6)
      ⟨last.start,heads out stack,data index position C negative out stack ref⟩=some r ∧
      r.steps ≤ 4*ref+6 ∧ r.final.heads=heads out (stackWord ref stack) ∧
      r.final.tapes=data index position C negative out (stackWord ref stack) ref := by
  obtain ⟨a,ha,atapes,ah,as⟩:=RecoveryBoundedNativeReference.push_run ref C stack hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock pushSlots (by decide) PCPUnaryStackPush.machine _
    (heads out stack) (data index position C negative out stack ref)
    (⟨PCPUnaryStackPush.machine.start,![0,stack.length,0],
      ![List.replicate ref true,stack,List.replicate C false]⟩ : Configuration 3 6)
    (fun j=>(push_input index position C ref negative out stack j).1)
    (fun j=>(push_input index position C ref negative out stack j).2) a ha
  refine ⟨r,hr,rs.le.trans as,?_,?_⟩
  · funext i
    by_cases hs : ∃ j,pushSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh j,ah]
      fin_cases j
      · rfl
      · change stack.length+2*ref+1=(stackWord ref stack).length
        simp [stackWord,frame_length,List.length_replicate,Nat.add_assoc]
      · rfl
    · rw [(rkeep i (by simpa using hs)).1]
      have h : i≠31 := by intro he; apply hs; exact ⟨1,he.symm⟩
      fin_cases i
      all_goals first | exact False.elim (h rfl) | rfl
  · have he:=HierarchyWidth.install_eq pushSlots (by decide)
      (data index position C negative out stack ref) r.final.tapes
      ![List.replicate ref true,stackWord ref stack,List.replicate C false]
      (by intro j; rw [rt j,atapes]; rfl) (by intro i hi; exact (rkeep i hi).2)
    rw [push_tapes] at he
    exact he.symm

theorem literal_stack_run (index position C : ℕ) (negative : Bool) (out stack : List Bool)
    (hi : PCPPNativeSumAppend.budget 0 index+1 ≤ C)
    (hp : PCPPNativeSumAppend.budget 0 position+1 ≤ C)
    (hz : PCPPNativeSumAppend.budget 0 0+1 ≤ C)
    (hsum : position+3 ≤ C) (hpush : 2*(position+negative.toNat)+2 ≤ C) :
    ∃ r, runFrom machine (budget index position C negative) (entry index position C negative out stack)=some r ∧
      r.steps ≤ budget index position C negative ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (stackWord (position+negative.toNat) stack) ∧
      r.final.tapes=data index position C negative (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (stackWord (position+negative.toNat) stack) (position+negative.toNat) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=first_run index position C negative out stack hi hp hz
  obtain ⟨b,hb,bs,bh,bt⟩:=second_run index position C negative
    (out++RecoveryBoundedNativeLiteral.emitted index position negative) stack hsum
  have hb' : runFrom second (2*(position+negative.toNat)+6) (restart a.final second.start)=some b := by
    change runFrom second _ ⟨second.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]; exact hb
  have hab:=Composition.run_join first second _ _ _ a b ha hb'
  obtain ⟨c,hc,cs,ch,ct⟩:=last_run index position C (position+negative.toNat) negative
    (out++RecoveryBoundedNativeLiteral.emitted index position negative) stack hpush
  have hc' : runFrom last (4*(position+negative.toNat)+6)
      (restart (Composition.joinedReceipt a b).final last.start)=some c := by
    change runFrom last _ ⟨last.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]; exact hc
  have joined:=Composition.run_join (Composition.machine first second) last _ _ _
    (Composition.joinedReceipt a b) c hab hc'
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,joined,?_,ch,ct⟩
  change a.steps+1+b.steps+1+c.steps ≤ budget index position C negative
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteralStack
