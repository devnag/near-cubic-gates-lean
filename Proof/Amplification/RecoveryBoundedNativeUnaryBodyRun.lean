import Proof.Amplification.RecoveryBoundedNativeUnaryBodyLayout
import Proof.Amplification.RecoveryBoundedNativeLiteralStepBound

/-! The unary-equality body reads the current value bit, emits and saves the
original literal's actual reference, then advances the retained value cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryBody
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem first_run (index position C value pos : ℕ) (old : Bool) (out stack : List Bool) :
    ∃ r, runFrom first 1 ⟨first.start,heads out stack pos,data index position C value old out stack⟩=some r ∧
      r.final.heads=heads out stack pos ∧
      r.final.tapes=data index position C value (RecoveryBoundedNativeUnaryFlag.negative value pos) out stack ∧
      r.steps=1 := by
  obtain ⟨a,ha,af,as⟩:=RecoveryBoundedNativeUnaryFlag.flag_run value pos old
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock flagSlots (by decide)
    RecoveryBoundedNativeUnaryFlag.machine 1 (heads out stack pos) (data index position C value old out stack)
    (RecoveryBoundedNativeUnaryFlag.cfg 0 value pos old)
    (fun j=>(flag_input index position C value pos old out stack j).1)
    (fun j=>(flag_input index position C value pos old out stack j).2) a ha
  refine ⟨r,hr,?_,?_,rs.trans as⟩
  · funext i
    by_cases hs : ∃ j,flagSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      rw [rh j,af]
      exact (flag_input index position C value pos old out stack j).1.symm
    · exact (rkeep i (by simpa using hs)).1
  · have he:=HierarchyWidth.install_eq flagSlots (by decide)
      (data index position C value old out stack) r.final.tapes
      ![[RecoveryBoundedNativeUnaryFlag.negative value pos],List.replicate value true]
      (by intro j; rw [rt j,af]; rfl) (by intro i hi; exact (rkeep i hi).2)
    rw [flag_tapes] at he
    exact he.symm

theorem second_run (index position W C value pos : ℕ) (negative : Bool) (out stack : List Bool)
    (hi : index ≤ W) (hp : position ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom second (32*C+100)
      ⟨second.start,heads out stack pos,data index position C value negative out stack⟩=some r ∧
      r.steps ≤ 32*C+100 ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) pos ∧
      r.final.tapes=data (index+1) (position+negative.toNat+1) C value negative
        (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=RecoveryBoundedNativeLiteralStep.bounded_run index position W C negative out stack hi hp hC
  have hr:=TapeEmbedding.run_embed RecoveryBoundedNativeLiteralStep.machine
    (fun _ : Fin 1=>pos) (fun _ : Fin 1=>List.replicate value true) _ _ a ha
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>pos) (fun _ : Fin 1=>List.replicate value true) a,hr,as,?_,?_⟩
  · change (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>ℕ) a.final.heads (fun _=>pos))=_
    rw [ah]; rfl
  · change (Fin.addCases (m:=34) (n:=1) (motive:=fun _=>List Bool) a.final.tapes (fun _=>List.replicate value true))=_
    rw [atapes]; rfl

theorem last_run (index position C value pos : ℕ) (negative : Bool) (out stack : List Bool) :
    ∃ r, runFrom last 1 ⟨last.start,heads out stack pos,data index position C value negative out stack⟩=some r ∧
      r.final.heads=heads out stack (pos+1) ∧
      r.final.tapes=data index position C value negative out stack ∧ r.steps=1 := by
  obtain ⟨a,ha,af,as⟩:=RecoveryBoundedNativeUnaryFlag.advance_run pos (List.replicate value true)
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock valueSlot (by decide)
    RecoveryBoundedNativeUnaryFlag.advance 1 (heads out stack pos) (data index position C value negative out stack)
    (⟨0,fun _=>pos,fun _=>List.replicate value true⟩ : Configuration 1 2)
    (fun j=>(value_input index position C value pos negative out stack j).1)
    (fun j=>(value_input index position C value pos negative out stack j).2) a ha
  refine ⟨r,hr,?_,?_,rs.trans as⟩
  · funext i
    by_cases hi : i=34
    · subst i
      exact (rh 0).trans (by rw [af]; rfl)
    · exact ((rkeep i (by intro j; fin_cases j; exact Ne.symm hi)).1).trans (heads_old out stack pos (pos+1) i hi)
  · funext i
    by_cases hi : i=34
    · subst i
      exact (rt 0).trans (by rw [af]; rfl)
    · exact (rkeep i (by intro j; fin_cases j; exact Ne.symm hi)).2

theorem body_run (index position W C value pos : ℕ) (old : Bool) (out stack : List Bool)
    (hi : index ≤ W) (hp : position ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    let negative:=RecoveryBoundedNativeUnaryFlag.negative value pos
    ∃ r, runFrom machine (32*C+104) (entry index position C value pos old out stack)=some r ∧
      r.steps ≤ 32*C+104 ∧
      r.final.heads=heads (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) (pos+1) ∧
      r.final.tapes=data (index+1) (position+negative.toNat+1) C value negative
        (out++RecoveryBoundedNativeLiteral.emitted index position negative)
        (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack) := by
  dsimp only
  let negative:=RecoveryBoundedNativeUnaryFlag.negative value pos
  obtain ⟨a,ha,ah,atapes,as⟩:=first_run index position C value pos old out stack
  obtain ⟨b,hb,bs,bh,bt⟩:=second_run index position W C value pos negative out stack hi hp hC
  have hb' : runFrom second (32*C+100) (restart a.final second.start)=some b := by
    change runFrom second _ ⟨second.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]; exact hb
  have hab:=Composition.run_join first second _ _ _ a b ha hb'
  obtain ⟨c,hc,ch,ct,cs⟩:=last_run (index+1) (position+negative.toNat+1) C value pos negative
    (out++RecoveryBoundedNativeLiteral.emitted index position negative)
    (RecoveryBoundedNativeLiteralStack.stackWord (position+negative.toNat) stack)
  have hc' : runFrom last 1 (restart (joinedReceipt a b).final last.start)=some c := by
    change runFrom last _ ⟨last.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]; exact hc
  have full:=Composition.run_join (Composition.machine first second) last _ _ _ (joinedReceipt a b) c hab hc'
  have he : (1+1+(32*C+100))+1+1=32*C+104 := by omega
  rw [he] at full
  refine ⟨joinedReceipt (joinedReceipt a b) c,full,?_,ch,ct⟩
  change a.steps+1+b.steps+1+c.steps ≤ 32*C+104
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryBody
