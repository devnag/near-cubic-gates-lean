import Proof.CaseAnalysis.RecoveryClauseFoldBank

/-! Complete paid transition and existing reverse AND loop on the exact
original clause stack and retained clause-count driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition RepairSource.VerifierDecoding
open RecoveryBoundedNativeUnaryPhase (trueBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine prepare reverseMachine
def budget (count C : ℕ):=prepareBudget C+1+(count*(24*C+66)+count+3)

theorem padded_reverse_run (base W C total : ℕ) (out pre : List Bool) (refs : List ℕ)
    (ht : refs.length=total) (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom (RecoveryBoundedNativeFoldLoop.machine true) (refs.length*(24*C+66)+total+3)
      (input base C total out pre refs)=some r ∧ r.final=output base C total out pre refs ∧
      r.steps ≤ refs.length*(24*C+66)+total+3 := by
  obtain ⟨p,pr,pf,ps⟩:=RecoveryBoundedNativeFoldLoop.loop_run true W C total false pre refs.reverse ⟨base,0,0,out⟩
    (by simpa only [List.length_reverse,Nat.zero_add] using ht)
    (by intro ref hr;exact href ref (List.mem_reverse.mp hr)) (by simpa only [List.length_reverse] using ha) hC
  rw [List.length_reverse] at pr ps
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config (RecoveryBoundedNativeFoldLoop.machine true) (caps C) _ _ p pr
  refine ⟨r,rr,?_,rs.le.trans ps⟩
  rw [rf,pf]
  rfl

theorem fold_run (H : Fin 73→ℕ) (A : Fin 73→List Bool) (base left right W C L : ℕ)
    (out pre source queryRefs stack : List Bool) (refs : List ℕ)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) base left right C L out pre source queryRefs)
    (hSH : H 71=(stack++RecoveryBoundedClauseList.stackWord refs).length)
    (hSA : A 71=stack++RecoveryBoundedClauseList.stackWord refs)
    (hDH : H 72=1) (hDA : A 72=CompareMachine.word refs.length)
    (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    let result:=out++trueBits
    ∃ r,runFrom machine (budget refs.length C) ⟨machine.start,H,A⟩=some r ∧ r.steps ≤ budget refs.length C ∧
      (∀ j,r.final.heads (slots j)=(output base C refs.length result stack refs).heads j) ∧
      (∀ j,r.final.tapes (slots j)=(output base C refs.length result stack refs).tapes j) ∧
      (∀ i,(∀ j,slots j≠i) → r.final.heads i=heads H result i ∧
        r.final.tapes i=written (cleared A C) result i) := by
  let result:=out++trueBits
  obtain ⟨p,pr,ps,ph,pt⟩:=prepare_run H A base left right W C L out pre source queryRefs h hl hr hC
  obtain ⟨q,qr,qf,qs⟩:=padded_reverse_run base W C refs.length result stack refs rfl href ha hC
  have hc : 1 ≤ C:=by nlinarith [Nat.zero_le (W^2)]
  obtain ⟨s,sr,_,ss,sh,st,skeep⟩:=RecoveryFocus.dock slots slots_injective (RecoveryBoundedNativeFoldLoop.machine true) _
    (heads H result) (written (cleared A C) result) (input base C refs.length result stack refs)
    (prepared_heads H A base left right C L refs.length out pre source queryRefs result stack refs h hSH hDH)
    (prepared_tapes H A base left right C L refs.length out pre source queryRefs result stack refs h hSA hDA hc) q qr
  have sr' : runFrom reverseMachine (refs.length*(24*C+66)+refs.length+3) (restart p.final reverseMachine.start)=some s := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some s
    rw [ph,pt]
    exact sr
  have full:=Composition.run_join prepare reverseMachine _ _ _ p s pr sr'
  refine ⟨joinedReceipt p s,full,?_,?_,?_,skeep⟩
  · change p.steps+1+s.steps ≤ budget refs.length C
    unfold budget
    have hs:=ss.le.trans qs
    omega
  · intro j
    change s.final.heads (slots j)=_
    rw [sh j,qf]
  · intro j
    change s.final.tapes (slots j)=_
    rw [st j,qf]

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseFold
