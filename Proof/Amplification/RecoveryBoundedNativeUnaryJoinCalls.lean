import Proof.Amplification.RecoveryBoundedNativeUnaryJoinLayout
import Proof.Amplification.RecoveryBoundedNativeUnaryBounds

/-! Execute the phase bridge and dock the actual reverse loop into the
same physical bank, reusing the original limit and preserving its value tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
open LocalBitMultitape RepairRepresentation Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem phase_run (C value total : ℕ) (a : RecoveryBoundedNativeUnaryLoop.State) (hi : a.index ≤ C) :
    ∃ r, runFrom second (RecoveryBoundedNativeUnaryPhase.trueBits.length+1+(2*C+4))
      (restart (RecoveryBoundedNativeUnaryLoop.configuration 3 C value a total 1) second.start)=some r ∧
      r.steps=RecoveryBoundedNativeUnaryPhase.trueBits.length+1+(2*C+4) ∧
      r.final.heads=foldHeads (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) a.stack.length a.offset 1 ∧
      r.final.tapes=foldData a.position C value total a.flag
        (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) a.stack := by
  obtain ⟨b,hb,bs,bh,bt⟩:=RecoveryBoundedNativeUnaryPhase.phase_run a.index a.position C a.flag a.out a.stack hi
  have run:=TapeEmbedding.run_embed RecoveryBoundedNativeUnaryPhase.machine (extraHeads a.offset 1) (extraData value total) _ _ b hb
  have input : TapeEmbedding.config (extraHeads a.offset 1) (extraData value total)
      (RecoveryBoundedNativeUnaryPhase.entry a.index a.position C a.flag a.out a.stack)=
      restart (RecoveryBoundedNativeUnaryLoop.configuration 3 C value a total 1) second.start := by
    apply configuration_ext
    · rfl
    · exact (prefix_heads C value total a).symm
    · exact (prefix_tapes C value total a).symm
  rw [input] at run
  refine ⟨TapeEmbedding.receipt (extraHeads a.offset 1) (extraData value total) b,run,bs,?_,?_⟩
  · change (Fin.addCases (m:=34) (n:=2) (motive:=fun _=>ℕ) b.final.heads (extraHeads a.offset 1))=_
    rw [bh]; rfl
  · change (Fin.addCases (m:=34) (n:=2) (motive:=fun _=>List Bool) b.final.tapes (extraData value total))=_
    rw [bt]; rfl

theorem reverse_run {n : ℕ} (base W C value pos : ℕ) (flag : Bool) (out pre : List Bool) (refs : List ℕ)
    (href : ∀ r∈refs,r ≤ W) (ha : base+refs.length ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom third (refs.length*(24*C+66)+refs.length+3)
      ⟨third.start,foldHeads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length pos 1,
        foldData base C value refs.length flag out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩=some r ∧
      r.steps ≤ refs.length*(24*C+66)+refs.length+3 ∧
      r.final.tapes 20=out++(RecoveryBoundedNative.foldNodes (n:=n) true base refs.reverse).flatMap PCPPRequestNodeSchema.native ∧
      r.final.tapes 25=List.replicate (base+refs.length) true ∧
      r.final.heads 31=pre.length ∧ r.final.heads 34=pos ∧ r.final.heads 35=1 := by
  obtain ⟨a,haRun,as,ao,aa,ast,ag⟩:=RecoveryBoundedNativeFoldLoop.original_fold_run (n:=n) base W C flag out pre refs href ha hC
  have stackEq : RecoveryBoundedNativeFoldLoop.stack pre refs.reverse=
      pre++RecoveryBoundedNativeUnaryLoop.stackWords refs := by
    simp only [RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse]
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock foldSlots (by decide) (RecoveryBoundedNativeFoldLoop.machine true) _
    (foldHeads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length pos 1)
    (foldData base C value refs.length flag out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs))
    (RecoveryBoundedNativeFoldLoop.configuration 0 true C flag pre refs.reverse ⟨base,0,0,out⟩ refs.length 1)
    (by intro j; rw [←stackEq]; exact fold_heads_input C refs.length pos base flag out pre refs.reverse j)
    (by intro j; rw [←stackEq]; exact fold_tapes_input C value refs.length base flag out pre refs.reverse j) a haRun
  refine ⟨r,hr,rs.le.trans as,?_,?_,?_,?_,?_⟩
  · exact (rt 20).trans ao
  · exact (rt 25).trans aa
  · exact (rh 31).trans ast
  · exact (rkeep 34 (by intro j; fin_cases j <;> decide)).1
  · exact (rh 34).trans ag

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
