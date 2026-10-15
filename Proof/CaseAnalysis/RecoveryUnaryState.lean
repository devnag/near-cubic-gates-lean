import Proof.CaseAnalysis.RecoveryUnaryBank

/-! The repeated selector needs the complete state returned by the original
reverse fold, including erased stack tails and the retained value word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def foldFinal (base C : ℕ) (flag : Bool) (out pre : List Bool) (refs : List ℕ) :=
  RecoveryBoundedNativeFoldLoop.configuration 3 true C flag pre []
    (RecoveryBoundedNativeFoldLoop.State.iterate true refs.reverse ⟨base,0,0,out⟩) refs.length 1

theorem reverse_state (base W C value pos : ℕ) (flag : Bool)
    (out pre : List Bool) (refs : List ℕ)
    (href : ∀ r∈refs,r ≤ W) (ha : base+refs.length ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (r : ExecutionReceipt 36 _)
    (hr : runFrom third (refs.length*(24*C+66)+refs.length+3)
      ⟨third.start,foldHeads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length pos 1,
        foldData base C value refs.length flag out
          (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩=some r) :
    (∀ j : Fin 35,
      r.final.heads (foldSlots j)=(foldFinal base C flag out pre refs).heads j ∧
      r.final.tapes (foldSlots j)=(foldFinal base C flag out pre refs).tapes j) ∧
      r.final.tapes 34=List.replicate value true := by
  obtain ⟨a,haRun,af,_as⟩:=RecoveryBoundedNativeFoldLoop.loop_run true W C refs.length flag
    pre refs.reverse ⟨base,0,0,out⟩
    (by simp) (by intro v hv; exact href v (List.mem_reverse.mp hv))
    (by simpa using ha) hC
  have stackEq : RecoveryBoundedNativeFoldLoop.stack pre refs.reverse=
      pre++RecoveryBoundedNativeUnaryLoop.stackWords refs := by
    simp only [RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse]
  obtain ⟨b,hb,_bc,_bs,bh,bt,bk⟩:=RecoveryFocus.dock foldSlots (by decide)
    (RecoveryBoundedNativeFoldLoop.machine true) _
    (foldHeads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length pos 1)
    (foldData base C value refs.length flag out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs))
    (RecoveryBoundedNativeFoldLoop.configuration 0 true C flag pre refs.reverse
      ⟨base,0,0,out⟩ refs.length 1)
    (by intro j; rw [←stackEq]; exact fold_heads_input C refs.length pos base flag out pre refs.reverse j)
    (by intro j; rw [←stackEq]; exact fold_tapes_input C value refs.length base flag out pre refs.reverse j)
    a haRun
  rw [List.length_reverse] at hb
  have same : b=r := Option.some.inj (hb.symm.trans hr)
  subst r
  constructor
  · intro j
    have h:=bh j
    have t:=bt j
    rw [af] at h t
    exact ⟨h,t⟩
  · exact (bk 34 (by intro j; fin_cases j <;> decide)).2

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
