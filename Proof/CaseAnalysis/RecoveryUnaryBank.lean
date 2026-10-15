import Proof.Amplification.RecoveryBoundedNativeUnaryJoinCalls

/-! The first29 output ports needed immediately by the original guarded
selector's AND appender. The physical reverse loop already restores these
ports; expose them without rebuilding or resetting the shared bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
open LocalBitMultitape RepairRepresentation SourceInterfaces RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reverse_bank {n : ℕ} (base W C value pos : ℕ) (flag : Bool)
    (out pre : List Bool) (refs : List ℕ)
    (href : ∀ r∈refs,r ≤ W) (ha : base+refs.length ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (r : ExecutionReceipt 36 _)
    (hr : runFrom third (refs.length*(24*C+66)+refs.length+3)
      ⟨third.start,foldHeads out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length pos 1,
        foldData base C value refs.length flag out
          (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)⟩=some r) :
    ∀ j : Fin 29,
      r.final.heads (j.castAdd 7)=PCPPNativeClauseBank.heads
        (out++(foldNodes (n:=n) true base refs.reverse).flatMap PCPPRequestNodeSchema.native) j ∧
      r.final.tapes (j.castAdd 7)=RecoveryBoundedNativeFold.oldData 0
        (base+refs.length) C
        (out++(foldNodes (n:=n) true base refs.reverse).flatMap PCPPRequestNodeSchema.native) j := by
  obtain ⟨a,haRun,af,_as⟩:=RecoveryBoundedNativeFoldLoop.loop_run true W C refs.length flag
    pre refs.reverse ⟨base,0,0,out⟩
    (by simp) (by intro v hv; exact href v (List.mem_reverse.mp hv))
    (by simpa using ha) hC
  have stackEq : RecoveryBoundedNativeFoldLoop.stack pre refs.reverse=
      pre++RecoveryBoundedNativeUnaryLoop.stackWords refs := by
    simp only [RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse]
  obtain ⟨b,hb,_bc,_bs,bh,bt,_bk⟩:=RecoveryFocus.dock foldSlots (by decide)
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
  have meaning:=RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=n) true refs.reverse ⟨base,0,0,out⟩
  intro j
  have h:=bh (j.castAdd 6)
  have t:=bt (j.castAdd 6)
  rw [af] at h t
  have slot : foldSlots (j.castAdd 6)=j.castAdd 7 := by fin_cases j <;> rfl
  rw [slot] at h t
  change b.final.heads (j.castAdd 7)=
    (RecoveryBoundedNativeFoldLoop.configuration 3 true C flag pre []
      (RecoveryBoundedNativeFoldLoop.State.iterate true refs.reverse ⟨base,0,0,out⟩)
      refs.length 1).heads ((j.castAdd 5).castAdd 1) at h
  change b.final.tapes (j.castAdd 7)=
    (RecoveryBoundedNativeFoldLoop.configuration 3 true C flag pre []
      (RecoveryBoundedNativeFoldLoop.State.iterate true refs.reverse ⟨base,0,0,out⟩)
      refs.length 1).tapes ((j.castAdd 5).castAdd 1) at t
  simp only [RecoveryBoundedNativeFoldLoop.configuration,RepairSource.VerifierDecoding.RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,Fin.addCases_left,
    RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFold.heads,RecoveryBoundedNativeFold.data] at h t
  rw [meaning.2] at h t
  rw [meaning.1,List.length_reverse] at t
  exact ⟨h,t⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
