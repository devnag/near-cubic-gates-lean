import Proof.CaseAnalysis.RecoveryRowsAll

/-! The original fixed-count join adds exactly one AND. Its saved grammar
reference is popped from the existing stack; the full row driver is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
open LocalBitMultitape Composition RepairRepresentation
open RecoveryBoundedNativeFoldLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def localMachine:=TapeEmbedding.machine 1 (RecoveryBoundedNativeFold.machine true)
noncomputable def before (C total ref : ℕ) (pre : List Bool) (a : State):=
  configuration 3 true C false (RecoveryBoundedClauseCollect.pushed ref pre) [] a total 1
noncomputable def after (C total ref : ℕ) (pre : List Bool) (a : State):=
  configuration 3 true C false pre [] (a.next true ref) total 1

theorem local_run (C W total ref : ℕ) (pre : List Bool) (a : State)
    (hr : ref≤W) (ha : a.acc≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ r,runFrom localMachine (24*C+64)
      ⟨localMachine.start,(before C total ref pre a).heads,(before C total ref pre a).tapes⟩=some r ∧
      r.steps≤24*C+64 ∧ r.final.heads=(after C total ref pre a).heads ∧
      r.final.tapes=(after C total ref pre a).tapes := by
  obtain ⟨base,br,bs,bh,bt⟩:=RecoveryBoundedNativeFold.bounded_run true ref a.acc W C a.erased false a.out pre hr ha hC
  have run:=TapeEmbedding.run_embed (RecoveryBoundedNativeFold.machine true)
    (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) _ _ base br
  let r:=TapeEmbedding.receipt (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) base
  refine ⟨r,?_,bs,?_,?_⟩
  · convert run using 1
    apply congrArg (fun c=>runFrom localMachine (24*C+64) c)
    apply configuration_ext
    · rfl
    · simp only [before,configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,State.entry,
        RecoveryBoundedNativeFold.entry,stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,
        List.flatMap_nil,List.append_nil,RecoveryBoundedClauseCollect.pushed,List.length_append,
        List.length_reverse,frame_length,List.length_replicate,Nat.add_assoc]
    · simp only [before,configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,State.entry,
        RecoveryBoundedNativeFold.entry,stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,
        List.flatMap_nil,List.append_nil,RecoveryBoundedClauseCollect.pushed]
  · change (TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) base.final).heads=_
    simp only [TapeEmbedding.config,bh,after,configuration,RepeatMachine.cfg,controlConfig,State.entry,
      State.next,RecoveryBoundedNativeFold.entry,stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,
      List.flatMap_nil,List.append_nil]
  · change (TapeEmbedding.config (fun _ : Fin 1=>1) (fun _=>CompareMachine.word total) base.final).tapes=_
    simp only [TapeEmbedding.config,bt,after,configuration,RepeatMachine.cfg,controlConfig,State.entry,
      State.next,RecoveryBoundedNativeFold.entry,stack,List.reverse_nil,RecoveryBoundedNativeUnaryLoop.stackWords,
      List.flatMap_nil,List.append_nil]

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountConjunction
