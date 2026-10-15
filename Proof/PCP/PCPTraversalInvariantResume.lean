import Proof.PCP.PCPTraversalInvariantDescend

/-! The checked left return supplies the exact common invariant for the
right recursive child, with the actual saved-left and true continuation. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stable_resume (cap n pos : ℕ) (source countWord rightStack continuation leftStack bits : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (st : Stable cap source countWord pos
      (rightStack++(frame (List.replicate n true)).reverse) (continuation++[false,true]) leftStack heads tapes)
    (hc : 2*n+2≤cap) (hleftFit : leftStack.length+2*bits.length+1≤cap)
    (hresult : tapes 77=ZeroPadding.pad cap (frame bits)) :
    ∃ outHeads outTapes,
      Path 9 0 (10*cap+29) heads tapes outHeads outTapes ∧
      Stable cap source countWord pos rightStack (continuation++[true,true])
        (leftStack++(frame bits).reverse) outHeads outTapes ∧
      CountAt cap n outTapes := by
  obtain ⟨leftCap,hleftCap,hleft⟩ := st.left.padded cap (st.work 82 (by decide) (by decide))
  obtain ⟨rightZeros,hright⟩ := st.right.zeros
  obtain ⟨continuationZeros,hcont⟩ := st.continuation.zeros
  obtain ⟨log,hlogBound,hlog⟩ := st.clearLog
  have hhright : heads 80=rightStack.length+2*n+1 := by
    simpa only [List.length_append,List.length_reverse,frame_length,List.length_replicate,Nat.add_assoc] using st.right.head
  have hhcont : heads 81=continuation.length+2 := by
    simpa only [List.length_append,List.length_cons,List.length_nil] using st.continuation.head
  have hcontInput : tapes 81=continuation++false::true::List.replicate continuationZeros false := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using hcont
  obtain ⟨hpath,hwork,hheads⟩ := resume_right_path bits leftStack rightStack continuation
    n cap leftCap rightZeros continuationZeros log heads tapes hc hleftCap hleftFit st.work st.workingHeads
    st.capacityTape hlog hresult hleft hright hcontInput st.left.head hhright hhcont st.capacityHead
  let out := resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes
  let moved := resumeRightHeads bits leftStack rightStack heads
  refine ⟨moved,out,hpath,?_,⟨cap,le_rfl,resume_right_count bits leftStack rightStack continuation
    n cap leftCap rightZeros continuationZeros log tapes⟩⟩
  refine ⟨hwork,hheads,low_resume st.lowHeads bits leftStack rightStack,
    (resume_other bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes 0 (by decide)).trans st.sourceTape,
    (resume_head_other heads bits leftStack rightStack 0 (by decide)).trans st.sourceHead,
    (resume_other bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes 2 (by decide)).trans st.countTape,
    (resume_head_other heads bits leftStack rightStack 2 (by decide)).trans st.countHead,
    resume_driver bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes,
    ⟨max log (cap+1),max_le hlogBound le_rfl,
      resume_log bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes⟩,?_,?_,?_,?_⟩
  · exact ⟨resume_head_right heads bits leftStack rightStack,
      ⟨2*n+1+rightZeros,resume_right_stack bits leftStack rightStack continuation
        n cap leftCap rightZeros continuationZeros log tapes⟩⟩
  · refine ⟨?_,⟨continuationZeros,?_⟩⟩
    · have h := (resume_head_other heads bits leftStack rightStack 81 (by decide)).trans hhcont
      simpa only [List.length_append,List.length_cons,List.length_nil] using h
    · simpa only [List.append_assoc,List.cons_append,List.nil_append] using
        resume_continuation bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes
  · apply StackAt.of_pad leftCap
    · simpa only [List.length_append,List.length_reverse,frame_length,Nat.add_assoc] using
        resume_head_left heads bits leftStack rightStack
    · exact resume_left_stack bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes
  · exact (resume_other bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log tapes 78 (by decide)).trans st.fresh

end NearCubicWires.RepairOrdinary.PCPTraversal
