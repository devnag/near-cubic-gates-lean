import Proof.PCP.PCPTraversalInvariantResume

/-! The right return restores all three outer stack prefixes in the same
invariant and returns the exact canonical internal-node code. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stable_combine (cap pos : ℕ) (source countWord rightStack continuation leftStack left right : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (st : Stable cap source countWord pos rightStack (continuation++[true,true])
      (leftStack++(frame left).reverse) heads tapes)
    (hc : 5≤cap) (hl : 2*left.length+2≤cap) (hr : 2*right.length+1≤cap)
    (hpos : 0<Nat.pair (value left) (value right))
    (hpair : PCPPairCanonical.budget left right+1≤cap)
    (htag : PCPPairCanonical.budget (2 : ℕ).bits (Nat.pair (value left) (value right)).bits+1≤cap)
    (hresult : tapes 77=ZeroPadding.pad cap (frame right)) :
    ∃ outHeads outTapes,
      Path 9 9 (24*cap+77) heads tapes outHeads outTapes ∧
      Stable cap source countWord pos rightStack continuation leftStack outHeads outTapes ∧
      outTapes 77=ZeroPadding.pad cap (frame (Nat.pair 2 (Nat.pair (value left) (value right))).bits) := by
  obtain ⟨leftZeros,hleft⟩ := st.left.zeros
  obtain ⟨continuationZeros,hcont⟩ := st.continuation.zeros
  obtain ⟨log,hlogBound,hlog⟩ := st.clearLog
  have hhleft : heads 82=leftStack.length+2*left.length+1 := by
    simpa only [List.length_append,List.length_reverse,frame_length,Nat.add_assoc] using st.left.head
  have hhcont : heads 81=continuation.length+2 := by
    simpa only [List.length_append,List.length_cons,List.length_nil] using st.continuation.head
  have hcontInput : tapes 81=continuation++true::true::List.replicate continuationZeros false := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using hcont
  obtain ⟨first,second,hpath,hwork,hheads⟩ := combine_return_path left right leftStack continuation
    cap leftZeros continuationZeros log heads tapes hc hl hr hpos hpair htag st.work st.workingHeads
    st.capacityTape hlog hleft hhleft hresult hcontInput hhcont st.capacityHead
  let returned := rightReturned continuation continuationZeros tapes
  let out := combinedOutput left right leftStack cap leftZeros log returned first second
  let moved := combineReturnHeads leftStack continuation heads
  have returned_other : ∀ i : Fin 128,i≠81 → returned i=tapes i := by
    intro i hi
    exact install_other ![81] tapes (fun _ => continuation++List.replicate (continuationZeros+2) false)
      i (by intro j; fin_cases j; exact Ne.symm hi)
  refine ⟨moved,out,hpath,?_,combined_result left right leftStack cap leftZeros log returned first second⟩
  refine ⟨hwork,hheads,low_combine_return st.lowHeads leftStack continuation,
    ((combined_other left right leftStack cap leftZeros log returned first second 0 (by decide)).trans
      (returned_other 0 (by decide))).trans st.sourceTape,
    (combine_head_other heads leftStack continuation 0 (by decide)).trans st.sourceHead,
    ((combined_other left right leftStack cap leftZeros log returned first second 2 (by decide)).trans
      (returned_other 2 (by decide))).trans st.countTape,
    (combine_head_other heads leftStack continuation 2 (by decide)).trans st.countHead,
    combined_driver left right leftStack cap leftZeros log returned first second,
    ⟨max log (cap+1),max_le hlogBound le_rfl,
      combined_log left right leftStack cap leftZeros log returned first second⟩,?_,?_,?_,?_⟩
  · refine ⟨(combine_head_other heads leftStack continuation 80 (by decide)).trans st.right.head,?_⟩
    obtain ⟨z,hz⟩ := st.right.zeros
    exact ⟨z,((combined_other left right leftStack cap leftZeros log returned first second 80 (by decide)).trans
      (returned_other 80 (by decide))).trans hz⟩
  · refine ⟨combine_head_continuation heads leftStack continuation,⟨continuationZeros+2,?_⟩⟩
    exact (combined_other left right leftStack cap leftZeros log returned first second 81 (by decide)).trans
      (install_slot ![81] (by decide) tapes (fun _ => continuation++List.replicate (continuationZeros+2) false) 0)
  · exact ⟨combine_head_left heads leftStack continuation,⟨2*left.length+1+leftZeros,
      combined_left_stack left right leftStack cap leftZeros log returned first second⟩⟩
  · exact ((combined_other left right leftStack cap leftZeros log returned first second 78 (by decide)).trans
      (returned_other 78 (by decide))).trans st.fresh

end NearCubicWires.RepairOrdinary.PCPTraversal
