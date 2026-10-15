import Proof.PCP.PCPTraversalInvariant

/-! The executed descent preserves the common subtree invariant with the
two physically pushed records and the actually copied left count. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stable_descend (cap n pos : ℕ) (source countWord rightStack continuation leftStack : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (st : Stable cap source countWord pos rightStack continuation leftStack heads tapes)
    (count : CountAt cap n tapes) (hn : 2≤n) (hc : 3*n+3≤cap)
    (hrightFit : rightStack.length+2*(n/2)+1≤cap) (hcontFit : continuation.length+2≤cap) :
    ∃ outHeads outTapes,
      Path 0 0 (11*cap+38) heads tapes outHeads outTapes ∧
      Stable cap source countWord pos
        (rightStack++(frame (List.replicate (n/2) true)).reverse)
        (continuation++[false,true]) leftStack outHeads outTapes ∧
      CountAt cap ((n+1)/2) outTapes := by
  obtain ⟨countCap,hcountCap,hcount⟩ := count
  obtain ⟨rightCap,hrightCap,hright⟩ := st.right.padded cap (st.work 80 (by decide) (by decide))
  obtain ⟨contCap,hcontCap,hcont⟩ := st.continuation.padded cap (st.work 81 (by decide) (by decide))
  obtain ⟨log,hlogBound,hlog⟩ := st.clearLog
  obtain ⟨hpath,hwork,hheads⟩ := descend_path n cap countCap rightCap contCap log rightStack continuation heads tapes
    hn hc hcountCap hrightCap hcontCap hrightFit hcontFit st.work st.workingHeads st.capacityTape hlog hcount
    hright hcont st.right.head st.continuation.head st.capacityHead
  let out := descendOutput n cap countCap rightCap contCap log rightStack continuation tapes
  let moved := descendHeads n rightStack continuation heads
  refine ⟨moved,out,hpath,?_,⟨cap,le_rfl,descend_count n cap countCap rightCap contCap log rightStack continuation tapes⟩⟩
  refine ⟨hwork,hheads,low_descend st.lowHeads n rightStack continuation,
    (descend_other n cap countCap rightCap contCap log rightStack continuation tapes 0 (by decide)).trans st.sourceTape,
    (descend_head_other heads n rightStack continuation 0 (by decide)).trans st.sourceHead,
    (descend_other n cap countCap rightCap contCap log rightStack continuation tapes 2 (by decide)).trans st.countTape,
    (descend_head_other heads n rightStack continuation 2 (by decide)).trans st.countHead,
    descend_driver n cap countCap rightCap contCap log rightStack continuation tapes,
    ⟨max log (cap+1),max_le hlogBound le_rfl,
      descend_log n cap countCap rightCap contCap log rightStack continuation tapes⟩,?_,?_,?_,?_⟩
  · apply StackAt.of_pad rightCap
    · have h := descend_head_right heads n rightStack continuation
      simpa only [List.length_append,List.length_reverse,frame_length,List.length_replicate,Nat.add_assoc] using h
    · exact descend_right_stack n cap countCap rightCap contCap log rightStack continuation tapes
  · apply StackAt.of_pad contCap
    · simpa only [List.length_append,List.length_cons,List.length_nil] using
        descend_head_continuation heads n rightStack continuation
    · exact descend_continuation n cap countCap rightCap contCap log rightStack continuation tapes
  · refine ⟨(descend_head_other heads n rightStack continuation 82 (by decide)).trans st.left.head,?_⟩
    obtain ⟨z,hz⟩ := st.left.zeros
    exact ⟨z,(descend_other n cap countCap rightCap contCap log rightStack continuation tapes 82 (by decide)).trans hz⟩
  · exact (descend_other n cap countCap rightCap contCap log rightStack continuation tapes 78 (by decide)).trans st.fresh

end NearCubicWires.RepairOrdinary.PCPTraversal
