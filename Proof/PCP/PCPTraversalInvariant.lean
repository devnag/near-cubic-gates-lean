import Proof.PCP.PCPTraversalHeadPost

/-! One common stack/cursor invariant for the already executed traversal
branches. Stack tails are actual allocated zero cells, not free truncations. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure StackAt (pre : List Bool) (slot : Fin 128) (heads : Fin 128 → ℕ)
    (tapes : Fin 128 → List Bool) : Prop where
  head : heads slot=pre.length
  zeros : ∃ z,tapes slot=pre++List.replicate z false

theorem StackAt.padded {pre : List Bool} {slot : Fin 128} {heads : Fin 128 → ℕ}
    {tapes : Fin 128 → List Bool} (h : StackAt pre slot heads tapes)
    (cap : ℕ) (hb : (tapes slot).length≤cap) :
    ∃ backing≤cap,tapes slot=ZeroPadding.pad backing pre := by
  obtain ⟨z,hz⟩ := h.zeros
  refine ⟨pre.length+z,?_,?_⟩
  · rw [hz,List.length_append,List.length_replicate] at hb
    exact hb
  · rw [hz]
    simp only [ZeroPadding.pad,Nat.add_sub_cancel_left]

theorem StackAt.of_pad {pre : List Bool} {slot : Fin 128} {heads : Fin 128 → ℕ}
    {tapes : Fin 128 → List Bool} (cap : ℕ) (hh : heads slot=pre.length)
    (ht : tapes slot=ZeroPadding.pad cap pre) : StackAt pre slot heads tapes :=
  ⟨hh,⟨cap-pre.length,ht⟩⟩

structure Stable (cap : ℕ) (source countWord : List Bool) (pos : ℕ)
    (rightStack continuation leftStack : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool) : Prop where
  work : WorkBound cap tapes
  workingHeads : WorkingHeads heads
  lowHeads : LowHeads heads
  sourceTape : tapes 0=source
  sourceHead : heads 0=pos
  countTape : tapes 2=countWord
  countHead : heads 2=1
  capacityTape : tapes 28=List.replicate cap true
  clearLog : ∃ log≤cap+1,tapes 127=List.replicate log false
  right : StackAt rightStack 80 heads tapes
  continuation : StackAt continuation 81 heads tapes
  left : StackAt leftStack 82 heads tapes
  fresh : tapes 78=[]

theorem Stable.capacityHead {cap pos : ℕ} {source countWord rightStack continuation leftStack : List Bool}
    {heads : Fin 128 → ℕ} {tapes : Fin 128 → List Bool}
    (h : Stable cap source countWord pos rightStack continuation leftStack heads tapes) : heads 28=0 :=
  h.lowHeads 28 (by decide) (by decide) (by decide)

def CountAt (cap n : ℕ) (tapes : Fin 128 → List Bool) : Prop :=
  ∃ backing≤cap,tapes 79=ZeroPadding.pad backing (List.replicate n true)

theorem stable_leaf (cap : ℕ) (pre bits suffix countWord rightStack continuation leftStack : List Bool)
    (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool)
    (st : Stable cap (pre++frame bits++suffix) countWord pre.length rightStack continuation leftStack heads tapes)
    (count : CountAt cap 1 tapes)
    (hc : 3≤cap) (hbits : 2*bits.length+1≤cap)
    (hpair : PCPPairCanonical.budget (1 : ℕ).bits bits+1≤cap) :
    ∃ outHeads outTapes,
      Path 0 9 (11*cap+38) heads tapes outHeads outTapes ∧
      Stable cap (pre++frame bits++suffix) countWord (pre.length+2*bits.length+1)
        rightStack continuation leftStack outHeads outTapes ∧
      outTapes 77=ZeroPadding.pad cap (frame (Nat.pair 1 (value bits)).bits) := by
  obtain ⟨countCap,_,hcount⟩ := count
  obtain ⟨log,hlogBound,hlog⟩ := st.clearLog
  obtain ⟨out,hpath,hresult,hwork,hsource,hcountWord,hdriver,hclear,hstacks⟩ :=
    leaf_branch pre bits suffix cap log countCap heads tapes hpair hc hbits st.work st.workingHeads
      st.capacityTape hlog hcount st.sourceTape st.capacityHead st.sourceHead
  let moved := installedHeads advanceSlots heads ![pre.length+2*bits.length+1,0,0]
  refine ⟨moved,out,hpath,?_,hresult⟩
  refine ⟨hwork,st.workingHeads.advance pre bits,low_advance st.lowHeads pre bits,
    hsource.trans st.sourceTape,advance_head_source heads pre bits,hcountWord.trans st.countTape,
    (advance_head_other heads pre bits 2 (by decide)).trans st.countHead,hdriver,
    ⟨max log (cap+1),max_le hlogBound le_rfl,hclear⟩,?_,?_,?_,?_⟩
  · refine ⟨(advance_head_other heads pre bits 80 (by decide)).trans st.right.head,?_⟩
    obtain ⟨z,hz⟩ := st.right.zeros
    exact ⟨z,(hstacks 80 (by decide)).trans hz⟩
  · refine ⟨(advance_head_other heads pre bits 81 (by decide)).trans st.continuation.head,?_⟩
    obtain ⟨z,hz⟩ := st.continuation.zeros
    exact ⟨z,(hstacks 81 (by decide)).trans hz⟩
  · refine ⟨(advance_head_other heads pre bits 82 (by decide)).trans st.left.head,?_⟩
    obtain ⟨z,hz⟩ := st.left.zeros
    exact ⟨z,(hstacks 82 (by decide)).trans hz⟩
  · exact (hstacks 78 (by decide)).trans st.fresh

end NearCubicWires.RepairOrdinary.PCPTraversal
