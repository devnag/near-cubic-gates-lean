import Proof.CaseAnalysis.CloseoutWitnessTraversal

/-! Complete all-raw-input halting for the fixed shared traversal. The
decoder bank is prepared; the outer cold producer pays that bank separately. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open CanonicalBinaryProgram PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def traversalBudget (w : ℕ) := (w+1)*nodeBudget w+3

theorem traversalBudget_bound (w : ℕ) : traversalBudget w≤262200*(w+1)^3 := by
  unfold traversalBudget nodeBudget
  nlinarith

theorem raw_space (x : State) (hx:x.Valid) (hstack:x.stack=[false]) :
    x.stack.length+(tree (value x.core.bits)).nodeCount*(2*x.core.bits.length+2)≤x.capacity := by
  have hn:=Nat.mul_le_mul_right (2*x.core.bits.length+2) (word_nodes x.core.bits)
  have hc:=hx.2.1
  simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity] at hc
  rw [hstack,List.length_singleton]
  nlinarith

theorem traversal_run (x : State) (hx:x.Valid) (hstack:x.stack=[false]) :
    ∃ y r,Visit (tree (value x.core.bits)) x y ∧
      runFrom machine (traversalBudget x.core.bits.length) (x.cfg machine.start)=some r ∧
      r.steps≤traversalBudget x.core.bits.length ∧
      r.final.heads=y.heads ∧ r.final.tapes=y.tapes := by
  obtain ⟨y,hy⟩:=visit (tree (value x.core.bits)) x hx rfl (raw_space x hx hstack)
  obtain ⟨last,hl,lf,_⟩:=peek_empty y (hy.stack.trans hstack)
  obtain ⟨m,hm,hstop⟩:=stop_receipt sizes programs 0 next 5 2
    (y.cfg (programs 5).start) last hl (by rw [lf];rfl)
  rw [lf] at hstop
  obtain ⟨n,hn,hpath⟩:=hy.path
  have whole:Timed machine (n+m) (x.cfg machine.start)
      (RecoveryCalls.stopped sizes y.heads y.tapes):=hpath.trans hstop
  obtain ⟨r,hr,hf,hs⟩:=whole.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hb:n+m≤traversalBudget x.core.bits.length:=by
    have hnodes:=Nat.mul_le_mul_right (nodeBudget x.core.bits.length) (word_nodes x.core.bits)
    unfold traversalBudget
    omega
  have more:=runFrom_moreFuel machine (n+m) (traversalBudget x.core.bits.length-(n+m)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨y,r,hy,more,hs.le.trans hb,by rw [hf];rfl,by rw [hf];rfl⟩

theorem canonical_traversal (x : State) (values : List ℕ) (hx:x.Valid)
    (hstack:x.stack=[false]) (hcode:value x.core.bits=CanonicalBinary.encodeBalancedList values) :
    ∃ r,runFrom machine (traversalBudget x.core.bits.length) (x.cfg machine.start)=some r ∧
      r.steps≤262200*(x.core.bits.length+1)^3 ∧
      r.final.tapes 27=x.out++atomStream x.core.bits.length values ∧
      r.final.tapes 28=List.replicate (x.count+values.length) true ∧
      r.final.heads 26=1 := by
  obtain ⟨y,r,hy,hr,hs,rh,rt⟩:=traversal_run x hx hstack
  have ha:(tree (value x.core.bits)).atoms=values:=by rw [hcode,tree_atoms]
  refine ⟨r,hr,hs.trans (traversalBudget_bound _),?_,?_,?_⟩
  · rw [rt]
    change y.out=_
    rw [hy.out,ha]
  · rw [rt]
    change List.replicate y.count true=_
    rw [hy.count,ha]
  · rw [rh]
    change y.stack.length=1
    rw [hy.stack,hstack]
    rfl

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
