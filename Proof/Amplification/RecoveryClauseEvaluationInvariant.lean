import Proof.Amplification.RecoveryClauseEvaluationTruth

/-! The reusable clause-call invariant carries only physical source, width,
backing and reset bounds. Its preservation supplies each subsequent literal
call from the actual output of its predecessor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RepairSource.VerifierDecoding RecoveryValuationStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Extra.Valid (e : Extra) (s : State) (word : List Bool) : Prop where
  source : e.source=ZeroPadding.pad (2*e.prefixLimit+1) (frame (word.take e.prefixLimit))
  row : e.row.length ≤ 2*(s.bits.length+1)+1
  counter : e.counter.length ≤ RecoveryReusableUnpair.capacity s.bits
  count : e.binaryCount.length=s.bits.length
  committed : e.committed.length ≤ s.bits.length
  cap : e.cap ≤ 3*(s.bits.length+1)
  prefixBound : e.cap*(s.bits.length+2)+1 ≤ e.prefixLimit
  reset : RecoveryReusableUnpair.capacity s.bits+1 ≤ s.capacity

theorem lookup_cost_bound (s : State) (e : Extra) (index word : List Bool)
    (hv : e.Valid s word) (hi : index.length=s.bits.length) :
    RecoveryAssignment.cost (assignmentData s e index word) e.cap e.binaryCount e.committed e.guard ≤ 
      128*(s.bits.length+1)^2 := by
  have h := RecoveryAssignment.assignment_budget (assignmentData s e index word)
    e.binaryCount e.committed e.guard hi hv.count hv.committed
  have hm := Nat.mul_le_mul_right (RecoveryValuationStream.budget s.bits.length+6) hv.cap
  simp only [RecoveryAssignment.cost,RecoveryValuationCount.limit,RecoveryValuationStream.budget,assignmentData] at h hm ⊢
  omega

theorem assignment_cost_bound (s : State) (e : Extra) (index word : List Bool)
    (hv : e.Valid s word) (hi : index.length=s.bits.length) :
    assignmentCost s e index word ≤ 32768*(s.bits.length+1)^2 := by
  have h := lookup_cost_bound s e index word hv hi
  have hp : 0<(s.bits.length+1)^2 := by positivity
  unfold assignmentCost RecoveryReusableUnpair.capacity RecoveryTapeSupport.capacity
  nlinarith

theorem assigned_valid (s : State) (which : Fin 3) (out : Data)
    (hv : s.Valid) (hi : out.index.length=s.bits.length) : (assignedState s which out).Valid := by
  constructor
  · exact hv.1
  · intro j
    by_cases hj : j=which
    · subst j; simp [assignedState,hi]
    · simpa [assignedState,hj] using hv.2 j

theorem assigned_extra_valid (s : State) (e : Extra) (which : Fin 3) (word : List Bool)
    (count : Nat) (out : Data) (guard : Bool) (hv : e.Valid s word)
    (hc : count ≤ e.cap) (hr : out.row.length ≤ 2*(s.bits.length+1)+1) :
    (assignedExtra e s count out guard).Valid (assignedState s which out) word := by
  have hcount : count+1 ≤ RecoveryReusableUnpair.capacity s.bits := by
    have h := (RecoveryAssignment.scratch_fits s.bits.length).1
    have hcap := hv.cap
    change count+1 ≤ 8192*(s.bits.length+1)^2
    omega
  refine ⟨hv.source,hr,?_,hv.count,hv.committed,hv.cap,hv.prefixBound,hv.reset⟩
  simp [assignedExtra,assignedState,ZeroPadding.pad_length,CompareMachine.word,Nat.max_eq_left hcount]

theorem checked_extra_valid (s : State) (e : Extra) (which : Fin 3) (literal word : List Bool)
    (hv : e.Valid s word) : e.Valid (RecoveryCheckedLiteral.checkedState s which literal) word := by
  refine ⟨hv.source,hv.row,hv.counter,hv.count,hv.committed,hv.cap,hv.prefixBound,?_⟩
  exact hv.reset.trans ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))

theorem truth_valid (s : State) (e : Extra) (word : List Bool)
    (hs : s.Valid) (he : e.Valid s word) :
    (truthState s e).Valid ∧ (truthExtra s e).Valid (truthState s e) word := by
  exact ⟨hs,⟨he.source,he.row,he.counter,he.count,he.committed,he.cap,he.prefixBound,he.reset⟩⟩

end NearCubicWires.RepairOrdinary.RecoveryClauseEvaluation
