import Proof.MachineModel.OrdinaryMatrixBucketRootCalls

namespace NearCubicWires.RepairOrdinary.MatrixBucketRootLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open MatrixScoreReusableRanks (D)
open MatrixBucketRootCalls (machine boundary result)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def roundBudget (r : Request) := 6*D r+30
def budget (r : Request) := (r.U+1)*roundBudget r

theorem loop_timed (r : Request) (remaining c cap : ℕ) (backing : Fin 23 → List Bool)
    (hb : ∀ i,(backing i).length≤D r) (hc : 1≤c)
    (hcount : c+remaining=MatrixBucketDimensions.capacity r.U) :
    ∃ work : Fin 23 → List Bool,(∀ i,(work i).length≤D r) ∧
      ∃ time≤(remaining+1)*roundBudget r,Timed machine time
        (boundary 0 r c cap backing) (result r (max cap (D r+1)) work) := by
  induction remaining generalizing c cap backing with
  | zero =>
    have he : c=MatrixBucketDimensions.capacity r.U := by omega
    subst c
    obtain ⟨work,hw,time,ht,hprefix⟩ := MatrixBucketRootCalls.test_finish r cap backing hb
    refine ⟨work,hw,time,?_,hprefix⟩
    unfold roundBudget MatrixBucketRootTest.budget at *
    omega
  | succ remaining ih =>
    have hlt : c<MatrixBucketDimensions.capacity r.U := by omega
    obtain ⟨tested,hw,t0,h0,p0⟩ := MatrixBucketRootCalls.test_continue r c cap backing hb hc hlt
    obtain ⟨t1,h1,p1⟩ := MatrixBucketRootCalls.increment_call r c (max cap (D r+1)) tested
    obtain ⟨work,hwork,t2,h2,p2⟩ := ih (c+1) (max cap (D r+1)) tested hw (by omega) (by omega)
    have hD : 104000*(r.U+1)≤D r := (MatrixBatchCapacity.request_capacity r).2
    have hU : c≤r.U := hlt.le.trans (MatrixBucketDimensions.capacity_le r.U)
    have hround : t0+t1≤roundBudget r := by
      unfold MatrixBucketRootTest.budget at h0
      unfold roundBudget
      omega
    have hall := (p0.trans p1).trans p2
    refine ⟨work,hwork,t0+t1+t2,?_,?_⟩
    · simp only [Nat.add_mul,Nat.one_mul] at *
      omega
    · simpa only [Nat.max_assoc,Nat.max_self] using hall

theorem search_run (r : Request) (cap : ℕ) (backing : Fin 23 → List Bool)
    (hb : ∀ i,(backing i).length≤D r) :
    ∃ work : Fin 23 → List Bool,(∀ i,(work i).length≤D r) ∧
      ∃ actual,runFrom machine (budget r) (boundary 0 r 1 cap backing)=some actual ∧
        actual.final=result r (max cap (D r+1)) work ∧ actual.steps≤budget r := by
  have hc := MatrixBucketDimensions.capacity_positive r.U Nat.one_le_two_pow
  obtain ⟨work,hw,time,ht,hprefix⟩ := loop_timed r (MatrixBucketDimensions.capacity r.U-1) 1 cap backing hb
    (by decide) (by omega)
  obtain ⟨actual,ha,hf,hs⟩ := hprefix.run
    (by simp [machine,MatrixBucketRootCalls.machine,result,MatrixBucketRootCalls.result,
      RecoveryCalls.machine,RecoveryCalls.stopped])
  have hbound : time≤budget r := by
    have hle := MatrixBucketDimensions.capacity_le r.U
    have hm := Nat.mul_le_mul_right (roundBudget r)
      (show MatrixBucketDimensions.capacity r.U-1+1≤r.U+1 by omega)
    exact ht.trans hm
  have he := runFrom_moreFuel machine time (budget r-time) _ actual ha
  rw [Nat.add_sub_of_le hbound] at he
  exact ⟨work,hw,actual,he,hf,hs.trans_le hbound⟩

end NearCubicWires.RepairOrdinary.MatrixBucketRootLoop
