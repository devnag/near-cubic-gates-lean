import Proof.CaseAnalysis.RecoveryGraphBudgetResources

/-! The explicit support sum can be funded by one ordinary polynomial in
an already paid coarse W, after the caller proves actual source dominance. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
open RepairSource ProjectionNormalization PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem support_bound (W R Q bound : ℕ) (source : List Bool)
    (hR : R ≤ W) (hQ : Q ≤ W) (hb : bound ≤ W)
    (hs : source.length ≤ W) (htwo : 2^R ≤ W) :
    support W R Q bound source ≤ 10000000000*(W+1)^6 := by
  have hcap : RecoveryProjectionRows.capacity R ≤ 1048576*(W+1)^4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) 4)
  have hp := Nat.mul_le_mul hQ (Nat.add_le_add_right
    (Nat.mul_le_mul hR (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hcap) 11)) 8)
  simp only [←Nat.mul_assoc] at hp
  have hqr := Nat.mul_le_mul hQ hR
  have hstack := Nat.mul_le_mul_right (2*W+1) (show bound+W ≤ 2*W by omega)
  have hsave := Nat.mul_le_mul_right (2*W+1) (show bound+2^R+1 ≤ 2*W+1 by omega)
  have hupper : support W R Q bound source ≤
      16384*(W+1)^2+1+8388608*(W+1)^3+268435600*(W+1)^4+(W+7)+
      W*(6*(W+W+5)+3)+W+W*W+
      (W*(W*(4*1048576*(W+1)^4+11)+8)+5)+
      (2*W)*(2*W+1)+(2*W+1)*(2*W+1) := by
    unfold support RecoveryProjectionRowsRewind.batchBudget RecoveryBoundedSelectorLoop.capacity
    omega
  apply hupper.trans
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3),Nat.zero_le (W^4),
    Nat.zero_le (W^5),Nat.zero_le (W^6)]

theorem support_sourcePoly {width randomness queries bound : ℕ→ℕ}
    (source : ℕ→List Bool) (hw : SourcePoly width) (hr : SourcePoly randomness)
    (hq : SourcePoly queries) (hb : SourcePoly bound)
    (hs : SourcePoly (fun n=>(source n).length))
    (htwo : SourcePoly (fun n=>2^randomness n)) :
    SourcePoly (fun n=>support (width n) (randomness n) (queries n) (bound n) (source n)) := by
  have hcap := (sourcePoly_pow (hw.add (polyDominated_const 1)) 2).const_mul 16384
  have hd := (sourcePoly_pow (hw.add (polyDominated_const 1)) 3).const_mul 8388608
  have hl := (sourcePoly_pow (hw.add (polyDominated_const 1)) 4).const_mul 268435600
  have hg := hw.mul ((((hw.add hw).add (polyDominated_const 5)).const_mul 6).add (polyDominated_const 3))
  have hp : SourcePoly (fun n=>RecoveryProjectionRowsRewind.batchBudget (randomness n) (queries n)+2) :=
    ((hq.mul ((hr.mul ((((sourcePoly_pow (hr.add (polyDominated_const 1)) 4).const_mul 1048576).const_mul 4).add
      (polyDominated_const 11))).add (polyDominated_const 8))).add (polyDominated_const 3)).add
        (polyDominated_const 2)
  have hfactor := (hw.const_mul 2).add (polyDominated_const 1)
  exact (((((((((hcap.add (polyDominated_const 1)).add hd).add hl).add
    (hw.add (polyDominated_const 7))).add hg).add hs).add (hq.mul hr)).add hp).add
      ((hb.add hw).mul hfactor)).add (((hb.add htwo).add (polyDominated_const 1)).mul hfactor)

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphBudget
