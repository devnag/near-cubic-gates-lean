import Proof.CaseAnalysis.RowsEstimatorDriverCalls

/-! Actual paid unary reset-driver production from d,p,G,C.
The original scalar inputs survive and the returned word is exact Driver.value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready (a : WilliamsAlgorithm) (d p G C : ℕ) : ∃ out,
    ClockJoin.ReadyRun (machine a) (budget a d p G C) (input a d p G C) out ∧
      (∀ i,i.val<4 → out i=input a d p G C i) ∧
      out (output a)=List.replicate (Driver.value a d p G C) true := by
  obtain ⟨x0,r0,k0,f0,v0⟩ := run0 a d p (input a d p G C)
    (by
      change (input a d p G C) ⟨0,by dsimp [tapes];omega⟩=List.replicate d true
      rfl)
    (by
      change (input a d p G C) ⟨1,by dsimp [tapes];omega⟩=List.replicate p true
      rfl)
    (by intro i hi;simp [input,show i.val≠0 by omega,show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega])
  obtain ⟨x1,r1,k1,f1,v1⟩ := run1 a (d+p) G x0
    (by
      change x0 ⟨6,by dsimp [tapes];omega⟩=List.replicate (d+p) true
      exact v0)
    (by
      change x0 ⟨2,by dsimp [tapes];omega⟩=List.replicate G true
      rw [k0 _ (by dsimp;omega)]
      rfl)
    f0
  obtain ⟨x2,r2,k2,f2,v2⟩ := run2 a C x1
    (by
      change x1 ⟨3,by dsimp [tapes];omega⟩=List.replicate C true
      rw [k1 _ (by dsimp;omega)]
      rw [k0 _ (by dsimp;omega)]
      rfl)
    f1
  obtain ⟨x3,r3,k3,f3,v3⟩ := run3 a (d+p+G) x2
    (by
      change x2 ⟨10,by dsimp [tapes];omega⟩=List.replicate (d+p+G) true
      rw [k2 _ (by dsimp;omega)]
      exact v1)
    f2
  obtain ⟨x4,r4,k4,f4,v4⟩ := run4 a (d+p) x3
    (by
      change x3 ⟨6,by dsimp [tapes];omega⟩=List.replicate (d+p) true
      rw [k3 _ (by dsimp;omega)]
      rw [k2 _ (by dsimp;omega)]
      rw [k1 _ (by dsimp;omega)]
      exact v0)
    f3
  obtain ⟨x5,r5,k5,f5,v5⟩ := run5 a d x4
    (by
      change x4 ⟨0,by dsimp [tapes];omega⟩=List.replicate d true
      rw [k4 _ (by dsimp;omega)]
      rw [k3 _ (by dsimp;omega)]
      rw [k2 _ (by dsimp;omega)]
      rw [k1 _ (by dsimp;omega)]
      rw [k0 _ (by dsimp;omega)]
      rfl)
    f4
  obtain ⟨x6,r6,k6,f6,v6⟩ := run6 a (2^d) x5
    (by
      change x5 ⟨75+2*e a,by dsimp [tapes];omega⟩=UnaryTemplate.tape (2^d)
      exact v5)
    f5
  obtain ⟨x7,r7,k7,f7,v7⟩ := run7 a (Driver.tableCoefficient a*(d+p+1)^(e a)) x6
    (by
      change x6 ⟨51+2*e a,by dsimp [tapes];omega⟩=List.replicate (Driver.tableCoefficient a*(d+p+1)^(e a)) true
      rw [k6 _ (by dsimp;omega)]
      rw [k5 _ (by dsimp;omega)]
      exact v4)
    f6
  obtain ⟨x8,r8,k8,f8,v8⟩ := run8 a ((2^d)^2) (Driver.tableCoefficient a*(d+p+1)^(e a)) x7
    (by
      change x7 ⟨82+2*e a,by dsimp [tapes];omega⟩=List.replicate ((2^d)^2) true
      rw [k7 _ (by dsimp;omega)]
      exact v6)
    (by
      change x7 ⟨85+2*e a,by dsimp [tapes];omega⟩=UnaryTemplate.tape (Driver.tableCoefficient a*(d+p+1)^(e a))
      exact v7)
    f7
  obtain ⟨x9,r9,k9,f9,v9⟩ := run9 a (64*(C+1)) (2000000*(d+p+G+1)^3) x8
    (by
      change x8 ⟨17,by dsimp [tapes];omega⟩=List.replicate (64*(C+1)) true
      rw [k8 _ (by dsimp;omega)]
      rw [k7 _ (by dsimp;omega)]
      rw [k6 _ (by dsimp;omega)]
      rw [k5 _ (by dsimp;omega)]
      rw [k4 _ (by dsimp;omega)]
      rw [k3 _ (by dsimp;omega)]
      simpa only [pow_one] using v2)
    (by
      change x8 ⟨37,by dsimp [tapes];omega⟩=List.replicate (2000000*(d+p+G+1)^3) true
      rw [k8 _ (by dsimp;omega)]
      rw [k7 _ (by dsimp;omega)]
      rw [k6 _ (by dsimp;omega)]
      rw [k5 _ (by dsimp;omega)]
      rw [k4 _ (by dsimp;omega)]
      exact v3)
    f8
  obtain ⟨x10,r10,k10,f10,v10⟩ := run10 a ((64*(C+1))+(2000000*(d+p+G+1)^3)) ((2^d)^2*(Driver.tableCoefficient a*(d+p+1)^(e a))) x9
    (by
      change x9 ⟨93+2*e a,by dsimp [tapes];omega⟩=List.replicate ((64*(C+1))+(2000000*(d+p+G+1)^3)) true
      exact v9)
    (by
      change x9 ⟨89+2*e a,by dsimp [tapes];omega⟩=List.replicate ((2^d)^2*(Driver.tableCoefficient a*(d+p+1)^(e a))) true
      rw [k9 _ (by dsimp;omega)]
      exact v8)
    f9
  refine ⟨x10,?_,?_,?_⟩
  · exact (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ r0 r1) r2) r3) r4) r5) r6) r7) r8) r9) r10)
  · intro i hi
    rw [k10 i (by omega)]
    rw [k9 i (by omega)]
    rw [k8 i (by omega)]
    rw [k7 i (by omega)]
    rw [k6 i (by omega)]
    rw [k5 i (by omega)]
    rw [k4 i (by omega)]
    rw [k3 i (by omega)]
    rw [k2 i (by omega)]
    rw [k1 i (by omega)]
    rw [k0 i (by omega)]
  · change x10 ⟨97+2*e a,by dsimp [tapes];omega⟩=_
    rw [v10]
    congr 1
    unfold Driver.value Driver.tableValue
    ring

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverLayout
