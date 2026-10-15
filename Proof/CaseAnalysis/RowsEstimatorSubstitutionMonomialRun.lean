import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomial

/-! An actual halted monomial receipt exposes the reusable accumulator bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
open SubstitutionFactor (data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem repeat_entry {t s : ℕ} (p : Machine t s) (port : Fin t) (H : Fin t → ℕ) (A : Fin t → List Bool) :
    SubstitutionRepeat.entry p 0 H A=(⟨(SubstitutionRepeat.machine p port).start,H,A⟩ : Configuration t _) := rfl

theorem run (C R : ℕ) (cs : List Pair) (m : List ℕ) (valid : Valid cs m)
    (pre tail : List Bool) (acc : List (List ℕ)) (hcache : SubstitutionCache.capacity cs ≤ C)
    (hf : Fits C R cs m valid acc) :
    Step machine (budget R cs m valid acc) (heads pre.length)
      (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) [] (ExtIncidence.stream acc) [])
      (heads (pre.length+(m.flatMap ExtIncidence.block).length))
      (data C (pre++m.flatMap ExtIncidence.block++false::tail) (cacheWord cs) [] (ExtIncidence.stream (value cs m valid acc)) []) := by
  obtain ⟨time,ht,tr⟩:=remaining C R cs m valid pre tail acc hcache hf
  obtain ⟨r,hr,rf,_⟩:=tr.run (by simp [machine,SubstitutionRepeat.machine,SubstitutionRepeat.final,
    RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel machine time (budget R cs m valid acc-time) _ r hr
  rw [Nat.add_sub_of_le ht,repeat_entry _ 0] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
