import Proof.MachineModel.OrdinaryMatrixDimensionField

/-! The reusable binary comparison in the numeric-dimension expansion.
The one-cell false flag is retained between unsuccessful comparisons. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnaryCompare
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity : Fin 4 → ℕ := ![0,0,1,0]

theorem compare_ready (w a b : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    ReadyRun CompetitorSignedDecision.compareMachine (4*w+4)
      ![frame (binary w a),frame (binary w b),[false],List.replicate (2*w+1) false]
      ![frame (binary w a),frame (binary w b),[decide (a≤b)],List.replicate (2*w+1) false] := by
  obtain ⟨base,hr,ht,hh,hs⟩ := CompetitorSignedDecision.compare_ready w a b ha hb
  obtain ⟨r,hp,hf,hsteps,_⟩ := ZeroPadding.run_config CompetitorSignedDecision.compareMachine
    capacity _ _ base hr
  have hi : ZeroPadding.config capacity
      (initialConfiguration CompetitorSignedDecision.compareMachine
        ![frame (binary w a),frame (binary w b),[],List.replicate (2*w+1) false]) =
      initialConfiguration CompetitorSignedDecision.compareMachine
        ![frame (binary w a),frame (binary w b),[false],List.replicate (2*w+1) false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,initialConfiguration,ZeroPadding.pad]
  rw [hi] at hp
  refine ⟨r,hp,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,ht,ZeroPadding.pad]
  · intro i; rw [hf]; exact hh i

end NearCubicWires.RepairOrdinary.MatrixUnaryCompare
