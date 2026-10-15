import Proof.Hierarchy.CompetitorReusableMonomial

/-! Reuse a stable runtime unary width by a paid physical scan. The target
and both local zero work tapes are the outputs of the preceding clear. -/
namespace NearCubicWires.RepairOrdinary.CompetitorUnaryWidthCopy
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w cap : ℕ) : Fin 4 → List Bool :=
  ![List.replicate w true,List.replicate cap false,List.replicate cap false,List.replicate cap false]
def output (w cap : ℕ) : Fin 4 → List Bool :=
  ![List.replicate w true,List.replicate cap false,ZeroPadding.pad cap (List.replicate w true),List.replicate cap false]

theorem copy_ready (w cap : ℕ) (hc : w+2≤cap) :
    ClockJoin.ReadyRun ClockUnarySum.machine (2*w+6) (input w cap) (output w cap) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := ClockUnarySum.sum_ready w 0
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config ClockUnarySum.machine ![0,cap,cap,cap] _ _ base hr
  have hi : ZeroPadding.config ![0,cap,cap,cap]
      (initialConfiguration ClockUnarySum.machine ![List.replicate w true,List.replicate 0 true,[],[]])=
      initialConfiguration ClockUnarySum.machine (input w cap) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [input,ZeroPadding.config,initialConfiguration,ZeroPadding.pad]
  rw [hi] at hrun
  simp only [Nat.add_zero] at hrun hs
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,ht,output,pad_zeros,max_eq_left hc]
    simp [ZeroPadding.pad]
  · intro i
    rw [hf]
    exact hh i

end NearCubicWires.RepairOrdinary.CompetitorUnaryWidthCopy
