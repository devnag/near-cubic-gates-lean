import Proof.Amplification.RecoveryPCPFormulaResumeSearchCountFrame
import Proof.PCP.PCPPairReusable

/-! The schedule needs a word of length N solely to run its native-width
prefix. Reuse the original unary framer on the already produced template. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open LocalBitMultitape RepairOrdinary VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_word (N : Nat) : ClockJoin.ReadyRun RecoveryPCPFormulaResumeSearchCount.frameMachine
    (4*N+6) ![UnaryTemplate.tape N,[]]
      ![UnaryTemplate.tape N,frame (List.replicate N true)] := by
  have h:=PCPPairReusable.padded_ready RecoveryPCPFormulaResumeSearchCount.frameMachine
    (RecoveryPCPFormulaResumeSearchCount.frameInput N)
    (RecoveryPCPFormulaResumeSearchCount.frameOutput N)
    (RecoveryPCPFormulaResumeSearchCount.frame_ready N) ![N+2,0]
  have he : ZeroPadding.pad (N+2) (CompareMachine.word N)=UnaryTemplate.tape N := by
    simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  convert h using 1 <;> funext i <;> fin_cases i
  all_goals first | exact he.symm | rfl | exact (ZeroPadding.pad_zero _).symm

end NearCubicWires.RepairSource.CloseoutSchedule
