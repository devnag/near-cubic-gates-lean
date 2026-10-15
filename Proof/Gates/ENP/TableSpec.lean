import Proof.Gates.Interfaces.Transfer
import Proof.CaseAnalysis.RecoverySearchJoin

set_option autoImplicit false

namespace NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairSource NearCubicWires.Bindings.MW20

/-- **Stage 2** (paper §11.6): the first honest oracle table of an oracle circuit, by SAT prefix self-reduction. -/
structure TStage where
  program : OrdinaryOracleProgram
  inPort : Fin program.base.tapeCount
  /-- The input word is not on the shared query tape (the stages of the common program share one query tape). -/
  inQuery : inPort ≠ program.queryTape
  flagPort : Fin program.base.tapeCount
  tablePort : Fin program.base.tapeCount
  /-- The table is not on the shared query tape (stage 3 reads it after the query tape has been reused). -/
  tableQuery : tablePort ≠ program.queryTape
  K : ℕ
  e : ℕ
  run : ∀ (o : OracleOutput) (post : List Bool),
    ∃ c ≤ K * (2 ^ o.ell + (o.word ++ post).length + 1) ^ e, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat program c
        (initialConfiguration program.base.machine (fun i => if i = inPort then o.word ++ post else [])) final ∧
      program.base.machine.halted final.control = true ∧
      (readTapeBit (final.tapes flagPort) 0 = true ↔ ∃ t, Transfer.HonestTable o.circuit t) ∧
      (∀ first : Transfer.FirstTable o.circuit,
        final.tapes tablePort = RepairOrdinary.frame (List.ofFn first.table)) ∧
      final.heads flagPort = 0 ∧ final.heads tablePort = 0 ∧
      (final.tapes program.queryTape).length ≤ c ∧ final.heads program.queryTape = 0

/-- The stage-2 producer exists (proved in `ENP.TStage`). -/
def TStageRuns : Prop := Nonempty TStage

end NearCubicGates.Close.ENP
