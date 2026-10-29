import SourceAdapters.ShortPCP.Assembly
import SourceAdapters.ShortPCP.MaskMachine
import SourceAdapters.ShortPCP.TimeCells
import SourceAdapters.Compile.OraclePrintMain
import SourceAdapters.RAMACSP.Assembly
import SourceAdapters.RAMACSP.GenSize
import SourceAdapters.RAMACSP.GenTFinal
import SourceAdapters.RAMACSP.GenItemsFinal
import SourceAdapters.Routing.TermsMachineFinal
import SourceAdapters.Routing.CoordinateMachineFinal

/-!
# Input 6: the short PCP as an oracle circuit (ordinary machine model)

`OrdinaryOracleCircuitPCP` (`Assembly/OrdinaryField.lean`; the `shortPCP` field type of the release statement) from
BCGT13 Theorem 11.1 and the deterministic irreducible-polynomial algorithm (BCGT13 Algorithm 17), by the proof of
`thm:short-pcp-ours`. Everything else is proved:
- Step 1 (`thm:embedding`, `lem:generator`): the affine constraint reduction of every bounded ordinary verifier
  (`ownReduction`): the event trace, the affine embedding equivalence, the parameter size, and the generator machine
  (the compiled-circuit printer `Routing.TermsMachine.termsCircuitWF`, the machine-items printer
  `RAMACSP.Gen.Items.machineItemsWF`, the coordinate array `Routing.CoordinateMachine.coordinateArrayWF`);
- Step 2: the single-run and amplified verifiers from BCGT13 Theorem 11.1 (`ShortPCP.OracleCircuitPCP.shortPCP_ordinary_of_leaves`)
  and the single-run verifier's implementation (`ShortPCP.Time.singleRunTime`);
- Step 3: the mask machine (`ShortPCP.MaskMachine.maskMachine`);
- Step 4: the bounded computation-to-circuit compiler (`Compile.OraclePrint.computationToCircuit`) and the top-level
  ordinary machine (`ShortPCP.OracleCircuitPCP.assemblyMachine`).
-/

namespace NearCubicGates.Adapters.Assembly

/-- The affine constraint reduction of every bounded ordinary verifier (proof of `thm:short-pcp-ours`, Step 1), from
the irreducible-polynomial algorithm alone. -/
theorem ownReduction (hIrr : NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17) :
    ∀ V, NearCubicGates.Adapters.Joins.AffineConstraintReduction V :=
  NearCubicGates.Adapters.RAMACSP.affineConstraint_ownReduction_of_SG hIrr NearCubicGates.Adapters.RAMACSP.parameterSize
    (NearCubicGates.Adapters.RAMACSP.generatorMachine_of_joins
      NearCubicGates.Adapters.Routing.TermsMachine.termsCircuitWF
      (fun irrPoly V hI hP => NearCubicGates.Adapters.RAMACSP.Gen.Items.machineItemsWF V irrPoly hP hI
        NearCubicGates.Adapters.Routing.CoordinateMachine.coordinateArrayWF))

/-- **Input 6 in the ordinary model** from BCGT13 Theorem 11.1 and the irreducible-polynomial algorithm. -/
theorem field6Ordinary (h11 : NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1)
    (hIrr : NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17) :
    OrdinaryOracleCircuitPCP :=
  NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP.shortPCP_ordinary_of_leaves h11 (ownReduction hIrr)
    NearCubicGates.Adapters.ShortPCP.Time.singleRunTime NearCubicGates.Adapters.Compile.OraclePrint.computationToCircuit
    NearCubicGates.Adapters.ShortPCP.MaskMachine.maskMachine NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP.assemblyMachine

end NearCubicGates.Adapters.Assembly
