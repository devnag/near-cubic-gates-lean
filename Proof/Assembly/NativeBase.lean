import Proof.Assembly.OrderedCallsSelectedInputs
import Proof.MachineModel.ControllerCappedRuntime
import Proof.MachineModel.TopDownPaidFamilySum
import Proof.Hierarchy.CompetitorRawRecordEmit
import Proof.CaseAnalysis.FinalSingleAppend
import Proof.MachineModel.TopDownPaidFamilyReserves
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

namespace NativeRecipes

noncomputable abbrev f_raw (a : WilliamsAlgorithm) := (P1TopDownPaidReusable.outputSlot a).castAdd 1

noncomputable abbrev f_entry (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B N : Nat) :=
  RepeatMachine.cfg 0 (P1TopDownPaidReusable.source a ds S R B 0 []) N 1

noncomputable abbrev f_after (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B b : Nat) (xs : List Nat) :=
  RepeatMachine.cfg 3 (P1TopDownPaidReusable.source a ds S R B xs.length (CompetitorCountFold.raw b xs)) xs.length 1

noncomputable abbrev f_machine (a : WilliamsAlgorithm) :=
  Composition.machine (TapeEmbedding.machine 11 (familyWriter (P1TopDownPaidReusable.machine a)))
    (P1TopDownPaidFamilySum.machine (f_raw a))

noncomputable abbrev f_budget (a : WilliamsAlgorithm) (S b v N : Nat) :=
  familyFuel N ((3*P1TopDownPaidPayload.tapes a+6)*(S+1))+1+P1TopDownPaidFamilySum.budget b v N

noncomputable abbrev _e_fields (b : Nat) (e : Stream.Entry) : Fin 10 → List Bool :=
 Fin.addCases (m:=6) (n:=4) (motive:=fun _=>List Bool) (Stream.recordFields b e.coefficient e.count e.denominator) (fun _ : Fin 4 => [])

noncomputable abbrev e_order : List (Fin 10) := [0,1,2,3,4,5]

noncomputable abbrev e_base (b : Nat) (e : Stream.Entry) (D cap : Nat) (payload : List Bool) : Fin 10 → List Bool :=
 Fin.addCases (m:=6) (n:=4) (motive:=fun _=>List Bool) (fun i : Fin 6 => RepairOrdinary.frame (Stream.recordFields b e.coefficient e.count e.denominator i))
   (![payload,List.replicate cap false,List.replicate D true,List.replicate (D+1) false] : Fin 4 → List Bool)

noncomputable abbrev e_emitCost (b : Nat) := 40*b+56

noncomputable abbrev e_bank (b : Nat) (e : Stream.Entry) (D cap : Nat) (payload : List Bool) : Fin 11 → List Bool :=
 Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool) (e_base b e D cap payload) (fun _ : Fin 1 => List.replicate (e_emitCost b) false)

noncomputable abbrev e_raw := listProgram (6 : Fin 10) 7 e_order

noncomputable abbrev e_emit := MaskedReset.machine e_raw (fun _ => true)

noncomputable abbrev e_eraseSlots : Fin 3 → Fin 11 := ![6,8,9]

noncomputable abbrev e_erase := RecoveryFocus.machine e_eraseSlots (RecoveryScratchErase.resetMachine 1)

noncomputable abbrev e_machine := Composition.machine e_erase e_emit

noncomputable abbrev r_tapes (a : WilliamsAlgorithm) := P1TopDownPaidPayload.tapes a+1+2+4+1+11

noncomputable abbrev r_inputH (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B N : Nat) : Fin (r_tapes a)→Nat :=
 Fin.addCases (f_entry a ds S R B N).heads (fun _ : Fin 11=>0)

noncomputable abbrev r_inputT (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B b v N : Nat) : Fin (r_tapes a)→List Bool :=
 Fin.addCases (f_entry a ds S R B N).tapes (P1TopDownPaidFamilySum.extra b v N)

noncomputable abbrev r_outputH (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B b : Nat) (xs : List Nat) : Fin (r_tapes a)→Nat :=
 P1TopDownPaidFamilySum.finalHeads (f_raw a) (f_after a ds S R B b xs).heads

noncomputable abbrev r_outputT (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B b v : Nat) (xs : List Nat)
 (Z : Fin 10→List Bool) : Fin (r_tapes a)→List Bool :=
 P1TopDownPaidFamilySum.final (f_raw a) (f_after a ds S R B b xs).tapes b v xs Z

end NativeRecipes
