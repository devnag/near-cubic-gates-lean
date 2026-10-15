import Proof.Amplification.RecoveryTseitinNativeCore

/-! A genuinely cold ordinary supplier of the original free-input circuit
formula. Only the raw arity, native original graph, raw original output index
and raw node count enter; every capacity, sentinel and scratch bank is made. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=wholeMachine prefixMachine Formula.machine
def budget (n count : Nat):=wholeBudget (prefixBudget n count) (Formula.budget n count) (Reuse.capacity n count)
def circuitInput {n : Nat} (circuit : BooleanCircuit n) : Fin 1370→List Bool :=
  input n circuit.nodes.length circuit.output.val (Reuse.source [] [] circuit.nodes)
theorem cold_run {n : Nat} (circuit : BooleanCircuit n) : ∃ r,
    run machine (budget n circuit.nodes.length) (circuitInput circuit)=some r ∧
      r.final.heads 1333=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length ∧
      r.final.tapes 1333=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit) ∧
      r.steps ≤ budget n circuit.nodes.length :=
  whole_core prefixMachine Formula.machine (prefixBudget n circuit.nodes.length)
    (Formula.budget n circuit.nodes.length) (Reuse.capacity n circuit.nodes.length)
    n circuit.nodes.length circuit.output.val (Reuse.source [] [] circuit.nodes)
    (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit))
    (prefix_run n circuit.nodes.length circuit.output.val (Reuse.source [] [] circuit.nodes))
    (Formula.formula_run circuit [] [])

theorem drivers_forward : CursorRestore.NoLeft driversMachine (1333 : Fin 1370) :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.unselected_forward sumSlots _ _ (by decide))
      (EquationRowCuts.unselected_forward powerSlots _ _ (by decide)))
    (EquationRowCuts.unselected_forward countSlots _ _ (by decide))
theorem prefix_forward : CursorRestore.NoLeft prefixMachine (1333 : Fin 1370) :=
  CursorRestore.composition_forward _ _ _ drivers_forward
    (CursorRestore.focus_forward tautSlots taut_injective tautMachine 239 taut_forward)
theorem output_forward : CursorRestore.NoLeft machine (1333 : Fin 1370) :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (CursorRestore.composition_forward _ _ _ prefix_forward cold_erase_forward) enter_forward)
    (CursorRestore.focus_forward formulaSlots formula_injective Formula.machine 1333 Formula.output_forward)

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
