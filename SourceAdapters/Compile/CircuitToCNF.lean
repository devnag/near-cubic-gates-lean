import Proof.Circuits.CircuitInputCNF
import Proof.Foundations.RecoverySourceSAT
import Proof.CaseAnalysis.RecoveryGraphBudgetScalar

/-!
The finished circuit-to-native-CNF tail of proof of `lem:multitape-refuter`, Step 3.
This module does not assert a general bounded-computation compiler.
Its input is an actual BooleanCircuit, and the serialization
theorem names the serializer’s raw tape layout explicitly.
The native Tseitin, decoder and serializer theorems supply the formula and encoded-size bounds.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.CircuitInputCNF
open NearCubicWires.TseitinCNF

set_option autoImplicit false

/-- proof of `lem:multitape-refuter`, Step 3: the native balanced source-oracle payload of free-input CNF. -/
def circuitSATCode {n : ℕ} (circuit : BooleanCircuit n) : ℕ :=
  RecoveryOracle.sourceSATCode (circuitInputFormula circuit)

/-- proof of `lem:multitape-refuter`, Step 3: repeated unit/binary literals give exactly three literals. -/
theorem circuitCNF_three {n : ℕ} (circuit : BooleanCircuit n) :
    ∀ clause ∈ circuitInputFormula circuit, clause.length = 3 := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using
    circuitInputFormula_threeLiteral circuit

/-- proof of `lem:multitape-refuter`, Step 3: the exact source oracle decoder accepts the emitted code. -/
theorem circuitSATCode_decode {n : ℕ} (circuit : BooleanCircuit n) :
    RecoveryOracle.decodeSourceSAT (circuitSATCode circuit) =
      some (circuitInputFormula circuit) :=
  RecoveryOracle.decodeSourceSAT_encode _

/-- proof of `lem:multitape-refuter`, Step 3: all gate constraints preserve satisfiability both ways. -/
theorem circuitSATCode_correct {n : ℕ} (circuit : BooleanCircuit n) :
    RecoveryOracle.sourceSAT (circuitSATCode circuit) = true ↔
      ∃ input : BitInput n, circuit.eval input = true := by
  exact (RecoveryOracle.sourceSAT_encode_iff _ (circuitCNF_three circuit)).trans
    (circuitInputFormula_satisfiable_iff circuit)

private theorem nodeClauses_length_le {n : ℕ} (index : ℕ) (node : BooleanNode n) :
    (circuitInputNodeClauses index node).length ≤ 3 := by
  cases node with
  | const value => cases value <;> simp [circuitInputNodeClauses]
  | input source => simp [circuitInputNodeClauses]
  | not child => simp [circuitInputNodeClauses]
  | and left right => simp [circuitInputNodeClauses]
  | or left right => simp [circuitInputNodeClauses]

private theorem nodesClauses_length_le {n : ℕ} (nodes : List (BooleanNode n))
    (start : ℕ) :
    (circuitInputNodesClausesFrom start nodes).length ≤ 3 * nodes.length := by
  induction nodes generalizing start with
  | nil => simp [circuitInputNodesClausesFrom]
  | cons node rest ih =>
      have hnode := nodeClauses_length_le start node
      have hrest := ih (start + 1)
      simp only [circuitInputNodesClausesFrom, List.length_append, List.length_cons]
      omega

/-- proof of `lem:multitape-refuter`, Step 3: linear gate-to-clause overhead, including inputs. -/
theorem circuitCNF_length {n : ℕ} (circuit : BooleanCircuit n) :
    (circuitInputFormula circuit).length ≤ n + 3 * circuit.size + 1 := by
  have h := nodesClauses_length_le circuit.nodes 0
  simp only [circuitInputFormula, List.length_append, circuitInputTautologies_length,
    List.length_singleton, BooleanCircuit.size]
  omega

/-- proof of `lem:multitape-refuter`, Step 3: explicit global polynomial native encoding bound. -/
theorem circuitSATCode_bits {n : ℕ} (circuit : BooleanCircuit n) :
    natBitLength (circuitSATCode circuit) ≤ 16000 * (n + circuit.size + 1) ^ 6 := by
  let s := n + circuit.size + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hindices : ∀ clause ∈ circuitInputFormula circuit, ∀ literal ∈ clause,
      literal.2 < n + circuit.nodes.length := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using
      circuitInputFormula_indices_lt circuit
  have hwidth : ∀ clause ∈ circuitInputFormula circuit, ∀ literal ∈ clause,
      natBitLength literal.2 ≤ s := by
    intro clause hc literal hl
    have hidx := hindices clause hc literal hl
    have hlog := Nat.log_le_self 2 literal.2
    unfold natBitLength
    dsimp [s, BooleanCircuit.size]
    omega
  have hb := RecoveryOracle.sourceSATCode_bits (circuitInputFormula circuit) s hs
    (circuitCNF_three circuit) hwidth
  have hlen : (circuitInputFormula circuit).length ≤ 3 * s := by
    have h := circuitCNF_length circuit
    dsimp [s]
    omega
  have hpow := Nat.pow_le_pow_left hlen 4
  have hsmall : (circuitInputFormula circuit).length * (16 * (s + 1)) + 1 ≤
      97 * s ^ 2 := by
    have hm := Nat.mul_le_mul_right (16 * (s + 1)) hlen
    nlinarith
  have hp : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ hs
  change natBitLength (RecoveryOracle.sourceSATCode (circuitInputFormula circuit)) ≤ _
  calc
    _ ≤ 1 + 2 * (circuitInputFormula circuit).length ^ 4 *
        ((circuitInputFormula circuit).length * (16 * (s + 1)) + 1) := hb
    _ ≤ 1 + 2 * (3 * s) ^ 4 * (97 * s ^ 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) hsmall) 1
    _ = 1 + 15714 * s ^ 6 := by ring
    _ ≤ 16000 * s ^ 6 := by omega

/-- proof of `lem:multitape-refuter`, Step 3: the serializer writes the exact framed source payload in
a global degree-48 budget. Its raw input layout is explicitly retained;
loading that layout from a bounded-computation request is still required. -/
theorem circuitSATCode_serialize {n : ℕ} (circuit : BooleanCircuit n) :
    ∃ receipt,
      run RecoveryTseitinNative.Serialize.machine
        (RecoveryBoundedGraphBudget.serializerCoefficient * (n + circuit.size + 1) ^ 48)
        (RecoveryTseitinNative.Serialize.input circuit) = some receipt ∧
      receipt.final.tapes 1504 = RepairOrdinary.frame (circuitSATCode circuit).bits ∧
      receipt.steps ≤
        RecoveryBoundedGraphBudget.serializerCoefficient * (n + circuit.size + 1) ^ 48 := by
  obtain ⟨receipt, hr, hout, hsteps⟩ := RecoveryTseitinNative.Serialize.serialize_run circuit
  have hb := RecoveryBoundedGraphBudget.serializer_scalar circuit (n + circuit.size)
    (by omega) (by dsimp [BooleanCircuit.size]; omega)
  have hm := run_moreFuel RecoveryTseitinNative.Serialize.machine _
    (RecoveryBoundedGraphBudget.serializerCoefficient * (n + circuit.size + 1) ^ 48 -
      RecoveryTseitinNative.Serialize.budget circuit) _ receipt hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨receipt, hm, hout, hsteps.trans hb⟩

end NearCubicGates.Adapters.Compile
