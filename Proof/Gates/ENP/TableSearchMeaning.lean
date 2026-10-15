import Proof.Gates.ENP.TableSpecParts

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TableSearch

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.RepairSource
open NearCubicWires.CanonicalRecoveryLanguage NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputCNF NearCubicWires.TseitinCNF NearCubicWires.BalancedCNFSATEncoding

variable {ℓ : ℕ} (C : OracleCircuit ℓ ℓ)

/-- **Honest tables are the inputs `c_T` accepts** (paper §11.6 stage 2: the constraints `C^O(R) = 0` for all `R`). -/
theorem honest_iff (t : BitInput (2 ^ ℓ)) : Transfer.HonestTable C t ↔ (TCirc.tCircuit C).eval t = true := by
  rw [TCirc.tCircuit_eval]
  rfl

/-- The first honest table is the lex-least input accepted by `c_T`. -/
def firstInput (first : Transfer.FirstTable C) : FirstInput (TCirc.tCircuit C) where
  input := first.table
  accepts := (honest_iff C _).mp first.honest
  minimal := fun x hx => first.minimal x ((honest_iff C x).mpr hx)

/-- **The stage-2 flag** (paper §11.6 stage 2: "finds the first oracle `O*`", or there is none): the corrected SAT
oracle on the uncommitted query of `c_T`'s input formula. -/
theorem flag_eq :
    RecoveryOracle.correctedSat (RecoveryQuery.code true
      (RecoveryFormulaPrefix.payload (circuitInputFormula (TCirc.tCircuit C))) 0 0) = true ↔
      ∃ t, Transfer.HonestTable C t := by
  rw [circuit_query, decide_eq_true_iff]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x, (honest_iff C x).mpr hx⟩
  · rintro ⟨t, ht⟩; exact ⟨t, (honest_iff C t).mp ht⟩

theorem search_eq (first : Transfer.FirstTable C) :
    RecoveryPrefixBody.search true (RecoveryFormulaPrefix.payload (circuitInputFormula (TCirc.tCircuit C))) (2 ^ ℓ) [] =
      List.ofFn first.table := by
  let c := TCirc.tCircuit C
  have hwell : wellSizedCNFEncoding (Encodable.encode (circuitInputFormula c)) (circuitInputFormula c) = true :=
    circuitInputFormula_wellSized c
  have hrange : 2 ^ ℓ ≤ natBitLength (Encodable.encode (circuitInputFormula c)) :=
    (Nat.le_add_right _ _).trans <| (circuitInputVariables_le_formula_length c).trans <|
      list_length_le_encoded_bitLength _
  rw [RecoveryPrefixBody.search_canonical true _ _ _ (RecoveryFormulaPrefix.payload_decodes _) hwell hrange,
    circuitPrefix_eq_first c (firstInput C first) (2 ^ ℓ) le_rfl]
  change (List.ofFn first.table).take (2 ^ ℓ) = List.ofFn first.table
  rw [List.take_of_length_le (by simp)]

theorem tFlagSpec : TFlagSpec := fun C => flag_eq C

theorem tTableSpec : TTableSpec := fun C first => search_eq C first

end NearCubicGates.Close.ENP.TableSearch
