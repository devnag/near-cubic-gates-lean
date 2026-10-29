import Proof.Gates.ENP.TableSearchMeaning
import Proof.CaseAnalysis.RecoverySearchJoin
import Proof.CaseAnalysis.RecoveryGraphSerializeDock
import Proof.CaseAnalysis.RecoverySearchGraphBudget

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TableSearch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.MW20
open NearCubicWires.CircuitInputCNF NearCubicWires.BalancedCNFSATEncoding

def serSlot (u : ℕ) (i : Fin 1659) : Fin (1664 + u) := (i.castAdd 5).castAdd u

theorem serSlot_val (u : ℕ) (i : Fin 1659) : (serSlot u i).val = i.val := rfl

theorem serSlot_injective (u : ℕ) : Function.Injective (serSlot u) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa only [serSlot_val] using this

noncomputable def first {u s : ℕ} (E : Machine (1664 + u) s) :=
  Composition.machine E (RecoveryFocus.machine (serSlot u) RecoveryBoundedGraphSerialize.serialize)

noncomputable abbrev program {u s : ℕ} (E : Machine (1664 + u) s) :=
  RecoveryBoundedColdSearchJoin.program (first E)

def flagPort (u : ℕ) : Fin (1664 + u + 790) := (369 : Fin 790).natAdd (1664 + u)

def tablePort (u : ℕ) : Fin (1664 + u + 790) := (787 : Fin 790).natAdd (1664 + u)
/-- The query port. -/
def queryPort (u : ℕ) : Fin (1664 + u + 790) := (356 : Fin 790).natAdd (1664 + u)

theorem program_queryTape {u s : ℕ} (E : Machine (1664 + u) s) : (program E).queryTape = queryPort u := rfl

structure Entry (u : ℕ) {n : ℕ} (c : BooleanCircuit n) (H : Fin (1664 + u) → ℕ) (A : Fin (1664 + u) → List Bool) :
    Prop where
  heads : ∀ j, H (serSlot u (RecoveryBoundedGraphSerialize.readySlots j)) = 0
  tapes : ∀ j, A (serSlot u (RecoveryBoundedGraphSerialize.readySlots j)) =
    RecoveryBoundedGraphSerializeReady.input 0 c j
  arityHead : H (serSlot u 144) = 0
  arity : A (serSlot u 144) = List.replicate n true

/-- The cost of the stage after a first-machine run within `fuel`. -/
noncomputable def cost {n : ℕ} (fuel : ℕ) (c : BooleanCircuit n) : ℕ :=
  fuel + 1 + RecoveryBoundedGraphSerializeReady.budget c + 2 +
    1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload (circuitInputFormula c)) n) ^ 3

theorem not_ready_144 : ∀ j, RecoveryBoundedGraphSerialize.readySlots j ≠ 144 :=
  RecoveryBoundedGraphSerialize.ready_old_away 144 (by decide) (by decide) (by decide) (by decide)

/-- **The back end on any circuit** (`sec:all-lengths`: prefix self-reduction on the SAT formula of `c`). -/
theorem run_circuit {u s : ℕ} (E : Machine (1664 + u) s) (fuel : ℕ) (A0 : Fin (1664 + u) → List Bool)
    (r : ExecutionReceipt (1664 + u) s) (hr : LocalBitMultitape.run E fuel A0 = some r)
    {n : ℕ} (c : BooleanCircuit n) (entry : Entry u c r.final.heads r.final.tapes) :
    ∃ c' ≤ cost fuel c, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program E) c'
        (initialConfiguration (program E).base.machine (Fin.addCases A0 (fun _ => []))) final ∧
      (program E).base.machine.halted final.control = true ∧
      readTapeBit (final.tapes (flagPort u)) 0 =
        RecoveryOracle.correctedSat (RecoveryQuery.code true
          (RecoveryFormulaPrefix.payload (circuitInputFormula c)) 0 0) ∧
      final.tapes (tablePort u) = RepairOrdinary.frame (RecoveryPrefixBody.search true
        (RecoveryFormulaPrefix.payload (circuitInputFormula c)) n []) ∧
      final.heads (flagPort u) = 0 ∧ final.heads (tablePort u) = 0 ∧
      (final.tapes (queryPort u)).length ≤ c' ∧ final.heads (queryPort u) = 0 := by
  obtain ⟨q, hq, qt, qh, _qs, qkeep⟩ := RecoveryBoundedGraphSerialize.serialize_run 0 c
    (fun i => r.final.heads (serSlot u i)) (fun i => r.final.tapes (serSlot u i)) entry.heads entry.tapes
  obtain ⟨r1, h1, _hc1, _hs1, hhead, htape, _hkeep⟩ := RecoveryFocus.dock (serSlot u) (serSlot_injective u)
    RecoveryBoundedGraphSerialize.serialize (RecoveryBoundedGraphSerializeReady.budget c) r.final.heads r.final.tapes
    ⟨RecoveryBoundedGraphSerialize.serialize.start, fun i => r.final.heads (serSlot u i),
      fun i => r.final.tapes (serSlot u i)⟩ (fun _ => rfl) (fun _ => rfl) q hq
  have whole := Composition.run_join E (RecoveryFocus.machine (serSlot u) RecoveryBoundedGraphSerialize.serialize)
    fuel (RecoveryBoundedGraphSerializeReady.budget c) _ r r1 hr h1
  have k144 := qkeep 144 not_ready_144
  obtain ⟨c', hc', final, trace, halt, heads, flag, table, qlen, qhead, _keep⟩ :=
    RecoveryBoundedColdSearchJoin.run (first E) (fuel + 1 + RecoveryBoundedGraphSerializeReady.budget c)
      (RecoveryFormulaPrefix.payload (circuitInputFormula c)) n 0 A0 (Composition.joinedReceipt r r1) whole
      ((htape 1657).trans qt) (by
        change r1.final.tapes (serSlot u 144) = _
        rw [htape 144, k144.2, ZeroPadding.pad_zero]
        exact entry.arity)
      ((hhead 1657).trans qh) (by
        change r1.final.heads (serSlot u 144) = 0
        rw [hhead 144, k144.1]
        exact entry.arityHead)
  refine ⟨c', hc', final, trace, halt, flag, table, ?_, ?_, qlen, qhead⟩
  · rw [heads]; exact Fin.addCases_right _
  · rw [heads]; exact Fin.addCases_right _

/-- **The back end on `c_T`** (`sec:all-lengths` stage 2; `sec:gadget-extract` "Let `O*` be the first such oracle"):
the flag says whether
an honest table exists, and the table port holds the first honest table. -/
theorem run {u s : ℕ} (E : Machine (1664 + u) s) (fuel : ℕ) (A0 : Fin (1664 + u) → List Bool)
    (r : ExecutionReceipt (1664 + u) s) (hr : LocalBitMultitape.run E fuel A0 = some r)
    {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (entry : Entry u (TCirc.tCircuit C) r.final.heads r.final.tapes) :
    ∃ c' ≤ cost fuel (TCirc.tCircuit C), ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program E) c'
        (initialConfiguration (program E).base.machine (Fin.addCases A0 (fun _ => []))) final ∧
      (program E).base.machine.halted final.control = true ∧
      (readTapeBit (final.tapes (flagPort u)) 0 = true ↔ ∃ t, Transfer.HonestTable C t) ∧
      (∀ first : Transfer.FirstTable C, final.tapes (tablePort u) = RepairOrdinary.frame (List.ofFn first.table)) ∧
      final.heads (flagPort u) = 0 ∧ final.heads (tablePort u) = 0 ∧
      (final.tapes (queryPort u)).length ≤ c' ∧ final.heads (queryPort u) = 0 := by
  obtain ⟨c', hc', final, trace, halt, flag, table, hf, ht, qlen, qhead⟩ := run_circuit E fuel A0 r hr _ entry
  refine ⟨c', hc', final, trace, halt, ?_, ?_, hf, ht, qlen, qhead⟩
  · rw [flag]; exact tFlagSpec C
  · intro first
    rw [table, tTableSpec C first]

/-- The serializer + search cost coefficient. -/
def backCoefficient : ℕ :=
  2 * RecoveryBoundedGraphBudget.serializerCoefficient + 4 +
    RecoveryBoundedSearchExecution.graphSearchCoefficient

/-- **The back end's cost** (`sec:all-lengths`: the stage-2 formula has size `2^{O(q)}`): polynomial in any bound `W` on the
arity and the node count. -/
theorem back_le {n : ℕ} (c : BooleanCircuit n) (W : ℕ) (hn : n ≤ W) (hc : c.nodes.length ≤ W) :
    RecoveryBoundedGraphSerializeReady.budget c + 2 +
      1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload (circuitInputFormula c)) n) ^ 3 ≤
      backCoefficient * (W + 1) ^ 144 := by
  have hs := RecoveryBoundedGraphBudget.serializer_scalar c W hn hc
  have hr := Nat.mul_le_mul_left 1099511627776
    (Nat.pow_le_pow_left (RecoveryBoundedSearchExecution.radius_bound c W hn hc) 3)
  have he : 1099511627776 * ((RecoveryBoundedGraphBudget.serializerCoefficient + 7) * (W + 1) ^ 48) ^ 3 =
      RecoveryBoundedSearchExecution.graphSearchCoefficient * (W + 1) ^ 144 := by
    unfold RecoveryBoundedSearchExecution.graphSearchCoefficient
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]
  have hr2 : 1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload (circuitInputFormula c)) n) ^ 3
      ≤ RecoveryBoundedSearchExecution.graphSearchCoefficient * (W + 1) ^ 144 := hr.trans_eq he
  have h48 : (W + 1) ^ 48 ≤ (W + 1) ^ 144 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (W + 1) ^ 144 := Nat.one_le_pow _ _ (by omega)
  have hsm := Nat.mul_le_mul_left RecoveryBoundedGraphBudget.serializerCoefficient h48
  have hb : RecoveryBoundedGraphSerializeReady.budget c = 2 * RecoveryTseitinNative.Serialize.budget c + 2 := rfl
  rw [hb]
  unfold backCoefficient
  generalize RecoveryBoundedGraphBudget.serializerCoefficient = a at *
  generalize RecoveryBoundedSearchExecution.graphSearchCoefficient = b at *
  generalize (W + 1) ^ 144 = p at *
  generalize (W + 1) ^ 48 = q at *
  generalize RecoveryTseitinNative.Serialize.budget c = S at *
  generalize 1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload (circuitInputFormula c)) n) ^ 3 = X at *
  have hd : (2 * a + 4 + b) * p = 2 * (a * p) + 4 * p + b * p := by ring
  rw [hd]
  omega

end NearCubicGates.Close.ENP.TableSearch
