import Proof.Gates.Recovery.AfterParts
import Proof.CaseAnalysis.RecoveryWorkspacePolynomial
import Proof.CaseAnalysis.RecoveryCapacityEnvelope
import Proof.Gates.OuterM.WidthW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.ENP
open NearCubicWires.BoundedOracleStructuralCircuit NearCubicWires.PaddedRunnerBudgetClosure

namespace Cost

theorem pow_mono_exp (V a b : ℕ) (hV : 1 ≤ V) (h : a ≤ b) : V ^ a ≤ V ^ b := Nat.pow_le_pow_right hV h

/-- The listed-pairs circuit is at most the workspace. -/
theorem circuit_nodes (d w R : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n) :
    (UGraph.circuit d w R vals hw x).nodes.length ≤
      originalWorkspace R (oracleSizeBound d R) vals.length vals.length := by
  have hcl : ∀ randomness, ((unitOuter w R vals hw).decision x randomness).clauses.length ≤
      (Codec.clauses (unitPCP w vals)).length := by
    intro randomness
    have h := congrArg List.length (Codec.decision_codes (unitPCP w vals) R vals.length hw le_rfl x randomness)
    rw [List.length_map] at h
    exact h.le
  have h := original_graph_bound (unitOuter w R vals hw) x (oracleSizeBound d R) _ hcl
  rw [USupply.unit_clauses_length] at h
  exact h

theorem cubic (K W : ℕ) :
    1099511627776 * ((K + 7) * (W + 1) ^ 48) ^ 3 = (1099511627776 * (K + 7) ^ 3) * (W + 1) ^ 144 := by
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]

end Cost

open Cost in
/-- **Stage cost** (`sec:all-lengths`, "SAT formulas of size `2^{O(q)}`"). -/
theorem uCostPoly (d : ℕ) : UCostPoly d := by
  obtain ⟨E1, C1, hcap⟩ := RecoveryCapacityDrivers.generic_polynomial 16384 (33 * 10000000000) 64
  set E := 150 + E1 + RecoveryFullBound.degree d with hE
  refine ⟨800000 + C1 + 10000000000000 + RecoveryFullBound.coefficient d * 2 ^ RecoveryFullBound.degree d +
    RecoveryBoundedColdGraph.coefficient + RecoveryBoundedSearchExecution.graphSearchCoefficient + 10, E,
    fun w R W vals hw n x hlen hb hW hsource htwo => ?_⟩
  have hf := original_workspace_fields R (oracleSizeBound d R) vals.length vals.length
  have hR : R ≤ W := hf.1.trans hW
  have hbW : oracleSizeBound d R ≤ W := hf.2.1.trans hW
  have hMW : vals.length ≤ W := hf.2.2.1.trans hW
  have hdw : descriptionWidth R (oracleSizeBound d R) ≤ W := hf.2.2.2.2.2.trans hW
  have hc : (UGraph.circuit d w R vals hw x).nodes.length ≤ W := (circuit_nodes d w R vals hw x).trans hW
  -- the pieces
  have hV1 : 1 ≤ W + 1 := by omega
  have g1 := RecoveryBoundedColdGraph.budget_bound R W (UGraph.circuit d w R vals hw x) hdw hc hR hbW htwo
  have g2 : 1099511627776 * (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload (UStage.formula d w R vals hw x))
      (descriptionWidth R (oracleSizeBound d R))) ^ 3 ≤ RecoveryBoundedSearchExecution.graphSearchCoefficient * (W + 1) ^ 144 := by
    have h := Nat.mul_le_mul_left 1099511627776
      (Nat.pow_le_pow_left (RecoveryBoundedSearchExecution.radius_bound (UGraph.circuit d w R vals hw x) W hdw hc) 3)
    exact h.trans_eq (cubic _ W)
  have g3 : UCount.progCost R vals.length ≤ 800000 * (W + 1) ^ 5 := by
    unfold UCount.progCost
    have h1 : (R + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
    have h2 : (vals.length + 2) ^ 3 ≤ (2 * (W + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) _
    have h3 : (2 * (W + 1)) ^ 3 = 8 * (W + 1) ^ 3 := by ring
    calc 100000 * ((R + 1) ^ 2 * (vals.length + 2) ^ 3) ≤ 100000 * ((W + 1) ^ 2 * (8 * (W + 1) ^ 3)) := by
          rw [← h3]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
      _ = 800000 * (W + 1) ^ 5 := by ring
  have g4 : RecoveryCapacityDrivers.budget W ≤ C1 * (W + 1) ^ E1 := hcap W
  have g5 := RecoveryProjectionCold.budget_bound W R vals.length hR hMW htwo
  have g6 : RecoveryFullBound.budget d R ≤
      RecoveryFullBound.coefficient d * 2 ^ RecoveryFullBound.degree d * (W + 1) ^ RecoveryFullBound.degree d := by
    refine (RecoveryFullBound.budget_bound d R).trans ?_
    have h : (R + 2) ^ RecoveryFullBound.degree d ≤ (2 * (W + 1)) ^ RecoveryFullBound.degree d :=
      Nat.pow_le_pow_left (by omega) _
    rw [mul_pow] at h
    calc RecoveryFullBound.coefficient d * (R + 2) ^ RecoveryFullBound.degree d
        ≤ RecoveryFullBound.coefficient d * (2 ^ RecoveryFullBound.degree d * (W + 1) ^ RecoveryFullBound.degree d) :=
          Nat.mul_le_mul_left _ h
      _ = _ := by ring
  -- all against (W + 1)^E
  have p5 := pow_mono_exp (W + 1) 5 E hV1 (by omega)
  have pE1 := pow_mono_exp (W + 1) E1 E hV1 (by omega)
  have p6 := pow_mono_exp (W + 1) 6 E hV1 (by omega)
  have pd := pow_mono_exp (W + 1) (RecoveryFullBound.degree d) E hV1 (by omega)
  have p48 := pow_mono_exp (W + 1) 48 E hV1 (by omega)
  have p144 := pow_mono_exp (W + 1) 144 E hV1 (by omega)
  have p0 : 1 ≤ (W + 1) ^ E := Nat.one_le_pow _ _ hV1
  have k3 := Nat.mul_le_mul_left 800000 p5
  have k4 := Nat.mul_le_mul_left C1 pE1
  have k5 := Nat.mul_le_mul_left 10000000000000 p6
  have k6 := Nat.mul_le_mul_left (RecoveryFullBound.coefficient d * 2 ^ RecoveryFullBound.degree d) pd
  have k1 := Nat.mul_le_mul_left RecoveryBoundedColdGraph.coefficient p48
  have k2 := Nat.mul_le_mul_left RecoveryBoundedSearchExecution.graphSearchCoefficient p144
  unfold UStage.cost UGraph.budget USupply.budget
  change RecoveryProjectionCold.budget R vals.length (RecoveryCapacityDrivers.capacityB W) ≤ _ at g5
  simp only [Nat.add_mul] at *
  omega

namespace Need

open NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspacePolynomial NearCubicWires.RepairSource.CloseoutRecoveryCapacity

/-- The workspace at `n = 2^R`: width `⌊log₂ n⌋`, cap `oracleSizeBound d ⌊log₂ n⌋`, `n` queries and `n` clauses. -/
noncomputable def wsAt (d n : ℕ) : ℕ :=
  originalWorkspace (Nat.log 2 n) (oracleSizeBound d (Nat.log 2 n)) n n

theorem wsAt_poly (d : ℕ) : SourcePoly (wsAt d) := by
  have hw : SourcePoly (fun n => Nat.log 2 n) := sourcePoly_id.mono fun n => Nat.log_le_self 2 n
  have hb : SourcePoly (fun n => oracleSizeBound d (Nat.log 2 n)) := by
    obtain ⟨deg, C, h⟩ := sourcePoly_pairClock (oracleDepth d)
    refine sourcePoly_of_le C deg fun n => ?_
    have h1 := h (Nat.log 2 n)
    have h2 : (Nat.log 2 n + 1) ^ deg ≤ (n + 1) ^ deg :=
      Nat.pow_le_pow_left (by have := Nat.log_le_self 2 n; omega) _
    exact h1.trans (Nat.mul_le_mul_left _ h2)
  have htwo : SourcePoly (fun n => 2 ^ Nat.log 2 n) := by
    refine sourcePoly_of_le 1 1 fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.pow_log_le_self 2 (by omega : n ≠ 0); simp; omega
  exact original_workspace hw hb sourcePoly_id sourcePoly_id htwo

theorem framed_len (codes : List ℕ) (B : ℕ) (h : ∀ v ∈ codes, v ≤ B) :
    (QueryBytes.framedCodes codes).length ≤ codes.length * (2 * B + 1) := by
  induction codes with
  | nil => simp [QueryBytes.framedCodes, FieldList.stream]
  | cons v vs ih =>
    have hv := (OuterM.bits_length_le v).trans (h v (by simp))
    have ih' := ih (fun u hu => h u (by simp [hu]))
    unfold QueryBytes.framedCodes FieldList.stream at ih' ⊢
    simp only [List.map_cons, List.flatten_cons, List.length_append, RepairOrdinary.frame_length,
      List.length_cons] at ih' ⊢
    nlinarith

/-- The bytes of a listed-pairs PCP: `|vals|` clauses of three codes `≤ 2|vals|`. -/
theorem fields_le (w : ℕ) (vals : List Bool) :
    (DedupBytes.fields (unitPCP w vals)).length ≤ vals.length * (12 * vals.length + 3) := by
  have hmem : ∀ codes ∈ Codec.clauses (unitPCP w vals),
      (QueryBytes.framedCodes codes).length ≤ 12 * vals.length + 3 := by
    intro codes hc
    unfold Codec.clauses at hc
    rw [List.mem_dedup, List.mem_map] at hc
    obtain ⟨c, hcmem, rfl⟩ := hc
    change c ∈ List.ofFn (fun i : Fin vals.length => unitClause i (vals.get i)) at hcmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hcmem
    have hcode : ∀ v ∈ clauseCodes (unitClause i (vals.get i)), v ≤ 2 * vals.length := by
      intro v hv
      unfold clauseCodes at hv
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hv
      unfold unitClause
      have := i.isLt
      split_ifs <;> simp [literalCode] <;> omega
    have hl : (clauseCodes (unitClause i (vals.get i))).length = 3 := by simp [clauseCodes]
    have := framed_len _ _ hcode
    rw [hl] at this
    exact le_trans this (by omega)
  have hlen := USupply.unit_clauses_length w vals
  unfold DedupBytes.fields
  rw [List.length_flatten, List.map_map]
  have := List.sum_le_card_nsmul ((Codec.clauses (unitPCP w vals)).map (List.length ∘ QueryBytes.framedCodes))
    (12 * vals.length + 3) (fun x hx => by
      rw [List.mem_map] at hx
      obtain ⟨codes, hc, rfl⟩ := hx
      exact hmem codes hc)
  simp only [List.length_map, smul_eq_mul, hlen] at this
  exact this

end Need

open Need in
/-- **Stage workspace** (`sec:all-lengths`): the workspace of a listed-pairs stage is polynomial in `2^R`. -/
theorem uNeedPoly (d : ℕ) : UNeedPoly d := by
  obtain ⟨E, C, hF⟩ := wsAt_poly d
  refine ⟨C + 16, E + 2, fun w R vals hw hlen => ?_⟩
  have hM : vals.length ≤ 2 ^ R := by rw [hlen]; exact Nat.pow_le_pow_right (by norm_num) hw
  have h1 : originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ wsAt d (2 ^ R) := by
    unfold wsAt
    rw [Nat.log_pow (by norm_num)]
    exact NearCubicWires.RepairSource.CloseoutRecoveryCapacity.workspace_mono le_rfl le_rfl hM hM
  have h2 : wsAt d (2 ^ R) ≤ C * (2 ^ R + 1) ^ E := hF (2 ^ R)
  have h3 := fields_le w vals
  have hX1 : 1 ≤ 2 ^ R + 1 := by omega
  have p1 : (2 ^ R + 1) ^ E ≤ (2 ^ R + 1) ^ (E + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have p2 : (2 ^ R + 1) ^ 2 ≤ (2 ^ R + 1) ^ (E + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have h4 : vals.length * (12 * vals.length + 3) ≤ 15 * (2 ^ R + 1) ^ 2 := by
    have : vals.length * (12 * vals.length + 3) ≤ (2 ^ R + 1) * (15 * (2 ^ R + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have h5 : 2 ^ R + 1 ≤ (2 ^ R + 1) ^ 2 := by nlinarith
  have k1 := Nat.mul_le_mul_left C p1
  calc originalWorkspace R (oracleSizeBound d R) vals.length vals.length +
        (DedupBytes.fields (unitPCP w vals)).length + 2 ^ R
      ≤ C * (2 ^ R + 1) ^ (E + 2) + 15 * (2 ^ R + 1) ^ (E + 2) + (2 ^ R + 1) ^ (E + 2) := by omega
    _ = (C + 16) * (2 ^ R + 1) ^ (E + 2) := by ring

end NearCubicGates.Close.Recovery.After
