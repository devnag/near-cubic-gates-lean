import Proof.CaseAnalysis.FinalRequestAtCursor
import Proof.CaseAnalysis.FinalSiteRoundPorts
import Proof.CaseAnalysis.RowsOriginalCount
import Proof.CaseAnalysis.RowsGateArityCheck

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryAddressRounds
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation SourceInterfaces
open RepairSource.VerifierDecoding RecoveryRootRound
open CloseoutFinalC10ExactRecordLoop CloseoutFinalC10RoundCursor
open CloseoutRowsEstimatorCoefficients.Stream (Entry)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The exact all-round consumer allows its physical address to stop at M.
Only the same body's real live and terminal steps remain premises. -/
theorem rounds_saturated (extra : ℕ) {bs : ℕ}
    (body : Machine (218 + (60 + extra)) bs) (cost entryWidth M : ℕ)
    (pfx : ℕ → List Entry) (input witness : List Bool)
    (Cache : ℕ → (ℕ → List Bool) → Prop)
    (hsat : ∀ j, M ≤ j → pfx j = pfx M)
    (hlive : ∀ j s, j < M → Cache j s →
      ∃ s', Cache (j + 1) s' ∧ Step body cost (fun _ => 0)
        (prefixBank extra entryWidth (pfx j) input witness s) (fun _ => 0)
        (prefixBank extra entryWidth (pfx (j + 1)) input witness s'))
    (hidle : ∀ s, Cache M s → Step body cost (fun _ => 0)
      (prefixBank extra entryWidth (pfx M) input witness s) (fun _ => 0)
      (prefixBank extra entryWidth (pfx M) input witness s)) :
    Rounds' extra body cost entryWidth pfx input witness
      (fun j s => Cache (min j M) s) := by
  intro j s h
  by_cases hj : j < M
  · rw [min_eq_left hj.le] at h
    obtain ⟨s', hs', hr⟩ := hlive j s hj h
    exact ⟨s', by simpa only [min_eq_left (show j + 1 ≤ M by omega)] using hs', hr⟩
  · have hm : M ≤ j := by omega
    rw [min_eq_right hm] at h
    refine ⟨s, ?_, ?_⟩
    · simpa only [min_eq_right (show M ≤ j + 1 by omega)] using h
    · rw [hsat j hm, hsat (j + 1) (by omega)]
      exact hidle s h

/-- The last valid increment already fits, including the saturated address M. -/
theorem terminal_fits (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity) :
    2 ^ (a.output rq).clauseBits + 2 ≤
      PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity) := by
  have hm : 0 < 2 ^ (a.output rq).clauseBits := pow_pos (by decide) _
  have h := CloseoutFinalC10RequestAtCursor.next_index_fits a rq
    ⟨2 ^ (a.output rq).clauseBits - 1, by omega⟩
  dsimp only at h
  omega

/-- An existing cold machine reads the same literal source once, preserving
all cache bytes, and physically emits the actual clause count in both forms. -/
theorem actual_count (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity) :
    let C := PCPPQueryCachedBounds.capacity a (rq.circuit.size + rq.arity)
    let A := PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 C []
    ∃ out, Step CloseoutRowsOriginalCount.machine (CloseoutRowsOriginalCount.budget rq (a.output rq))
      (CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads) (CloseoutRowsOriginalCount.input A)
      (CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads) out ∧
      (∀ j : Fin 19, out (j.castAdd 55) = A j) ∧
      out 70 = UnaryTemplate.tape (2 ^ (a.output rq).clauseBits) ∧
      out 72 = List.replicate (2 ^ (a.output rq).clauseBits) true := by
  dsimp only
  exact CloseoutRowsOriginalCount.run rq (a.output rq) PCPPQueryClauseReuse.heads _ rfl rfl rfl rfl

def testInput (j M C : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad C (UnaryTemplate.tape j), List.replicate M true,
    List.replicate C false, List.replicate C false]
def testOutput (j M C : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad C (UnaryTemplate.tape j), List.replicate M true,
    ZeroPadding.pad C [decide (j = M)], List.replicate C false]

/-- Real comparison, including its reusable flag and reset log. The index
operand is precisely the padded template on physical cache tape 14. -/
theorem terminal_test (j M C : ℕ) (hC : j + 2 ≤ C) :
    Step CloseoutRowsGateArityCheck.machine (2 * min j M + 6) (fun _ => 0)
      (testInput j M C) (fun _ => 0) (testOutput j M C) := by
  let caps : Fin 4 → ℕ := ![C, 0, C, C]
  obtain ⟨r, hr, ht, hh, _⟩ := CloseoutRowsGateArityCheck.arity_run j M
  have h := (Step.of_run hr (funext hh) ht).pad caps
  have hin : (fun i => ZeroPadding.pad (caps i) (CloseoutRowsGateArityCheck.input j M i))
      = testInput j M C := by
    funext i
    fin_cases i
    · exact pad_template C j hC
    all_goals simp [caps, CloseoutRowsGateArityCheck.input, testInput, ZeroPadding.pad]
  have hout : (fun i => ZeroPadding.pad (caps i) (CloseoutRowsGateArityCheck.output j M i))
      = testOutput j M C := by
    funext i
    fin_cases i
    · exact pad_template C j hC
    · simp [caps, CloseoutRowsGateArityCheck.output, testOutput, ZeroPadding.pad]
    · rfl
    · change ZeroPadding.pad C (List.replicate (min j M + 2) false) = List.replicate C false
      have hmin : min j M + 2 ≤ C :=
        (Nat.add_le_add_right (Nat.min_le_left j M) 2).trans hC
      simp [ZeroPadding.pad, Nat.add_sub_of_le hmin]
  rw [hin, hout] at h
  exact h

theorem terminal_bit (j M C : ℕ) :
    readTapeBit (testOutput j M C 2) 0 = decide (j = M) := by
  simp [testOutput, ZeroPadding.pad, readTapeBit, List.getD]

/-- Every hot test and unary bump has one j-independent bound. -/
theorem test_and_bump_bound (D q j : ℕ) (M : ℕ)
    (hM : M ≤ clauseEnvelope D q) (hj : j ≤ M) :
    (2 * min j M + 6) + (2 * j + 2) ≤ 4 * clauseEnvelope D q + 8 := by omega

/-- Squaring the clause envelope stays polynomial in native q. It does not
square the independent residual table width 2^(q-K). -/
theorem unary_total_bound (D q : ℕ) :
    unaryCursorCost (clauseEnvelope D q) ≤
      (2 ^ (D + 1) * (q + 1) ^ D) * (2 ^ (D + 1) * (q + 1) ^ D + 1) := by
  rw [unaryCursorCost_eq]
  have h := CloseoutFinalC10SiteRoundPorts.clauseEnvelope_le D q
  exact Nat.mul_le_mul h (Nat.add_le_add_right h 1)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10UnaryAddressRounds
