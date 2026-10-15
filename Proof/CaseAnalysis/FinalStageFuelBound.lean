import Proof.CaseAnalysis.FinalFuelMajorant
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Hierarchy.CompetitorWitnessTripleSemantics
import Proof.CaseAnalysis.WitnessOracleParameter

/-! # `StageBlock.hfuel`: what it actually demands, and where the demand comes from

`StageBlock.hfuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is

```
hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
  actualFuel sources k p S x bits ≤ S.budget n
```

It is the only one of the fourteen fields with no `Soundness.cutoff ≤ n` guard.
Its consumer is `verdict_of_stage`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`), whose deliverable is a
`Weak.StepAtInputs`-shaped `Verdict` at the len-only budget `S.budget` for EVERY
`n` and EVERY witness `bits`; the guard is absent because the consumer has none.

This module settles what that costs, in three steps and with no new hypothesis.

* §1 `actualFuel_eq`: `actualFuel` is a function of the input length `n` and the
  three per-phase CALL COUNTS `(records … ph).length`, and of nothing else.  The
  closed form `fuelAt` names `S.stageFuel`, `S.entryWidth` and `dockedFuel`
  explicitly.  It contains no `Nat` subtraction and no `Nat.log`: nothing in it
  truncates, at `n = 0` or anywhere else.
* §2 `fuel_bounded_iff`: at one length, `hfuel` is satisfiable by SOME budget if
  and only if the per-phase call count is bounded over `bits`.  Both directions
  are proved; the reduction is exact, not a sufficient condition.
* §3 The call count is driven by `2 ^ (pcppOf …).clauseBits`, whose only
  imported bound is `PointwisePCPPAlgorithm.clauseCountBound`
  (`Proof/Foundations/RepresentationSourceContracts.lean`), stated in terms of the
  GUESSED ORACLE's size.  `oracleOf_size_le` proves that size IS bounded by the
  input length -- but only for `bits` satisfying the machine's own header cap
  `16 * bits.length ≤ n`, via `Oracle.decoded_size`
  (`Proof/CaseAnalysis/WitnessOracleParameter.lean`).  `decoder_free` and
  `no_decoder_size_majorant` prove the RAW codec admits every circuit of the
  native arity at EVERY fixed length, so the codec alone has no majorant.
* §4 `oracleOf_size_majorant`: the paper's size guard, now applied by `oracleOf`
  (`Proof/CaseAnalysis/FinalTotalDecode.lean`, `paper.tex:4292`), restores one.
  `gate_rejects_wide` shows its `else` branch is genuinely reached.

`Proof/CaseAnalysis/FinalFuelMajorant.lean` records that "no length-only
decoded-size majorant is claimed"; §3 says why the codec cannot have one.
-/

namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound

open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation
open SourceInterfaces SupplierPipeline CanonicalBinary CanonicalWitnessCodec
open RepairOrdinary.RadixSemantics
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open RepairOrdinary.CloseoutFinalC10StageSeam
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10CallCountMajorant
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData sources k p)

/-! ## §1 The closed form: `actualFuel` is the call counts and nothing else -/

def fuelAt (n : ℕ) (c : Phase → ℕ) : ℕ :=
  workerBudget (Soundness.cutoff (constantsOf sources))
    (fun _ => C10ComposeWidths.innerFuel
      (fun ph => stagedFuel (S.stageFuel ph)
        (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
          (joinScalarWidth (S.entryWidth n) (c ph)))
        (S.entryWidth n) (c ph) n)
      (fun ph => joinScalarWidth (S.entryWidth n) (c ph))
      C10TailVerdictUniform.tbud) n

/-- The fold's scalar width is the join width at the call count. -/
theorem widthOf_eq {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    widthOf sources k p S x bits ph
      = joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length := by
  unfold widthOf
  exact foldWidth_eq_joinScalarWidth (S.entryWidth n) _

/-- **`actualFuel` depends on the witness ONLY through the three call counts.** -/
theorem actualFuel_eq {n : ℕ} (x : BitInput n) (bits : List Bool) :
    actualFuel sources k p S x bits
      = fuelAt sources k p S n (fun ph => (records sources k p S x bits ph).length) := by
  have hF : phaseFuel sources k p S x bits
      = fun ph => stagedFuel (S.stageFuel ph)
          (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
            (joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length))
          (S.entryWidth n) (records sources k p S x bits ph).length n := by
    funext ph
    rfl
  have hW : widthOf sources k p S x bits
      = fun ph => joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length := by
    funext ph
    exact widthOf_eq sources k p S x bits ph
  unfold actualFuel fuelAt
  rw [hF, hW]

/-! ## §2 Monotone up, bounded below: the exact satisfiability criterion -/

theorem lengths_mono {W W' : Phase → ℕ} (h : ∀ ph, W ph ≤ W' ph) (j : Fin 6) :
    C10ComposeWidths.lengths W j ≤ C10ComposeWidths.lengths W' j := by
  unfold C10ComposeWidths.lengths
  have hj := h (C10WidthCopies.phaseOf j)
  split
  · exact hj
  · unfold CompetitorRationalDecision.width
    omega

theorem widthCopies_budget_mono {V V' : Fin 6 → ℕ} (h : ∀ j, V j ≤ V' j) :
    C10WidthCopies.budget V ≤ C10WidthCopies.budget V' := by
  unfold C10WidthCopies.budget C10WidthCopies.charge
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  omega

theorem maxWidth_mono {W W' : Phase → ℕ} (h : ∀ ph, W ph ≤ W' ph) :
    C10ComposeWidths.maxWidth W ≤ C10ComposeWidths.maxWidth W' := by
  unfold C10ComposeWidths.maxWidth
  exact max_le_max (h Phase.penalty) (max_le_max (h Phase.moment) (h Phase.clause))

theorem innerFuel_mono {F F' W W' : Phase → ℕ} (hF : ∀ ph, F ph ≤ F' ph)
    (hW : ∀ ph, W ph ≤ W' ph) :
    C10ComposeWidths.innerFuel F W C10TailVerdictUniform.tbud ≤
      C10ComposeWidths.innerFuel F' W' C10TailVerdictUniform.tbud := by
  unfold C10ComposeWidths.innerFuel C10ComposeWidths.bodyFuel
  have h1 := C10FuelMajorant.bodyThreeFuel_mono hF
  have h2 := widthCopies_budget_mono (fun j => lengths_mono hW j)
  have h3 := C10TailVerdictUniform.tbud_mono (maxWidth_mono hW)
  omega

/-- **The demanded fuel is monotone in the call counts** -- the direction the
consumer needs, since `hfuel` is an UPPER bound on `actualFuel`. -/
theorem fuelAt_mono (n : ℕ) {c c' : Phase → ℕ} (h : ∀ ph, c ph ≤ c' ph) :
    fuelAt sources k p S n c ≤ fuelAt sources k p S n c' := by
  unfold fuelAt
  refine workerBudget_mono _ _ _ n ?_
  exact innerFuel_mono
    (fun ph => C10FuelMajorant.stagedFuel_mono (S.stageFuel ph) (S.entryWidth n) n (h ph))
    (fun ph => joinScalarWidth_mono (S.entryWidth n) (h ph))

/-- The staged seam's fuel is at least the call count: the cold fold pays at
least one step per emitted record (`CompetitorSumFold.loopBudget`). -/
theorem le_stagedFuel (stageFuel : ℕ → ℕ) (entryWidth c n : ℕ) :
    c ≤ stagedFuel stageFuel
      (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth entryWidth c))
      entryWidth c n := by
  have hb : 1 ≤ CompetitorSumFold.bodyBudget (joinScalarWidth entryWidth c) + 3 := by omega
  have hmul : c * 1 ≤ c * (CompetitorSumFold.bodyBudget (joinScalarWidth entryWidth c) + 3) :=
    Nat.mul_le_mul_left _ hb
  have hloop : c ≤ CompetitorSumFold.loopBudget (joinScalarWidth entryWidth c) c := by
    unfold CompetitorSumFold.loopBudget
    omega
  unfold stagedFuel dockedFuel dockBudget CompetitorSumEntry.budget
  omega

/-- **The demanded fuel dominates every call count.**  This is the half that
makes an unbounded call count fatal. -/
theorem le_fuelAt (n : ℕ) (c : Phase → ℕ) (ph : Phase) : c ph ≤ fuelAt sources k p S n c := by
  have hp := le_stagedFuel (S.stageFuel Phase.penalty) (S.entryWidth n) (c Phase.penalty) n
  have hm := le_stagedFuel (S.stageFuel Phase.moment) (S.entryWidth n) (c Phase.moment) n
  have hc := le_stagedFuel (S.stageFuel Phase.clause) (S.entryWidth n) (c Phase.clause) n
  simp only [fuelAt, workerBudget, C10ComposeWidths.innerFuel, C10ComposeWidths.bodyFuel,
    C10TailCompose.bodyThreeFuel]
  cases ph <;> omega

/-- **THE CRITERION.**  At one input length, `hfuel` holds for SOME budget
exactly when the per-phase call count admits a bound over all witnesses.  Both
directions; no hypothesis is introduced and none is handed on. -/
theorem fuel_bounded_iff {n : ℕ} (x : BitInput n) :
    (∃ b : ℕ, ∀ bits : List Bool, actualFuel sources k p S x bits ≤ b) ↔
      (∃ K : ℕ, ∀ (bits : List Bool) (ph : Phase),
        (records sources k p S x bits ph).length ≤ K) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, fun bits ph => ?_⟩
    have h1 := le_fuelAt sources k p S n
      (fun ph => (records sources k p S x bits ph).length) ph
    rw [← actualFuel_eq sources k p S x bits] at h1
    exact h1.trans (hb bits)
  · rintro ⟨K, hK⟩
    refine ⟨fuelAt sources k p S n (fun _ => K), fun bits => ?_⟩
    rw [actualFuel_eq sources k p S x bits]
    exact fuelAt_mono sources k p S n (fun ph => hK bits ph)

/-- **The below-cutoff half of `hfuel` is a floor on the budget, nothing more.**
`below_run` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`) uses `hfuel`
under `n < cutoff` only through this inequality, so a `hfuel` guarded like its
thirteen siblings would have to be replaced by `∀ n, n < cutoff → 2*n+3 ≤ S.budget n`. -/
theorem below_cutoff_floor {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : n < Soundness.cutoff (constantsOf sources)) :
    2 * n + 3 ≤ actualFuel sources k p S x bits := by
  unfold actualFuel workerBudget
  omega

/-! ## §3 The decoded oracle: the RAW decoder is free, and the gate is what
bounds it -/

variable (clock : OrdinaryClock (fun n => n ^ (k + 2)))

/-- **The RAW decoder, made total.**  `decodeBooleanCircuit`
(`Proof/Circuits/CanonicalWitnessCodec.lean`) with the same total fallback the
pre-gate `oracleOf` used.  No size test: the negatives below are about THIS
function, which is what they were always about. -/
def decodedOracle (n : ℕ) (bits : List Bool) :
    BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n) :=
  (decodeBooleanCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
      (value (BoundedFields.oracle bits))).getD
    (C10TotalDecode.trivialCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))

theorem decodedOracle_pin (n : ℕ) (bits : List Bool)
    (c : BooleanCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (hd : decodeBooleanCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
      (value (BoundedFields.oracle bits)) = some c) :
    decodedOracle sources k clock n bits = c := by
  simp [decodedOracle, hd]

/-- **The gate, unfolded once.**  `oracleOf`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) is the raw decoder followed by the
machine's own size test, `paper.tex:4292`. -/
theorem oracleOf_eq_if (oracleDegree n : ℕ) (bits : List Bool) :
    C10TotalDecode.oracleOf sources k clock oracleDegree n bits =
      (if (decodedOracle sources k clock n bits).size ≤
            RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
              ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
        then decodedOracle sources k clock n bits
        else C10TotalDecode.trivialCircuit
          ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)) :=
  rfl

/-- **The length-only decoded-size majorant, on the witnesses the machine's own
header admits.**  `Oracle.decoded_size`
(`Proof/CaseAnalysis/WitnessOracleParameter.lean`) caps every decoded guessed
oracle at `N` once `16*|raw| ≤ N`, which is exactly the bounded-header cap
`BoundedFields.fields` (`Proof/CaseAnalysis/WitnessBoundedFields.lean`) enforces on
the accepting path.  Both branches of the gate stay inside it: the accepted one
by the codec bound, the rejected one because `trivialCircuit` has size `1`. -/
theorem oracleOf_size_le (oracleDegree n : ℕ) (bits : List Bool) (hn : 2 ≤ n)
    (hbits : 16 * bits.length ≤ n) :
    (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size ≤ n := by
  have hlen : (BoundedFields.oracle bits).length = bits.length := (BoundedFields.lengths bits).1
  have htriv : (C10TotalDecode.trivialCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)).size = 1 := rfl
  have hraw : (decodedOracle sources k clock n bits).size ≤ n := by
    cases hd : decodeBooleanCircuit
        ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
        (value (BoundedFields.oracle bits)) with
    | none =>
        have hfall : decodedOracle sources k clock n bits
            = C10TotalDecode.trivialCircuit
              ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n) := by
          unfold decodedOracle
          rw [hd]
          rfl
        rw [hfall, htriv]
        omega
    | some c =>
        rw [decodedOracle_pin sources k clock n bits c hd]
        exact Oracle.decoded_size _ n (BoundedFields.oracle bits) c hn
          (by rw [hlen]; exact hbits) hd
  by_cases hle : (decodedOracle sources k clock n bits).size ≤
      RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
        ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
  · rw [oracleOf_eq_if, if_pos hle]
    exact hraw
  · rw [oracleOf_eq_if, if_neg hle, htriv]
    omega

/-- A Boolean circuit of arity `q` with at least `m` gates. -/
def wideCircuit (q m : ℕ) : BooleanCircuit q where
  nodes := List.replicate (m + 1) (BooleanNode.const false)
  output := ⟨m, by simp⟩
  wellFormed := by
    intro i
    have h : (List.replicate (m + 1) (BooleanNode.const (n := q) false)).get i
        = BooleanNode.const false := by simp
    rw [h]
    exact True.intro

theorem wideCircuit_size (q m : ℕ) : m ≤ (wideCircuit q m).size := by
  have h : (wideCircuit q m).size = m + 1 := by
    simp [wideCircuit, BooleanCircuit.size]
  omega

theorem exists_bits_value (v : ℕ) : ∃ bits : List Bool, value bits = v :=
  ⟨SignedSortKey.binary (Nat.log 2 v + 1) v,
    SignedSortKey.binary_value _ _ (Nat.lt_pow_succ_log_self (by decide) v)⟩

/-- **At EVERY input length the RAW DECODER ranges over ALL circuits of the
native arity.**  Was `oracle_free`; the construction is unchanged, and the
subject is the codec, which applies no size test.  The witness header's own
`16*|oracle| ≤ |x|` cap (`BoundedFields.fields`,
`Proof/CaseAnalysis/WitnessBoundedFields.lean`) is not part of the codec. -/
theorem decoder_free (n : ℕ)
    (c : BooleanCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)) :
    ∃ bits : List Bool, decodedOracle sources k clock n bits = c := by
  obtain ⟨bits, hbits⟩ := exists_bits_value (encodeTaggedList [0, ExecutableInterfaces.encodeBooleanCircuit c, 0])
  refine ⟨bits, ?_⟩
  have hfield := CompetitorWitnessTriple.extracted_values bits 0 (ExecutableInterfaces.encodeBooleanCircuit c) 0 hbits
  have horacle : value (BoundedFields.oracle bits) = ExecutableInterfaces.encodeBooleanCircuit c := hfield.2.2.1
  exact decodedOracle_pin sources k clock n bits c
    (by rw [horacle]; exact decodeBooleanCircuit_encode c)

/-- **The RAW-decoded oracle's size is unbounded at every fixed input length.**
Was `oracle_size_unbounded`. -/
theorem decoded_size_unbounded (n m : ℕ) :
    ∃ bits : List Bool, m ≤ (decodedOracle sources k clock n bits).size := by
  obtain ⟨bits, hbits⟩ := decoder_free sources k clock n
    (wideCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n) m)
  refine ⟨bits, ?_⟩
  rw [hbits]
  exact wideCircuit_size _ m

/-- **No length-only majorant on the RAW-decoded oracle size exists.**  Was
`no_oracle_size_majorant`.  This is why `PointwisePCPPAlgorithm.clauseCountBound`
(`Proof/Foundations/RepresentationSourceContracts.lean`), which bounds `2 ^ clauseBits`
by the guessed oracle's size, gives nothing off the codec's own gate -- and, by
`oracleOf_size_majorant` below, exactly why the gate had to be applied. -/
theorem no_decoder_size_majorant (n : ℕ) :
    ¬ ∃ M : ℕ, ∀ bits : List Bool, (decodedOracle sources k clock n bits).size ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨bits, hbits⟩ := decoded_size_unbounded sources k clock n (M + 1)
  have := hbits.trans (hM bits)
  omega

/-! ## §4 What the gate restores: the majorant the raw decoder cannot have -/

/-- **The majorant `no_decoder_size_majorant` denies to the codec, supplied by the
gate.**  `M := max (oracleSizeBound oracleDegree q) 1` bounds the GATED oracle at
every witness, with no hypothesis at all.  It depends on `n` alone, which is what
`fuel_bounded_iff` needs of the call-count cap, so `hfuel`'s obstruction is the
`bits` quantifier only as long as the guard is absent. -/
theorem oracleOf_size_majorant (oracleDegree n : ℕ) :
    ∃ M : ℕ, ∀ bits : List Bool,
      (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size ≤ M := by
  refine ⟨max (RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
    ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)) 1,
    fun bits => ?_⟩
  have htriv : (C10TotalDecode.trivialCircuit
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)).size = 1 := rfl
  by_cases hle : (decodedOracle sources k clock n bits).size ≤
      RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
        ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
  · rw [oracleOf_eq_if, if_pos hle]
    exact hle.trans (le_max_left _ _)
  · rw [oracleOf_eq_if, if_neg hle, htriv]
    exact le_max_right _ _

/-- **The gate is not decoration: its `else` branch is reached.**  `decoder_free`
puts a circuit above the cap in range of the codec at every length, and the gate
rejects exactly that witness, replacing it with `trivialCircuit`. -/
theorem gate_rejects_wide (oracleDegree n : ℕ) :
    ∃ bits : List Bool,
      RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
          ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)
          < (decodedOracle sources k clock n bits).size ∧
        C10TotalDecode.oracleOf sources k clock oracleDegree n bits
          = C10TotalDecode.trivialCircuit
            ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n) := by
  obtain ⟨bits, hbits⟩ := decoded_size_unbounded sources k clock n
    (RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
      ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n) + 1)
  have hgt : ¬ (decodedOracle sources k clock n bits).size ≤
      RecoveryScheduleEnvelope.oracleSizeBound oracleDegree
        ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n) := by
    omega
  refine ⟨bits, by omega, ?_⟩
  rw [oracleOf_eq_if, if_neg hgt]

end
end NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
