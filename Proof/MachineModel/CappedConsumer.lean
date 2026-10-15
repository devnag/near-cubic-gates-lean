import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.MachineModel.CappedDecode
import Proof.CaseAnalysis.FinalDecidesBridgeUniform

/-! Paper C.10's chosen guarded worker reaches the literal Machine/Theorem2.5
consumers. Data choices precede the physical/semantic requirements. Legal
contradiction witnesses use the unchanged pinned SYM/THR bridges at an arbitrary fixed reciprocal cap;
rejected descriptions need no records. The outer onset is independent of the
cold preprocessing cutoff. No physical admission or record run is asserted here. -/
namespace NearCubicWires.P1Independent.CappedConsumer
open RepairSource RepairSource.CloseoutFinal
open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open SelectedRecoveryIntegration CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open C10TotalDecode C10DecidesUniform C10Verdict C10Fusion C10GuardedStageConsumer

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- All implementation choices are fixed before their proof requirements. -/
structure WorkerData where
  den : ℕ
  hden : 0 < den
  k : ℕ
  clock : OrdinaryClock (fun n => n^(k+2))
  tapes : ℕ
  states : ℕ
  worker : LocalBitMultitape.Machine tapes states
  result : Fin tapes
  fuel : ℕ → ℕ
  onset : ℕ
  passed : (n : ℕ) → BitInput n → List Bool → Bool

variable (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma) (W : WorkerData)

/-- The admitted Verdict's oracle and proof value are the selected total decoder's
values. Successful legal decoding pins them to the contradiction witness. -/
def DecodedVerdictAt (ht : 2 ≤ W.tapes) (n : ℕ) (x : BitInput n) (bits : List Bool) : Type 1 :=
  let oracle := oracleOf sources W.k W.clock p.degree n bits
  Σ' (_Atom : Type)
     (evaluate : _Atom → BitInput (req sources W.k W.clock x oracle).arity → Bool)
     (ports : Phase → Fin W.tapes) (width : Phase → ℕ),
     Verdict (constantsOf sources) (pcppAt sources W.k W.clock x oracle)
       (CappedDecode.proofValueOf sources W.k W.clock p W.den x oracle bits) evaluate
       W.worker ht W.fuel n x bits W.result ports width

/-- Exactly the header/oracle/size/typed-family premises of the existing pinned
completeness bridges, with one common fixed positive reciprocal cap. No semantic [0,1] condition. -/
def LegalWitness (n : ℕ) (x : BitInput n) (bits : List Bool) : Prop :=
  16*bits.length ≤ n ∧ CompetitorWitnessTriple.headerValid bits ∧
  ∃ oracle : BooleanCircuit ((outer sources W.k W.clock).result.pcp.nativeWidth n),
    decodeBooleanCircuit ((outer sources W.k W.clock).result.pcp.nativeWidth n)
      (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle ∧
    oracle.size ≤ oracleSizeBound p.degree ((outer sources W.k W.clock).result.pcp.nativeWidth n) ∧
    ((∃ family : CappedDecode.SymFamily sources W.k W.clock p W.den x oracle,
        SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
          NormalizedSymmetricThresholdCircuit.descriptionBits (CappedDecode.symLimits sources W.k W.clock p W.den x oracle)
          (CloseoutWitnessPolicy.variableCount sources W.k W.clock x oracle)
          (RadixSemantics.value (BoundedFields.family bits)) = some family ∧
        BoundedFields.symmetric bits = true) ∨
     (∃ family : CappedDecode.ThrFamily sources W.k W.clock p W.den x oracle,
        SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
          NormalizedThresholdThresholdCircuit.descriptionBits (CappedDecode.thrLimits sources W.k W.clock p W.den x oracle)
          (CloseoutWitnessPolicy.variableCount sources W.k W.clock x oracle)
          (RadixSemantics.value (BoundedFields.family bits)) = some family ∧
        BoundedFields.symmetric bits = false))

/-- These are still construction regions until expanded into short local tasks.
The admitted payload is data in Type1, not an already-proved physical fact. -/
structure Requirements : Type 1 where
  htapes : 2 ≤ W.tapes
  hcut : Soundness.cutoff (constantsOf sources) ≤ W.onset
  rejected : ∀ n x bits, n < W.onset ∨ W.passed n x bits = false →
    RejectedAt W.worker htapes W.result W.fuel n x bits
  admitted : ∀ n x bits, W.onset ≤ n → W.passed n x bits = true →
    DecodedVerdictAt sources p W htapes n x bits
  /-- Existing native guards are proved eventually on dyadic source lengths;
  do not require arbitrary-input admission beyond what completeness consumes. -/
  admits_legal : ∀ s, W.onset ≤ s → ∀ (x : BitInput (2^s)) (guess : BitInput (2^s/16)),
    LegalWitness sources p W (2^s) x (List.ofFn guess) →
    W.passed (2^s) x (List.ofFn guess) = true

variable (H : Requirements sources p W)

/-- One selected machine and budget, shared with both completeness bridges. -/
def pipeline_of_requirements : Pipeline sources W.k W.clock (constantsOf sources)
    W.worker H.htapes W.result W.fuel :=
  pipeline_of_guarded sources W.k W.clock (constantsOf sources)
    W.worker H.htapes W.result W.fuel W.onset W.passed H.rejected
    (fun n x bits hn hp => by
      obtain ⟨Atom, evaluate, ports, width, V⟩ := H.admitted n x bits hn hp
      exact ⟨oracleOf sources W.k W.clock p.degree n bits, Atom, _, evaluate, ports, width, V⟩)

/-- Direct replacement of the overstrong all-input StageBlock shortcut. -/
def machine_of_guarded : CloseoutFinal.Machine sources p.degree p.clauseDegree p.copies where
  k := W.k
  clock := W.clock
  tapes := W.tapes
  states := W.states
  worker := W.worker
  htapes := H.htapes
  result := W.result
  fuel := W.fuel
  pipeline := pipeline_of_requirements sources p W H
  gateOnset := W.onset
  symCap := 1 / (W.den : ℝ)
  thrCap := 1 / (W.den : ℝ)
  hsym := one_div_pos.mpr (Nat.cast_pos.mpr W.hden)
  hthr := one_div_pos.mpr (Nat.cast_pos.mpr W.hden)
  symDecides := symDecides_of_pinned' sources W.k W.clock (constantsOf sources)
    W.worker H.htapes W.result W.fuel p.degree p.clauseDegree p.copies (1 / (W.den : ℝ)) W.onset
    (fun s hs => H.hcut.trans (hs.trans (Nat.lt_two_pow_self).le)) (by
      intro s hs input oracle family guess hlen hheader horacle hsize hfamily hmode
      have hadmit := H.admits_legal s hs input guess
        ⟨hlen, hheader, oracle, horacle, hsize, Or.inl ⟨family, hfamily, hmode⟩⟩
      have ho := oracleOf_pin sources W.k W.clock p.degree (2^s)
        (List.ofFn guess) oracle horacle hsize
      subst oracle
      obtain ⟨Atom, evaluate, ports, width, V⟩ := H.admitted (2^s) input (List.ofFn guess)
        (hs.trans (Nat.lt_two_pow_self).le) hadmit
      have hp := CappedDecode.proofValueOf_sym sources W.k W.clock p W.den input
        (oracleOf sources W.k W.clock p.degree (2^s) (List.ofFn guess))
        (List.ofFn guess) family hmode hfamily
      refine ⟨Atom, evaluate, ports, width, ?_⟩
      rw [← hp]
      exact V)
  thrDecides := thrDecides_of_pinned' sources W.k W.clock (constantsOf sources)
    W.worker H.htapes W.result W.fuel p.degree p.clauseDegree p.copies (1 / (W.den : ℝ)) W.onset
    (fun s hs => H.hcut.trans (hs.trans (Nat.lt_two_pow_self).le)) (by
      intro s hs input oracle family guess hlen hheader horacle hsize hfamily hmode
      have hadmit := H.admits_legal s hs input guess
        ⟨hlen, hheader, oracle, horacle, hsize, Or.inr ⟨family, hfamily, hmode⟩⟩
      have ho := oracleOf_pin sources W.k W.clock p.degree (2^s)
        (List.ofFn guess) oracle horacle hsize
      subst oracle
      obtain ⟨Atom, evaluate, ports, width, V⟩ := H.admitted (2^s) input (List.ofFn guess)
        (hs.trans (Nat.lt_two_pow_self).le) hadmit
      have hp := CappedDecode.proofValueOf_thr sources W.k W.clock p W.den input
        (oracleOf sources W.k W.clock p.degree (2^s) (List.ofFn guess))
        (List.ofFn guess) family hmode hfamily
      refine ⟨Atom, evaluate, ports, width, ?_⟩
      rw [← hp]
      exact V)

/-- The literal headline, conditional on chosen data, its displayed requirements
and Runtime at precisely that chosen k/clock/fuel. No StageBlock is required. -/
theorem theorem25_of_guarded
    (chooseWorker : (sources : EightSources) → ∀ gamma : ℝ, 0 < gamma → gamma < 1/2 →
      (p : Parameters sources gamma) → WorkerData)
    (requirements : (sources : EightSources) → ∀ gamma : ℝ, ∀ hg : 0 < gamma,
      ∀ hh : gamma < 1/2, (p : Parameters sources gamma) →
      Requirements sources p (chooseWorker sources gamma hg hh p))
    (runtime : (sources : EightSources) → ∀ gamma : ℝ, ∀ hg : 0 < gamma,
      ∀ hh : gamma < 1/2, (p : Parameters sources gamma) →
      Runtime sources (chooseWorker sources gamma hg hh p).k
        (chooseWorker sources gamma hg hh p).clock (chooseWorker sources gamma hg hh p).fuel) :
    Theorem25Target :=
  theorem25_of_leaves
    (fun sources gamma hg hh p => machine_of_guarded sources p
      (chooseWorker sources gamma hg hh p) (requirements sources gamma hg hh p))
    runtime

end
end NearCubicWires.P1Independent.CappedConsumer
