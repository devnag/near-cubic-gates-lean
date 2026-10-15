import Proof.CaseAnalysis.RowsGateSourceLayout

/-! The original cold gate parser, exact public guard and original CW
decomposition execute in one guarded machine. Ordinary bottom gates and
support-compressed retained tops specialize the same request handoff. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces RecoveryRootRound
open CanonicalBinary CanonicalWitnessCodec SupplierPipeline RadixSemantics CompilerSemantics
open CloseoutRowsGateSupport DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem call_run {core : ℕ} (a : DecompositionAlgorithm) (compressed : Bool)
    (g : SupportedNormalizedGate core) (bits : List Bool) (request : ExactDecompositionRequest)
    (h : decodeSupportedNormalizedGate core (value bits)=some g)
    (word : CloseoutRowsGateNative.word compressed (gateFields g.gate) (gateMembers g.support)
      (CloseoutRowsGateCold.signSource bits) g.gate.threshold.natAbs=thresholdWord request.gate) :
    ∃ r,runFrom (machine a compressed) (budget a bits request)
      (RecoveryCalls.restarted (machine a compressed) (heads a) (input a core bits))=some r ∧
      r.steps≤budget a bits request ∧ Output a request r.final := by
  obtain ⟨decoded,hd,meaning⟩ := CloseoutRowsGateGuard.guard_run compressed core bits
  have native : decoded 1033=frame (thresholdWord request.gate) := by
    rw [meaning.2.2 g h,word]
  obtain ⟨source,hs,_ss,fields⟩ := source_run a request decoded native
  obtain ⟨r,hr,rt,rh,rs⟩ := CloseoutRowsGateSourceCalls.joined (first a compressed) (second a)
    (fun scanned => scanned (old a 1037)) _ _ (heads a) _ _
    (first_run a compressed core bits decoded hd) source hs (by
      change readTapeBit (decoded 1037) 0=true
      exact meaning.2.1.mpr (by rw [h];rfl))
  refine ⟨r,hr,rs,?_⟩
  unfold Output at fields ⊢
  rw [rt,rh]
  exact fields

theorem ordinary_run {core : ℕ} (a : DecompositionAlgorithm) (g : SupportedNormalizedGate core)
    (bits : List Bool) (h : decodeSupportedNormalizedGate core (value bits)=some g) :
    ∃ r,runFrom (machine a false) (budget a bits ⟨core,nonStrictAsStrict g.gate⟩)
      (RecoveryCalls.restarted (machine a false) (heads a) (input a core bits))=some r ∧
      r.steps≤budget a bits ⟨core,nonStrictAsStrict g.gate⟩ ∧
      Output a ⟨core,nonStrictAsStrict g.gate⟩ r.final :=
  call_run a false g bits ⟨core,nonStrictAsStrict g.gate⟩ h
    (CloseoutRowsGateNative.ordinary_word g _ (CloseoutRowsGateGuard.sign_of_gate g bits h))

theorem retained_run {core : ℕ} (a : DecompositionAlgorithm) (c : NormalizedThresholdThresholdCircuit core)
    (bits : List Bool) (h : decodeSupportedNormalizedGate c.bottomCount (value bits)=some c.top) :
    ∃ r,runFrom (machine a true) (budget a bits ⟨c.top.support.card,nonStrictAsStrict (retainedTopGate c)⟩)
      (RecoveryCalls.restarted (machine a true) (heads a) (input a c.bottomCount bits))=some r ∧
      r.steps≤budget a bits ⟨c.top.support.card,nonStrictAsStrict (retainedTopGate c)⟩ ∧
      Output a ⟨c.top.support.card,nonStrictAsStrict (retainedTopGate c)⟩ r.final :=
  call_run a true c.top bits ⟨c.top.support.card,nonStrictAsStrict (retainedTopGate c)⟩ h
    (CloseoutRowsGateNative.retained_word c _ (CloseoutRowsGateGuard.sign_of_gate c.top bits h))

theorem budget_bound (a : DecompositionAlgorithm) (bits : List Bool) (request : ExactDecompositionRequest) :
    budget a bits request≤4000000000000000000001020*(bits.length+2)^26+2+
      DecompositionSource.coefficient a*(request.arity+request.gate.encodingBits+1)^DecompositionSource.degree a := by
  have hg := CloseoutRowsGateGuard.budget_bound bits
  have hs := DecompositionSource.entry_budget a request
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
