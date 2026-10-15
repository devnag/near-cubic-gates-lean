import Proof.SourceAssembly.MaskSource

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
open FixedLivePackets PacketProduction
namespace SourceAssemblyBundle
open MaskedFamilySource
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes ControllerSelectedContinuation.bodyTapes

abbrev Choices : Type :=
  Σ (capIndex : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
  Σ (remainingDegree : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
  Σ (r : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
  Σ (base : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
  Σ (scratch : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
  Σ (site : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Bool → NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Σ states,
     NearCubicWires.LocalBitMultitape.Machine
     (NearCubicWires.P1TopDown.ControllerSelectedContinuation.bodyTapes sources p
      (NearCubicWires.P1TopDown.ControllerCappedRuntime.hierarchyIndex sources p
       (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p))
      (r sources gamma hg hh p) (scratch sources gamma hg hh p)) states)),
  Σ (remainingFuel : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat → Nat)),
  Σ (widths : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
    (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → Phase → Nat)),
  Σ (remainingCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
  Σ (remainingOnset : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
  Σ (tableCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
  ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)

noncomputable abbrev Choices.capIndex (d : Choices) := d.1

noncomputable abbrev Choices.remainingDegree (d : Choices) := d.2.1

noncomputable abbrev Choices.r (d : Choices) := d.2.2.1

noncomputable abbrev Choices.base (d : Choices) := d.2.2.2.1

noncomputable abbrev Choices.scratch (d : Choices) := d.2.2.2.2.1

noncomputable abbrev Choices.site (d : Choices) := d.2.2.2.2.2.1

noncomputable abbrev Choices.remainingFuel (d : Choices) := d.2.2.2.2.2.2.1

noncomputable abbrev Choices.widths (d : Choices) := d.2.2.2.2.2.2.2.1

noncomputable abbrev Choices.remainingCoefficient (d : Choices) := d.2.2.2.2.2.2.2.2.1

noncomputable abbrev Choices.remainingOnset (d : Choices) := d.2.2.2.2.2.2.2.2.2.1

noncomputable abbrev Choices.tableCoefficient (d : Choices) := d.2.2.2.2.2.2.2.2.2.2.1

noncomputable abbrev Choices.tableDegree (d : Choices) := d.2.2.2.2.2.2.2.2.2.2.2

def Physical (mask : MaskProducer) (selector : CyclicChoice.Laws) (packets : MaskedFamilySource.PacketLibrary selector) (rows : MaskedFamilySource.RowLibrary selector) (compiler : Packets.CompilerLaws) (tables : TableCertificate) (semantics : Certificate) (buildSource : SourceBuilder) (d : Choices) : Prop :=
  let capIndex := Choices.capIndex d
  let remainingDegree := Choices.remainingDegree d
  let r := Choices.r d
  let base := Choices.base d
  let scratch := Choices.scratch d
  let site := Choices.site d
  let remainingFuel := Choices.remainingFuel d
  let widths := Choices.widths d
  let remainingCoefficient := Choices.remainingCoefficient d
  let remainingOnset := Choices.remainingOnset d
  let tableCoefficient := Choices.tableCoefficient d
  let tableDegree := Choices.tableDegree d
  (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → (MaskedSelected mask selector packets rows compiler tables semantics buildSource) sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n) (widths sources gamma hg hh p n x bits))

def Runtime (d : Choices) : Prop :=
  let capIndex := Choices.capIndex d
  let remainingDegree := Choices.remainingDegree d
  let r := Choices.r d
  let base := Choices.base d
  let scratch := Choices.scratch d
  let site := Choices.site d
  let remainingFuel := Choices.remainingFuel d
  let widths := Choices.widths d
  let remainingCoefficient := Choices.remainingCoefficient d
  let remainingOnset := Choices.remainingOnset d
  let tableCoefficient := Choices.tableCoefficient d
  let tableDegree := Choices.tableDegree d
  open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1TopDown in
  ∀ (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma),
   let C := ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p);
   ∀ n, remainingOnset sources gamma hg hh p≤n → remainingFuel sources gamma hg hh p n+3≤
   remainingCoefficient sources gamma hg hh p*(n+1)^(remainingDegree sources gamma hg hh p)+
   tableCoefficient sources gamma hg hh p*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree sources gamma hg hh p+2)*
   SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^(tableDegree sources gamma hg hh p))

def Construction (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
    (tables : TableCertificate) (semantics : Certificate) : Prop :=
  ∀ mask packets rows buildSource, ∃ d : Choices,
    Physical mask selector packets rows compiler tables semantics buildSource d ∧ Runtime d

theorem assemble (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
    (tables : TableCertificate) (semantics : Certificate)
    (built : Construction selector compiler tables semantics) :
    RemainingSource selector compiler tables semantics := by
  intro mask packets rows buildSource
  obtain ⟨d, phases, bounded⟩ := built mask packets rows buildSource
  exact ⟨Choices.capIndex d, Choices.remainingDegree d, Choices.r d,
    Choices.base d, Choices.scratch d, Choices.site d, Choices.remainingFuel d,
    Choices.widths d, phases, Choices.remainingCoefficient d, Choices.remainingOnset d,
    Choices.tableCoefficient d, Choices.tableDegree d, bounded⟩

end
end SourceAssemblyBundle
end
