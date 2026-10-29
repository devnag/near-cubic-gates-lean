import Proof.Assembly.RowAdapter

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open NativeRecipes
namespace FixedLivePackets
noncomputable section

abbrev datumValue (d : P1TopDownPaidReusable.Datum) : Nat :=
  (selected (CompetitorSelectedCells.cells d.row.odd d.f d.select)).sum

def dataList {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (layout : Packets.Layout a F g)
    (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r) : List Datum :=
  F.rows.attach.map (fun r => Packets.datum a F g layout r.val r.property (facts r.val r.property))

/-- All analytic and semantic facts refer to the specified packets and mask. -/
def TableCertificate : Prop :=
  ∀ (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp))
    (g : Packets.Geometry (Packets.request sources L target mode atoms))
    (layout : Packets.Layout (decompositionOf sources) (Packets.request sources L target mode atoms) g)
    (facts : ∀ r ∈ (Packets.request sources L target mode atoms).rows,
      Packets.PacketFacts (decompositionOf sources) (Packets.request sources L target mode atoms) g r),
    let ds := dataList (decompositionOf sources) (Packets.request sources L target mode atoms) g layout facts
    (∀ d ∈ ds,
      (∀ i j, d.f i j < 2^d.Q) ∧
      (∀ i : Fin ((EquationRow.request d.row).U*(EquationRow.request d.row).U),
        Int.ModEq ((2 : Int)^d.Q)
          (SupplierPrinter.weightedDominance (leftScore (EquationRow.request d.row))
            (rightScore (EquationRow.request d.row)) (weight (EquationRow.request d.row)) i.divNat i.modNat)
          (d.f i.divNat i.modNat))) ∧
    (ds.map datumValue).sum = (LiveRows.fraction sources L target mode atoms).1

structure Resources (a : WilliamsAlgorithm) (B R S : Nat) (d : Datum) : Prop where
  capacity : (Header.stream d.row).length ≤ d.C
  precision : d.Q ≤ (EquationRow.request d.row).p
  rewind : P1TopDownPaidReloadCore.fuel a d.row d.C d.Q ≤ R
  buffer : RowPayload.budget (scalarWidth (EquationRow.request d.row) d.Q) ≤ B
  reset : B+1 ≤ R
  workspace : P1TopDownPaidReloadCore.budget a d.row d.C d.Q B+1 ≤ S
  bufferWorkspace : B ≤ S

def NativeRows (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
    (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (printer : WilliamsAlgorithm)
    (S R B b : Nat) (ds : List Datum) (total denominator : Nat) : Prop :=
  let F := Packets.request sources L target mode atoms
  let g := Packets.geometry selector F
  ∃ layout : Packets.Layout (decompositionOf sources) F g,
    ds = dataList (decompositionOf sources) F g layout (compiler sources L target mode atoms g) ∧
    (∀ d ∈ ds, Resources printer B R S d) ∧
    (∀ d ∈ ds, scalarWidth (EquationRow.request d.row) d.Q = b) ∧
    total = (LiveRows.fraction sources L target mode atoms).1 ∧
    denominator = (LiveRows.fraction sources L target mode atoms).2

def ValuesContract (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) : Prop :=
  ∀ (sources : EightSources) (L target : Nat) (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (printer : WilliamsAlgorithm)
    (S R B b : Nat) (ds : List Datum) (total denominator : Nat),
    NativeRows selector compiler sources L target mode atoms printer S R B b ds total denominator →
    (∀ k (hk : k < ds.length), Valid printer B R S ds[k]) ∧
    ds.map Datum.emit = (ds.map datumValue).map (SignedSortKey.binary b) ∧
    (∀ x ∈ ds.map datumValue, x < 2^b) ∧ (ds.map datumValue).sum = total

theorem values (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
    (tables : TableCertificate) : ValuesContract selector compiler := by
  intro sources L target mode q circuit pcpp atoms printer S R B b ds total denominator h
  obtain ⟨layout,hds,hresource,hwidth,htotal,hden⟩ := h
  have table := tables sources L target mode atoms
    (Packets.geometry selector (Packets.request sources L target mode atoms)) layout
    (compiler sources L target mode atoms (Packets.geometry selector (Packets.request sources L target mode atoms)))
  rw [← hds] at table
  refine ⟨?_,?_,?_,table.2.trans htotal.symm⟩
  · intro k hk
    have mem := List.getElem_mem hk
    have resource := hresource _ mem
    have semantic := table.1 _ mem
    exact ⟨resource.capacity,resource.precision,semantic.1,semantic.2,
      resource.rewind,resource.buffer,resource.reset,resource.workspace,resource.bufferWorkspace⟩
  · rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    unfold Datum.emit
    rw [hwidth d hd]
    rfl
  · intro x hx
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
    rw [← hwidth d hd]
    apply CompetitorSelectedCount.scalar_fit
    · exact CompetitorSelectedCells.cells_length d.row.odd d.f d.select
    · exact CompetitorSelectedCells.cells_fit d.Q d.row.odd d.f d.select (table.1 d hd).1

end
end FixedLivePackets
