import Proof.Assembly.Packets
import Proof.MachineModel.ClosureBinaryRequest
import Proof.MachineModel.ClosureCompactFamily
import Proof.MachineModel.ClosureBinaryPool
import Proof.CaseAnalysis.FinalModeNativeStageFields

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierTouching
open NearCubicWires.SupplierListPolynomial NearCubicWires.SupplierListSchedule
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierRadix
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open scoped BigOperators

namespace FixedLivePackets
open P1Closure CloseoutRawRows
namespace Packets
noncomputable section

structure Layout {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (g : Geometry F) where
  w : Nat
  degree : Nat
  C : Nat
  residualLarge : 67 ≤ residual F
  positiveWidth : 1 ≤ w
  degreeBound : ∀ r ∈ F.rows, r.degree ≤ degree
  widthFromTouch : q * LiveRows.bound F.occurrences (live F) ≤
      normalizedLiveCount q L * supportIncidenceMass (occurrenceSupport F.occurrences) →
    ∀ r ∈ F.rows, (alphabet a F)^r.degree < 2^w
  load : 200*(normalizedLiveCount q L+w*(normalizedLiveCount q L+2)) ≤ residual F

variable {q L : Nat} (a : DecompositionAlgorithm) (F : Family q L) (g : Geometry F)
  (layout : Layout a F g) (r : Row F.occurrences L)

theorem width (hr : r ∈ F.rows) (facts : PacketFacts a F g r) : ∀ ms ∈ packets a F g r, ms.length < 2^layout.w := by
  intro ms hm
  obtain ⟨yi,rfl⟩ := List.mem_ofFn.mp hm
  exact (facts.1 yi).2.2.trans_lt (layout.widthFromTouch g.touch r hr)

abbrev radix : P1Radix (pool a F g) :=
  BinaryRequest.radix a (live F) F.occurrences (residual F) g.arity layout.degree

theorem bankDegree (hr : r ∈ F.rows) (facts : PacketFacts a F g r) :
    letI := radix a F g layout
    P1BankDegree (pool a F g) (ExtIncidence.NativeRowInput.bank (packets a F g r)) := by
  letI := radix a F g layout
  apply p1BankDegree_of_family
  · intro rows hrows bits hbits
    obtain ⟨ms,hms,rfl⟩ := List.mem_map.mp hrows
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hbits
    exact List.length_ofFn
  · apply CompactBounds.raw_family_degree
    intro ms hms m hm
    obtain ⟨yi,rfl⟩ := List.mem_ofFn.mp hms
    exact ((facts.1 yi).2.1 m hm).trans (layout.degreeBound r hr)

theorem gate (hr : r ∈ F.rows) (facts : PacketFacts a F g r) :
    letI := radix a F g layout
    (RowBinLift.batch ((live F).card+1)
      (P1CompactCloseoutRowsCacheInput.family (pool a F g)
        (ExtIncidence.NativeRowInput.bank (packets a F g r)))).length^100 ≤ 2^(residual F) := by
  letI := radix a F g layout
  have hw := ExtIncidence.NativeRowInput.bank_width (packets a F g r) layout.w
    (width a F g layout r hr facts)
  rw [CompactNativeRequest.family_eq,C10SupplierRowInput.batch_length_eq _ _ layout.w _ hw]
  apply raw_cuts_gate (pool a F g) (live F).card layout.w (residual F)
  · simp only [ExtIncidence.NativeRowInput.bank,packets,List.length_map,List.length_ofFn,
      C10SupplierRowInput.liveList_length,le_refl]
  · exact hw
  · exact layout.positiveWidth
  · rw [g.card]
    exact layout.load

def rowInput (hr : r ∈ F.rows) (facts : PacketFacts a F g r) : EquationRow.Input := by
  letI := radix a F g layout
  letI := bankDegree a F g layout r hr facts
  exact P1CompactInput.input (residual F) ((live F).card+1) layout.w (pool a F g)
    (ExtIncidence.NativeRowInput.bank (packets a F g r)) layout.residualLarge
    (gate a F g layout r hr facts)
    (ExtIncidence.NativeRowInput.bank_width (packets a F g r) layout.w
      (width a F g layout r hr facts))

def datum (hr : r ∈ F.rows) (facts : PacketFacts a F g r) : P1TopDownPaidReusable.Datum := by
  letI := radix a F g layout
  let row := rowInput a F g layout r hr facts
  exact
    { row := row
      C := layout.C
      Q := (live F).card+1
      f := CompetitorCountTable.rowValues
        (P1CompactCloseoutRowsCacheInput.family (pool a F g)
          (ExtIncidence.NativeRowInput.bank (packets a F g r))) row
      select := fun i j => r.select (C10ExternalRowLoop.printerPoint (live F) (residual F) g.arity i.val j.val) }

end
end Packets
end FixedLivePackets
