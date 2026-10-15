import Proof.MachineModel.ClosureBinaryPreparedWriter
import Proof.MachineModel.ClosureLocalSupport

/-! The header capacity follows from its executed producer, rather than
being an extra answer-size assumption. Its allocation remains paid input
until the enclosing cold initialization constructs the runtime driver. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryHeaderCapacity
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput

theorem initialized_output {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (Q w M : Nat) (source out : List Bool) :
    CompactNativeInitialize.input gs Q w M source out 180=out := by
  unfold CompactNativeInitialize.input
  rw [install_other _ _ _ _ (by decide : ∀ j,CompactNativeInitialize.metadataSlots j≠180)]
  rfl

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

theorem header_length {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (s : Nat) (harity : (s+1)/2+s/2=liveᶜ.card)
    (P : StructuralGF2Polynomial) (w degree S : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length<2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)
    (hS : (stream (CloseoutRowsUniversal.lower a live occ P)).length ≤ S) :
    (CloseoutRowsEstimator.Header.stream
      (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree)).length ≤ 
      BinaryPreparedWriter.budget a live occ s harity P w degree S+1 := by
  letI:=BinaryRequest.radix a live occ s harity degree
  obtain ⟨written,hword⟩:=BinaryPreparedWriter.run a live occ s harity P w degree S [] []
    hs hmon hpos hload hdegree hS
  simp only [List.nil_append] at hword
  have blank : BinaryPreparedWriter.entry a live occ s harity P w degree S [] [] 180=[] := by
    change CompactNativeInitialize.input (BinaryPool.pool a live occ s harity) (live.card+1) w
      (2^live.card) [] [] 180=[]
    exact initialized_output _ _ _ _ _ _
  have bound:=LocalSupport.step_fits written 180
    (BinaryPreparedWriter.budget a live occ s harity P w degree S+1)
    (by rw [blank];exact Nat.zero_le _) (by change 0+_+1 ≤ _;omega)
  rw [hword] at bound
  exact bound

end NearCubicWires.P1Closure.BinaryHeaderCapacity
