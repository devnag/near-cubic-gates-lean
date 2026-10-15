import Proof.CaseAnalysis.Language
import Proof.Hierarchy.HierarchyProjectionPrefix

/-! Reuse the existing cold hierarchy prefix for the schedule's exact native
width. No projection-source invocation or replacement normalization is needed. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary ProjectionNormalization SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def nativeMachine (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) :=
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let source:=fixedProjection sources
  HierarchyPrefix.machine k H.coefficient (padding sources k clock)
    source.degrees.proofLog source.degrees.queries source.coefficient
    (VerifierEncoding.code H.verifier)

def nativeBudget (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (input : List Bool) :=
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let source:=fixedProjection sources
  HierarchyPrefix.budget k H.coefficient (padding sources k clock)
    source.degrees.proofLog source.degrees.queries source.coefficient
    (VerifierEncoding.code H.verifier) input

def nativeInput (sources : EightSources) (k : Nat) (input : List Bool) :=
  HierarchyPrefix.input k (fixedProjection sources).degrees.proofLog
    (fixedProjection sources).degrees.queries input

def nativeRaw (sources : EightSources) (k : Nat) :=
  let source:=fixedProjection sources
  HierarchyPrefix.dimensionSlots k source.degrees.proofLog source.degrees.queries
    (DimensionsFromInput.rawR source.degrees.proofLog source.degrees.queries)

def nativeBits (sources : EightSources) (k : Nat) :=
  let source:=fixedProjection sources
  HierarchyPrefix.dimensionSlots k source.degrees.proofLog source.degrees.queries
    (DimensionsFromInput.bitsR source.degrees.proofLog source.degrees.queries)

theorem native_run (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (input : List Bool) : ∃ out,
    ClockJoin.ReadyRun (nativeMachine sources k clock) (nativeBudget sources k clock input)
      (nativeInput sources k input) out ∧
      out (nativeRaw sources k)=List.replicate ((outer sources k clock).result.pcp.nativeWidth input.length) true ∧
      out (nativeBits sources k)=frame ((outer sources k clock).result.pcp.nativeWidth input.length).bits := by
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let source:=fixedProjection sources
  obtain ⟨out,hr,_,_,_,hraw,hbits,_,_⟩:=HierarchyPrefix.prefix_run k H.coefficient
    (padding sources k clock) (VerifierEncoding.code H.verifier) input (Nat.le_max_right _ _) source
  have hlen : (HierarchyPadding.rawInput k H.coefficient (padding sources k clock)
      (VerifierEncoding.code H.verifier) input).length=
      HierarchyEncode.length H (padding sources k clock) input.length :=
    HierarchyEncode.padded_length H (padding sources k clock) (Nat.le_max_right _ _) input
  rw [hlen] at hraw hbits
  exact ⟨out,hr,hraw,hbits⟩

end
end NearCubicWires.RepairSource.CloseoutSchedule
