import Proof.PCP.PCPPNativeOriginalMass

/-! Same-source metadata and byte counters, on fresh tapes alongside the
literal original hierarchy fields. These are the actual resource inputs. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeMetadataMass
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def queryBytes (p : RawProjectionPCP) (R Q : ℕ) := QueryBytes.framedCodes (normalizedRows p R Q).flatten
def extras (p : RawProjectionPCP) (R Q : ℕ) (i : Fin 19) : List Bool :=
  if i=0 then queryBytes p R Q else if i=2 then VerifierDecoding.CompareMachine.word (R*Q)
  else if i=5 then DedupBytes.fields p else []
def extraHeads (i : Fin 19) : ℕ := if i=2 then 1 else 0
def heads : Fin 71 → ℕ := Fin.addCases (m:=52) (n:=19) (motive:=fun _=>ℕ) PCPPNativeMetadata.heads extraHeads
def input (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) : Fin 71 → List Bool :=
  Fin.addCases (m:=52) (n:=19) (motive:=fun _=>List Bool)
    (PCPPNativeMetadata.input oracle Q (Codec.clauses p).length) (extras p R Q)
def querySlots : Fin 5 → Fin 71 := ![52,53,54,55,56]
def clauseSlots (i : Fin 12) : Fin 71 :=
  if i=0 then 48 else if i=4 then 57 else if i=5 then 58 else ⟨59+i.val,by omega⟩
theorem query_injective : Function.Injective querySlots := by decide
theorem clause_injective : Function.Injective clauseSlots := by decide
noncomputable def first := TapeEmbedding.machine 19 PCPPNativeMetadata.machine
noncomputable def second := RecoveryFocus.machine querySlots PCPSerializerCapacity.MassReady.machine
noncomputable def third := RecoveryFocus.machine clauseSlots PCPPNativeTripleMass.machine
noncomputable def machine := Composition.machine (Composition.machine first second) third
noncomputable def entry (oracle : List Bool) (p : RawProjectionPCP) (R Q : ℕ) :=
  (⟨machine.start,heads,input oracle p R Q⟩ : Configuration 71 _)
def budget (p : RawProjectionPCP) (R Q s : ℕ) :=
  PCPPNativeMetadata.budget R Q s (Codec.clauses p).length+1+(16*(queryBytes p R Q).length+18)+1+
    PCPPNativeTripleMass.budget (DedupBytes.rows p).dedup
def ports : Fin 9 → Fin 71 := ![0,32,36,45,48,52,53,57,58]
def values {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) : Fin 9 → List Bool :=
  ![PCPPNative.descriptor oracle,List.replicate oracle.size true,List.replicate R true,List.replicate Q true,
    List.replicate (Codec.clauses p).length true,queryBytes p R Q,List.replicate (queryBytes p R Q).length true,
    DedupBytes.fields p,List.replicate (DedupBytes.fields p).length true]

end NearCubicWires.RepairOrdinary.PCPPNativeMetadataMass
