import Proof.MachineModel.ClosureBinaryRequest
import Proof.MachineModel.ClosureCompactFamily

/-! The physical compact writer at the binary-order pool. Length-proof casts
change only the types of the old indices: raw source bytes and mask-bank
bytes are unchanged. The fixed cold writer computes its metadata and emits
the literal binary request header, with complete final heads and tapes.
Physical cache/dimension/raw-source construction remains an upstream duty.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryWriter
open LocalBitMultitape RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput
open ExtIncidence ExtDecompositionBatch RepairSource.VerifierDecoding

def castPacket {B N : Nat} (h : B=N) (ms : List (List (Fin B))) : List (List (Fin N)) :=
  ms.map (List.map (Fin.cast h))

theorem castPacket_length {B N : Nat} (h : B=N) (ms : List (List (Fin B))) :
    (castPacket h ms).length=ms.length := List.length_map _

theorem rawIndices_cast {B N : Nat} (h : B=N) (ms : List (List (Fin B))) :
    rawIndices (castPacket h ms)=rawIndices ms := by
  subst N
  simp [castPacket]

theorem rawRows_cast {B N : Nat} (h : B=N) (ms : List (List (Fin B))) :
    rawRows (castPacket h ms)=rawRows ms := by
  subst N
  simp [castPacket]

theorem rawWord_cast {B N : Nat} (h : B=N) (ms : List (List (Fin B))) :
    P1CompactNativeFamily.rawWord (castPacket h ms)=P1CompactNativeFamily.rawWord ms := by
  simp only [P1CompactNativeFamily.rawWord,rawIndices_cast]

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial)

noncomputable def packets : List (List (List (Fin (BinaryPool.pool a live occ s harity).length))) :=
  (ps a live occ s harity P).map (castPacket (BinaryPool.pool_length a live occ s harity).symm)

theorem packets_length : (packets a live occ s harity P).length=(ps a live occ s harity P).length :=
  List.length_map _

theorem bank_eq : NativeRowInput.bank (packets a live occ s harity P)=bank a live occ s harity P := by
  simp only [packets,bank,NativeRowInput.bank,List.map_map,Function.comp_def,rawRows_cast]

theorem raw_source_eq : (packets a live occ s harity P).flatMap P1CompactNativeFamily.rawWord =
    (ps a live occ s harity P).flatMap P1CompactNativeFamily.rawWord := by
  simp only [packets,List.flatMap_map,rawWord_cast]

theorem rows_lt (w : Nat) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w) :
    ∀ ms∈packets a live occ s harity P,ms.length<2^w := by
  intro ms hm
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
  rw [castPacket_length]
  exact ps_rows_lt a live occ s harity P w hmon old ho

variable (w degree : Nat) (hs : 67 ≤ s)
  (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
  (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
  (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)

theorem stream_eq :
    letI := BinaryRequest.radix a live occ s harity degree
    CloseoutRowsEstimator.Header.stream
      (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree) =
      (packets a live occ s harity P).flatMap
        (P1CompactNativeFamily.emit (BinaryPool.pool a live occ s harity) (live.card+1) w) := by
  letI := BinaryRequest.radix a live occ s harity degree
  simp only [BinaryRequest.input,P1CompactInput.input,CloseoutRowsEstimator.Header.stream,
    CloseoutRows.commonInput,CloseoutRows.commonWidth]
  rw [←bank_eq a live occ s harity P]
  simp only [NativeRowInput.bank,List.flatMap_map,List.flatMap_assoc]
  rfl

theorem run (out pre tail : List Bool) :
    letI := BinaryRequest.radix a live occ s harity degree
    Step CompactColdFamily.machine
      (CompactColdFamily.budget (BinaryPool.pool a live occ s harity) (live.card+1) w
        (packets a live occ s harity P))
      (CompactColdFamily.ambientH out pre)
      (CompactNativeInitialize.input (BinaryPool.pool a live occ s harity) (live.card+1) w
        (ps a live occ s harity P).length
        (pre++(ps a live occ s harity P).flatMap P1CompactNativeFamily.rawWord++tail) out)
      (CompactColdFamily.finalHeads (BinaryPool.pool a live occ s harity) (live.card+1) w
        (packets a live occ s harity P) out pre tail)
      (CompactColdFamily.finalTapes (BinaryPool.pool a live occ s harity) (live.card+1) w
        (packets a live occ s harity P) out pre tail) ∧
    CompactColdFamily.finalTapes (BinaryPool.pool a live occ s harity) (live.card+1) w
      (packets a live occ s harity P) out pre tail 180 =
        out ++ CloseoutRowsEstimator.Header.stream
          (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree) := by
  letI := BinaryRequest.radix a live occ s harity degree
  letI := BinaryRequest.bankDegree a live occ s harity P degree hdegree
  constructor
  · have hmask : ∀ ms∈packets a live occ s harity P,
        P1MaskDegree (BinaryPool.pool a live occ s harity) (rawRows ms) := by
      intro ms hm
      apply P1BankDegree.bound (bank:=bank a live occ s harity P)
      rw [←bank_eq a live occ s harity P]
      exact List.mem_map.mpr ⟨ms,hm,rfl⟩
    have h := CompactColdFamily.family_run (BinaryPool.pool a live occ s harity) (live.card+1) w
      (packets a live occ s harity P) out pre tail hmask
      (rows_lt a live occ s harity P w hmon) (by omega)
    simpa only [CompactColdFamily.source,packets_length,raw_source_eq] using h
  · rw [CompactColdFamily.output_word,stream_eq]

end NearCubicWires.P1Closure.BinaryWriter
