import Proof.CaseAnalysis.RowsCircuitThresholdBody

/-! The original canonical bottom field stream already is the counted
word list consumed by the body. No serializer or second traversal is added. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitWords
open LocalBitMultitape RadixSemantics PCPPNativeCanonicalTree
open CloseoutRowsCircuitHeader CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words (bits : List Bool):=Reencode.fields (codeWord bits 2)

theorem code_length (bits : List Bool) (i : Fin 4) : (codeWord bits i).length=bits.length:=
  (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)

theorem words_count (bits : List Bool) :
    (words bits).length=CloseoutRowsCircuitCount.count (codeWord bits 2):=by
  simp only [words,Reencode.fields,List.length_map,CloseoutRowsCircuitCount.count]

theorem count_bound (bits : List Bool) : (words bits).length ≤ bits.length+1:=by
  rw [words_count]
  exact (CloseoutRowsCircuitCount.count_bound _).trans (by rw [code_length])

theorem word_length (bits b : List Bool) (hb : b∈words bits) : b.length=bits.length:=by
  obtain ⟨a,_ha,rfl⟩:=List.mem_map.mp hb
  exact (SignedSortKey.binary_length _ _).trans (code_length bits 2)

theorem stream (bits : List Bool) : (words bits).flatMap frame=
    PCPPNativeCanonicalWalk.atomStream (codeWord bits 2).length (tree (value (codeWord bits 2))).atoms:=
  Reencode.fields_stream (codeWord bits 2)

theorem stream_length (bits : List Bool) :
    ((words bits).flatMap frame).length=(words bits).length*(2*bits.length+1):=by
  rw [List.length_flatMap]
  have each:(words bits).map (fun b=>(frame b).length)=(words bits).map (fun _=>2*bits.length+1):=by
    apply List.map_congr_left
    intro b hb
    rw [frame_length,word_length bits b hb]
  rw [each,List.map_const',List.sum_replicate]
  rfl

theorem values (bits : List Bool) : PCPSerializerMass.values (words bits)=
    (tree (value (codeWord bits 2))).atoms:=Reencode.fields_values _

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitWords
