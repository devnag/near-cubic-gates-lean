import Proof.Amplification.RecoveryValuationStream

/-! All-code correspondence between the serialized valuation-entry parser
and the actual read-and-check row controller, including every short suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationStream
open LocalBitMultitape RadixSemantics
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem readEntry_full (width : Nat) (bits : List Bool) (h : width<bits.length) :
    readEntry width bits=some ((value (bits.take width),bits[width]?.getD false),bits.drop (width+1)) := by
  have hd := List.drop_eq_getElem_cons h
  have hfield : readField width bits=some (value (bits.take width),bits.drop width) := by
    simp only [readField,if_pos (by omega : width≤bits.length)]
  unfold readEntry
  rw [hfield]
  change (readBit (bits.drop width)).bind (fun pair=>some ((value (bits.take width),pair.1),pair.2))=_
  rw [hd,List.getElem?_eq_getElem h]
  rfl

theorem readEntry_short (width : Nat) (bits : List Bool) (h : bits.length<width+1) :
    readEntry width bits=none := by
  by_cases hw : width≤bits.length
  · have hd : bits.drop width=[] := List.drop_eq_nil_iff.mpr (by omega)
    simp [readEntry,readField,hw,readBit,hd]
  · simp [readEntry,readField,hw]

theorem readEntry_isSome (width : Nat) (bits : List Bool) :
    (readEntry width bits).isSome=decide (width+1≤bits.length) := by
  by_cases h : width<bits.length
  · simp [readEntry_full width bits h,show width+1≤bits.length by omega]
  · simp [readEntry_short width bits (by omega),show ¬width+1≤bits.length by omega]

def readKey (d : Data) (bits : List Bool) := bits.take d.width
def readValue (d : Data) (bits : List Bool) := bits[d.width]?.getD false

theorem bounded_read (d : Data) (pre bits : List Bool)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length)
    (hi : d.index.length=d.width) (hb : d.row.length≤2*(d.width+1)+1) :
    ∃ r : ExecutionReceipt 8 (Fintype.card (RecoveryCalls.Control sizes)),
      runFrom machine (budget d.width) (d.cfg machine.start)=some r ∧
      r.final.tapes 7=[(readEntry d.width bits).isSome] ∧ r.final.heads 7=0 ∧
      ((readEntry d.width bits).isSome=true →
        r.final=(d.done (readKey d bits) (readValue d bits)).cfg (RecoveryCalls.controlCode sizes none)) ∧
      r.steps≤budget d.width := by
  by_cases h : d.width<bits.length
  · have hkey : (readKey d bits).length=d.width := by simp [readKey,List.length_take,show d.width≤bits.length by omega]
    have htake : bits.take (d.width+1)=readKey d bits++[readValue d bits] := by
      change bits.take (d.width+1)=bits.take d.width++[bits[d.width]?.getD false]
      rw [List.getElem?_eq_getElem h]
      exact List.take_succ_eq_append_getElem h
    have hsource : d.source=pre++Streaming.marks (readKey d bits++[readValue d bits])++frame (bits.drop (d.width+1)) := by
      rw [←htake,List.append_assoc,←Streaming.frame_append,List.take_append_drop]
      exact hs
    obtain ⟨r,hr,hf,ht⟩ := success_run d pre (readKey d bits) (frame (bits.drop (d.width+1)))
      (readValue d bits) hsource hp hi hkey hb
    exact ⟨r,hr,by simp [hf,Data.cfg,Data.done,readEntry_full _ _ h],by rw [hf]; rfl,fun _=>hf,ht⟩
  · have hshort := readEntry_short d.width bits (by omega)
    obtain ⟨r,hr,hf,hh,ht⟩ := failure_run d pre bits hs hp (by omega) hb
    exact ⟨r,hr,by simpa only [hshort,Option.isSome_none] using hf,hh,
      by simp only [hshort,Option.isSome_none,Bool.false_eq_true,IsEmpty.forall_iff],ht⟩

end NearCubicWires.RepairOrdinary.RecoveryValuationStream
