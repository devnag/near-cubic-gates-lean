import Proof.Amplification.RecoveryCertificateCountTotal
import Proof.PCP.VerifierDecodingField

/-! The existing physical field copier at the literal flat-certificate ABI.
The all-input bound depends on the original scalar width. No whole witness
length scan is needed to decide the semantic readField guard. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCertificateField
open LocalBitMultitape
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bounded_read (width : Nat) (pre word backing : List Bool)
    (hb : backing.length≤2*width+1) :
    ∃ receipt : ExecutionReceipt 3 6,
      runFrom FieldMachine.machine (4*width+2)
        (FieldMachine.scan 0 (pre++frame word) pre.length width 0 [] backing)=some receipt ∧
      (receipt.final.control=4 ↔ (readField width word).isSome=true) ∧
      (width≤word.length → receipt.final=FieldMachine.finished (pre++frame word)
        (frame (word.take width)) (pre.length+2*width) width) := by
  by_cases hw : width≤word.length
  · have hlen : (word.take width).length=width := by simp [List.length_take,hw]
    have hsource : pre++Streaming.marks (word.take width)++frame (word.drop width)=pre++frame word := by
      rw [List.append_assoc,← Streaming.frame_append,List.take_append_drop]
    obtain ⟨r,hr,hf,_,_⟩ := FieldMachine.field_run pre (word.take width) (frame (word.drop width)) backing
      (by rw [hlen]; exact hb)
    rw [hlen,hsource] at hr hf
    exact ⟨r,hr,by simp [hf,FieldMachine.finished,readField,hw],fun _ => hf⟩
  · obtain ⟨r,hr,hf,_,_⟩ := FieldMachine.field_reject_run pre word backing width (by omega) hb
    have ht : 2*word.length+1≤4*width+2 := by omega
    have hm := runFrom_moreFuel FieldMachine.machine (2*word.length+1)
      (4*width+2-(2*word.length+1)) _ r hr
    rw [Nat.add_sub_of_le ht] at hm
    exact ⟨r,hm,by simp [hf,FieldMachine.scan,readField,hw],by intro h; contradiction⟩

end NearCubicWires.RepairOrdinary.RecoveryCertificateField
