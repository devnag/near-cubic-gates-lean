import Proof.Amplification.RecoveryCanonicalNative

/-! The canonical row tables are exact readable prefixes of the buffers
physically copied with the existing whole-witness length driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def innerRest (code : Nat) (c : Certificate) := packList (packRow (Serialization.width code)) c.outer++
  List.replicate ((witness code c).length-(innerBits code c).length) false
def outerRest (code : Nat) (c : Certificate) :=
  List.replicate ((witness code c).length-(outerBits code c).length) false

theorem suffix_lengths (code : Nat) (c : Certificate) :
    (innerBits code c).length≤(witness code c).length ∧
      (outerBits code c).length≤(witness code c).length := by
  simp only [innerBits,outerBits,witness,TableFirst.pack,packList,List.length_append,
    List.length_replicate,List.length_singleton]
  omega

theorem row_fits (code : Nat) (c : Certificate) (hc : Fits code c)
    (row : BalancedCertificate.Row) (hm : row∈c.inner++c.outer) :
    RowFitsWidth (Serialization.width code) row := by
  have h := hc.2.2.2.2.2 row hm
  have hb := Serialization.fields_fit code
  exact ⟨h.2.2.2.trans_lt hb.2.2,h.1.trans_lt hb.1,
    h.2.2.1.trans_lt hb.2.1,h.2.1.trans_lt hb.1⟩

theorem inner_rows (code : Nat) (c : Certificate) (hc : Fits code c) :
    readMany (readRow (RecoveryColdView.width code.bits)) c.inner.length (innerBuffer code c)=
      some (c.inner,innerRest code c) := by
  unfold innerBuffer
  rw [RecoveryColdCompact.buffer_eq _ _ (suffix_lengths code c).1,width_code]
  change readMany (readRow (Serialization.width code)) c.inner.length
    ((c.inner.flatMap (packRow (Serialization.width code))++
      packList (packRow (Serialization.width code)) c.outer)++_)=_
  rw [List.append_assoc]
  apply readMany_pack
  intro row hm rest
  exact readRow_pack _ row (row_fits code c hc row (List.mem_append_left _ hm)) rest

theorem outer_rows (code : Nat) (c : Certificate) (hc : Fits code c) :
    readMany (readRow (RecoveryColdView.width code.bits)) c.outer.length (outerBuffer code c)=
      some (c.outer,outerRest code c) := by
  unfold outerBuffer
  rw [RecoveryColdCompact.buffer_eq _ _ (suffix_lengths code c).2,width_code]
  apply readMany_pack
  intro row hm rest
  exact readRow_pack _ row (row_fits code c hc row (List.mem_append_right _ hm)) rest

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
