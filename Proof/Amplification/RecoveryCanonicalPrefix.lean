import Proof.Amplification.RecoveryVerifier

/-! Canonical witness valuationPrefix facts at the actual cold parser boundary.
These identify the retained valuation cursor without a second parser or
an extra certificate field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_code (code : Nat) : RecoveryColdView.width code.bits=Serialization.width code := by
  change max 1 code.bits.length+2=natBitLength code+2
  rw [RecoveryColdAllCode.bound_code]

theorem limit_code (code : Nat) : RecoveryColdView.limit code.bits=TableFirst.limit code := by
  change 3*(max 1 code.bits.length+1)=3*(natBitLength code+1)
  rw [RecoveryColdAllCode.bound_code]

def valuationPrefix (code : Nat) (c : Certificate) := packList (packEntry (Serialization.width code)) c.table
def suffix (code : Nat) (c : Certificate) :=
  RawSyntaxCertificate.pack (Serialization.width code) c.view++
    (packList (packRow (Serialization.width code)) c.inner++
      packList (packRow (Serialization.width code)) c.outer)

theorem word_eq (code : Nat) (c : Certificate) :
    TableFirst.pack (Serialization.width code) c=valuationPrefix code c++suffix code c := by
  simp only [TableFirst.pack,valuationPrefix,suffix,List.append_assoc]

theorem suffix_pos (code : Nat) (c : Certificate) : 0<(suffix code c).length := by
  simp only [suffix,List.length_append,RawSyntaxCertificate.pack,List.length_replicate,
    List.length_singleton]
  omega

theorem valuation_parse (code : Nat) (c : Certificate) (hc : Fits code c) :
    readList (RecoveryColdView.limit code.bits) (readEntry (RecoveryColdView.width code.bits))
      (TableFirst.pack (Serialization.width code) c)=some (c.table,suffix code c) := by
  rw [limit_code,width_code,word_eq]
  have hlim := (TableFirst.counts_fit code).2.1
  apply readList_pack _ _ _ _ (hc.2.1.trans hlim)
  intro entry he rest
  exact readEntry_pack _ entry ((hc.2.2.1 entry he).trans_lt (fields_fit code).1) rest

theorem prefix_length (code : Nat) (c : Certificate) :
    (valuationPrefix code c).length=c.table.length*(RecoveryColdView.width code.bits+2)+1 := by
  unfold valuationPrefix
  rw [packList_length _ _ (Serialization.width code+1) (by intro entry _; exact packEntry_length _ entry)]
  rw [width_code]
  ring

theorem drop_offset (word pre tail : List Bool) (k : Nat)
    (hw : word=pre++tail) (ht : 0<tail.length) (hd : word.drop k=tail) : k=pre.length := by
  have hl := congrArg List.length hd
  rw [List.length_drop,hw,List.length_append] at hl
  omega

theorem ready_offset (code : Nat) (c : Certificate) (hc : Fits code c)
    (table : List (Nat×Bool)) (tail : List Bool) (count : Nat)
    (hp : readList (RecoveryColdView.limit code.bits) (readEntry (RecoveryColdView.width code.bits))
      (TableFirst.pack (Serialization.width code) c)=some (table,tail))
    (hd : tail=(TableFirst.pack (Serialization.width code) c).drop
      (count*(RecoveryColdView.width code.bits+2)+1)) :
    count*(RecoveryColdView.width code.bits+2)+1=(valuationPrefix code c).length := by
  have he := Option.some.inj (hp.symm.trans (valuation_parse code c hc))
  have ht := congrArg Prod.snd he
  change tail=suffix code c at ht
  rw [ht] at hd
  exact drop_offset _ _ _ _ (word_eq code c) (suffix_pos code c) hd.symm

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
