import Proof.Amplification.RecoveryCanonicalScanner

/-! Exact two-table count parsing for the bounded canonical witness.
Each actual row skip is four times the physically produced scalar width. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def innerBits (code : Nat) (c : Certificate) := c.inner.flatMap (packRow (Serialization.width code))++
  packList (packRow (Serialization.width code)) c.outer
def outerBits (code : Nat) (c : Certificate) := c.outer.flatMap (packRow (Serialization.width code))

theorem table_drop (code : Nat) (c : Certificate) :
    (TableFirst.pack (Serialization.width code) c).drop (tablePosition code c)=tableWords code c := by
  have hw : TableFirst.pack (Serialization.width code) c=
      (valuationPrefix code c++RawSyntaxCertificate.pack (Serialization.width code) c.view)++tableWords code c := by
    simp only [TableFirst.pack,valuationPrefix,tableWords,List.append_assoc]
  have hp : tablePosition code c=
      (valuationPrefix code c++RawSyntaxCertificate.pack (Serialization.width code) c.view).length := by
    simp only [tablePosition,List.length_append]
  rw [hp,hw,List.drop_left]

theorem inner_read (code : Nat) (c : Certificate) (hc : Fits code c) :
    readCount (RecoveryColdView.limit code.bits)
      ((TableFirst.pack (Serialization.width code) c).drop (tablePosition code c))=
      some (c.inner.length,innerBits code c) := by
  rw [table_drop,limit_code]
  have hn := hc.2.2.2.1.trans (TableFirst.counts_fit code).2.1
  simpa only [tableWords,packList,List.append_assoc,List.singleton_append,List.cons_append,
    List.nil_append,innerBits] using
    readCount_pack (TableFirst.limit code) c.inner.length hn (innerBits code c)

theorem rows_length (w : Nat) (rows : List BalancedCertificate.Row) :
    (rows.flatMap (packRow w)).length=4*w*rows.length := by
  induction rows with
  | nil=>simp
  | cons row rows ih=>
    simp only [List.flatMap_cons,List.length_append,packRow_length,ih,List.length_cons]
    ring

theorem inner_drop (code : Nat) (c : Certificate) :
    (innerBits code c).drop (4*RecoveryColdView.width code.bits*c.inner.length)=
      packList (packRow (Serialization.width code)) c.outer := by
  rw [width_code,←rows_length]
  exact List.drop_left

theorem outer_read (code : Nat) (c : Certificate) (hc : Fits code c) :
    readCount (RecoveryColdView.limit code.bits)
      ((innerBits code c).drop (4*RecoveryColdView.width code.bits*c.inner.length))=
      some (c.outer.length,outerBits code c) := by
  rw [inner_drop,limit_code]
  have hn := hc.2.2.2.2.1.trans (TableFirst.counts_fit code).2.2
  simpa only [packList,List.append_assoc,List.singleton_append,outerBits] using
    readCount_pack (TableFirst.limit code) c.outer.length hn (outerBits code c)

theorem table_answer (code : Nat) (c : Certificate) (hc : Fits code c) :
    RecoveryColdTables.answer (RecoveryColdView.width code.bits) (RecoveryColdView.limit code.bits)
      (TableFirst.pack (Serialization.width code) c) (tablePosition code c)=true := by
  simp only [RecoveryColdTables.answer,inner_read code c hc,Option.any_some,outer_read code c hc,
    Option.isSome_some]

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
