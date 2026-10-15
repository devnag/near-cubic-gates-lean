import Proof.Amplification.RecoveryCertificateParsing

/-! Literal flat certificate serialization and its bounded inverse. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairOrdinary BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readPair (width : Nat) : Parser (Nat×Nat) := fun bits => do
  let (left,rest) ← readField width bits
  let (right,tail) ← readField width rest
  some ((left,right),tail)
def packEntry (width : Nat) (entry : Nat×Bool) : List Bool :=
  SignedSortKey.binary width entry.1++[entry.2]
def readEntry (width : Nat) : Parser (Nat×Bool) := fun bits => do
  let (index,rest) ← readField width bits
  let (bit,tail) ← readBit rest
  some ((index,bit),tail)
def packRow (width : Nat) (row : Row) : List Bool :=
  SignedSortKey.binary width row.kind++SignedSortKey.binary width row.code++
    SignedSortKey.binary width row.count++SignedSortKey.binary width row.payload
def readRow (width : Nat) : Parser Row := fun bits => do
  let (kind,r1) ← readField width bits
  let (code,r2) ← readField width r1
  let (count,r3) ← readField width r2
  let (payload,r4) ← readField width r3
  some (⟨kind,code,count,payload⟩,r4)
def pack (width : Nat) (certificate : Certificate) : List Bool :=
  RawSyntaxCertificate.pack width certificate.view++packList (packEntry width) certificate.table++
    packList (packRow width) certificate.inner++packList (packRow width) certificate.outer
def readCertificate (width limit : Nat) : Parser Certificate := fun bits => do
  let (view,r1) ← readList limit (readList limit (readPair width)) bits
  let (table,r2) ← readList limit (readEntry width) r1
  let (inner,r3) ← readList limit (readRow width) r2
  let (outer,r4) ← readList limit (readRow width) r3
  some (⟨view,table,inner,outer⟩,r4)

theorem readPair_pack (width : Nat) (pair : Nat×Nat)
    (hl : pair.1<2^width) (hr : pair.2<2^width) (suffix : List Bool) :
    readPair width (RawSyntaxCertificate.packLiteral width pair++suffix)=some (pair,suffix) := by
  rcases pair with ⟨left,right⟩
  simp [readPair,RawSyntaxCertificate.packLiteral,List.append_assoc,
    readField_pack width left hl,readField_pack width right hr]

theorem readEntry_pack (width : Nat) (entry : Nat×Bool)
    (hi : entry.1<2^width) (suffix : List Bool) :
    readEntry width (packEntry width entry++suffix)=some (entry,suffix) := by
  rcases entry with ⟨index,bit⟩
  simp [readEntry,packEntry,List.append_assoc,readField_pack width index hi,readBit]

def RowFitsWidth (width : Nat) (row : Row) : Prop :=
  row.kind<2^width ∧ row.code<2^width ∧ row.count<2^width ∧ row.payload<2^width

theorem readRow_pack (width : Nat) (row : Row) (h : RowFitsWidth width row) (suffix : List Bool) :
    readRow width (packRow width row++suffix)=some (row,suffix) := by
  rcases row with ⟨kind,code,count,payload⟩
  simp [readRow,packRow,List.append_assoc,readField_pack width kind h.1,
    readField_pack width code h.2.1,readField_pack width count h.2.2.1,
    readField_pack width payload h.2.2.2]

theorem readRaw_pack (width limit : Nat) (view : RawSyntaxCertificate.View)
    (hv : view.length≤limit)
    (hc : ∀ clause∈view,clause.length≤limit ∧ ∀ literal∈clause,literal.1<2^width ∧ literal.2<2^width)
    (suffix : List Bool) :
    readList limit (readList limit (readPair width)) (RawSyntaxCertificate.pack width view++suffix)=
      some (view,suffix) := by
  apply readList_pack limit (readList limit (readPair width)) (RawSyntaxCertificate.packClause width) view hv
  intro clause hm tail
  apply readList_pack limit (readPair width) (RawSyntaxCertificate.packLiteral width) clause (hc clause hm).1
  intro literal hl rest
  exact readPair_pack width literal ((hc clause hm).2 literal hl).1 ((hc clause hm).2 literal hl).2 rest

def width (code : Nat) := natBitLength code+2
def limit (code : Nat) := 3*(natBitLength code+1)^2

theorem fields_fit (code : Nat) : code<2^width code ∧ natBitLength code<2^width code ∧ 2<2^width code := by
  have hc : code<2^natBitLength code := Nat.lt_pow_succ_log_self (by omega) _
  have hp : 2^natBitLength code≤2^width code := Nat.pow_le_pow_right (by omega) (by simp [width])
  have hn : natBitLength code<2^natBitLength code := Nat.lt_two_pow_self
  have ht : 2^2≤2^width code := Nat.pow_le_pow_right (by omega) (by simp [width])
  exact ⟨hc.trans_le hp,hn.trans_le hp,by omega⟩

theorem counts_fit (code : Nat) : natBitLength code≤limit code ∧
    3*natBitLength code≤limit code ∧ 2*natBitLength code+1≤limit code := by
  unfold limit
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem readCertificate_pack (code : Nat) (certificate : Certificate) (hf : Fits code certificate)
    (suffix : List Bool) :
    readCertificate (width code) (limit code) (pack (width code) certificate++suffix)=some (certificate,suffix) := by
  obtain ⟨hc,hd⟩ := hf
  obtain ⟨hview,hclauses⟩ := RawSyntaxCertificate.view_bounds code certificate.view hc
  obtain ⟨hcode,hcount,hkind⟩ := fields_fit code
  obtain ⟨hlim,hlim3,hlim2⟩ := counts_fit code
  have hraw : ∀ tail,readList (limit code) (readList (limit code) (readPair (width code)))
      (RawSyntaxCertificate.pack (width code) certificate.view++tail)=some (certificate.view,tail) := by
    intro tail
    apply readRaw_pack (width code) (limit code) certificate.view (hview.trans hlim)
    intro clause hm
    refine ⟨((hclauses clause hm).1).trans hlim,?_⟩
    intro literal hl
    have h := (hclauses clause hm).2 literal hl
    exact ⟨h.1.trans_lt hcode,h.2.trans_lt hcode⟩
  have htable : ∀ tail,readList (limit code) (readEntry (width code))
      (packList (packEntry (width code)) certificate.table++tail)=some (certificate.table,tail) := by
    intro tail
    apply readList_pack _ _ _ _ (hd.1.trans hlim3)
    intro entry hm rest
    exact readEntry_pack _ entry ((hd.2.1 entry hm).trans_lt hcode) rest
  have hrows : ∀ rows : List Row,rows.length≤limit code →
      (∀ row∈rows,RowFits code (natBitLength code) row) →
      ∀ tail,readList (limit code) (readRow (width code))
        (packList (packRow (width code)) rows++tail)=some (rows,tail) := by
    intro rows hn hs tail
    apply readList_pack _ _ _ _ hn
    intro row hm rest
    have h := hs row hm
    exact readRow_pack _ row ⟨h.2.2.2.trans_lt hkind,h.1.trans_lt hcode,
      h.2.2.1.trans_lt hcount,h.2.1.trans_lt hcode⟩ rest
  have hi := hrows certificate.inner (hd.2.2.1.trans hlim3)
    (fun row hm => hd.2.2.2.2 row (List.mem_append_left _ hm))
  have ho := hrows certificate.outer (hd.2.2.2.1.trans hlim2)
    (fun row hm => hd.2.2.2.2 row (List.mem_append_right _ hm))
  simp [readCertificate,pack,List.append_assoc,hraw,htable,hi,ho]

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
