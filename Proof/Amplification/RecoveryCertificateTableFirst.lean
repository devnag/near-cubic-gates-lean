import Proof.Amplification.RecoveryCertificateWord
import Proof.Amplification.RecoveryCommittedBitLookup

/-! The selected physical certificate starts with the shared finite valuation.
The linear list cap follows from Fits; no semantic language or source premise
changes. The table prefix is quadratic and is copied once by the checker. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.TableFirst
open RepairOrdinary BalancedCertificate Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def limit (code : Nat) := 3*(natBitLength code+1)
def pack (width : Nat) (certificate : Certificate) : List Bool :=
  packList (packEntry width) certificate.table++RawSyntaxCertificate.pack width certificate.view++
    packList (packRow width) certificate.inner++packList (packRow width) certificate.outer
def readCertificate (width limit : Nat) : Parser Certificate := fun bits => do
  let (table,r1) ← readList limit (readEntry width) bits
  let (view,r2) ← readList limit (readList limit (readPair width)) r1
  let (inner,r3) ← readList limit (readRow width) r2
  let (outer,r4) ← readList limit (readRow width) r3
  some (⟨view,table,inner,outer⟩,r4)

theorem counts_fit (code : Nat) : natBitLength code≤limit code ∧
    3*natBitLength code≤limit code ∧ 2*natBitLength code+1≤limit code := by
  unfold limit
  omega

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

theorem pack_length (width : Nat) (certificate : Certificate) :
    (pack width certificate).length=(Serialization.pack width certificate).length := by
  simp only [pack,Serialization.pack,List.length_append]
  omega

theorem pack_bound (code : Nat) (certificate : Certificate) (hf : Fits code certificate) :
    (pack (width code) certificate).length≤128*(natBitLength code+1)^3 := by
  rw [pack_length]
  exact Serialization.pack_bound code certificate hf

theorem table_prefix_bound (code : Nat) (certificate : Certificate) (hf : Fits code certificate) :
    (packList (packEntry (width code)) certificate.table).length≤16*(natBitLength code+1)^2 := by
  rw [packList_length _ _ (width code+1) (by intro entry _; exact packEntry_length _ entry)]
  have h := Nat.mul_le_mul_left (width code+2) hf.2.1
  unfold width at *
  nlinarith

def checkWord (code : Nat) (bits : List Bool) : Bool :=
  match readCertificate (width code) (limit code) bits with
  | some (certificate,[]) => check code certificate
  | _ => false

theorem checkWord_sound (code : Nat) (bits : List Bool) (hc : checkWord code bits=true) :
    correctedSat code=true := by
  unfold checkWord at hc
  split at hc
  next certificate _ => exact check_sound code certificate hc
  next => contradiction

theorem checkWord_pack (code : Nat) (certificate : Certificate) (hf : Fits code certificate) :
    checkWord code (pack (width code) certificate)=check code certificate := by
  have hp := readCertificate_pack code certificate hf []
  rw [List.append_nil] at hp
  simp only [checkWord,hp]

theorem bounded_word_iff (code : Nat) :
    correctedSat code=true ↔ ∃ bits : List Bool,
      bits.length≤128*(natBitLength code+1)^3 ∧ checkWord code bits=true := by
  constructor
  · intro hs
    obtain ⟨certificate,hc,hf⟩ := (bounded_certificate code).mp hs
    exact ⟨pack (width code) certificate,pack_bound code certificate hf,(checkWord_pack code certificate hf).trans hc⟩
  · rintro ⟨bits,_,hc⟩
    exact checkWord_sound code bits hc

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.TableFirst
