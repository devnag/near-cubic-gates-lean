import Proof.Amplification.RecoveryCertificateSerialization

/-! The selected all-code NP certificate is one flat polynomial-length word.
The word checker is a semantic specification for the remaining ordinary
machine; no ordinary execution is asserted in this file. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairOrdinary BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem packEntry_length (width : Nat) (entry : Nat×Bool) :
    (packEntry width entry).length=width+1 := by simp [packEntry]
theorem packRow_length (width : Nat) (row : Row) : (packRow width row).length=4*width := by
  simp only [packRow,List.length_append,SignedSortKey.binary_length]
  omega

theorem raw_pack_bound (code : Nat) (view : RawSyntaxCertificate.View)
    (hc : RawSyntaxCertificate.check code view=true) :
    (RawSyntaxCertificate.pack (width code) view).length≤16*(natBitLength code+1)^3 := by
  obtain ⟨hv,hc⟩ := RawSyntaxCertificate.view_bounds code view hc
  have hl := RawSyntaxCertificate.literals_bound view (natBitLength code)
    (by intro clause hm; exact (hc clause hm).1)
  have hs : RawSyntaxCertificate.literals view≤(natBitLength code)^2 := by nlinarith
  have hp := Nat.mul_le_mul_left (2*width code+1) hs
  rw [RawSyntaxCertificate.pack_length]
  unfold width at *
  nlinarith

theorem pack_bound (code : Nat) (certificate : Certificate) (hf : Fits code certificate) :
    (pack (width code) certificate).length≤128*(natBitLength code+1)^3 := by
  have hraw := raw_pack_bound code certificate.view hf.1
  have ht := packList_length (packEntry (width code)) certificate.table (width code+1)
    (by intro entry _; exact packEntry_length _ entry)
  have hi := packList_length (packRow (width code)) certificate.inner (4*width code)
    (by intro row _; exact packRow_length _ row)
  have ho := packList_length (packRow (width code)) certificate.outer (4*width code)
    (by intro row _; exact packRow_length _ row)
  have ht' := Nat.mul_le_mul_left (width code+2) hf.2.1
  have hi' := Nat.mul_le_mul_left (4*width code+1) hf.2.2.2.1
  have ho' := Nat.mul_le_mul_left (4*width code+1) hf.2.2.2.2.1
  simp only [pack,List.length_append,ht,hi,ho]
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

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
