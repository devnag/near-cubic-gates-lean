import Proof.Amplification.RecoveryPrefixCanonicalMeaning

/-! The new executed recurrence returns the existing canonical SAT prefix;
only its compact query encoding and physical representation differ. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixBody
open CanonicalSATSelfReduction CanonicalRecoveryLanguage CanonicalBinary TseitinCNF
open RecoveryPrefix RecoveryQuery
open private constrainPrefixBit_code_mono from Proof.Circuits.CanonicalSATSelfReduction
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem search_eq_choices (flat : Bool) (payload : Nat) (formula : EncodedCNF) (n : Nat)
    (xs : List Bool) (hd : PayloadDecodes flat payload formula)
    (hthree : formula.all (fun clause=>clause.length=3)=true)
    (hw : wellSizedCNFEncoding (Encodable.encode (constrainPrefixChoices 0 formula xs))
      (constrainPrefixChoices 0 formula xs)=true)
    (hr : xs.length+n ≤ natBitLength (Encodable.encode (constrainPrefixChoices 0 formula xs))) :
    search flat payload n xs=xs++prefixSATChoices n xs.length (constrainPrefixChoices 0 formula xs) := by
  induction n generalizing xs with
  | zero => simp [search,prefixSATChoices]
  | succ n ih =>
    have hindex : xs.length<natBitLength (Encodable.encode (constrainPrefixChoices 0 formula xs)) := by omega
    have hz := constrainPrefixBit_wellSized false xs.length (constrainPrefixChoices 0 formula xs) hw hindex
    have hquery := query_legacy flat payload formula xs hd hthree hz
    have hnext : wellSizedCNFEncoding (Encodable.encode (constrainPrefixChoices 0 formula (nextPrefix flat payload xs)))
        (constrainPrefixChoices 0 formula (nextPrefix flat payload xs))=true := by
      rw [nextPrefix,constrain_one]
      exact constrainPrefixBit_wellSized _ _ _ hw hindex
    have hnextRange : (nextPrefix flat payload xs).length+n ≤
        natBitLength (Encodable.encode (constrainPrefixChoices 0 formula (nextPrefix flat payload xs))) := by
      have hm : natBitLength (Encodable.encode (constrainPrefixChoices 0 formula xs)) ≤
          natBitLength (Encodable.encode (constrainPrefixBit (!answer flat payload xs) xs.length
            (constrainPrefixChoices 0 formula xs))) := Nat.add_le_add_right (Nat.log_mono_right
        (constrainPrefixBit_code_mono (!answer flat payload xs) xs.length (constrainPrefixChoices 0 formula xs))) 1
      rw [nextPrefix_length,nextPrefix,constrain_one]
      omega
    have ht := ih (nextPrefix flat payload xs) hnext hnextRange
    rw [search,ht]
    rw [nextPrefix_length,nextPrefix,constrain_one,hquery]
    cases hb : canonicalSatBit (constrainPrefixBit false xs.length (constrainPrefixChoices 0 formula xs)) <;>
      simp [prefixSATChoices,hb,List.append_assoc]

theorem three_of_wellSized (code : Nat) (formula : EncodedCNF)
    (hw : wellSizedCNFEncoding code formula=true) : formula.all (fun clause=>clause.length=3)=true := by
  rw [wellSizedCNFEncoding,Bool.and_eq_true] at hw
  rw [List.all_eq_true] at hw ⊢
  intro clause hc
  have h := hw.2 clause hc
  rw [Bool.and_eq_true] at h
  exact h.1

theorem search_canonical (flat : Bool) (payload : Nat) (formula : EncodedCNF) (n : Nat)
    (hd : PayloadDecodes flat payload formula)
    (hw : wellSizedCNFEncoding (Encodable.encode formula) formula=true)
    (hr : n ≤ natBitLength (Encodable.encode formula)) :
    search flat payload n []=recoveredPrefix n formula := by
  have h := search_eq_choices flat payload formula n [] hd (three_of_wellSized _ _ hw) hw
    (by simpa only [List.length_nil,Nat.zero_add,constrainPrefixChoices] using hr)
  simpa only [List.length_nil,Nat.zero_add,List.nil_append,constrainPrefixChoices,recoveredPrefix] using h

end NearCubicWires.RepairSource.RecoveryPrefixBody
