import Proof.Amplification.RecoveryPrefixBodyInvariant
import Proof.Amplification.RecoveryCanonicalChoice

/-! The executed compact query has the same zero-first choice as the
existing canonical proof/circuit self-reduction on its guarded source formulas. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixBody
open CanonicalSATSelfReduction CanonicalRecoveryLanguage CanonicalBinary TseitinCNF
open RecoveryPrefix RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem matches_iff (assignment : Nat→Bool) (start : Nat) (xs : List Bool) :
    PrefixMatches assignment start xs ↔ ∀ i<xs.length,assignment (start+i)=xs.getD i false := by
  induction xs generalizing start with
  | nil => simp [PrefixMatches]
  | cons b xs ih =>
    rw [PrefixMatches,ih]
    constructor
    · rintro ⟨h0,ht⟩ i hi
      cases i with
      | zero => simpa [List.getD] using h0
      | succ i =>
        have h := ht i (by simp only [List.length_cons] at hi; omega)
        simpa [List.getD,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · intro h
      constructor
      · simpa [List.getD] using h 0 (by simp)
      · intro i hi
        have ht := h (i+1) (by simp only [List.length_cons]; omega)
        simpa [List.getD,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem constrain_append (start : Nat) (formula : EncodedCNF) (xs ys : List Bool) :
    constrainPrefixChoices start formula (xs++ys)=
      constrainPrefixChoices (start+xs.length) (constrainPrefixChoices start formula xs) ys := by
  induction xs generalizing start formula with
  | nil => simp [constrainPrefixChoices]
  | cons b xs ih => simpa [constrainPrefixChoices,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (ih (start+1) (constrainPrefixBit b start formula))

theorem constrain_one (formula : EncodedCNF) (xs : List Bool) (bit : Bool) :
    constrainPrefixChoices 0 formula (xs++[bit])=
      constrainPrefixBit bit xs.length (constrainPrefixChoices 0 formula xs) := by
  simpa only [Nat.zero_add,constrainPrefixChoices] using constrain_append 0 formula xs [bit]

theorem query_legacy (flat : Bool) (payload : Nat) (formula : EncodedCNF) (xs : List Bool)
    (hd : PayloadDecodes flat payload formula) (hthree : formula.all (fun clause=>clause.length=3)=true)
    (hw : wellSizedCNFEncoding
      (Encodable.encode (constrainPrefixBit false xs.length (constrainPrefixChoices 0 formula xs)))
      (constrainPrefixBit false xs.length (constrainPrefixChoices 0 formula xs))=true) :
    answer flat payload xs=canonicalSatBit (constrainPrefixBit false xs.length (constrainPrefixChoices 0 formula xs)) := by
  apply Bool.eq_iff_iff.mpr
  rw [answer,RecoveryPrefix.query_iff flat payload formula xs hd,canonicalSatBit_eq_true_iff _ hw]
  simp only [hthree,true_and,FormulaSatisfiable]
  apply exists_congr
  intro assignment
  rw [←constrain_one,formulaEval_constrainPrefixChoices_iff,matches_iff]
  simp

end NearCubicWires.RepairSource.RecoveryPrefixBody
