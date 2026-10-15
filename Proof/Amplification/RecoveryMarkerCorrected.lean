import Proof.Amplification.RecoveryMarkerCanonical

/-! The accepted marker's exact legacy syntax determines corrected SAT
dispatch. The compact payload meaning is supplied by the actual existing
flat or nested table checker; no prefix clauses are executed or expanded. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
open RepairSource.RecoveryOracle BalancedCNFSATEncoding CanonicalBinary
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailCommitted : TailWords→Nat
  | none=>0
  | some words=>value words.1
def tailCount : TailWords→Nat
  | none=>0
  | some words=>value words.2

theorem marker_not_raw (code : Nat) (flat : Bool) (payload : List Bool) (tail : TailWords)
    (hc : decodeCNF code=formula flat payload tail) :
    wellSizedCNFEncoding code (decodeCNF code)=false := by
  rw [hc]
  simp [wellSizedCNFEncoding,formula]

theorem flat_decode (code : Nat) (payload : List Bool) (tail : TailWords)
    (hc : decodeCNF code=formula true payload tail) :
    decodeFlatCompact code=(decodeBalancedList (value payload)).map
      (fun clauses=>⟨decodeClauseCodes clauses,tailCommitted tail,tailCount tail⟩) := by
  unfold decodeFlatCompact
  rw [hc]
  cases tail <;> rfl

theorem nested_flat_none (code : Nat) (payload : List Bool) (tail : TailWords)
    (hc : decodeCNF code=formula false payload tail) : decodeFlatCompact code=none := by
  unfold decodeFlatCompact
  rw [hc]
  cases tail <;> rfl

theorem nested_decode (code : Nat) (payload : List Bool) (tail : TailWords)
    (hc : decodeCNF code=formula false payload tail) :
    decodeNestedCompact code=(decodeNestedBalancedCNFPayload (value payload)).map
      (fun clauses=>⟨decodeClauseCodes clauses,tailCommitted tail,tailCount tail⟩) := by
  unfold decodeNestedCompact
  rw [hc]
  cases tail <;> rfl

theorem marker_corrected (code : Nat) (flat : Bool) (payload : List Bool)
    (tail : TailWords) (clauses : List Nat)
    (hc : decodeCNF code=formula flat payload tail)
    (hd : (if flat then decodeBalancedList (value payload)
      else decodeNestedBalancedCNFPayload (value payload))=some clauses)
    (hm : compactMeaning ⟨decodeClauseCodes clauses,tailCommitted tail,tailCount tail⟩) :
    correctedSat code=true := by
  obtain ⟨witness,hw⟩ := (compactVerifier_iff _).mpr hm
  apply (correctedWitnessVerifier_iff code).mp
  refine ⟨witness,?_⟩
  have hr := marker_not_raw code flat payload tail hc
  cases flat
  · have hf := nested_flat_none code payload tail hc
    have hn := nested_decode code payload tail hc
    simp only [Bool.false_eq_true,ite_false] at hd
    rw [hd] at hn
    simp only [correctedWitnessVerifier,hr,Bool.false_eq_true,ite_false,hf,hn,Option.map_some]
    exact hw
  · have hf := flat_decode code payload tail hc
    simp only [ite_true] at hd
    rw [hd] at hf
    simp only [correctedWitnessVerifier,hr,Bool.false_eq_true,ite_false,hf,Option.map_some]
    exact hw

end NearCubicWires.RepairOrdinary.RecoveryMarker
