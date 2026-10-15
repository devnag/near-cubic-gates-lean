import Proof.Amplification.RecoveryMarkerCanonicalCells

/-! Canonical completeness of the same whole marker recognizer, for all
four legacy marker forms. No witness scalar field supplies classification. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_third (x : State) (tail : TailWords)
    (hc : outerCode x=Encodable.encode (tailClauses tail)) :
    (thirdOutput x).inner.present=true := by
  cases tail with
  | none=>
    have hz : outerCode x=0 := hc
    have hp : (loaded x).outer.flag=false := by rw [load_flag,hz]; rfl
    simp only [thirdOutput,hp,Bool.false_eq_true,ite_false]
    rfl
  | some words=>
    obtain ⟨hp,hclause,htail⟩ := load_cons x [(false,value words.1),(true,value words.2)] [] hc
    have h := canonical_prefix (loaded x) (value words.1) (value words.2) hclause htail
    simp only [thirdOutput,hp,ite_true]
    exact h

theorem canonical_payload (x : State) (flat : Bool) (payload : List Bool) (tail : TailWords)
    (hc : outerCode x=Encodable.encode ([(flat,value payload)]::tailClauses tail)) :
    (payloadOutput x).inner.present=true := by
  obtain ⟨hp,hclause,htail⟩ := load_cons x [(flat,value payload)] (tailClauses tail) hc
  have ha : RecoveryMarkerAtom.answer 0 (loaded x)=true := by
    rw [RecoveryMarkerAtom.answer_eq_codeCheck]
    change RecoveryMarkerAtom.codeCheck 0 (RecoveryMarkerAtom.inputCode (loaded x))=true
    rw [hclause,singleton_check]
    rfl
  have hflag := (RecoveryMarkerAtom.output_answer 0 (loaded x)).trans ha
  have hnext : outerCode (RecoveryMarkerAtom.output 0 (loaded x))=Encodable.encode (tailClauses tail) := by
    change value (RecoveryMarkerAtom.output 0 (loaded x)).outer.bits=_
    rw [RecoveryMarkerAtom.output_outer_bits]
    exact htail
  have h := canonical_third (RecoveryMarkerAtom.output 0 (loaded x)) tail hnext
  simp only [payloadOutput,hp,hflag,ite_true]
  exact h

theorem canonical_marker (x : State) (flat : Bool) (payload : List Bool) (tail : TailWords)
    (hc : outerCode x=Encodable.encode (formula flat payload tail)) : (output x).inner.present=true := by
  have hstart : outerCode (RecoveryMarkerFlags.answered x false)=Encodable.encode
      ([]::[(flat,value payload)]::tailClauses tail) := hc
  obtain ⟨hp,hclause,htail⟩ := load_cons (RecoveryMarkerFlags.answered x false) []
    ([(flat,value payload)]::tailClauses tail) hstart
  have hempty := empty_zero (loaded (RecoveryMarkerFlags.answered x false)) hclause
  have hnext : outerCode (emptyStep (loaded (RecoveryMarkerFlags.answered x false)))=
      Encodable.encode ([(flat,value payload)]::tailClauses tail) := htail
  have h := canonical_payload (emptyStep (loaded (RecoveryMarkerFlags.answered x false))) flat payload tail hnext
  simp only [output,hp,hempty,ite_true,Bool.false_eq_true,ite_false]
  exact h

end NearCubicWires.RepairOrdinary.RecoveryMarker
