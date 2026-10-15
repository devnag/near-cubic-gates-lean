import Proof.Amplification.RecoveryMarkerCellMeaning

/-! Accepting the actual prefix branch reconstructs its exact two signed
literals, empty original outer tail, and retained physical field words. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarker
open LocalBitMultitape RecoveryMarkerClause RadixSemantics
open RecoveryMarkerMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem variable_width (x : State) : (RecoveryMarkerAtom.variableWord x).length=x.width :=
  (RecoveryMarkerAtom.variable_length x).trans (RecoveryRawLiteral.output_width x.inner)

theorem prefix_accepted (x : State) (ha : (prefixOutput x).inner.present=true) :
    ∃ committed count : List Bool,committed.length=x.width ∧ count.length=x.width ∧
      RecoveryMarkerAtom.inputCode x=Encodable.encode [(false,value committed),(true,value count)] ∧
      outerCode x=0 ∧
      read (prefixOutput x)={read x with committed:=frame committed,count:=frame count} := by
  cases h1 : (RecoveryMarkerAtom.output 1 x).inner.present
  · simp only [prefixOutput,h1,Bool.false_eq_true,ite_false] at ha
    contradiction
  · cases h2 : (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x)).inner.present
    · simp only [prefixOutput,h1,h2,ite_true,Bool.false_eq_true,ite_false] at ha
      contradiction
    · have ha1 : RecoveryMarkerAtom.answer 1 x=true := (RecoveryMarkerAtom.output_answer 1 x).symm.trans h1
      have ha2 : RecoveryMarkerAtom.answer 2 (RecoveryMarkerAtom.output 1 x)=true :=
        (RecoveryMarkerAtom.output_answer 2 _).symm.trans h2
      have hout : prefixOutput x=outerOutput (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x)) := by
        simp only [prefixOutput,h1,h2,ite_true,outerOutput]
      rw [hout] at ha ⊢
      have hempty : outerCode (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x))=0 := by
        change (!(outerStep (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x))).outer.flag)=true at ha
        rw [show (outerStep (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x))).outer.flag=
          decide (outerCode (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x))≠0)
          from RecoveryThreeCellReader.after_flag _ 0,RecoveryMarkerAtom.not_nonzero,decide_eq_true_eq] at ha
        exact ha
      have hc := prefix_clause x ha1 ha2
      have hv1 := RecoveryMarkerAtom.accepted_variable 1 x ha1
      have hv2 := RecoveryMarkerAtom.accepted_variable 2 (RecoveryMarkerAtom.output 1 x) ha2
      refine ⟨RecoveryMarkerAtom.variableWord x,RecoveryMarkerAtom.variableWord (RecoveryMarkerAtom.output 1 x),
        variable_width x,(variable_width _).trans (RecoveryMarkerAtom.output_width 1 x),?_,?_,?_⟩
      · rw [hv1,hv2]
        exact hc
      · change value x.outer.bits=0
        change value (RecoveryMarkerAtom.output 2 (RecoveryMarkerAtom.output 1 x)).outer.bits=0 at hempty
        rw [RecoveryMarkerAtom.output_outer_bits,RecoveryMarkerAtom.output_outer_bits] at hempty
        exact hempty
      · rw [outerOutput,read_answered,read_outer,
          RecoveryMarkerAtom.accepted_metadata 2 _ ha2,
          RecoveryMarkerAtom.accepted_metadata 1 x ha1]
        rfl

end NearCubicWires.RepairOrdinary.RecoveryMarker
