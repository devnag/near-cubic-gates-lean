import Proof.CaseAnalysis.RecoveryLiteralRun
import Proof.CaseAnalysis.RecoveryLiteralMeaning

/-! The complete executed literal returns the exact original compiler's
native graph, actual graph count and live output reference. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
open LocalBitMultitape SourceInterfaces RepairRepresentation BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem output_graph (second neg : Bool) (A : Fin 61→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (h20 : A 20=out) :
    output second neg A before ref node C out 20=out++if neg then emitted second ref else [] := by
  cases neg <;> cases second <;>
    simp [output,RecoveryBoundedLiteralNode.output,RecoveryBoundedClauseReplace.output,RecoveryBoundedClauseGate.output,kind_second,
      RecoveryBoundedClauseSelect.output,RecoveryBoundedClauseSelect.lookupOutput,RecoveryBoundedClauseSelect.target,h20]
theorem output_count (second neg : Bool) (A : Fin 61→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) (h25 : A 25=List.replicate node true) :
    output second neg A before ref node C out 25=List.replicate (node+neg.toNat) true := by
  cases neg <;> cases second <;>
    simp [output,RecoveryBoundedLiteralNode.output,RecoveryBoundedClauseReplace.output,RecoveryBoundedClauseGate.output,
      RecoveryBoundedClauseSelect.output,RecoveryBoundedClauseSelect.lookupOutput,RecoveryBoundedClauseSelect.target,h25]
theorem output_reference (second neg : Bool) (A : Fin 61→List Bool) (before : List ℕ)
    (ref node C : ℕ) (out : List Bool) :
    output second neg A before ref node C out (RecoveryBoundedClauseSelect.target second)=
      ZeroPadding.pad C (List.replicate (if neg then node else ref) true) := by
  cases neg <;> cases second <;> rfl

theorem original_run {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hlength : values.length=q) (literal : Literal q) (second : Bool)
    (H : Fin 61→ℕ) (A : Fin 61→List Bool) (W C L : ℕ) (out : List Bool)
    (hLookup : ∀ j,H (RecoveryBoundedClauseSelect.lookupSlots j)=0)
    (aLookup : ∀ j,A (RecoveryBoundedClauseSelect.lookupSlots j)=RecoveryBoundedClauseLookup.input
      ((references values).take (query literal).val) (reference values hlength literal) C L
      (sourceWord ((references values).drop ((query literal).val+1))) j)
    (hGate : ∀ j,H (RecoveryBoundedClauseGate.slots (kind second) j)=PCPPNativeClauseBank.heads out j)
    (aGate : ∀ j,A (RecoveryBoundedClauseGate.slots (kind second) j)=RecoveryBoundedUniversalGates.data 0 0 C out j)
    (hReplace : ∀ j,H (RecoveryBoundedClauseReplace.slots second j)=0)
    (aReplace : ∀ j,A (RecoveryBoundedClauseReplace.slots second j)=RecoveryBoundedClauseReplace.data b.nodes.length 0 C 0 j)
    (hSign : readTapeBit (A 48) (H 48)=negative literal)
    (hL : RecoveryBoundedClauseLookup.rawBudget ((references values).take (query literal).val) (reference values hlength literal) ≤ L)
    (hW : b.nodes.length ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    let before:=(references values).take (query literal).val
    let ref:=reference values hlength literal
    let compiled:=compileLiteral b values hlength literal
    ∃ r,runFrom (machine second) (budget second before ref b.nodes.length C) ⟨(machine second).start,H,A⟩=some r ∧
      r.steps ≤ budget second before ref b.nodes.length C ∧ r.final.heads=heads second (negative literal) H ref out ∧
      r.final.tapes=output second (negative literal) A before ref b.nodes.length C out ∧
      r.final.tapes 20=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native ∧
      r.final.tapes 25=List.replicate compiled.compiled.final.nodes.length true ∧
      r.final.tapes (RecoveryBoundedClauseSelect.target second)=ZeroPadding.pad C (List.replicate compiled.compiled.output.val true) := by
  have href : reference values hlength literal ≤ W :=
    (literalWire values hlength literal).output.isLt.le.trans hW
  have hn : b.nodes.length+1 ≤ C := by nlinarith [Nat.zero_le (W^2)]
  obtain ⟨r,hr,rs,rh,rt⟩:=literal_run second (negative literal) H A
    ((references values).take (query literal).val) (reference values hlength literal) b.nodes.length W C L out
    (sourceWord ((references values).drop ((query literal).val+1)))
    hLookup aLookup hGate aGate hReplace aReplace hSign hL href hC hn
  refine ⟨r,hr,rs,rh,rt,?_,?_,?_⟩
  · rw [rt,output_graph]
    · rw [original_native]
      cases hneg : negative literal
      · rfl
      · rw [emitted_not]
    · have h:=aGate 20
      change A 20=ZeroPadding.pad 0 out at h
      simpa only [ZeroPadding.pad_zero] using h
  · rw [rt,output_count,original_count]
    exact aReplace 0
  · rw [rt,output_reference,original_output]

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteral
