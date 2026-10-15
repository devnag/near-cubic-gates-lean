import Proof.CaseAnalysis.RecoveryGrammarUnaryRowRun

/-! The original less-than disjunction runs from its actual retained row
scalars and shares the same uniform paid atom budget. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedSelectorLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def less (next : Selection):=prepared next RecoveryBoundedGrammarStep.less

theorem less_run {q bound W C D L S B P : ℕ} (room : Room W C D L S B P)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (row : Fin (bound+1))
    (scalars : ScalarFits q bound row.val W) (current next : Selection) (start : ℕ)
    (out stack packet source : List Bool) (extra : Fin 12→List Bool)
    (hblock : start+rowLimit q bound current.limit≤rowWidth q bound)
    (hindex : rowIndex q bound row.val current.index=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start)
    (hzero : current.value.val=0)
    (hi : rowIndex q bound row.val current.index+rowLimit q bound current.limit≤W)
    (hp : b.nodes.length+rowUpper q row.val current.upper*(3*rowLimit q bound current.limit+1)+3*rowLimit q bound current.limit≤W)
    (hg : (compileExpr b (BoolExpr.any ((List.range (rowUpper q row.val current.upper)).map
      (fun value=>unaryEqualsExpr row start (rowLimit q bound current.limit) value hblock)))).final.nodes.length≤W)
    (ho : out.length≤S) (hk : stack.length≤S) (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (less next) (atomBudget B) B P source (metadata q bound row.val C B extra)
      ⟨selectedFields current q bound row.val C,b.nodes.length,out,stack,packet⟩
      (expressionState b (BoolExpr.any ((List.range (rowUpper q row.val current.upper)).map
        (fun value=>unaryEqualsExpr row start (rowLimit q bound current.limit) value hblock)))
        out stack (ZeroPadding.pad B (selectedWord next q bound row.val C)) (selectedFields next q bound row.val C)) := by
  have hC:=room.originalC
  subst C
  let limit:=rowLimit q bound current.limit
  let upper:=rowUpper q row.val current.upper
  let nextFields:=selectedFields next q bound row.val (capacity W)
  let nextWord:=selectedWord next q bound row.val (capacity W)
  let tail:=List.replicate (B-nextWord.length) false
  let expression:=BoolExpr.any ((List.range upper).map (fun value=>unaryEqualsExpr row start limit value hblock))
  let compiled:=compileExpr b expression
  have cr:=room.packet_fits scalars current
  have nr:=room.packet_fits scalars next
  have limitBound:=scalars.limit current.limit
  have upperBound:=scalars.upper current.upper
  have refBound : compiled.output.val≤W:=Nat.le_of_lt (compiled.output.isLt.trans_le hg)
  have currentFields : RecoveryBoundedGrammarPrototype.fields (capacity W)
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) 0 limit upper=
      selectedFields current q bound row.val (capacity W) := by
    rw [←hindex]
    unfold selectedFields
    rw [hzero]
  have refRoom : 2*compiled.output.val+2≤B:=by have hr:=room.reference;omega
  have wordRoom : (RecoveryBoundedRowReload.word nextFields++tail).length≤B:=room.pad_packet_length scalars next
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarStep.less_run b row start limit upper W D L S B P
    out stack source tail nextFields hblock (by rw [←hindex];exact hi) hp hg upperBound
    (room.unaryLog limit limitBound) room.lessLog room.cB room.dB room.lB room.wB
    (by have hh:=cr.2.1;omega) (by have hh:=cr.2.2.2.1;omega)
    room.positive ho hk (by have hP:=room.stack;omega) hs wordRoom nr.2.2.2.2.2.2 nr.2.2.2.2.2.1
    (room.lessRun upper upperBound) refRoom
  rw [currentFields] at rr
  have whole : Runs (less next)
      (preparedBudget (capacity W) (rowIndex q bound row.val next.index) next.value.val (rowLimit q bound next.limit)
        (rowUpper q row.val next.upper) B (RecoveryBoundedGrammarStep.lessBudget upper W compiled.output.val B nextFields))
      B P source (metadata q bound row.val (capacity W) B extra)
      ⟨selectedFields current q bound row.val (capacity W),b.nodes.length,out,stack,packet⟩
      (expressionState b expression out stack (ZeroPadding.pad B nextWord) nextFields) := by
    exact prepared_run RecoveryBoundedGrammarStep.less next (capacity W) (rowIndex q bound row.val next.index)
      next.value.val (rowLimit q bound next.limit) (rowUpper q row.val next.upper) B P
      (RecoveryBoundedGrammarStep.lessBudget upper W compiled.output.val B nextFields)
      (selectedFields current q bound row.val (capacity W)) b.nodes.length compiled.final.nodes.length
      out stack packet (out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)
      (RecoveryBoundedAddress.pushed compiled.output.val stack) source (metadata q bound row.val (capacity W) B extra)
      (metadata_scalar next q bound row.val (capacity W) B P b.nodes.length _ out stack packet source extra)
      hPacket nr.1 nr.2.1 nr.2.2.1 nr.2.2.2.1 nr.2.2.2.2.1 nr.2.2.2.2.2.1 r rr rs rh rt
  apply whole.more
  exact room.atom_budget scalars next (RecoveryBoundedAddressReuse.resetBudget upper W) compiled.output.val
    (by have hu:=room.lessRun upper upperBound;omega) refBound

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
