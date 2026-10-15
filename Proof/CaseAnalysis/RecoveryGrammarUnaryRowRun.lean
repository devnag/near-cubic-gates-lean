import Proof.CaseAnalysis.RecoveryGrammarAtomBudget

/-! The original unary atom in a finite grammar row, with its actual
retained scalar input and a physically produced next packet. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def unary (next : Selection):=prepared next RecoveryBoundedGrammarStep.unary

theorem unary_run {q bound W C D L S B P : ℕ} (room : Room W C D L S B P)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (row : Fin (bound+1))
    (scalars : ScalarFits q bound row.val W) (current next : Selection) (start : ℕ)
    (out stack packet source : List Bool) (extra : Fin 12→List Bool)
    (hblock : start+rowLimit q bound current.limit≤rowWidth q bound)
    (hindex : rowIndex q bound row.val current.index=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start)
    (hi : rowIndex q bound row.val current.index+rowLimit q bound current.limit≤W)
    (hp : b.nodes.length+3*rowLimit q bound current.limit≤W)
    (hg : (compileExpr b (unaryEqualsExpr row start (rowLimit q bound current.limit) current.value.val hblock)).final.nodes.length≤W)
    (ho : out.length≤S) (hk : stack.length≤S) (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (unary next) (atomBudget B) B P source (metadata q bound row.val C B extra)
      ⟨selectedFields current q bound row.val C,b.nodes.length,out,stack,packet⟩
      (expressionState b (unaryEqualsExpr row start (rowLimit q bound current.limit) current.value.val hblock)
        out stack (ZeroPadding.pad B (selectedWord next q bound row.val C)) (selectedFields next q bound row.val C)) := by
  let limit:=rowLimit q bound current.limit
  let upper:=rowUpper q row.val current.upper
  let nextFields:=selectedFields next q bound row.val C
  let nextWord:=selectedWord next q bound row.val C
  let tail:=List.replicate (B-nextWord.length) false
  let compiled:=compileExpr b (unaryEqualsExpr row start limit current.value.val hblock)
  have cr:=room.packet_fits scalars current
  have nr:=room.packet_fits scalars next
  have limitBound:=scalars.limit current.limit
  have refBound : compiled.output.val≤W:=Nat.le_of_lt (compiled.output.isLt.trans_le hg)
  have currentFields : RecoveryBoundedGrammarPrototype.fields C
      (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=q) row start) current.value.val limit upper=
      selectedFields current q bound row.val C := by rw [←hindex];rfl
  have refRoom : 2*compiled.output.val+2≤B:=by have hr:=room.reference;omega
  have wordRoom : (RecoveryBoundedRowReload.word nextFields++tail).length≤B:=
    room.pad_packet_length scalars next
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarStep.unary_run b row start limit current.value.val upper W C D S B P
    out stack source tail nextFields hblock (by rw [←hindex];exact hi) hp room.capacity
    (room.unaryLog limit limitBound) room.cB room.dB room.wB
    (by have hh:=cr.2.2.1;omega) (by have hh:=cr.2.1;omega) (by have hh:=cr.2.2.2.1;omega)
    room.positive ho hk (by have hP:=room.stack;omega) hs wordRoom nr.2.2.2.2.2.2 nr.2.2.2.2.2.1
    (room.unaryRun limit limitBound) refRoom
  rw [currentFields] at rr
  have whole : Runs (unary next)
      (preparedBudget C (rowIndex q bound row.val next.index) next.value.val (rowLimit q bound next.limit)
        (rowUpper q row.val next.upper) B (RecoveryBoundedGrammarStep.unaryBudget limit C compiled.output.val B nextFields))
      B P source (metadata q bound row.val C B extra)
      ⟨selectedFields current q bound row.val C,b.nodes.length,out,stack,packet⟩
      (expressionState b (unaryEqualsExpr row start limit current.value.val hblock) out stack
        (ZeroPadding.pad B nextWord) nextFields) := by
    exact prepared_run RecoveryBoundedGrammarStep.unary next C (rowIndex q bound row.val next.index)
      next.value.val (rowLimit q bound next.limit) (rowUpper q row.val next.upper) B P
      (RecoveryBoundedGrammarStep.unaryBudget limit C compiled.output.val B nextFields)
      (selectedFields current q bound row.val C) b.nodes.length compiled.final.nodes.length
      out stack packet (out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native)
      (RecoveryBoundedAddress.pushed compiled.output.val stack) source (metadata q bound row.val C B extra)
      (metadata_scalar next q bound row.val C B P b.nodes.length _ out stack packet source extra)
      hPacket nr.1 nr.2.1 nr.2.2.1 nr.2.2.2.1 nr.2.2.2.2.1 nr.2.2.2.2.2.1 r rr rs rh rt
  apply whole.more
  exact room.atom_budget scalars next (RecoveryBoundedUnaryReuse.budget limit C) compiled.output.val
    (by have hu:=room.unaryRun limit limitBound;omega) refBound

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
