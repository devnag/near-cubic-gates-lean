import Proof.CaseAnalysis.RecoveryGrammarLessRowRun

/-! The terminal constant and original reverse fold close a finite row
subexpression on the same paid stack and retained scalar bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def fold (conjunction : Bool) (next : Selection):=
  prepared next (RecoveryBoundedGrammarStep.fold conjunction)
def foldState (n : ℕ) (conjunction : Bool) (base : ℕ) (refs : List ℕ)
    (out pre packet : List Bool) (fields : Fin 78→List Bool) : RowState:=
  ⟨fields,base+refs.length+1,out++([BooleanNode.const conjunction]++
    RecoveryBoundedNative.foldNodes (n:=n) conjunction base refs.reverse).flatMap PCPPRequestNodeSchema.native,
    RecoveryBoundedAddress.pushed (base+refs.length) pre,packet⟩

theorem fold_run {q bound row W C D L S B P : ℕ} (room : Room W C D L S B P)
    (scalars : ScalarFits q bound row W) (n : ℕ) (conjunction : Bool) (current next : Selection)
    (base : ℕ) (refs : List ℕ) (out pre packet source : List Bool) (extra : Fin 12→List Bool)
    (hcurrent : selectedFields current q bound row C=RecoveryBoundedGrammarPrototype.fields C 0 0 refs.length 0)
    (href : ∀ ref∈refs,ref≤W) (ha : base+refs.length≤W)
    (ho : out.length≤S) (hk : (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length≤S)
    (hs : source.length≤B) (hPacket : packet.length≤B) :
    Runs (fold conjunction next) (atomBudget B) B P source (metadata q bound row C B extra)
      ⟨selectedFields current q bound row C,base,out,pre++RecoveryBoundedNativeUnaryLoop.stackWords refs,packet⟩
      (foldState n conjunction base refs out pre (ZeroPadding.pad B (selectedWord next q bound row C))
        (selectedFields next q bound row C)) := by
  let nextFields:=selectedFields next q bound row C
  let nextWord:=selectedWord next q bound row C
  let tail:=List.replicate (B-nextWord.length) false
  let result:=out++([BooleanNode.const conjunction]++
    RecoveryBoundedNative.foldNodes (n:=n) conjunction base refs.reverse).flatMap PCPPRequestNodeSchema.native
  have nr:=room.packet_fits scalars next
  have countBound : refs.length≤W:=by omega
  have refRoom : 2*(base+refs.length)+2≤B:=by have hr:=room.reference;omega
  have wordRoom : (RecoveryBoundedRowReload.word nextFields++tail).length≤B:=room.pad_packet_length scalars next
  have stackRoom : pre.length+refs.length*(2*W+1)≤P := by
    have hh:=room.stack
    have hm:=Nat.mul_le_mul_right (2*W+1) countBound
    simp only [List.length_append] at hk
    omega
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedGrammarStep.fold_run n conjunction base W C S B P
    out pre source tail refs nextFields href ha room.capacity room.cB room.wB (by have hh:=room.reference;omega)
    room.positive ho hk stackRoom hs wordRoom nr.2.2.2.2.2.2 nr.2.2.2.2.2.1
    (room.foldRun conjunction refs.length countBound) refRoom
  rw [←hcurrent] at rr
  have whole : Runs (fold conjunction next)
      (preparedBudget C (rowIndex q bound row next.index) next.value.val (rowLimit q bound next.limit)
        (rowUpper q row next.upper) B (RecoveryBoundedGrammarStep.foldBudget conjunction refs.length C (base+refs.length) B nextFields))
      B P source (metadata q bound row C B extra)
      ⟨selectedFields current q bound row C,base,out,pre++RecoveryBoundedNativeUnaryLoop.stackWords refs,packet⟩
      (foldState n conjunction base refs out pre (ZeroPadding.pad B nextWord) nextFields) := by
    exact prepared_run (RecoveryBoundedGrammarStep.fold conjunction) next C (rowIndex q bound row next.index)
      next.value.val (rowLimit q bound next.limit) (rowUpper q row next.upper) B P
      (RecoveryBoundedGrammarStep.foldBudget conjunction refs.length C (base+refs.length) B nextFields)
      (selectedFields current q bound row C) base (base+refs.length+1)
      out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) packet result
      (RecoveryBoundedAddress.pushed (base+refs.length) pre) source (metadata q bound row C B extra)
      (metadata_scalar next q bound row C B P base _ out _ packet source extra)
      hPacket nr.1 nr.2.1 nr.2.2.1 nr.2.2.2.1 nr.2.2.2.2.1 nr.2.2.2.2.2.1 r rr rs rh rt
  apply whole.more
  exact room.atom_budget scalars next (RecoveryBoundedGrammarFold.budget conjunction refs.length C) (base+refs.length)
    (by have hu:=room.foldRun conjunction refs.length countBound;omega) ha

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
