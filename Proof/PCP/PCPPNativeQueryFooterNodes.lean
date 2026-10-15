import Proof.PCP.PCPPNativeQueryTailFocus

/-! Actual original descriptor through header, copied-node loop, footer
and footer conversion. The original output index is physically available
as raw unary, and the descriptor cursor has reached the exact end. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape SourceInterfaces RepairRepresentation PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def parsedNodes := Composition.machine (Composition.machine headerNodes footer) value
def parsedNodesBudget {n : ℕ} (oracle : BooleanCircuit n) (F : ℕ) :=
  headerNodesBudget oracle F+1+PCPPQueryNatural.budget oracle.output.val+1+(4*oracle.output.val+16)
theorem value_low_away (i : Fin 122) (j : Fin 5) : valueSlots j≠i.castAdd 46 := by
  have h := value_away j
  apply Fin.ne_of_val_ne
  change (valueSlots j).val≠i.val
  omega
theorem footer_counter_away (i : Fin 2) (j : Fin 11) : footerSlots j≠(i.natAdd 122).castAdd 44 := by
  fin_cases i <;> fin_cases j <;> decide
theorem value_counter_away (i : Fin 2) (j : Fin 5) : valueSlots j≠(i.natAdd 122).castAdd 44 := by
  fin_cases i <;> fin_cases j <;> decide

theorem parsed_nodes_run {n r : ℕ} (base C F : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : PCPPNativeNodeLoop.workspace base 0 C F projection oracle.nodes) :
    ∃ result,runFrom parsedNodes (parsedNodesBudget oracle F)
      ⟨parsedNodes.start,heads 0 out,data (PCPPNative.descriptor oracle) (rowCache projection) base base C F out⟩=some result ∧
      result.steps ≤ parsedNodesBudget oracle F ∧
      lowFrame (PCPPNative.descriptor oracle) (rowCache projection) (PCPPNative.descriptor oracle).length
        base (base+2*oracle.size) C F (out++copied base oracle projection) result.final.heads result.final.tapes ∧
      result.final.tapes 164=List.replicate oracle.output.val true ∧ result.final.heads 164=0 ∧
      result.final.tapes 123=UnaryTemplate.tape n ∧ result.final.heads 123=1 ∧
      result.final.tapes 122=UnaryTemplate.tape oracle.size ∧ result.final.heads 122=1 := by
  obtain ⟨a,ha,as,alow,aa,aah,ac,ach,afresh⟩ := header_nodes_run base C F oracle projection out hCF hw
  have hsource : (originalHead oracle++originalBody oracle)++natWord oracle.output.val++[]=PCPPNative.descriptor oracle := by
    rw [List.append_nil,original_parts]
  have hcursor : (originalHead oracle++originalBody oracle).length+(natWord oracle.output.val).length=
      (PCPPNative.descriptor oracle).length := by rw [original_parts]; simp only [List.length_append]
  obtain ⟨b,hb,bs,blow,bt,bh,bfresh,bkeep⟩ := footer_run (originalHead oracle++originalBody oracle) []
    (rowCache projection) oracle.output.val base (base+2*oracle.size) C F (out++copied base oracle projection)
    a.final.heads a.final.tapes
    (by rw [hsource]; simpa only [List.length_append] using alow) afresh
  obtain ⟨c,hc,cs,ch,ct,_cth,_ct,ckeep⟩ := value_run oracle.output.val b.final.heads b.final.tapes ⟨bh,bt⟩ bfresh
  have hab := Composition.run_join headerNodes footer _ _ _ a b ha hb
  let result := Composition.joinedReceipt (Composition.joinedReceipt a b) c
  have hr := Composition.run_join (Composition.machine headerNodes footer) value _ _ _
    (Composition.joinedReceipt a b) c hab hc
  have counters (i : Fin 2) : c.final.heads ((i.natAdd 122).castAdd 44)=a.final.heads ((i.natAdd 122).castAdd 44) ∧
      c.final.tapes ((i.natAdd 122).castAdd 44)=a.final.tapes ((i.natAdd 122).castAdd 44) := by
    have hbkeep := bkeep _ (footer_counter_away i)
    have hckeep := ckeep _ (value_counter_away i)
    exact ⟨hckeep.1.trans hbkeep.1,hckeep.2.trans hbkeep.2⟩
  refine ⟨result,hr,?_,?_,ct,ch,((counters 1).2).trans aa,((counters 1).1).trans aah,
    ((counters 0).2).trans ac,((counters 0).1).trans ach⟩
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold parsedNodesBudget
    omega
  · rw [hsource,hcursor] at blow
    change lowFrame (PCPPNative.descriptor oracle) (rowCache projection) (PCPPNative.descriptor oracle).length
      base (base+2*oracle.size) C F (out++copied base oracle projection) c.final.heads c.final.tapes
    intro i
    have hk := ckeep (i.castAdd 46) (value_low_away i)
    exact ⟨hk.1.trans (blow i).1,hk.2.trans (blow i).2⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
