import Proof.PCP.PCPPRequestNodePrepareDock

/-! Complete native descriptor preparation: three canonical fields and a
physically computed two/three-field flag, with the continuous source retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodePrepare
open LocalBitMultitape RepairRepresentation ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := dock PCPPRequestNodeFields.machine
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  Composition.leftConfig 21 (extended (PCPPRequestNodeFields.entry source pos))
def budget {n : ℕ} (node : BooleanNode n) :=
  PCPPRequestNodeFields.budget (PCPPRequestNodeSchema.fields node 0)
    (PCPPRequestNodeSchema.fields node 1) (PCPPRequestNodeSchema.fields node 2)+37

theorem cold_run {n : ℕ} (pre tail : List Bool) (node : BooleanNode n) :
    ∃ r,runFrom machine (budget node)
      (entry (pre++PCPPRequestNodeSchema.native node++tail) pre.length)=some r ∧
      r.steps≤budget node ∧
      r.final.tapes 0=pre++PCPPRequestNodeSchema.native node++tail ∧
      r.final.heads 0=pre.length+(PCPPRequestNodeSchema.native node).length ∧
      (∀ i : Fin 3,∃ padding,r.final.tapes (old (PCPPRequestNodeFields.outputSlot i))=
        frame (CanonicalBinary.encodeNat (PCPPRequestNodeSchema.fields node i)).bits++List.replicate padding false) ∧
      (∀ i : Fin 3,r.final.heads (old (PCPPRequestNodeFields.outputSlot i))=0) ∧
      r.final.tapes 406=[PCPPRequestNodeSchema.binaryNode node] ∧ r.final.heads 406=0 := by
  let a := PCPPRequestNodeSchema.fields node 0
  let b := PCPPRequestNodeSchema.fields node 1
  let c := PCPPRequestNodeSchema.fields node 2
  obtain ⟨first,hfirst,fs,f0,fh0,fout,foh⟩ := PCPPRequestNodeFields.cold_run pre tail a b c
  obtain ⟨padding,hpadding⟩ := fout 0
  have htag : first.final.tapes 85=
      frame (PCPPRequestTagArity.code (PCPPRequestNodeSchema.tag node))++List.replicate padding false := by
    rw [show PCPPRequestNodeFields.outputSlot 0=85 from rfl] at hpadding
    simpa only [Matrix.cons_val_zero,a,PCPPRequestNodeSchema.first_tag,PCPPRequestTagArity.code] using hpadding
  obtain ⟨result,hresult,rs,rt,rh,rflag,rflagh⟩ := dock_run PCPPRequestNodeFields.machine
    _ _ first hfirst (PCPPRequestNodeSchema.tag node) padding htag (foh 0)
  refine ⟨result,?_,?_,?_,?_,?_,?_,rflag,rflagh⟩
  · simpa only [machine,entry,budget,PCPPRequestNodeFields.source,
      PCPPRequestNodeSchema.native,List.append_assoc,a,b,c] using hresult
  · change result.steps≤PCPPRequestNodeFields.budget a b c+37
    omega
  · exact (rt 0).trans (by simpa only [PCPPRequestNodeFields.source,
      PCPPRequestNodeSchema.native,List.append_assoc,a,b,c] using f0)
  · exact (rh 0).trans (by simpa only [PCPPRequestNodeSchema.native,List.length_append,
      Nat.add_assoc,a,b,c] using fh0)
  · intro i
    obtain ⟨p,hp⟩ := fout i
    refine ⟨p,(rt (PCPPRequestNodeFields.outputSlot i)).trans ?_⟩
    have hf : (![a,b,c] : Fin 3 → ℕ) i=PCPPRequestNodeSchema.fields node i := by
      fin_cases i <;> rfl
    rw [hf] at hp
    exact hp
  · intro i
    exact (rh (PCPPRequestNodeFields.outputSlot i)).trans (foh i)

end NearCubicWires.RepairOrdinary.PCPPRequestNodePrepare
