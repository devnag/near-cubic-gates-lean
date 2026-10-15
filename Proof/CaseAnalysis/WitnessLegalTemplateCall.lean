import Proof.CaseAnalysis.WitnessLegalTemplateDock

/-! The actual source/cache fields supply one paid legal-family policy.
The resulting store and policy ports are retained for the cold family dock. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate.Call
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

structure Fields (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ)
    (data : Fin (extra e)→List Bool) : Prop where
  domain : data (LegalTemplate.templateSlots e 0)=UnaryTemplate.tape R
  raw : data (LegalTemplate.slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 1)))=List.replicate R true
  template : data (LegalTemplate.slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 3)))=UnaryTemplate.tape R
  arity : data (LegalTemplate.slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 5)))=
    frame (SignedSortKey.binary (natBitLength R) R)
  wire : data (LegalTemplate.slots e (LegalPolicy.wireSlot e))=List.replicate (LegalPolicy.W e den R) true
  description : data (LegalTemplate.slots e (LegalPolicy.descriptionSlots e 91))=
    List.replicate (DescriptionPolicy.value sym R q0 (LegalPolicy.W e den R)) true
  terms : data (LegalTemplate.slots e (LegalPolicy.termSlots e 42))=List.replicate (LegalPolicy.T delta copies q0 cb) true
  width : data (LegalTemplate.slots e (LegalPolicy.massSlots e 1))=List.replicate b true
  store : Store (CompetitorSumWidth.width (LegalPolicy.T delta copies q0 cb) b) CompetitorSumWidth.zero []
    (LegalTemplate.project e data)

theorem call_run (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) {t : ℕ}
    (fields : Fin 4→Fin t) (hf : Function.Injective fields) (data : Fin t→List Bool) (cursor : Fin t→ℕ)
    (R q0 cb b : ℕ) (hden : 0<den) (hR : 0<R)
    (hdata : ∀ i,data (fields i)=values R q0 cb b i) (hheads : ∀ i,cursor (fields i)=cursors i) :
    ∃ actual,runFrom (machine e den delta copies sym fields) (LegalTemplate.budget e den delta copies sym R q0 cb b)
      ⟨(machine e den delta copies sym fields).start,heads e cursor,input e data⟩=some actual ∧
      actual.steps≤LegalTemplate.budget e den delta copies sym R q0 cb b ∧
      (∀ i,actual.final.heads (slots e fields i)=LegalTemplate.heads e i) ∧
      Fields e den delta copies sym R q0 cb b (actual.final.tapes ∘ slots e fields) ∧
      (∀ i,(∀ j,fields j≠i) → actual.final.heads (old e i)=cursor i ∧ actual.final.tapes (old e i)=data i):=by
  have localExists:=LegalTemplate.template_run e den delta copies sym R q0 cb b hden hR
  let inner:=Classical.choose localExists
  have localFacts:=Classical.choose_spec localExists
  have actualExists:=RecoveryFocus.dock (slots e fields) (slots_injective e fields hf)
    (LegalTemplate.machine e den delta copies sym) _ (heads e cursor) (input e data)
    (LegalTemplate.entry e den delta copies sym R q0 cb b)
    (heads_local e fields cursor hheads) (input_local e fields data R q0 cb b hdata) inner localFacts.1
  let actual:=Classical.choose actualExists
  have actualFacts:=Classical.choose_spec actualExists
  have ah:=actualFacts.2.2.2.1
  have atape:=actualFacts.2.2.2.2.1
  have away:=actualFacts.2.2.2.2.2
  have same:actual.final.tapes ∘ slots e fields=inner.final.tapes:=funext atape
  refine ⟨actual,actualFacts.1,actualFacts.2.2.1.trans_le localFacts.2.1,
    fun i=>(ah i).trans (congrFun localFacts.2.2.1 i),?_,?_⟩
  · rw [same]
    exact ⟨localFacts.2.2.2.1,localFacts.2.2.2.2.1,localFacts.2.2.2.2.2.1,
      localFacts.2.2.2.2.2.2.1,localFacts.2.2.2.2.2.2.2.1,localFacts.2.2.2.2.2.2.2.2.1,
      localFacts.2.2.2.2.2.2.2.2.2.1,localFacts.2.2.2.2.2.2.2.2.2.2.1,
      localFacts.2.2.2.2.2.2.2.2.2.2.2⟩
  · intro i hi
    have keep:=away (old e i) (outside e fields i hi)
    exact ⟨keep.1.trans (by simp only [heads,old,Fin.addCases_left]),
      keep.2.trans (by simp only [input,old,Fin.addCases_left])⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate.Call
