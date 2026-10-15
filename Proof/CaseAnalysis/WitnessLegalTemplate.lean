import Proof.CaseAnalysis.WitnessLegalPolicyRun
import Proof.CaseAnalysis.WitnessCorePolicy
import Proof.CaseAnalysis.RowsCircuitBottomReturned

/-! The retained actual cache template supplies the original legal-policy
worker through the existing paid unary copy. No source field is serialized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate
open LocalBitMultitape RecoveryRootRound RepairRepresentation RepairSource
open CompetitorSumFold
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev L (e : ℕ):=LegalPolicy.tapes e
def tapes (e : ℕ):=5+L e
def templateSlots (e : ℕ) (i : Fin 5) : Fin (tapes e):=i.castAdd (L e)
def slots (e : ℕ) (i : Fin (L e)) : Fin (tapes e):=
  if i.val=0 then templateSlots e 1 else i.natAdd 5
def heads (e : ℕ) (i : Fin (tapes e)) : ℕ:=if i.val=0 then 1 else 0
def input (e R q0 cb b : ℕ) : Fin (tapes e)→List Bool:=
  Fin.addCases (MatrixTemplateCopy.resetInput R) (LegalPolicy.input e 0 q0 cb b)
def template (e : ℕ):=RecoveryFocus.machine (templateSlots e) PCPPNativeTemplateRaw.machine
def policy (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  RecoveryFocus.machine (slots e) (LegalPolicy.machine e den delta copies sym)
def machine (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool):=
  Composition.machine (template e) (policy e den delta copies sym)
def entry (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ):=
  (⟨(machine e den delta copies sym).start,heads e,input e R q0 cb b⟩ : Configuration (tapes e) _)
def budget (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ):=
  4*R+16+1+LegalPolicy.budget e den delta copies sym R q0 cb b
def project (e : ℕ) (bank : Fin (tapes e)→List Bool) (i : Fin 94):=
  bank (slots e (LegalPolicy.massSlots e (MassCold.nativeSlots i)))

theorem template_injective (e : ℕ) : Function.Injective (templateSlots e):=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin (tapes e)=>k.val) h)
theorem slots_injective (e : ℕ) : Function.Injective (slots e):=by
  intro i j h
  have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp only [templateSlots,Fin.val_castAdd,Fin.val_natAdd] at hv <;> apply Fin.ext <;> omega
private theorem template_outside (e : ℕ) (i : Fin (tapes e)) (hi : 5 ≤ i.val) :
    ∀ j,templateSlots e j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin (tapes e)=>k.val) h
  change j.val=i.val at hv;omega
private theorem slots_nonzero (e : ℕ) (i : Fin (L e)) : (slots e i).val≠0:=by
  unfold slots
  split_ifs
  · change (1 : ℕ)≠0;omega
  · change 5+i.val≠0;omega

theorem template_run (e den : ℕ) (delta : ℚ) (copies : ℕ) (sym : Bool) (R q0 cb b : ℕ)
    (hden : 0<den) (hR : 0<R) : ∃ actual,
    runFrom (machine e den delta copies sym) (budget e den delta copies sym R q0 cb b)
      (entry e den delta copies sym R q0 cb b)=some actual ∧
      actual.steps≤budget e den delta copies sym R q0 cb b ∧ actual.final.heads=heads e ∧
      actual.final.tapes (templateSlots e 0)=UnaryTemplate.tape R ∧
      actual.final.tapes (slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 1)))=List.replicate R true ∧
      actual.final.tapes (slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 3)))=UnaryTemplate.tape R ∧
      actual.final.tapes (slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 5)))=
        frame (SignedSortKey.binary (natBitLength R) R) ∧
      actual.final.tapes (slots e (LegalPolicy.wireSlot e))=List.replicate (LegalPolicy.W e den R) true ∧
      actual.final.tapes (slots e (LegalPolicy.descriptionSlots e 91))=
        List.replicate (DescriptionPolicy.value sym R q0 (LegalPolicy.W e den R)) true ∧
      actual.final.tapes (slots e (LegalPolicy.termSlots e 42))=List.replicate (LegalPolicy.T delta copies q0 cb) true ∧
      actual.final.tapes (slots e (LegalPolicy.massSlots e 1))=List.replicate b true ∧
      Store (CompetitorSumWidth.width (LegalPolicy.T delta copies q0 cb) b) CompetitorSumWidth.zero []
        (project e actual.final.tapes):=by
  have tExists:=PCPPNativeTemplateRaw.template_run R
  let t:=Classical.choose tExists
  have tFacts:=Classical.choose_spec tExists
  have ht:=tFacts.1
  have ts:=tFacts.2.1
  have t0:=tFacts.2.2.1
  have t1:=tFacts.2.2.2.1
  have th:=tFacts.2.2.2.2.2.2
  have fExists:=RecoveryFocus.dock (templateSlots e) (template_injective e)
    PCPPNativeTemplateRaw.machine _ (heads e) (input e R q0 cb b) (PCPPNativeTemplateRaw.entry R)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;rw [input,templateSlots,Fin.addCases_left];rfl) t ht
  let f:=Classical.choose fExists
  have fFacts:=Classical.choose_spec fExists
  have hf:=fFacts.1
  have fs:=fFacts.2.2.1
  have fh:=fFacts.2.2.2.1
  have ft:=fFacts.2.2.2.2.1
  have fa:=fFacts.2.2.2.2.2
  have fheads:f.final.heads=heads e:=by
    funext i
    by_cases hi:i.val<5
    · let j:Fin 5:=⟨i.val,hi⟩
      have he:i=templateSlots e j:=Fin.ext rfl
      rw [he,fh,th]
      simp only [PCPPNativeTemplateRaw.heads,heads,templateSlots,Fin.ext_iff,Fin.val_zero,Fin.val_castAdd]
      rfl
    · exact (fa i (template_outside e i (by omega))).1
  have outExists:=LegalPolicy.policy_run e den delta copies sym R q0 cb b hden hR
  let out:=Classical.choose outExists
  have outFacts:=Classical.choose_spec outExists
  have hout:=outFacts.1
  have oR:=outFacts.2.1
  have oTemplate:=outFacts.2.2.1
  have oBinary:=outFacts.2.2.2.1
  have oW:=outFacts.2.2.2.2.1
  have oL:=outFacts.2.2.2.2.2.1
  have oT:=outFacts.2.2.2.2.2.2.2.1
  have ob:=outFacts.2.2.2.2.2.2.2.2.1
  have oStore:=outFacts.2.2.2.2.2.2.2.2.2
  have pin:∀ i,f.final.tapes (slots e i)=LegalPolicy.input e R q0 cb b i:=by
    intro i
    by_cases hi:i.val=0
    · rw [slots,if_pos hi,ft,t1]
      simp only [LegalPolicy.input,hi,ite_true]
    · rw [slots,if_neg hi,(fa _ (template_outside e _ (by simp only [Fin.val_natAdd];omega))).2,
        input,Fin.addCases_right]
      simp only [LegalPolicy.input,if_neg hi]
  have lastExists:=hout.focus_at (slots e) (slots_injective e) (heads e) f.final.tapes pin
    (by intro i;simp only [heads,if_neg (slots_nonzero e i)])
  let last:=Classical.choose lastExists
  have lastFacts:=Classical.choose_spec lastExists
  have hl:=lastFacts.1
  have lh:=lastFacts.2.1
  have lt:=lastFacts.2.2.1
  have ls:=lastFacts.2.2.2
  have continued:runFrom (policy e den delta copies sym) (LegalPolicy.budget e den delta copies sym R q0 cb b)
      (Composition.restart f.final (policy e den delta copies sym).start)=some last:=by
    change runFrom (policy e den delta copies sym) _ ⟨_,f.final.heads,f.final.tapes⟩=some last
    rw [fheads];exact hl
  have actualExists:=joined (template e) (policy e den delta copies sym) (4*R+16)
    (LegalPolicy.budget e den delta copies sym R q0 cb b) (heads e) (input e R q0 cb b)
    f last hf continued (by rw [fs,ts]) ls
  let actual:=Classical.choose actualExists
  have actualFacts:=Classical.choose_spec actualExists
  have actualHeads:=actualFacts.2.2.1
  have actualTapes:=actualFacts.2.2.2
  have get (i : Fin (L e)):actual.final.tapes (slots e i)=out i:=by
    rw [actualTapes,lt];exact install_slot _ (slots_injective e) _ _ _
  refine ⟨actual,actualFacts.1,actualFacts.2.1,actualHeads.trans lh,?_,(get _).trans oR,
    (get _).trans oTemplate,(get _).trans oBinary,(get _).trans oW,(get _).trans oL,
    (get _).trans oT,(get _).trans ob,?_⟩
  · rw [actualTapes,lt,install_other _ _ _ _ (by
      intro i he
      have hv:=congrArg (fun k : Fin (tapes e)=>k.val) he
      exact slots_nonzero e i hv)]
    exact (ft 0).trans t0
  · have he:project e actual.final.tapes=LegalPolicy.project e out:=by
      funext i;exact get _
    rw [he];exact oStore

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalTemplate
