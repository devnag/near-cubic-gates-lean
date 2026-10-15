import Proof.CaseAnalysis.RowsGateSupportArity
import Proof.Supplier.EquationHeaderAppend
import Proof.Supplier.EquationRowForward
import Proof.Supplier.EquationRowCutsForward

/-! The original count or the retained top's support supplies the actual
native arity prefix. Both choices use existing paid counters and header
writers; the five parsed source fields remain available to the same run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNativePrefix
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlots (compressed : Bool) : Fin 3 → Fin 24 := ![if compressed then 2 else 1,5,6]
def headerSlots (i : Fin 18) : Fin 24 := if i.val=0 then 5 else ⟨i.val+6,by omega⟩
theorem count_injective (compressed : Bool) : Function.Injective (countSlots compressed) := by
  cases compressed <;> decide
theorem header_val (i : Fin 18) : (headerSlots i).val=if i.val=0 then 5 else i.val+6 := by
  unfold headerSlots
  split_ifs <;> rfl
theorem header_injective : Function.Injective headerSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [header_val,header_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
def input (a : Fin 5 → List Bool) : Fin 24 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (5+19) => List Bool) a (fun _ => [])
noncomputable def count (compressed : Bool) := RecoveryFocus.machine (countSlots compressed)
  (if compressed then CloseoutRowsSupportCount.readyMachine else UWalkUnary.machine false false)
noncomputable def header := RecoveryFocus.machine headerSlots EquationHeaderAppend.machine
noncomputable def machine (compressed : Bool) := Composition.machine (count compressed) header
def arity (compressed : Bool) (n : ℕ) (membership : List Bool) :=
  if compressed then CloseoutRowsSupportCount.ones membership else n
def countBudget (n : ℕ) (membership : List Bool) := 4*(n+membership.length)+6
def budget (compressed : Bool) (n : ℕ) (membership : List Bool) :=
  countBudget n membership+1+EquationHeaderAppend.budget (arity compressed n membership)

theorem count_ready (compressed : Bool) (n : ℕ) (membership : List Bool) (a : Fin 5 → List Bool)
    (h1 : a 1=CompareMachine.word n) (h2 : a 2=frame membership) : ∃ out,
    ClockJoin.ReadyRun (count compressed) (countBudget n membership) (input a) out ∧
      out 5=List.replicate (arity compressed n membership) true ∧
      (∀ i : Fin 5,out (i.castAdd 19)=a i) ∧ (∀ i,7 ≤ i.val → out i=[]) := by
  have localRun : ∃ fields,
      ClockJoin.ReadyRun
        (if compressed then CloseoutRowsSupportCount.readyMachine else UWalkUnary.machine false false)
        (countBudget n membership) (fun i => input a (countSlots compressed i)) fields ∧
      fields 0=input a (countSlots compressed 0) ∧
      fields 1=List.replicate (arity compressed n membership) true := by
    cases compressed
    · have hi : (fun i => input a (countSlots false i))=UWalkUnary.input 0 n := by
        funext i;fin_cases i <;> simp [input,Fin.addCases,countSlots,UWalkUnary.input,UWalkUnary.source,h1]
      rw [hi]
      refine ⟨_,ClockJoin.enlarge _ _ _ _ _ (UWalkUnary.ready false false 0 n)
        (by unfold countBudget;omega),?_,?_⟩
      · simpa [input,Fin.addCases,countSlots,UWalkUnary.result,UWalkUnary.source] using h1.symm
      · simp [UWalkUnary.result,UWalkUnary.output,UWalkUnary.lead,arity]
    · obtain ⟨out,hout,ho,hc⟩ := CloseoutRowsSupportCount.count_ready membership
      have hi : (fun i => input a (countSlots true i))=CloseoutRowsSupportCount.readyInput membership := by
        funext i;fin_cases i <;> simp [input,Fin.addCases,countSlots,CloseoutRowsSupportCount.readyInput,h2]
      rw [hi]
      exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hout (by unfold countBudget;omega),
        ho.trans (by simpa [input,Fin.addCases,countSlots] using h2.symm),hc⟩
  obtain ⟨fields,run,hsource,hcount⟩ := localRun
  refine ⟨install (countSlots compressed) (input a) fields,
    run.focus (countSlots compressed) (count_injective compressed) (input a) (fun _ => rfl),
    (install_slot _ (count_injective compressed) _ _ 1).trans hcount,?_,?_⟩
  · intro i
    by_cases he : (i.castAdd 19)=countSlots compressed 0
    · rw [he,install_slot _ (count_injective compressed),hsource,←he]
      simp only [input,Fin.addCases_left]
    · rw [install_other _ _ _ _ (by
        intro j hj
        fin_cases j
        · exact he hj.symm
        · have hv := congrArg Fin.val hj
          change 5=i.val at hv
          omega
        · have hv := congrArg Fin.val hj
          change 6=i.val at hv
          omega)]
      simp only [input,Fin.addCases_left]
  · intro i hi
    rw [install_other _ _ _ _ (by
      intro j hj
      have hv := congrArg Fin.val hj
      cases compressed <;> fin_cases j <;> simp [countSlots] at hv <;> omega)]
    simp [input,Fin.addCases,show ¬i.val < 5 by omega]

theorem prefix_run (compressed : Bool) (n : ℕ) (membership : List Bool) (a : Fin 5 → List Bool)
    (h1 : a 1=CompareMachine.word n) (h2 : a 2=frame membership) : ∃ actual,
    run (machine compressed) (budget compressed n membership) (input a)=some actual ∧
      actual.steps ≤ budget compressed n membership ∧
      actual.final.tapes 23=natWord (arity compressed n membership) ∧
      actual.final.heads 23=(natWord (arity compressed n membership)).length ∧
      (∀ i : Fin 5,actual.final.tapes (i.castAdd 19)=a i ∧ actual.final.heads (i.castAdd 19)=0) := by
  obtain ⟨bank,⟨first,hf,ft,fh,fs⟩,raw,old,fresh⟩ := count_ready compressed n membership a h1 h2
  obtain ⟨base,hb,bt,bh,_,_,bs⟩ := EquationHeaderAppend.append_run (arity compressed n membership) []
  have hi : ∀ i,first.final.tapes (headerSlots i)=
      (EquationHeaderAppend.entry (arity compressed n membership) []).tapes i := by
    intro i
    rw [ft]
    by_cases hz : i.val=0
    · have he : i=0 := Fin.ext hz
      subst i
      exact raw
    · have hn : i≠0 := by intro he;exact hz (congrArg Fin.val he)
      rw [headerSlots,if_neg hz,fresh _ (by simp;omega)]
      simp [EquationHeaderAppend.entry,EquationHeaderAppend.tapes,hn]
  obtain ⟨last,hl,_,ls,lh,lt,keep⟩ := RecoveryFocus.dock headerSlots header_injective
    EquationHeaderAppend.machine _ first.final.heads first.final.tapes _
    (by intro i;rw [fh];simp [EquationHeaderAppend.entry,EquationHeaderAppend.heads]) hi base hb
  have run := Composition.run_join (count compressed) header _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,run,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps ≤ _
    unfold budget
    omega
  · exact (lt 17).trans (by simpa only [List.nil_append] using bt)
  · exact (lh 17).trans (by simpa only [List.nil_append] using bh)
  · intro i
    have outside : ∀ j,headerSlots j≠i.castAdd 19 := by
      intro j he
      have hv := congrArg Fin.val he
      rw [header_val] at hv
      change (if j.val=0 then 5 else j.val+6)=i.val at hv
      split_ifs at hv <;> omega
    have hk := keep (i.castAdd 19) outside
    exact ⟨hk.2.trans ((congrFun ft _).trans (old i)),hk.1.trans (fh _)⟩

theorem output_forward (compressed : Bool) : CursorRestore.NoLeft (machine compressed) 23 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward (countSlots compressed) _ _ (by
      intro j he;cases compressed <;> fin_cases j <;> simp [countSlots] at he))
    (CursorRestore.focus_forward headerSlots header_injective _ 17 EquationRowRaw.header_append_forward)

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNativePrefix
