import Proof.CaseAnalysis.RowsGateNaturalLength

/-! Complete gate metadata from its retained native fields. All original
weights are charged for description; the same bitmap supplies support size.
These three paid scans are preprocessing before circuit cap checks and rows. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateMetadata
open LocalBitMultitape RecoveryRootRound RepairRepresentation CloseoutRowsGateSupport
open RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def weightSlots (i : Fin 8) : Fin 15 := i.castAdd 7
def naturalSlots : Fin 5→Fin 15 := ![8,9,10,11,12]
def supportSlots : Fin 3→Fin 15 := ![3,13,14]
theorem weight_injective : Function.Injective weightSlots := by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 15=>k.val) h)
theorem natural_injective : Function.Injective naturalSlots := by decide
theorem support_injective : Function.Injective supportSlots := by decide

def input (fields : List (Bool×List Bool)) (membership : List Bool) (n : ℕ) : Fin 15→List Bool :=
  fun i=>Fin.addCases (m:=8) (n:=7) (motive:=fun _=>List Bool)
    (CloseoutRowsGateWeightLength.input fields membership) ![natWord n,[],[],[],[],[],[]] i
noncomputable def weights := RecoveryFocus.machine weightSlots CloseoutRowsGateWeightLength.machine
noncomputable def natural := RecoveryFocus.machine naturalSlots CloseoutRowsGateNaturalLength.machine
noncomputable def support := RecoveryFocus.machine supportSlots CloseoutRowsSupportCount.readyMachine
noncomputable def first := Composition.machine weights natural
noncomputable def machine := Composition.machine first support
def budget (w count n m : ℕ) := CloseoutRowsGateWeightLength.budget w count+1+(4*natBitLength n+8)+1+(4*m+4)

theorem weight_members (fields : List (Bool×List Bool)) (membership : List Bool) (w : ℕ)
    (out : Fin 8→List Bool) (h : ClockJoin.ReadyRun CloseoutRowsGateWeightLength.machine w
      (CloseoutRowsGateWeightLength.input fields membership) out) : out 3=frame membership := by
  have hn : NoWrite CloseoutRowsGateWeightLength.machine 3 :=
    rewind (AppendOutputLength.record (preparedMachine false) 2) (3 : Fin 7)
      (CloseoutRowsGateNativeCount.record_count _ 2 3
        (CloseoutRowsGateNativeRetained.prepared_read false 3 (Or.inr rfl)))
  obtain ⟨r,hr,rt,_rh,_rs⟩ := h
  rw [←rt]
  exact run_tape _ 3 hn _ _ r hr

theorem metadata_run (fields : List (Bool×List Bool)) (membership : List Bool) (n w : ℕ)
    (hw : ∀ field∈fields,field.2.length ≤ w) : ∃ out,
    ClockJoin.ReadyRun machine (budget w fields.length n membership.length) (input fields membership n) out ∧
      out 6=List.replicate (fields.flatMap fieldWord).length true ∧
      out 11=List.replicate (natWord n).length true ∧
      out 13=List.replicate (CloseoutRowsSupportCount.ones membership) true := by
  obtain ⟨a,ha,_ac,aL⟩ := CloseoutRowsGateWeightLength.measured_run fields membership w hw
  have aM := weight_members fields membership _ a ha
  have h1 := ha.focus weightSlots weight_injective (input fields membership n)
    (by intro i;simp only [input,weightSlots,Fin.addCases_left])
  let amid := install weightSlots (input fields membership n) a
  have afresh (i : Fin 15) (hi : 8 ≤ i.val) : amid i=input fields membership n i := by
    apply install_other
    intro j he;have hv:=congrArg Fin.val he
    change j.val=i.val at hv
    omega
  obtain ⟨b,hb,_bn,_bc,bL⟩ := CloseoutRowsGateNaturalLength.measured_run n
  have h2 := hb.focus naturalSlots natural_injective amid (by
    intro i;fin_cases i <;> rw [afresh _ (by decide)] <;> rfl)
  have joined := ClockJoin.join weights natural _ _ _ _ _ h1 h2
  let bmid := install naturalSlots amid b
  have bM : bmid 3=frame membership := by
    dsimp only [bmid]
    rw [install_other _ _ _ _ (by decide)]
    change install weightSlots _ _ (weightSlots 3)=_
    rw [install_slot _ weight_injective]
    exact aM
  have bfresh (i : Fin 15) (hi : 13 ≤ i.val) : bmid i=[] := by
    dsimp only [bmid]
    rw [install_other _ _ _ _ (by
      intro j he;have hv:=congrArg Fin.val he
      fin_cases j <;> simp [naturalSlots] at hv <;> omega),afresh _ (by omega)]
    have hval : i.val=13 ∨ i.val=14 := by omega
    rcases hval with hval|hval
    · have he : i=13:=Fin.ext hval;subst i;rfl
    · have he : i=14:=Fin.ext hval;subst i;rfl
  obtain ⟨c,hc,_cm,cL⟩ := CloseoutRowsSupportCount.count_ready membership
  have h3 := hc.focus supportSlots support_injective bmid (by
    intro i;fin_cases i
    · exact bM
    · exact bfresh 13 (by decide)
    · exact bfresh 14 (by decide))
  have all := ClockJoin.join first support _ _ _ _ _ joined h3
  refine ⟨_,all,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    dsimp only [bmid]
    rw [install_other _ _ _ _ (by decide)]
    change install weightSlots _ _ (weightSlots 6)=_
    rw [install_slot _ weight_injective]
    exact aL
  · rw [install_other _ _ _ _ (by decide)]
    change install naturalSlots _ _ (naturalSlots 3)=_
    rw [install_slot _ natural_injective]
    exact bL
  · change install supportSlots _ _ (supportSlots 1)=_
    rw [install_slot _ support_injective]
    exact cL

end NearCubicWires.RepairOrdinary.CloseoutRowsGateMetadata
