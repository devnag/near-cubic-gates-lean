import Proof.PCP.PCPPNativeOracleOutputTemplate

namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleOutputCold
open LocalBitMultitape SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizeSlots : Fin 4 → Fin 21 := ![18,19,20,3]
def outputSlots (i : Fin 18) : Fin 21 := i.castAdd 3
theorem size_injective : Function.Injective sizeSlots := by decide
theorem output_injective : Function.Injective outputSlots := by decide
def input (bits : List Bool) (s : ℕ) (i : Fin 21) := if i=0 then bits else if i=18 then List.replicate s true else []
noncomputable def first := RecoveryFocus.machine sizeSlots MatrixDimensionHeader.machine
noncomputable def second := RecoveryFocus.machine outputSlots PCPPNativeOracleOutput.machine
noncomputable def raw := Composition.machine first second
noncomputable def machine := Rewind.machine raw
def rawBudget {R : ℕ} (oracle : BooleanCircuit R) := 2*oracle.size+4+PCPPNativeOracleOutput.budget oracle
def budget {R : ℕ} (oracle : BooleanCircuit R) := 2*rawBudget oracle+2
def coldInput (bits : List Bool) (s : ℕ) : Fin 22 → List Bool :=
  Fin.addCases (m := 21) (n := 1) (motive := fun _ => List Bool) (input bits s) (fun _ => [])

theorem raw_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ result,
    run raw (rawBudget oracle) (input (PCPPNative.descriptor oracle) oracle.size)=some result ∧
    result.steps ≤ rawBudget oracle ∧ result.final.tapes 0=PCPPNative.descriptor oracle ∧
    result.final.tapes 14=List.replicate oracle.output.val true ∧
    result.final.tapes 15=List.replicate oracle.output.val true ∧
    result.final.tapes 19=List.replicate oracle.size true ∧ result.final.tapes 20=List.replicate oracle.size true := by
  obtain ⟨sized,hs,s1,s2,s3,sh,ss⟩ := MatrixRawDimension.raw_run oracle.size
  obtain ⟨a,ha,_,as,ah,atapes,away⟩ := RecoveryFocus.dock sizeSlots size_injective MatrixDimensionHeader.machine _
    (fun _ => 0) (input (PCPPNative.descriptor oracle) oracle.size)
    (initialConfiguration MatrixDimensionHeader.machine (MatrixRawDimension.input oracle.size))
    (by intro i; rfl) (by intro i; fin_cases i <;> rfl) sized hs
  have untouched (i : Fin 18) (hi : i≠3) :
      a.final.heads (outputSlots i)=0 ∧ a.final.tapes (outputSlots i)=
        PCPPNativeOracleOutput.templateInput (PCPPNative.descriptor oracle) oracle.size i := by
    have hk := away (outputSlots i) (by
      intro j he
      have hv := congrArg (fun i : Fin 21 => i.val) he
      have h3 : i.val≠3 := fun he => hi (Fin.ext he)
      have hj : (sizeSlots j).val=18 ∨ (sizeSlots j).val=19 ∨ (sizeSlots j).val=20 ∨ (sizeSlots j).val=3 := by
        fin_cases j <;> decide
      change (sizeSlots j).val=i.val at hv
      omega)
    have h18 : outputSlots i≠18 := by
      intro he
      have hv := congrArg (fun i : Fin 21 => i.val) he
      change i.val=18 at hv
      omega
    refine ⟨hk.1,?_⟩
    rw [hk.2]
    simp only [input,h18,ite_false,PCPPNativeOracleOutput.templateInput,hi,ite_false]
    simp only [outputSlots,Fin.ext_iff,Fin.val_castAdd,Fin.val_zero]
  obtain ⟨base,hbase,bs,b0,b14,b15⟩ := PCPPNativeOracleOutput.template_run oracle
  obtain ⟨b,hb,_,bt,bheads,btapes,baway⟩ := RecoveryFocus.dock outputSlots output_injective PCPPNativeOracleOutput.machine _
    a.final.heads a.final.tapes (PCPPNativeOracleOutput.templateEntry oracle)
    (by
      intro i
      by_cases hi : i=3
      · subst i; exact (ah 3).trans (congrFun sh 3)
      · simpa only [PCPPNativeOracleOutput.templateEntry,PCPPNativeOracleOutput.heads,hi,ite_false] using (untouched i hi).1)
    (by
      intro i
      by_cases hi : i=3
      · subst i; exact (atapes 3).trans s3
      · exact (untouched i hi).2) base hbase
  have joined := Composition.run_join first second _ _ _ a b ha hb
  have ht : (2*oracle.size+3)+1+PCPPNativeOracleOutput.budget oracle=rawBudget oracle := by unfold rawBudget; omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt a b,joined,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ rawBudget oracle
    rw [as,ss,bt]
    unfold rawBudget
    omega
  · exact (btapes 0).trans b0
  · exact (btapes 14).trans b14
  · exact (btapes 15).trans b15
  · exact (baway 19 (by decide)).2.trans ((atapes 1).trans s1)
  · exact (baway 20 (by decide)).2.trans ((atapes 2).trans s2)

theorem cold_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ out,
    ClockJoin.ReadyRun machine (budget oracle) (coldInput (PCPPNative.descriptor oracle) oracle.size) out ∧
    out 0=PCPPNative.descriptor oracle ∧ out 14=List.replicate oracle.output.val true ∧
    out 15=List.replicate oracle.output.val true ∧ out 19=List.replicate oracle.size true ∧ out 20=List.replicate oracle.size true := by
  obtain ⟨base,hb,bs,b0,b14,b15,b19,b20⟩ := raw_run oracle
  obtain ⟨result,hr,ht,hh,hs,_⟩ := Rewind.reset_run raw _ _ base hb
  have ready : ClockJoin.ReadyRun machine (2*base.steps+2)
      (coldInput (PCPPNative.descriptor oracle) oracle.size) result.final.tapes := ⟨result,hr,rfl,hh,hs.le⟩
  have more := ClockJoin.enlarge machine _ (budget oracle) _ _ ready (by unfold budget; omega)
  exact ⟨_,more,(ht 0).trans b0,(ht 14).trans b14,(ht 15).trans b15,(ht 19).trans b19,(ht 20).trans b20⟩

end NearCubicWires.RepairOrdinary.PCPPNativeOracleOutputCold
