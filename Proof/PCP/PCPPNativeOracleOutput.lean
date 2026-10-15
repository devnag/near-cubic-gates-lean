import Proof.PCP.PCPPNativeOracleFooterPosition

/-! The executed original header/node scan reaches the actual footer;
its original output index is decoded and copied to raw unary. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeOracleOutput
open LocalBitMultitape SourceInterfaces RepairRepresentation RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scanSlots (i : Fin 4) : Fin 18 := i.castAdd 14
def footerSlots (i : Fin 11) : Fin 18 := if i=0 then 0 else ⟨3+i.val,by omega⟩
def valueSlots : Fin 5 → Fin 18 := ![13,14,15,16,17]
theorem scan_injective : Function.Injective scanSlots := by decide
theorem footer_injective : Function.Injective footerSlots := by decide
theorem value_injective : Function.Injective valueSlots := by decide
def heads (i : Fin 18) := if i=3 then 1 else 0
def input (bits : List Bool) (s : ℕ) (i : Fin 18) :=
  if i=0 then bits else if i=3 then CompareMachine.word s else []
noncomputable def first := RecoveryFocus.machine scanSlots PCPPNativeOracleFooterPosition.machine
noncomputable def second := RecoveryFocus.machine footerSlots PCPPQueryNatural.machine
noncomputable def third := RecoveryFocus.machine valueSlots PCPPNativeTemplateRaw.machine
noncomputable def machine := Composition.machine (Composition.machine first second) third
noncomputable def entry {R : ℕ} (oracle : BooleanCircuit R) :=
  (⟨machine.start,heads,input (PCPPNative.descriptor oracle) oracle.size⟩ : Configuration 18 _)
def budget {R : ℕ} (oracle : BooleanCircuit R) := PCPPNativeOracleFooterPosition.budget oracle+1+
  PCPPQueryNatural.budget oracle.output.val+1+(4*oracle.output.val+16)

theorem output_run {R : ℕ} (oracle : BooleanCircuit R) : ∃ result,
    runFrom machine (budget oracle) (entry oracle)=some result ∧ result.steps ≤ budget oracle ∧
    result.final.tapes 0=PCPPNative.descriptor oracle ∧ result.final.heads 0=(PCPPNative.descriptor oracle).length ∧
    result.final.tapes 14=List.replicate oracle.output.val true ∧ result.final.heads 14=0 ∧
    result.final.tapes 15=List.replicate oracle.output.val true ∧ result.final.heads 15=0 ∧
    result.final.tapes 16=UnaryTemplate.tape oracle.output.val ∧ result.final.heads 16=0 := by
  obtain ⟨scan,hscan,scanSteps,scanHeads,scanTapes⟩ := PCPPNativeOracleFooterPosition.position_run oracle
  obtain ⟨a,ha,_,as,ah,atapes,away⟩ := RecoveryFocus.dock scanSlots scan_injective PCPPNativeOracleFooterPosition.machine _
    heads (input (PCPPNative.descriptor oracle) oracle.size) (PCPPNativeOracleFooterPosition.entry oracle)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl) scan hscan
  have aFresh (i : Fin 18) (hi : 4 ≤ i.val) : a.final.heads i=0 ∧ a.final.tapes i=[] := by
    have hk := away i (by
      intro j he
      have hv := congrArg (fun i : Fin 18 => i.val) he
      change j.val=i.val at hv
      omega)
    have h0 : i≠0 := by intro he; subst i; contradiction
    have h3 : i≠3 := by intro he; subst i; contradiction
    simpa only [heads,input,h0,h3,ite_false] using hk
  obtain ⟨raw,hr,rs,r0,rh0,rt,rh⟩ := PCPPQueryNatural.natural_run (PCPPNativeOracleFooterPosition.bodyPrefix oracle) [] oracle.output.val
  have he : PCPPNativeOracleFooterPosition.bodyPrefix oracle++natWord oracle.output.val++[]=PCPPNative.descriptor oracle := by
    rw [List.append_nil,PCPPNativeQuery.original_parts]
    rfl
  rw [he] at hr r0
  obtain ⟨b,hb,_,bs,bh,bt,baway⟩ := RecoveryFocus.dock footerSlots footer_injective PCPPQueryNatural.machine _
    a.final.heads a.final.tapes
    (PCPPQueryNatural.entry (PCPPNative.descriptor oracle) (PCPPNativeOracleFooterPosition.bodyPrefix oracle).length)
    (by
      intro i
      by_cases hi : i=0
      · subst i
        exact (ah 0).trans (congrFun scanHeads 0)
      · have hf := aFresh (footerSlots i) (by
          have hiv : i.val≠0 := fun h => hi (Fin.ext h)
          simp only [footerSlots,hi,ite_false,Fin.val_mk]
          omega)
        simpa only [PCPPQueryNatural.entry,hi,ite_false] using hf.1)
    (by
      intro i
      by_cases hi : i=0
      · subst i
        exact (atapes 0).trans (congrFun scanTapes 0)
      · have hf := aFresh (footerSlots i) (by
          have hiv : i.val≠0 := fun h => hi (Fin.ext h)
          simp only [footerSlots,hi,ite_false,Fin.val_mk]
          omega)
        simpa only [PCPPQueryNatural.entry,hi,ite_false] using hf.2) raw hr
  have bFresh (i : Fin 18) (hi : 14 ≤ i.val) : b.final.heads i=0 ∧ b.final.tapes i=[] := by
    have hk := baway i (by
      intro j he
      have hj : (footerSlots j).val≤13 := by fin_cases j <;> decide
      have hv := congrArg (fun i : Fin 18 => i.val) he
      omega)
    exact ⟨hk.1.trans (aFresh i (by omega)).1,hk.2.trans (aFresh i (by omega)).2⟩
  obtain ⟨value,hvalue,vs,_,v1,v2,v3,vh⟩ := PCPPNativeTemplateRaw.template_run oracle.output.val
  obtain ⟨c,hc,_,cs,ch,ct,caway⟩ := RecoveryFocus.dock valueSlots value_injective PCPPNativeTemplateRaw.machine _
    b.final.heads b.final.tapes (PCPPNativeTemplateRaw.entry oracle.output.val)
    (by
      intro i; fin_cases i
      · exact (bh 10).trans rh
      all_goals exact (bFresh _ (by decide)).1)
    (by
      intro i; fin_cases i
      · exact (bt 10).trans rt
      all_goals exact (bFresh _ (by decide)).2) value hvalue
  have hab := Composition.run_join first second _ _ _ a b ha hb
  have joined := Composition.run_join (Composition.machine first second) third _ _ _ (Composition.joinedReceipt a b) c hab hc
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ budget oracle
    rw [as,cs,scanSteps,vs]
    unfold budget
    omega
  · change c.final.tapes 0=_
    exact (caway 0 (by decide)).2.trans ((bt 0).trans r0)
  · change c.final.heads 0=_
    have hp := (caway 0 (by decide)).1.trans ((bh 0).trans rh0)
    have hl : (PCPPNativeOracleFooterPosition.bodyPrefix oracle).length+2*natBitLength oracle.output.val+1=
        (PCPPNative.descriptor oracle).length := by
      rw [PCPPNativeQuery.original_parts]
      simp only [PCPPNativeOracleFooterPosition.bodyPrefix,List.length_append,DecompositionSource.natWord_length]
      omega
    exact hp.trans hl
  · exact (ct 1).trans v1
  · exact (ch 1).trans (congrFun vh 1)
  · exact (ct 2).trans v2
  · exact (ch 2).trans (congrFun vh 2)
  · exact (ct 3).trans v3
  · exact (ch 3).trans (congrFun vh 3)

end NearCubicWires.RepairOrdinary.PCPPNativeOracleOutput
