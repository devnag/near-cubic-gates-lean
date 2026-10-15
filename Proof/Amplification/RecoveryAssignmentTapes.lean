import Proof.Amplification.RecoveryValuationReadyReturn

/-! Literal fourteen-tape layout joining the counted shared valuation scan
with the executed committed-prefix selector. -/
namespace NearCubicWires.RepairOrdinary.RecoveryAssignment
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def cfg {s : Nat} (d : Data) (count cap : Nat)
    (binaryCount committed : List Bool) (guard : Bool) (q : Fin s) : Configuration 14 s :=
  TapeEmbedding.config (fun _ : Fin 4=>0)
    ![frame binaryCount,frame committed,[guard],List.replicate d.capacity false]
    (RecoveryValuationCount.cfg d count cap q)
def prefixData (d : Data) (binaryCount committed : List Bool) (guard : Bool) : RecoveryPrefixAssignment.Data :=
  ⟨binaryCount,d.index,committed,guard,d.found,d.value,d.capacity⟩
def selectorSlots : Fin 8→Fin 14 := ![10,3,12,6,11,4,5,13]
theorem selectorSlots_injective : Function.Injective selectorSlots := by decide
noncomputable def tableMachine := TapeEmbedding.machine 4 RecoveryValuationCount.machine
noncomputable def selectorMachine := RecoveryFocus.machine selectorSlots RecoveryPrefixAssignment.machine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem selector_input_heads (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (j : Fin 8) :
    ((prefixData d binaryCount committed guard).cfg RecoveryPrefixAssignment.machine.start).heads j=
      (cfg d count cap binaryCount committed guard selectorMachine.start).heads (selectorSlots j) := by
  fin_cases j <;> simp [prefixData,RecoveryPrefixAssignment.Data.cfg,cfg,RecoveryValuationCount.cfg,Data.cfg,
    TapeEmbedding.config,Fin.addCases,selectorSlots]

theorem selector_input_tapes (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (j : Fin 8) :
    ((prefixData d binaryCount committed guard).cfg RecoveryPrefixAssignment.machine.start).tapes j=
      (cfg d count cap binaryCount committed guard selectorMachine.start).tapes (selectorSlots j) := by
  fin_cases j <;> simp [prefixData,RecoveryPrefixAssignment.Data.cfg,cfg,RecoveryValuationCount.cfg,Data.cfg,
    TapeEmbedding.config,Fin.addCases,selectorSlots]

theorem selector_input (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool) :
    RecoveryFocus.config selectorSlots
      (cfg d count cap binaryCount committed guard selectorMachine.start).heads
      (cfg d count cap binaryCount committed guard selectorMachine.start).tapes
      ((prefixData d binaryCount committed guard).cfg RecoveryPrefixAssignment.machine.start)=
      cfg d count cap binaryCount committed guard selectorMachine.start := by
  exact focus_configuration selectorSlots selectorSlots_injective _ _ _ _ rfl
    (selector_input_heads d count cap binaryCount committed guard)
    (selector_input_tapes d count cap binaryCount committed guard)
    (by intro i _; rfl) (by intro i _; rfl)

theorem selector_run (d : Data) (count cap : Nat) (binaryCount committed : List Bool) (guard : Bool)
    (hw : binaryCount.length=d.index.length) (hsmall : 2*binaryCount.length+3≤d.capacity)
    (hcap : RecoveryCommittedBit.rawCost d.index committed≤d.capacity) :
    ∃ r,runFrom selectorMachine (RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard))
      (cfg d count cap binaryCount committed guard selectorMachine.start)=some r ∧
      r.steps≤RecoveryPrefixAssignment.cost (prefixData d binaryCount committed guard) ∧
      r.final.heads 5=0 ∧ r.final.tapes 5=[if value d.index<value binaryCount then
        (value committed).testBit (value d.index) else d.value] ∧
      r.final.heads 7=0 ∧ r.final.tapes 7=[d.valid] := by
  obtain ⟨base,hr,hs,out,_,_,_,_,hv,hf⟩ := RecoveryPrefixAssignment.assignment_run
    (prefixData d binaryCount committed guard) hw hsmall hcap
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config selectorSlots selectorSlots_injective
    RecoveryPrefixAssignment.machine
    (cfg d count cap binaryCount committed guard selectorMachine.start).heads
    (cfg d count cap binaryCount committed guard selectorMachine.start).tapes _ _ base hr
  rw [selector_input] at hrun
  have h5 : RecoveryFocus.pick selectorSlots 5=some 6 := RecoveryFocus.pick_slot selectorSlots selectorSlots_injective 6
  have hn : ¬∃ j,selectorSlots j=7 := by decide
  have h7 : RecoveryFocus.pick selectorSlots 7=none := by simp [RecoveryFocus.pick,hn]
  refine ⟨r,hrun,by rw [hsteps]; exact hs,?_,?_,?_,?_⟩
  · simp [hfinal,hf,RecoveryFocus.config,h5,RecoveryPrefixAssignment.Data.cfg]
  · simp [hfinal,hf,RecoveryFocus.config,h5,RecoveryPrefixAssignment.Data.cfg,hv,
      RecoveryPrefixAssignment.selected,prefixData]
  · simp [hfinal,RecoveryFocus.config,h7,cfg,RecoveryValuationCount.cfg,Data.cfg,TapeEmbedding.config,Fin.addCases]
  · simp [hfinal,RecoveryFocus.config,h7,cfg,RecoveryValuationCount.cfg,Data.cfg,TapeEmbedding.config,Fin.addCases]

end NearCubicWires.RepairOrdinary.RecoveryAssignment
