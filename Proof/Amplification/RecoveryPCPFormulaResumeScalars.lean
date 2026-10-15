import Proof.Amplification.RecoveryPCPFormulaResumeCapacityRun
import Proof.Amplification.RecoveryPCPFormulaResumeCountPair
import Proof.Amplification.RecoveryPCPFormulaResumeRandom

/-! The actual original binary R/Q fields now produce every scalar datum
required by the formula consumer: capacities, both exponential counters,
ordinary width/query counters and the initial framed randomness word. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeColdScalars
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding ProjectionNormalization RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capSlots (i : Fin 55) : Fin 66 := i.castAdd 11
def countSlots (i : Fin 9) : Fin 66 := if i=0 then 3 else ⟨54+i.val,by have hi:=i.isLt; omega⟩
def randomSlots : Fin 4→Fin 66 := ![63,64,3,65]
theorem cap_injective : Function.Injective capSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 66=>i.val) h)
theorem count_injective : Function.Injective countSlots := by
  intro i j h; apply Fin.ext
  have hv:=congrArg (fun i : Fin 66=>i.val) h
  dsimp [countSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
theorem random_injective : Function.Injective randomSlots := by decide
noncomputable def first := RecoveryFocus.machine capSlots RecoveryPCPFormulaResumeCapacity.machine
noncomputable def countMachine := RecoveryFocus.machine countSlots RecoveryPCPFormulaResumeCountPair.machine
noncomputable def counted := Composition.machine first countMachine
noncomputable def randomMachine := RecoveryFocus.machine randomSlots RecoveryColdPaddedCopy.machine
noncomputable def machine := Composition.machine counted randomMachine
def input (rBits qBits : List Bool) : Fin 66→List Bool :=
  Fin.addCases (m:=55) (n:=11) (motive:=fun _=>List Bool)
    (RecoveryPCPFormulaResumeCapacity.input rBits qBits) (fun _=>[])
def budget (rBits qBits : List Bool) := RecoveryPCPFormulaResumeCapacity.budget rBits qBits+1+
  RecoveryPCPFormulaResumeCountPair.budget (value rBits)+1+(4*value rBits+8)

theorem scalars_ready (rBits qBits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget rBits qBits) (input rBits qBits) out ∧
      out 3=CompareMachine.word (value rBits) ∧
      out 17=List.replicate (RecoveryProjectionRows.capacity (value rBits)) true ∧
      out 31=CompareMachine.word (value qBits) ∧
      out 37=List.replicate (RecoverySourceClauseLoad.uniformBudget (value qBits) (value rBits)) true ∧
      out 58=CompareMachine.word (2^value rBits-1) ∧
      out 61=List.replicate (2^value rBits) true ∧
      out 64=frame (List.replicate (value rBits) false) := by
  obtain ⟨caps,hcaps,c3,_c5,c17,c31,_c33,_c35,c37⟩ := RecoveryPCPFormulaResumeCapacity.capacity_run rBits qBits
  let a:=install capSlots (input rBits qBits) caps
  have ha:=hcaps.focus capSlots cap_injective (input rBits qBits) (by
    intro i; simp only [input,capSlots,Fin.addCases_left])
  have a3 : a 3=CompareMachine.word (value rBits) := (install_slot capSlots cap_injective _ caps 3).trans c3
  have afresh (i : Fin 66) (hi : (55 : Nat)≤(i : Fin 66).val) : a i=[] := by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j h; have hv:=congrArg (fun i : Fin 66=>i.val) h; have hj:=j.isLt
      change j.val=i.val at hv; omega)]
    let k : Fin 11 := ⟨i.val-55,by have hi':=i.isLt; omega⟩
    have he : i=k.natAdd 55 := by apply Fin.ext; dsimp [k]; omega
    rw [he]
    simp only [input,Fin.addCases_right]
  obtain ⟨counts,hcounts,d0,d4,d7⟩ := RecoveryPCPFormulaResumeCountPair.counts_ready (value rBits)
  let b:=install countSlots a counts
  have hb:=hcounts.focus countSlots count_injective a (by
    intro i
    by_cases hi : i=0
    · subst i; exact a3
    · rw [afresh (countSlots i) (by
        have hn : i.val≠0 := fun h=>hi (Fin.ext h)
        simp only [countSlots,hi,ite_false]; omega)]
      simp only [RecoveryPCPFormulaResumeCountPair.input,hi,ite_false])
  have firstRun:=ClockJoin.join first countMachine _ _ _ _ _ ha hb
  have b3 : b 3=CompareMachine.word (value rBits) := (install_slot countSlots count_injective a counts 0).trans d0
  have bkeep (i : Fin 66) (hi : i.val<55) (hn : i≠3) : b i=a i := by
    apply install_other
    intro j h
    have hv:=congrArg (fun i : Fin 66=>i.val) h
    dsimp [countSlots] at hv
    split_ifs at hv with hj
    · exact hn (Fin.ext hv.symm)
    · have hjn : j.val≠0 := fun he=>hj (Fin.ext he)
      dsimp at hv; omega
  have bfresh (i : Fin 66) (hi : (63 : Nat)≤(i : Fin 66).val) : b i=[] := by
    dsimp only [b]
    rw [install_other _ _ _ _ (by
      intro j h; have hv:=congrArg (fun i : Fin 66=>i.val) h; have hj:=j.isLt
      dsimp [countSlots] at hv; split_ifs at hv <;> dsimp at hv <;> omega)]
    exact afresh i (by omega)
  obtain ⟨random,hrandom,r1,r2⟩ := RecoveryPCPFormulaResumeRandomCold.random_ready (value rBits)
  have hr:=hrandom.focus randomSlots random_injective b (by
    intro i; fin_cases i
    · exact bfresh 63 (by decide)
    · exact bfresh 64 (by decide)
    · exact b3
    · exact bfresh 65 (by decide))
  let out:=install randomSlots b random
  have whole:=ClockJoin.join counted randomMachine _ _ _ _ _ firstRun hr
  refine ⟨out,whole,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (install_slot randomSlots random_injective b random 2).trans r2
  · rw [show out 17=b 17 from install_other randomSlots b random 17 (by decide),bkeep 17 (by decide) (by decide)]
    exact (install_slot capSlots cap_injective _ caps 17).trans c17
  · rw [show out 31=b 31 from install_other randomSlots b random 31 (by decide),bkeep 31 (by decide) (by decide)]
    exact (install_slot capSlots cap_injective _ caps 31).trans c31
  · rw [show out 37=b 37 from install_other randomSlots b random 37 (by decide),bkeep 37 (by decide) (by decide)]
    exact (install_slot capSlots cap_injective _ caps 37).trans c37
  · rw [show out 58=b 58 from install_other randomSlots b random 58 (by decide)]
    exact (install_slot countSlots count_injective a counts 4).trans d4
  · rw [show out 61=b 61 from install_other randomSlots b random 61 (by decide)]
    exact (install_slot countSlots count_injective a counts 7).trans d7
  · exact (install_slot randomSlots random_injective b random 1).trans r1

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeColdScalars
