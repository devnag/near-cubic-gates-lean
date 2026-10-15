import Proof.MachineModel.OrdinaryWitnessPrefix

/-! The literal initialization caller needs its copied witness head reset.
Pay one masked rewind of the prefix producer while retaining the unread
witness suffix and every local scalar tape. -/
namespace NearCubicWires.RepairOrdinary.WitnessPrefixReady
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 6) : Bool := decide (i=5)
def machine : Machine 7 33 := MaskedReset.machine WitnessPrefix.machine selected
def config {s : ℕ} (state : Fin s) (w counter bound cap extra : ℕ)
    (source out : List Bool) (cursor : ℕ) : Configuration 7 s :=
  ⟨state,![0,0,0,0,cursor,0,0],
    ![frame (binary w counter),frame (binary w bound),[false],List.replicate cap false,
      source,out,List.replicate extra false]⟩

theorem prefix_run (w cap : ℕ) (pre bits suffix : List Bool)
    (hb : bits.length+1<2^w) (hcap : 2*w+1≤cap) :
    ∃ extra, extra≤WitnessPrefix.budget w bits.length ∧ ∃ r : ExecutionReceipt 7 33,
      runFrom machine (2*WitnessPrefix.budget w bits.length+2)
        (config machine.start w 0 bits.length cap 0 (pre++frame (bits++suffix)) [] pre.length)=some r ∧
      r.final=config 32 w (bits.length+1) bits.length cap extra
        (pre++frame (bits++suffix)) (frame bits) (pre.length+2*bits.length) := by
  obtain ⟨base,hbase,hbf⟩ := WitnessPrefix.prefix_run w cap pre bits suffix [] hb hcap
  simp only [List.nil_append] at hbf
  have hhead : ∀ i : Fin 6, selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=5 := by simpa [selected] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run WitnessPrefix.machine
      (WitnessPrefix.budget w bits.length) _ base hbase).1 (5 : Fin 6)
    simpa [WitnessPrefixBody.config,TapeEmbedding.config,WitnessCounterCheck.config,Fin.addCases] using h
  obtain ⟨r,hr,hf,_,_⟩ := MaskedReset.reset_run WitnessPrefix.machine selected
    (WitnessPrefix.budget w bits.length) _ base hbase hhead
  have hi : Rewind.recording
      (WitnessPrefixBody.config WitnessPrefix.machine.start w 0 bits.length cap false
        (pre++frame (bits++suffix)) [] pre.length) 0 =
      config machine.start w 0 bits.length cap 0 (pre++frame (bits++suffix)) [] pre.length := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Rewind.recording,Rewind.config,WitnessPrefixBody.config,
        TapeEmbedding.config,WitnessCounterCheck.config,config,Fin.addCases]
    · funext i
      fin_cases i <;> simp [Rewind.recording,Rewind.config,WitnessPrefixBody.config,
        TapeEmbedding.config,WitnessCounterCheck.config,config,Fin.addCases]
  rw [hi] at hr
  have hs := runFrom_steps_le WitnessPrefix.machine (WitnessPrefix.budget w bits.length) _ base hbase
  have ht : 2*base.steps+2≤2*WitnessPrefix.budget w bits.length+2 := by omega
  have hmore := runFrom_moreFuel machine _
    (2*WitnessPrefix.budget w bits.length+2-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le ht] at hmore
  refine ⟨base.steps,hs,r,hmore,?_⟩
  rw [hf,hbf]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,WitnessPrefixBody.config,
      TapeEmbedding.config,WitnessCounterCheck.config,config,selected,Fin.addCases]
  · funext i
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,WitnessPrefixBody.config,
      TapeEmbedding.config,WitnessCounterCheck.config,config,Fin.addCases]

end NearCubicWires.RepairOrdinary.WitnessPrefixReady
