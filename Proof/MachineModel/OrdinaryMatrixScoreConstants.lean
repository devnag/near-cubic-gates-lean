import Proof.MachineModel.OrdinaryMatrixScoreTopBit

/-! Cold scalar setup supplies the actual width, capacity, top-bit offset,
and zero constant for every subsequent assignment's reusable accumulator. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreConstants
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def topSlots : Fin 4 → Fin 18 := ![1,11,12,13]
def zeroSlots : Fin 5 → Fin 18 := ![0,14,15,16,17]
noncomputable def first := TapeEmbedding.machine 7 MatrixScoreCapacity.machine
noncomputable def top := RecoveryFocus.machine topSlots MatrixScoreTopBit.machine
noncomputable def prepare := Composition.machine first top
noncomputable def zero := RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def machine := Composition.machine prepare zero
def input (w : ℕ) : Fin 18 → List Bool := fun i => if i.val=0 then List.replicate w true else []

theorem constants_run (s : ℕ) :
    ∃ actual : ExecutionReceipt 18 43,
      run machine (24*(s+1)+89) (input (s+1))=some actual ∧
      actual.final.tapes 0=List.replicate (s+1) true ∧
      actual.final.tapes 8=List.replicate (MatrixScoreCapacity.capacity (s+1)) true ∧
      actual.final.tapes 11=frame (binary (s+1) (2^s)) ∧
      actual.final.tapes 15=frame (binary (s+1) 0) ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps=24*(s+1)+89 := by
  obtain ⟨base,hb,b0,b1,b8,bh,bs⟩ := MatrixScoreCapacity.capacity_run (s+1)
  have he := TapeEmbedding.run_embed MatrixScoreCapacity.machine (fun _ : Fin 7 => 0)
    (fun _ : Fin 7 => []) _ _ base hb
  let expanded := TapeEmbedding.receipt (fun _ : Fin 7 => 0) (fun _ : Fin 7 => []) base
  have eh : ∀ i,expanded.final.heads i=0 := by
    intro i
    fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bh]
  obtain ⟨topBit,ht,_,t1,th,ts⟩ := MatrixScoreTopBit.top_bit_run s
  let topInput := initialConfiguration MatrixScoreTopBit.machine
    ![frame (List.replicate (s+1) false++[true]),[],[],[]]
  have ti : RecoveryFocus.config topSlots expanded.final.heads expanded.final.tapes topInput=
      Composition.restart expanded.final top.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [eh,topInput,initialConfiguration]
    · intro i
      fin_cases i
      · exact b1
      all_goals rfl
  obtain ⟨middle,hm,hmf,hms⟩ := RecoveryFocus.run_config topSlots (by decide) MatrixScoreTopBit.machine
    expanded.final.heads expanded.final.tapes _ topInput topBit ht
  rw [ti] at hm
  have hj := Composition.run_join first top (12*(s+1)+69) (8*(s+1)+14) _ expanded middle he hm
  let prepared := Composition.joinedReceipt expanded middle
  have ph : ∀ i,prepared.final.heads i=0 := by
    intro i
    change middle.final.heads i=0
    rw [hmf]
    cases h : RecoveryFocus.pick topSlots i <;> simp [RecoveryFocus.config,h,eh,th]
  have p0 : prepared.final.tapes 0=List.replicate (s+1) true := by
    change middle.final.tapes 0=_
    rw [hmf]
    simpa [RecoveryFocus.config,show RecoveryFocus.pick topSlots 0=none by decide,
      expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using b0
  have p8 : prepared.final.tapes 8=List.replicate (MatrixScoreCapacity.capacity (s+1)) true := by
    change middle.final.tapes 8=_
    rw [hmf]
    simpa [RecoveryFocus.config,show RecoveryFocus.pick topSlots 8=none by decide,
      expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using b8
  have p11 : prepared.final.tapes 11=frame (binary (s+1) (2^s)) := by
    change middle.final.tapes (topSlots 1)=_
    rw [hmf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot topSlots (by decide)] using t1
  have blank (i : Fin 18) (hi : (14 : ℕ) ≤ i.val) : prepared.final.tapes i=[] := by
    change middle.final.tapes i=[]
    rw [hmf]
    have hn : RecoveryFocus.pick topSlots i=none := by
      fin_cases i <;> simp at hi
      all_goals decide
    simp only [RecoveryFocus.config,hn]
    fin_cases i <;> simp at hi
    all_goals simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases]
  obtain ⟨zeroed,hz,z0,_,z2,_,_,zh,zs⟩ := ClockScalarFields.zero_run (s+1)
  let zeroInput := initialConfiguration ClockNormalize.machine (ClockScalarFields.zeroInput (s+1))
  have zi : RecoveryFocus.config zeroSlots prepared.final.heads prepared.final.tapes zeroInput=
      Composition.restart prepared.final zero.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [ph,zeroInput,initialConfiguration]
    · intro i
      fin_cases i
      · exact p0
      · exact blank 14 (by decide)
      · exact blank 15 (by decide)
      · exact blank 16 (by decide)
      · exact blank 17 (by decide)
  obtain ⟨last,hl,hlf,hls⟩ := RecoveryFocus.run_config zeroSlots (by decide) ClockNormalize.machine
    prepared.final.heads prepared.final.tapes _ zeroInput zeroed hz
  rw [zi] at hl
  have hall := Composition.run_join prepare zero ((12*(s+1)+69)+1+(8*(s+1)+14))
    (4*(s+1)+4) _ prepared last hj hl
  have hin : Composition.leftConfig 6 (Composition.leftConfig 9
      (TapeEmbedding.config (fun _ : Fin 7 => 0) (fun _ : Fin 7 => [])
        (initialConfiguration MatrixScoreCapacity.machine (MatrixScoreCapacity.input (s+1)))))=
      initialConfiguration machine (input (s+1)) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,TapeEmbedding.config,Fin.addCases,
        initialConfiguration,input,MatrixScoreCapacity.input]
  rw [hin] at hall
  have htime : ((12*(s+1)+69)+1+(8*(s+1)+14))+1+(4*(s+1)+4)=24*(s+1)+89 := by omega
  rw [htime] at hall
  have other (i : Fin 18) (hn : RecoveryFocus.pick zeroSlots i=none) : last.final.tapes i=prepared.final.tapes i := by
    rw [hlf]; simp [RecoveryFocus.config,hn]
  refine ⟨Composition.joinedReceipt prepared last,hall,?_,(other 8 (by decide)).trans p8,
    (other 11 (by decide)).trans p11,?_,?_,?_⟩
  · change last.final.tapes (zeroSlots 0)=_
    rw [hlf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot zeroSlots (by decide)] using z0
  · change last.final.tapes (zeroSlots 2)=_
    rw [hlf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot zeroSlots (by decide)] using z2
  · intro i
    change last.final.heads i=0
    rw [hlf]
    cases h : RecoveryFocus.pick zeroSlots i <;> simp [RecoveryFocus.config,h,ph,zh]
  · change (base.steps+1+middle.steps)+1+last.steps=_
    rw [bs,hms,ts,hls,zs]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreConstants
