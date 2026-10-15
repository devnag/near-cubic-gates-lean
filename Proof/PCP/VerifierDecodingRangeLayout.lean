import Proof.PCP.VerifierDecodingField
import Proof.Amplification.RecoveryRootRoundTapes

/-! Physical fixed-width state-index validation: read from the retained code,
compare against the already produced binary state count, and keep all ambient
code/width cursors. There is no conversion from an unchecked numerical index. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
open LocalBitMultitape RepairOrdinary StablePartition.Workspace RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 6 ≃ Fin 6 where
  toFun := ![3,1,4,5,0,2]
  invFun := ![4,1,5,0,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fieldProgram : Machine 6 6 := TapeEmbedding.machine 3 FieldMachine.machine
def compareProgram : Machine 6 7 :=
  TapeRenaming.machine layout (TapeEmbedding.machine 2 RecoveryRootRound.compareMachine)

def store (source target bound : List Bool) (width capacity : ℕ) (flag : Bool) : Fin 6 → List Bool :=
  ![source,target,CompareMachine.word width,frame bound,[flag],List.replicate capacity false]
def heads (pos : ℕ) : Fin 6 → ℕ := ![pos,0,1,0,0,0]
def fieldInput (source backing bound : List Bool) (pos width capacity : ℕ) : Configuration 6 6 :=
  ⟨0,heads pos,store source backing bound width capacity false⟩
def compareInput (source bits bound : List Bool) (pos capacity : ℕ) : Configuration 6 7 :=
  ⟨compareProgram.start,heads pos,store source (frame bits) bound bits.length capacity false⟩
def compared (source bits bound : List Bool) (pos capacity : ℕ) : Configuration 6 7 :=
  ⟨6,heads pos,store source (frame bits) bound bits.length (max capacity (2*bits.length+1))
    (decide (value bound ≤ value bits))⟩

theorem field_layout (pre bits tail backing bound : List Bool) (capacity : ℕ)
    (hb : backing.length ≤ 2*bits.length+1) :
    let source := pre++Streaming.marks bits++tail
    ∃ receipt : ExecutionReceipt 6 6,
      runFrom fieldProgram (4*bits.length+2) (fieldInput source backing bound pre.length bits.length capacity) = some receipt ∧
      receipt.final = ⟨4,(compareInput source bits bound (pre.length+2*bits.length) capacity).heads,
        (compareInput source bits bound (pre.length+2*bits.length) capacity).tapes⟩ ∧
      receipt.steps = 4*bits.length+2 := by
  dsimp only
  let source := pre++Streaming.marks bits++tail
  obtain ⟨r,hr,hf,hs,_⟩ := FieldMachine.field_run pre bits tail backing hb
  let eh : Fin 3 → ℕ := fun _ => 0
  let et : Fin 3 → List Bool := ![frame bound,[false],List.replicate capacity false]
  have hp := TapeEmbedding.run_embed FieldMachine.machine eh et _ _ r hr
  let result := TapeEmbedding.receipt eh et r
  have hi : TapeEmbedding.config eh et (FieldMachine.scan 0 source pre.length bits.length 0 [] backing) =
      fieldInput source backing bound pre.length bits.length capacity := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,FieldMachine.scan,fieldInput,store,et,Fin.addCases,overlay]
  rw [hi] at hp
  refine ⟨result,hp,?_,hs⟩
  apply configuration_ext
  · change r.final.control = 4
    simp [hf,FieldMachine.finished]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
      FieldMachine.finished,compareInput,heads,eh,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
      FieldMachine.finished,compareInput,store,et,Fin.addCases]

theorem compare_layout (source bits bound : List Bool) (pos capacity : ℕ)
    (hw : bound.length = bits.length) :
    ∃ receipt : ExecutionReceipt 6 7,
      runFrom compareProgram (4*bits.length+4) (compareInput source bits bound pos capacity) = some receipt ∧
      receipt.final = compared source bits bound pos capacity ∧ receipt.steps = 4*bits.length+4 := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryRootRound.compare_ready bound bits capacity hw
  have hc : r.final.control = 6 := by
    have hh := (prefix_of_run RecoveryRootRound.compareMachine _ _ r hr).2
    have he : ∀ state : Fin 7, RecoveryRootRound.compareMachine.halted state = true → state = 6 := by
      intro state h
      fin_cases state <;> simp [RecoveryRootRound.compareMachine,Rewind.machine,Fin.addCases] at h ⊢
    exact he _ hh
  let eh : Fin 2 → ℕ := ![pos,1]
  let et : Fin 2 → List Bool := ![source,CompareMachine.word bits.length]
  have he := TapeEmbedding.run_embed RecoveryRootRound.compareMachine eh et _ _ r hr
  have hp := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 RecoveryRootRound.compareMachine) _ _ _ he
  let result := TapeRenaming.receipt layout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config layout (TapeEmbedding.config eh et
      (initialConfiguration RecoveryRootRound.compareMachine
        ![frame bound,frame bits,[false],List.replicate capacity false])) = compareInput source bits bound pos capacity := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        compareInput,heads,eh,layout,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        compareInput,store,et,layout,Fin.addCases]
  rw [hi,hw] at hp
  refine ⟨result,hp,?_,by simpa only [result,TapeRenaming.receipt,TapeEmbedding.receipt,hw] using hs⟩
  apply configuration_ext
  · exact hc
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,compared,heads,eh,layout,Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,compared,store,et,layout,Fin.addCases,ht,hw]

end NearCubicWires.RepairSource.VerifierDecoding.RangeMachine
