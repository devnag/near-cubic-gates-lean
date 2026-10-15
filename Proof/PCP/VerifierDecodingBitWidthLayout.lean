import Proof.PCP.VerifierDecodingClear
import Proof.MachineModel.ClockLengthReady

/-! The state-width supplier reuses the shared actual binary length counter.
The six-tape store retains the original unary dimension, its framed copy,
the canonical binary dimension, two paid scratch tapes, and the unary width. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.BitWidthMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def binaryLayout : Fin 6 ≃ Fin 6 where
  toFun := ![2,3,1,4,0,5]
  invFun := ![4,2,0,1,3,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def widthLayout : Fin 6 ≃ Fin 6 where
  toFun := ![2,5,0,1,3,4]
  invFun := ![2,3,0,4,5,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def frameProgram : Machine 6 5 := TapeEmbedding.machine 4 UnaryFrameMachine.machine
def binaryProgram : Machine 6 14 := TapeRenaming.machine binaryLayout (TapeEmbedding.machine 2 ClockLengthReady.machine)
def widthProgram : Machine 6 6 := TapeRenaming.machine widthLayout (TapeEmbedding.machine 4 LengthMachine.machine)

def framed (n : ℕ) := frame (List.replicate n true)
def dimension (n : ℕ) := frame (ClockBinary.word n)
def width (n : ℕ) := (ClockBinary.word n).length

def frameInput (n : ℕ) : Configuration 6 5 :=
  ⟨0,![1,0,0,0,0,0],![CompareMachine.word n,[],[],[],[],[]]⟩
def binaryInput (n : ℕ) : Configuration 6 14 :=
  ⟨binaryProgram.start,![1,0,0,0,0,0],![CompareMachine.word n,framed n,[],[],[],[]]⟩
def widthInput (n a b : ℕ) : Configuration 6 6 :=
  ⟨widthProgram.start,![1,0,0,0,0,0],
    ![CompareMachine.word n,framed n,dimension n,List.replicate a false,List.replicate b false,[]]⟩
def finished (n a b : ℕ) : Configuration 6 6 :=
  ⟨5,![1,0,0,0,0,1],
    ![CompareMachine.word n,framed n,dimension n,List.replicate a false,List.replicate b false,
      CompareMachine.word (width n)]⟩

theorem frame_layout (n : ℕ) :
    ∃ receipt : ExecutionReceipt 6 5,
      runFrom frameProgram (4*n+2) (frameInput n) = some receipt ∧
      receipt.final = ⟨4,(binaryInput n).heads,(binaryInput n).tapes⟩ ∧ receipt.steps = 4*n+2 := by
  obtain ⟨r,hr,hf,hs,_⟩ := UnaryFrameMachine.unary_frame_run n
  let eh : Fin 4 → ℕ := fun _ => 0
  let et : Fin 4 → List Bool := fun _ => []
  have he := TapeEmbedding.run_embed UnaryFrameMachine.machine eh et _ _ r hr
  let result := TapeEmbedding.receipt eh et r
  have hi : TapeEmbedding.config eh et (UnaryFrameMachine.cfg 0 n 1 0 []) = frameInput n := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at he
  refine ⟨result,he,?_,hs⟩
  apply configuration_ext
  · change r.final.control = 4
    simp [hf,UnaryFrameMachine.cfg]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
      UnaryFrameMachine.cfg,binaryInput,eh,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
      UnaryFrameMachine.cfg,binaryInput,et,Fin.addCases,framed]

def binaryBudget (n : ℕ) := ClockLengthReady.budget (List.replicate n true)

theorem binary_layout (n : ℕ) (hn : 0 < n) :
    ∃ a b, a ≤ 2*PCPResourceLedger.ell n+3 ∧
      b ≤ ClockInputLength.cost n (List.replicate n true) ∧
      ∃ receipt : ExecutionReceipt 6 14,
        runFrom binaryProgram (binaryBudget n) (binaryInput n) = some receipt ∧
        receipt.final = ⟨13,(widthInput n a b).heads,(widthInput n a b).tapes⟩ ∧
        receipt.steps ≤ binaryBudget n := by
  obtain ⟨a,b,ha,hb,r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockLengthReady.count_run (List.replicate n true) (by simpa)
  have hc : r.final.control = 13 := by
    have hh := (prefix_of_run ClockLengthReady.machine _ _ r hr).2
    have he : ∀ state : Fin 14, ClockLengthReady.machine.halted state = true → state = 13 := by
      intro state h
      fin_cases state <;> simp [ClockLengthReady.machine,Rewind.machine,Fin.addCases] at h ⊢
    exact he _ hh
  let eh : Fin 2 → ℕ := ![1,0]
  let et : Fin 2 → List Bool := ![CompareMachine.word n,[]]
  have he := TapeEmbedding.run_embed ClockLengthReady.machine eh et _ _ r hr
  have hren := TapeRenaming.run_rename binaryLayout (TapeEmbedding.machine 2 ClockLengthReady.machine) _ _ _ he
  let result := TapeRenaming.receipt binaryLayout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config binaryLayout (TapeEmbedding.config eh et
      (initialConfiguration ClockLengthReady.machine (ClockLengthReady.source (List.replicate n true)))) =
      binaryInput n := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        binaryInput,eh,binaryLayout,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        binaryInput,et,binaryLayout,ClockLengthReady.source,ClockLengthReady.input,framed,Fin.addCases]
  rw [hi] at hren
  refine ⟨a,b,by simpa using ha,by simpa using hb,result,hren,?_,hs⟩
  apply configuration_ext
  · exact hc
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,widthInput,eh,binaryLayout,Fin.addCases,hh]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,widthInput,et,binaryLayout,Fin.addCases,h0,h1,h2,h3,
      dimension,framed]

theorem width_layout (n a b : ℕ) :
    ∃ receipt : ExecutionReceipt 6 6,
      runFrom widthProgram (4*width n+3) (widthInput n a b) = some receipt ∧
      receipt.final = finished n a b ∧ receipt.steps = 4*width n+3 := by
  obtain ⟨r,hr,hf,hs,_⟩ := LengthMachine.length_run (ClockBinary.word n)
  let eh : Fin 4 → ℕ := ![1,0,0,0]
  let et : Fin 4 → List Bool := ![CompareMachine.word n,framed n,List.replicate a false,List.replicate b false]
  have he := TapeEmbedding.run_embed LengthMachine.machine eh et _ _ r hr
  have hren := TapeRenaming.run_rename widthLayout (TapeEmbedding.machine 4 LengthMachine.machine) _ _ _ he
  let result := TapeRenaming.receipt widthLayout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config widthLayout (TapeEmbedding.config eh et
      (initialConfiguration LengthMachine.machine ![dimension n,[]])) = widthInput n a b := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        widthInput,eh,widthLayout,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        widthInput,et,widthLayout,Fin.addCases]
  dsimp only [dimension] at hi
  rw [hi] at hren
  refine ⟨result,hren,?_,hs⟩
  apply configuration_ext
  · change r.final.control = 5
    simp [hf,LengthMachine.cfg]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,LengthMachine.cfg,finished,eh,widthLayout,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,LengthMachine.cfg,finished,et,widthLayout,Fin.addCases,
      dimension,CompareMachine.word,width]

end NearCubicWires.RepairSource.VerifierDecoding.BitWidthMachine
