import Proof.MachineModel.OrdinaryMatrixUnaryDifference

/-! Cold, linear-cost entries for both unary encodings that occur in the
dimension pipeline. No terminal blank or auxiliary driver is an input. -/
namespace NearCubicWires.RepairOrdinary.MatrixRawDimension
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resetMachine := Rewind.machine MatrixDimensionHeader.machine
def resetInput (n : ℕ) : Fin 5 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (4+1) => List Bool) (input n) (fun _ : Fin 1 => [])

theorem reset_run (n : ℕ) :
    ∃ r : ExecutionReceipt 5 6,
      run resetMachine (4*n+8) (resetInput n)=some r ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*n+8 := by
  obtain ⟨base,hb,h1,h2,h3,_,hs⟩ := raw_run n
  obtain ⟨r,hr,ht,hh,hsteps,_⟩ := Rewind.reset_run MatrixDimensionHeader.machine (2*n+3) (input n) base hb
  have htime : 2*base.steps+2=4*n+8 := by omega
  rw [htime] at hr hsteps
  exact ⟨r,hr,(ht 1).trans h1,(ht 2).trans h2,(ht 3).trans h3,hh,hsteps⟩

end NearCubicWires.RepairOrdinary.MatrixRawDimension

namespace NearCubicWires.RepairOrdinary.MatrixTemplateCopy
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def wordInput (n : ℕ) : Fin 5 → List Bool := ![CompareMachine.word n,[],[],[],[]]
def wordCapacity (n : ℕ) : Fin 5 → ℕ := ![n+2,0,0,0,0]

theorem word_run (n : ℕ) :
    ∃ r : ExecutionReceipt 5 8,
      run resetMachine (4*n+12) (wordInput n)=some r ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*n+12 := by
  obtain ⟨base,hb,_,h1,h2,h3,hh,hs⟩ := reset_run n
  have hi : ZeroPadding.config (wordCapacity n) (initialConfiguration resetMachine (wordInput n))=
      initialConfiguration resetMachine (resetInput n) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,wordCapacity,initialConfiguration,wordInput,
        resetInput,input,Fin.addCases,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  unfold run at hb
  rw [←hi] at hb
  obtain ⟨r,hr,hf,ht,_⟩ := ZeroPadding.run_unpad resetMachine (wordCapacity n) _ _ base hb
  have h1' := congrArg (fun cfg : Configuration 5 8 => cfg.tapes 1) hf
  have h2' := congrArg (fun cfg : Configuration 5 8 => cfg.tapes 2) hf
  have h3' := congrArg (fun cfg : Configuration 5 8 => cfg.tapes 3) hf
  have hh' (i : Fin 5) := congrArg (fun cfg : Configuration 5 8 => cfg.heads i) hf
  refine ⟨r,hr,?_,?_,?_,?_,ht.trans hs⟩
  · simpa [ZeroPadding.config,wordCapacity,ZeroPadding.pad,h1] using h1'
  · simpa [ZeroPadding.config,wordCapacity,ZeroPadding.pad,h2] using h2'
  · simpa [ZeroPadding.config,wordCapacity,ZeroPadding.pad,h3] using h3'
  · intro i; exact (hh' i).trans (hh i)

end NearCubicWires.RepairOrdinary.MatrixTemplateCopy
