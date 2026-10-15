import Proof.MachineModel.OrdinaryWilliamsMetadataPower

/-! A raw physical unary dimension supplies the reusable dimension
template. Its terminating blank is read, rather than allocated for free. -/
namespace NearCubicWires.RepairOrdinary.MatrixRawDimension
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (n : ℕ) : Fin 4 → ℕ := ![n+1,0,0,0]
def input (n : ℕ) : Fin 4 → List Bool := ![List.replicate n true,[],[],[]]

theorem raw_run (n : ℕ) :
    ∃ r : ExecutionReceipt 4 4,
      run MatrixDimensionHeader.machine (2*n+3) (input n)=some r ∧
      r.final.tapes 1=List.replicate n true ∧
      r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧
      r.final.heads=![n+1,0,0,1] ∧ r.steps=2*n+3 := by
  obtain ⟨base,hb,hf,hs⟩ := MatrixDimensionHeader.header_run [] [] n
  simp only [List.length_nil] at hb
  have hi : ZeroPadding.config (capacity n)
      (initialConfiguration MatrixDimensionHeader.machine (input n)) =
      MatrixDimensionHeader.input ([]++List.replicate n true++false::[]) 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,initialConfiguration,input,
        MatrixDimensionHeader.input,ZeroPadding.pad]
  rw [←hi] at hb
  obtain ⟨r,hr,he,ht,_⟩ := ZeroPadding.run_unpad MatrixDimensionHeader.machine (capacity n) _ _ base hb
  rw [hf] at he
  have htape (i : Fin 4) := congrArg (fun cfg : Configuration 4 4 => cfg.tapes i) he
  have hhead := congrArg (fun cfg : Configuration 4 4 => cfg.heads) he
  refine ⟨r,hr,?_,?_,?_,?_,ht.trans hs⟩
  · simpa [ZeroPadding.config,capacity,ZeroPadding.pad,MatrixDimensionHeader.output] using htape 1
  · simpa [ZeroPadding.config,capacity,ZeroPadding.pad,MatrixDimensionHeader.output] using htape 2
  · simpa [ZeroPadding.config,capacity,ZeroPadding.pad,MatrixDimensionHeader.output] using htape 3
  · simpa [ZeroPadding.config,MatrixDimensionHeader.output] using hhead

end NearCubicWires.RepairOrdinary.MatrixRawDimension
