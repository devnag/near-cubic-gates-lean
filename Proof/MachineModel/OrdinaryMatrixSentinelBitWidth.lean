import Proof.MachineModel.OrdinaryMatrixRawDimension

/-! Use the dimension template actually emitted by the raw-dimension
scan in the accepted binary/bit-width producer, with cold scratch. -/
namespace NearCubicWires.RepairOrdinary.MatrixSentinelBitWidth
open LocalBitMultitape RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (n : ℕ) : Fin 6 → ℕ := ![n+2,0,0,0,0,0]
def input (n : ℕ) : Configuration 6 25 :=
  ⟨BitWidthMachine.machine.start,![1,0,0,0,0,0],![UnaryTemplate.tape n,[],[],[],[],[]]⟩

theorem width_run (n : ℕ) (hn : 0<n) :
    ∃ r : ExecutionReceipt 6 25,
      runFrom BitWidthMachine.machine (8*n^2+34*n+11) (input n)=some r ∧
      r.final.tapes 0=UnaryTemplate.tape n ∧
      r.final.tapes 2=frame (binary (natBitLength n) n) ∧
      r.final.tapes 5=CompareMachine.word (natBitLength n) ∧
      r.final.heads=![1,0,0,0,0,1] ∧ r.steps ≤ 8*n^2+34*n+11 := by
  obtain ⟨base,hb,h0,h2,h5,hh,hs⟩ := BitWidthMachine.state_width_run n n hn (by rfl)
  obtain ⟨r,hr,hf,ht,_⟩ := ZeroPadding.run_config BitWidthMachine.machine (capacity n) _ _ base hb
  have hi : ZeroPadding.config (capacity n) (BitWidthMachine.input n)=input n := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,BitWidthMachine.input,
        BitWidthMachine.frameInput,Composition.leftConfig,input,CompareMachine.word,
        UnaryTemplate.tape,ZeroPadding.pad]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,?_,?_,ht.trans_le hs⟩
  · rw [hf]
    simp [ZeroPadding.config,capacity,h0,CompareMachine.word,UnaryTemplate.tape,ZeroPadding.pad]
  · rw [hf]
    simpa [ZeroPadding.config,capacity,ZeroPadding.pad,fixedBits_binary] using h2
  · rw [hf]
    simpa [ZeroPadding.config,capacity,ZeroPadding.pad] using h5
  · rw [hf]; exact hh

end NearCubicWires.RepairOrdinary.MatrixSentinelBitWidth
