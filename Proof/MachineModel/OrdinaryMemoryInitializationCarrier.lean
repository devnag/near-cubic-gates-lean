import Proof.MachineModel.OrdinaryMemoryInitialSources
import Proof.PCP.PCPResourceLedger

/-! The entire two-source initialization emitter at the common width ledger.
Only the actual source frames, unary widths and tape-one key are supplied;
all remaining tapes start blank. Initialization costs O((n+B+1)(w+1)). -/
namespace NearCubicWires.RepairOrdinary.MemoryInitializationCarrier
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (w : ℕ) (input witness : List Bool) : Fin 11 → List Bool :=
  fun i => if i = 1 then List.replicate (2*w) true
    else if i = 5 then List.replicate (2*w+2) true
    else if i = 8 then frame input else if i = 9 then frame witness
    else if i = 10 then binary (2*w+2) (2^w) else []
def capacities (w : ℕ) : Fin 11 → ℕ := ![2*w,0,0,4*w+5,2*w+2,0,1,1,0,0,0]
def budget (w n B : ℕ) : ℕ := 80*(n+B+1)*(w+1)

theorem padded_input (w : ℕ) (input witness : List Bool) :
    ZeroPadding.config (capacities w)
      (initialConfiguration MemoryInitialSources.machine (tapes w input witness)) =
    MemoryInitialSources.config MemoryInitialSources.machine.start (2*w) (2*w+2) 0 0 (2^w)
      (4*w+5) [] (frame input) (frame witness) 0 0 false := by
  have hz (n : ℕ) : binary n 0 = List.replicate n false := by
    induction n with
    | zero => rfl
    | succ n ih => simp [binary, ih, List.replicate_succ]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config, initialConfiguration, MemoryInitialSources.config,
      MemoryInitialCell.config, TapeEmbedding.config, MemoryRecordEmitter.config, Fin.addCases]
  · funext i
    fin_cases i <;> simp [ZeroPadding.config, initialConfiguration, MemoryInitialSources.config,
      MemoryInitialCell.config, TapeEmbedding.config, MemoryRecordEmitter.config,
      Fin.addCases, tapes, capacities, hz, ZeroPadding.pad]

theorem fits (L w n B : ℕ) (hL : 2≤L) (hn : n≤B) (hB : B≤L) (hw : 4*L+4≤2^w) :
    (2*n+1)+(2*B+1)<2^(2*w) ∧ 2*n+1<2^(2*w+2) ∧ 2^w+(2*B+1)<2^(2*w+2) := by
  have he := (PCPResourceLedger.record_capacity n B 0 0 0 L w hL hn hB
    (by omega) (by omega) (by omega) hw).1
  have hp : 2^(2*w+2) = (2^w)^2*4 := by
    rw [pow_add, Nat.mul_comm 2 w, pow_mul]
    norm_num
  dsimp only [PCPResourceLedger.events] at he
  constructor
  · omega
  rw [hp]
  constructor <;> nlinarith

theorem whole_budget (w n B : ℕ) :
    MemoryInitialLoop.budget (2*w) (2*w+2) n+1+
      MemoryInitialLoop.budget (2*w) (2*w+2) B ≤ budget w n B := by
  dsimp only [MemoryInitialLoop.budget, MemoryInitialLoop.loopBudget, MemoryInitialPair.budget, budget]
  nlinarith

theorem initialized_run (L w : ℕ) (input witness : List Bool)
    (hL : 2≤L) (hn : input.length≤witness.length) (hB : witness.length≤L) (hw : 4*L+4≤2^w) :
    ∃ r : ExecutionReceipt 11 154,
      run MemoryInitialSources.machine (budget w input.length witness.length)
        (tapes w input witness) = some r ∧
      r.final.tapes 2 = MemoryInitialEmission.fields (2*w) (2*w+2) w 0
        (MemoryInitialization.events input witness) ∧
      ZeroPadding.config (capacities w) r.final =
        MemoryInitialSources.config 153 (2*w) (2*w+2) ((frame input).length+(frame witness).length)
          (frame input).length (2^w+(frame witness).length) (4*w+5)
          (MemoryInitialEmission.fields (2*w) (2*w+2) w 0 (MemoryInitialization.events input witness))
          (frame input) (frame witness) (frame input).length (frame witness).length false := by
  obtain ⟨hs,hx,hk⟩ := fits L w input.length witness.length hL hn hB hw
  obtain ⟨base, hb, hf⟩ := MemoryInitialSources.initialized_run (2*w) (2*w+2) w (4*w+5)
    input witness (by simpa using hs) (by simpa using hx) (by simpa using hk) (by omega) (by omega)
  rw [← padded_input] at hb
  obtain ⟨r, hr, hrf, _, _⟩ := ZeroPadding.run_unpad MemoryInitialSources.machine (capacities w) _ _ base hb
  have hbudget := whole_budget w input.length witness.length
  have hmore := runFrom_moreFuel MemoryInitialSources.machine _
    (budget w input.length witness.length-
      (MemoryInitialLoop.budget (2*w) (2*w+2) input.length+1+
        MemoryInitialLoop.budget (2*w) (2*w+2) witness.length)) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  have hfinal := hrf.trans hf
  refine ⟨r,hmore,?_,hfinal⟩
  have hout := congrArg (fun c => c.tapes 2) hfinal
  simpa [ZeroPadding.config, capacities, MemoryInitialSources.config,
    MemoryInitialCell.config, TapeEmbedding.config, MemoryRecordEmitter.config, Fin.addCases] using hout

end NearCubicWires.RepairOrdinary.MemoryInitializationCarrier
