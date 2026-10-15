import Proof.MachineModel.OrdinaryMemoryInitializationCarrier

/-! Literal field extraction from the raw fixed-verifier input. Each framed
field gets fresh output/reset tapes; prior fields and the moving source cursor
are retained. This is linear in the input and introduces no scalar decoding. -/
namespace NearCubicWires.RepairOrdinary.VerifierFieldLoad
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (source : List Bool) (cursor : ℕ)
    (code input bound : List Bool) (cScratch xScratch bScratch : ℕ) : Configuration 7 s :=
  ⟨state, ![cursor,0,0,0,0,0,0],
    ![source,code,List.replicate cScratch false,input,List.replicate xScratch false,
      bound,List.replicate bScratch false]⟩
def codeMachine : Machine 7 4 := TapeEmbedding.machine 4 FrameLoad.machine
def inputLayout : Fin 7 ≃ Fin 7 where
  toFun := ![0,3,4,1,2,5,6]
  invFun := ![0,3,4,1,2,5,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def boundLayout : Fin 7 ≃ Fin 7 where
  toFun := ![0,5,6,3,4,1,2]
  invFun := ![0,5,6,3,4,1,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem inputInverse : (inputLayout.symm : Fin 7 → Fin 7) = ![0,3,4,1,2,5,6] := rfl
@[simp] theorem boundInverse : (boundLayout.symm : Fin 7 → Fin 7) = ![0,5,6,3,4,1,2] := rfl
def inputMachine : Machine 7 4 := TapeRenaming.machine inputLayout codeMachine
def boundMachine : Machine 7 4 := TapeRenaming.machine boundLayout codeMachine
def tailMachine : Machine 7 8 := Composition.machine inputMachine boundMachine
def machine : Machine 7 12 := Composition.machine codeMachine tailMachine

theorem code_run (pre bits post input bound : List Bool) (xScratch bScratch : ℕ) :
    ∃ r : ExecutionReceipt 7 4,
      runFrom codeMachine (4*bits.length+3)
        (config 0 (pre++frame bits++post) pre.length [] input bound 0 xScratch bScratch) = some r ∧
      r.final = config 3 (pre++frame bits++post) (pre.length+(frame bits).length)
        (frame bits) input bound (frame bits).length xScratch bScratch := by
  obtain ⟨base,hb,hf,_,_⟩ := FrameLoad.load_run pre bits post [] (by simp)
  let extra : Fin 4 → List Bool := ![input,List.replicate xScratch false,bound,List.replicate bScratch false]
  have hr := TapeEmbedding.run_embed FrameLoad.machine (fun _ : Fin 4 => 0) extra _ _ base hb
  have hi : TapeEmbedding.config (fun _ : Fin 4 => 0) extra
      (FrameLoad.scan 0 (pre++frame bits++post) pre.length [] []) =
      config 0 (pre++frame bits++post) pre.length [] input bound 0 xScratch bScratch := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, FrameLoad.scan, config, Fin.addCases]
    · funext i
      fin_cases i <;> simp [TapeEmbedding.config, FrameLoad.scan, config, extra, Fin.addCases,
        StablePartition.Workspace.overlay]
  rw [hi] at hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 4 => 0) extra base, hr, ?_⟩
  simp only [TapeEmbedding.receipt, hf]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeEmbedding.config, FrameLoad.reset, config, Fin.addCases, Nat.add_assoc]
  · funext i
    fin_cases i <;> simp [TapeEmbedding.config, FrameLoad.reset, config, extra, Fin.addCases]

theorem swap_input {s : ℕ} (state : Fin s) (source : List Bool) (cursor : ℕ)
    (code input bound : List Bool) (cScratch xScratch bScratch : ℕ) :
    TapeRenaming.config inputLayout (config state source cursor code input bound cScratch xScratch bScratch) =
      config state source cursor input code bound xScratch cScratch bScratch := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config]
theorem swap_bound {s : ℕ} (state : Fin s) (source : List Bool) (cursor : ℕ)
    (code input bound : List Bool) (cScratch xScratch bScratch : ℕ) :
    TapeRenaming.config boundLayout (config state source cursor code input bound cScratch xScratch bScratch) =
      config state source cursor bound input code bScratch xScratch cScratch := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config, config]

theorem input_run (pre bits post code bound : List Bool) (cScratch bScratch : ℕ) :
    ∃ r : ExecutionReceipt 7 4,
      runFrom inputMachine (4*bits.length+3)
        (config 0 (pre++frame bits++post) pre.length code [] bound cScratch 0 bScratch) = some r ∧
      r.final = config 3 (pre++frame bits++post) (pre.length+(frame bits).length)
        code (frame bits) bound cScratch (frame bits).length bScratch := by
  obtain ⟨base,hb,hf⟩ := code_run pre bits post code bound cScratch bScratch
  have hr := TapeRenaming.run_rename inputLayout codeMachine _ _ base hb
  rw [swap_input] at hr
  refine ⟨TapeRenaming.receipt inputLayout base,hr,?_⟩
  simp only [TapeRenaming.receipt,hf,swap_input]

theorem bound_run (pre bits post code input : List Bool) (cScratch xScratch : ℕ) :
    ∃ r : ExecutionReceipt 7 4,
      runFrom boundMachine (4*bits.length+3)
        (config 0 (pre++frame bits++post) pre.length code input [] cScratch xScratch 0) = some r ∧
      r.final = config 3 (pre++frame bits++post) (pre.length+(frame bits).length)
        code input (frame bits) cScratch xScratch (frame bits).length := by
  obtain ⟨base,hb,hf⟩ := code_run pre bits post input code xScratch cScratch
  have hr := TapeRenaming.run_rename boundLayout codeMachine _ _ base hb
  rw [swap_bound] at hr
  refine ⟨TapeRenaming.receipt boundLayout base,hr,?_⟩
  simp only [TapeRenaming.receipt,hf,swap_bound]

end NearCubicWires.RepairOrdinary.VerifierFieldLoad
