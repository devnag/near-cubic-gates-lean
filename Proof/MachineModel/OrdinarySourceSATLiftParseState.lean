import Proof.MachineModel.OrdinarySourceSATLiftFullGraph

/-! Physical request-parser endpoints and the disjoint-bank facts needed
by its capacity and source consumers. These describe executed call results. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeroCore (p : OrdinaryOracleProgram) : Fin p.base.tapeCount := ⟨0,by have := p.base.twoTapes; omega⟩
noncomputable def cold (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) : Fin (tapes p) → List Bool :=
  (program p).base.inputTapes (boundInput input b)
noncomputable def aData (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :=
  Function.update (Function.update (cold p input b) (parse p 0) (boundInput input b))
    (parse p 1) (List.replicate (boundInput input b).length false)
noncomputable def bData (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :=
  Function.update (Function.update (aData p input b) (core p (zeroCore p)) (frame input))
    (parse p 3) (List.replicate (2*input.length+1) false)
noncomputable def cData (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :=
  Function.update (Function.update (bData p input b) (parse p 2) (frame (List.replicate b true)))
    (parse p 3) (List.replicate (max (2*input.length+1) (2*b+1)) false)
noncomputable def parsed (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :=
  Function.update (Function.update (cData p input b) (power p 0) (List.replicate b true))
    (parse p 4) (List.replicate b false)
noncomputable def firstHeads (p : OrdinaryOracleProgram) (input : List Bool) : Fin (tapes p) → ℕ :=
  Function.update (fun _ => 0) (parse p 0) (2*input.length+1)
noncomputable def parsedHeads (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) : Fin (tapes p) → ℕ :=
  Function.update (fun _ => 0) (parse p 0) (boundInput input b).length

theorem core_ne_parse (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount) (j : Fin 5) :
    core p i≠parse p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hi := i.isLt
  dsimp [core,parse] at hv
  omega

theorem core_ne_power (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount) (j : Fin 18) :
    core p i≠power p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hi := i.isLt
  dsimp [core,power,kernel] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem kernel_ne_parse (p : OrdinaryOracleProgram) (i : Fin 156) (j : Fin 5) :
    kernel p i≠parse p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hi := i.isLt
  have hq := p.queryTape.isLt
  dsimp [kernel,core,parse] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem kernel_ne_power (p : OrdinaryOracleProgram) (i : Fin 156) (j : Fin 18) (hi : i≠1) :
    kernel p i≠power p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hiv := i.isLt
  have hq := p.queryTape.isLt
  have hi1 : i.val≠1 := fun h => hi (Fin.ext h)
  dsimp [kernel,core,power] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem power_ne_parse (p : OrdinaryOracleProgram) (i : Fin 18) (j : Fin 5) :
    power p i≠parse p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hi := i.isLt
  dsimp [power,kernel,parse] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem parsed_core (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin p.base.tapeCount) : parsed p input b (core p i)=p.base.inputTapes input i := by
  classical
  have he : core p i=core p (zeroCore p) ↔ i.val=0 := by
    constructor
    · intro h; exact congrArg (fun i : Fin p.base.tapeCount => i.val) (core_injective p h)
    · intro h; exact congrArg (core p) (Fin.ext h)
  simp only [parsed,cData,bData,aData,Function.update_apply,core_ne_parse,core_ne_power,if_false,he]
  simp [cold,Program.inputTapes,core]

theorem parsed_power (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) (i : Fin 18) :
    parsed p input b (power p i)=ProjectionNormalization.DimensionPolynomial.input 2 b i := by
  classical
  have he : power p i=power p 0 ↔ i.val=0 := by
    constructor
    · intro h; exact congrArg (fun i : Fin 18 => i.val) (power_injective p h)
    · intro h; exact congrArg (power p) (Fin.ext h)
  have hc : power p i≠core p (zeroCore p) := Ne.symm (core_ne_power p _ i)
  simp only [parsed,cData,bData,aData,Function.update_apply,power_ne_parse,hc,if_false,he]
  have hz : (power p i).val≠0 := by
    by_cases hi7 : i.val=7
    · simp [power,hi7,kernel]
    · simp [power,hi7]
  simp only [cold,Program.inputTapes,if_neg hz,ProjectionNormalization.DimensionPolynomial.input]

theorem parsed_kernel (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin 156) (h0 : i≠0) (h1 : i≠1) : parsed p input b (kernel p i)=[] := by
  classical
  have hc : kernel p i≠core p (zeroCore p) := Ne.symm (core_kernel_disjoint p _ i h0)
  have hp : kernel p i≠power p 0 := kernel_ne_power p i 0 h1
  simp only [parsed,cData,bData,aData,Function.update_apply,kernel_ne_parse,hc,hp,if_false]
  have hi : i.val≠0 := fun h => h0 (Fin.ext h)
  simp [cold,Program.inputTapes,kernel,hi]

theorem parsed_heads_core (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin p.base.tapeCount) : parsedHeads p input b (core p i)=0 := by
  classical
  simp [parsedHeads,Function.update,core_ne_parse]
theorem parsed_heads_kernel (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin 156) : parsedHeads p input b (kernel p i)=0 := by
  classical
  simp [parsedHeads,Function.update,kernel_ne_parse]
theorem parsed_heads_power (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin 18) : parsedHeads p input b (power p i)=0 := by
  classical
  simp [parsedHeads,Function.update,power_ne_parse]

theorem high_ne_core (p : OrdinaryOracleProgram) (i : Fin (tapes p)) (hi : p.base.tapeCount+179 ≤ i.val)
    (j : Fin p.base.tapeCount) : i≠core p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hj := j.isLt
  dsimp [core] at hv
  omega

theorem high_ne_kernel (p : OrdinaryOracleProgram) (i : Fin (tapes p)) (hi : p.base.tapeCount+179 ≤ i.val)
    (j : Fin 156) : i≠kernel p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hj := j.isLt
  have hq := p.queryTape.isLt
  dsimp [kernel,core] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem high_ne_power (p : OrdinaryOracleProgram) (i : Fin (tapes p)) (hi : p.base.tapeCount+179 ≤ i.val)
    (j : Fin 18) : i≠power p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hj := j.isLt
  dsimp [power,kernel] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem high_ne_parse (p : OrdinaryOracleProgram) (i : Fin (tapes p)) (hi : p.base.tapeCount+179 ≤ i.val)
    (j : Fin 5) : i≠parse p j := by
  intro he
  have hv := congrArg (fun i : Fin (tapes p) => i.val) he
  have hj := j.isLt
  dsimp [parse] at hv
  omega

theorem parsed_high (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin (tapes p)) (hi : p.base.tapeCount+179 ≤ i.val) : parsed p input b i=[] := by
  classical
  simp only [parsed,cData,bData,aData,Function.update_apply,high_ne_parse p i hi,
    high_ne_core p i hi,high_ne_power p i hi,if_false]
  simp [cold,Program.inputTapes,show i.val≠0 by omega]

theorem parsed_heads_high (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (i : Fin (tapes p)) (hi : p.base.tapeCount+179 ≤ i.val) : parsedHeads p input b i=0 := by
  classical
  simp [parsedHeads,Function.update,high_ne_parse p i hi]

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
