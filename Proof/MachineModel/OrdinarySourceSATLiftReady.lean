import Proof.MachineModel.OrdinarySourceSATLiftPowerGraph

/-! The cold request physically produces the source's isolated input and
the shared polynomial unary capacity. No workspace premise escapes this
preparation parent. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure ColdReady (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (heads : Fin (tapes p) → ℕ) (data : Fin (tapes p) → List Bool) : Prop where
  core_heads : ∀ i,heads (core p i)=0
  core_tapes : ∀ i,data (core p i)=p.base.inputTapes input i
  workspace : Workspace (wiring p) b heads data
  fresh : ∀ i,p.base.tapeCount+179 ≤ i.val → heads i=0 ∧ data i=[]

def prepareBudget (input : List Bool) (b : ℕ) :=
  parseBudget input b+PCPSerializerCapacity.Power.budget 2 268435456 b+1

noncomputable def powered (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (out : Fin 18 → List Bool) : Fin (tapes p) → List Bool :=
  install (power p) (parsed p input b) out

theorem power_call (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :
    ∃ out,Path p 4 5 (PCPSerializerCapacity.Power.budget 2 268435456 b+1)
      (parsedHeads p input b) (parsedHeads p input b) (parsed p input b) (powered p input b out) ∧
      out (PCPSerializerCapacity.Power.outputSlot 2)=List.replicate (capacity b) true := by
  exact PowerGraph.power_call 268435456 p input b

theorem powered_ready (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ)
    (out : Fin 18 → List Bool)
    (hcap : out (PCPSerializerCapacity.Power.outputSlot 2)=List.replicate (capacity b) true) :
    ColdReady p input b (parsedHeads p input b) (powered p input b out) := by
  let data := powered p input b out
  refine ⟨parsed_heads_core p input b,?_,?_,?_⟩
  · intro i
    exact (install_other (power p) (parsed p input b) out (core p i)
      (fun j => Ne.symm (core_ne_power p i j))).trans (parsed_core p input b i)
  · refine ⟨?_,?_,?_,?_⟩
    · intro i _hi
      exact parsed_heads_kernel p input b i
    · change data (power p (PCPSerializerCapacity.Power.outputSlot 2))=_
      exact (install_slot (power p) (power_injective p) (parsed p input b) out _).trans hcap
    · refine ⟨0,Nat.zero_le _,?_⟩
      change data (kernel p 2)=[]
      exact (install_other (power p) (parsed p input b) out (kernel p 2)
        (fun j => Ne.symm (kernel_ne_power p 2 j (by decide)))).trans
        (parsed_kernel p input b 2 (by decide) (by decide))
    · intro i hi
      have h0 : i≠0 := by intro he; subst i; simp at hi
      have h1 : i≠1 := by intro he; subst i; simp at hi
      have he : data (kernel p i)=[] :=
        (install_other (power p) (parsed p input b) out (kernel p i)
          (fun j => Ne.symm (kernel_ne_power p i j h1))).trans (parsed_kernel p input b i h0 h1)
      change (data (kernel p i)).length ≤ _
      rw [he]
      exact Nat.zero_le _
  · intro i hi
    refine ⟨parsed_heads_high p input b i hi,?_⟩
    exact (install_other (power p) (parsed p input b) out i
      (fun j => Ne.symm (high_ne_power p i hi j))).trans (parsed_high p input b i hi)

theorem cold_prepare (p : OrdinaryOracleProgram) (input : List Bool) (b : ℕ) :
    ∃ data,Path p 0 5 (prepareBudget input b) (fun _ => 0) (parsedHeads p input b)
      (cold p input b) data ∧ ColdReady p input b (parsedHeads p input b) data := by
  obtain ⟨out,hpath,hcap⟩ := power_call p input b
  refine ⟨powered p input b out,?_,powered_ready p input b out hcap⟩
  have whole := (parse_path p input b).trans hpath
  convert whole using 1
  unfold prepareBudget
  omega

end NearCubicWires.RepairSource.OrdinarySourceSATLift.Full
