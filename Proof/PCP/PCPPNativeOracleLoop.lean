import Proof.PCP.PCPPNativeNodeLoopMeaning

/-! The original oracle-node loop consumes the physically present native
size sentinel, returns that same sentinel at head1, and emits exactly the
native encoding of the previously verified copied shared-DAG nodes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeLoop
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem step_budget_bound {n r : ℕ} (base index C F : ℕ) (projection : Fin n → ProjectedRandomBit r)
    (node : BooleanNode n) (hF : nodeBudget base index C projection node+1 ≤ F)
    (hp : base+2*index+2 ≤ F) : PCPPNativeNodeStep.budget base index C F projection node ≤ 6*F+8 := by
  unfold PCPPNativeNodeStep.budget PCPPNativeNodeReusable.budget
  omega

def workspace {n r : ℕ} (base index C F : ℕ) (projection : Fin n → ProjectedRandomBit r) : List (BooleanNode n) → Prop
  | [] => True
  | node::nodes => nodeCapacity base index C projection node ∧ nodeBudget base index C projection node+1 ≤ F ∧
      base+2*index+2 ≤ F ∧ workspace base (index+1) C F projection nodes

theorem requirements_of_workspace {n r : ℕ} (base index C F : ℕ) (projection : Fin n → ProjectedRandomBit r)
    (nodes : List (BooleanNode n)) (hw : workspace base index C F projection nodes) :
    requirements base index C F (6*F+8) projection nodes := by
  induction nodes generalizing index with
  | nil => trivial
  | cons node nodes ih =>
    rcases hw with ⟨hc,hf,hp,ht⟩
    exact ⟨hc,hf,hp,step_budget_bound base index C F projection node hf hp,ih (index+1) ht⟩

def templateCaps (count : ℕ) (i : Fin 123) := if i=122 then count+2 else 0
noncomputable def templateConfiguration (phase : Fin 5) (bits queries : List Bool)
    (cursor base position C F : ℕ) (out : List Bool) (count driverHead : ℕ) :=
  ZeroPadding.config (templateCaps count) (configuration phase bits queries cursor base position C F out count driverHead)

theorem template_count (phase : Fin 5) (bits queries : List Bool)
    (cursor base position C F : ℕ) (out : List Bool) (count driverHead : ℕ) :
    (templateConfiguration phase bits queries cursor base position C F out count driverHead).tapes 122=UnaryTemplate.tape count ∧
      (templateConfiguration phase bits queries cursor base position C F out count driverHead).heads 122=driverHead := by
  constructor
  · change ZeroPadding.pad (count+2) (CompareMachine.word count)=UnaryTemplate.tape count
    exact DecompositionSerializerCount.padded_count count
  · rfl

theorem oracle_run {n r : ℕ} (pre tail : List Bool) (base C F : ℕ) (oracle : BooleanCircuit n)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hw : workspace base 0 C F projection oracle.nodes) :
    ∃ result,runFrom machine (oracle.size*(6*F+11)+3)
      (templateConfiguration 0 (source pre tail oracle.nodes) (rowCache projection) pre.length base base C F out oracle.size 1)=some result ∧
      result.steps ≤ oracle.size*(6*F+11)+3 ∧
      result.final=templateConfiguration 3 (source pre tail oracle.nodes) (rowCache projection)
        (pre.length+(nativeWords oracle.nodes).length) base (base+2*oracle.size) C F
        (out++(PCPPNative.copiedNodes base oracle projection oracle.size).flatMap PCPPRequestNodeSchema.native) oracle.size 1 := by
  obtain ⟨raw,hr,rs,rf⟩ := loop_run oracle.nodes pre tail base 0 C F (6*F+8) projection out hCF
    (requirements_of_workspace base 0 C F projection oracle.nodes hw) oracle.size 0 (by simp [BooleanCircuit.size])
  have ht : oracle.nodes.length*(6*F+8+2)+oracle.size+3=oracle.size*(6*F+11)+3 := by
    change oracle.size*(6*F+8+2)+oracle.size+3=oracle.size*(6*F+11)+3
    ring
  rw [ht] at hr rs
  simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add] at hr rf
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine (templateCaps oracle.size) _ _ raw hr
  refine ⟨result,hresult,by omega,?_⟩
  rw [resultFinal,rf,emitted_copiedNodes]
  rfl

end NearCubicWires.RepairOrdinary.PCPPNativeNodeLoop
