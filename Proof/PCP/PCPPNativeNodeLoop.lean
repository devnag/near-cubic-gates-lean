import Proof.PCP.PCPPNativeNodeStep
import Proof.PCP.VerifierDecodingRepeat

/-! The original-node loop is driven by an actual sentinel count tape.
Each body is the checked reusable node substitution plus position advance;
every entry/return and the final driver rewind are executed. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeLoop
open LocalBitMultitape SourceInterfaces RecoveryExecution PCPPNativeNodeMachine
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {s : ℕ} (_ : Fin s) (_ : Fin 122 → Bool) := true
noncomputable def machine := RepeatMachine.machine PCPPNativeNodeStep.machine accepted
def nativeWords {n : ℕ} (nodes : List (BooleanNode n)) := nodes.flatMap PCPPRequestNodeSchema.native
def source {n : ℕ} (pre tail : List Bool) (nodes : List (BooleanNode n)) := pre++nativeWords nodes++tail
def emitted {n r : ℕ} (base index : ℕ) (projection : Fin n → ProjectedRandomBit r) : List (BooleanNode n) → List Bool
  | [] => []
  | node::nodes => emittedNode base index projection node++emitted base (index+1) projection nodes
def requirements {n r : ℕ} (base index C F cost : ℕ) (projection : Fin n → ProjectedRandomBit r) : List (BooleanNode n) → Prop
  | [] => True
  | node::nodes => nodeCapacity base index C projection node ∧ nodeBudget base index C projection node+1 ≤ F ∧
      base+2*index+2 ≤ F ∧ PCPPNativeNodeStep.budget base index C F projection node ≤ cost ∧
      requirements base (index+1) C F cost projection nodes
noncomputable def configuration (phase : Fin 5) (bits queries : List Bool)
    (cursor base position C F : ℕ) (out : List Bool) (total driverHead : ℕ) :=
  RepeatMachine.cfg phase (PCPPNativeNodeStep.entry bits queries cursor base position C F out) total driverHead

theorem phase_equal {s : ℕ} (phase : Fin 5) (a b : Configuration 122 s) (total pos : ℕ)
    (hh : a.heads=b.heads) (ht : a.tapes=b.tapes) :
    RepeatMachine.cfg phase a total pos=RepeatMachine.cfg phase b total pos := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem loop_run {n r : ℕ} (nodes : List (BooleanNode n)) (pre tail : List Bool)
    (base index C F cost : ℕ) (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hCF : C+1 ≤ F) (hreq : requirements base index C F cost projection nodes)
    (total pos : ℕ) (hcount : pos+nodes.length=total) :
    ∃ result,runFrom machine (nodes.length*(cost+2)+total+3)
      (configuration 0 (source pre tail nodes) (rowCache projection) pre.length base (base+2*index) C F out total (pos+1))=some result ∧
      result.steps ≤ nodes.length*(cost+2)+total+3 ∧
      result.final=configuration 3 (source pre tail nodes) (rowCache projection)
        (pre.length+(nativeWords nodes).length) base (base+2*(index+nodes.length)) C F
        (out++emitted base index projection nodes) total 1 := by
  induction nodes generalizing pre index out pos with
  | nil =>
    have hp : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hcount
    subst pos
    have endRun := RepeatMachine.exhaust PCPPNativeNodeStep.machine accepted
      (PCPPNativeNodeStep.entry (source (n := n) pre tail []) (rowCache projection) pre.length base (base+2*index) C F out) total
    obtain ⟨result,hr,rf,rs⟩ := endRun.run (by
      simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨result,?_,?_,?_⟩
    · simpa only [machine,List.length_nil,Nat.zero_mul,Nat.zero_add,configuration] using hr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
    · simpa only [configuration,nativeWords,List.flatMap_nil,List.length_nil,Nat.add_zero,emitted,List.append_nil] using rf
  | cons node nodes ih =>
    rcases hreq with ⟨hC,hF,hposition,hcost,hrest⟩
    have sourceFirst : source pre tail (node::nodes)=originalSource pre (nativeWords nodes++tail) node := by
      simp only [source,nativeWords,List.flatMap_cons,originalSource,List.append_assoc]
    have sourceNext : source (pre++PCPPRequestNodeSchema.native node) tail nodes=source pre tail (node::nodes) := by
      simp only [source,nativeWords,List.flatMap_cons,List.append_assoc]
    obtain ⟨a,ha,as,ah,atapes⟩ := PCPPNativeNodeStep.step_run pre (nativeWords nodes++tail) base index C F projection node out hC hF hCF hposition
    rw [←sourceFirst] at ha atapes
    have iteration := RepeatMachine.iteration PCPPNativeNodeStep.machine accepted
      (PCPPNativeNodeStep.entry (source pre tail (node::nodes)) (rowCache projection) pre.length base (base+2*index) C F out)
      total pos a (by rfl) (by simp only [List.length_cons] at hcount; omega) ha
    simp only [accepted,ite_true] at iteration
    have mid : RepeatMachine.cfg 0 a.final total (pos+2)=
        configuration 0 (source (pre++PCPPRequestNodeSchema.native node) tail nodes) (rowCache projection)
          (pre++PCPPRequestNodeSchema.native node).length base (base+2*(index+1)) C F
          (out++emittedNode base index projection node) total ((pos+1)+1) := by
      apply phase_equal
      · simpa only [PCPPNativeNodeStep.entry,List.length_append] using ah
      · simpa only [PCPPNativeNodeStep.entry,sourceNext] using atapes
    rw [mid] at iteration
    obtain ⟨b,hb,bs,bf⟩ := ih (pre++PCPPRequestNodeSchema.native node) (index+1)
      (out++emittedNode base index projection node) hrest (pos+1) (by simp only [List.length_cons] at hcount; omega)
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨result,hr,rf,rs,_⟩ := hprefix.followedBy b hb
    have timeBound : (a.steps+2)+(nodes.length*(cost+2)+total+3) ≤ (node::nodes).length*(cost+2)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have more := runFrom_moreFuel machine _
      ((node::nodes).length*(cost+2)+total+3-((a.steps+2)+(nodes.length*(cost+2)+total+3))) _ result hr
    rw [Nat.add_sub_of_le timeBound] at more
    refine ⟨result,more,?_,?_⟩
    · rw [rs]
      nlinarith
    · have finalEq := rf.trans bf
      simpa only [configuration,source,nativeWords,List.flatMap_cons,emitted,List.length_cons,
        List.length_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using finalEq

end NearCubicWires.RepairOrdinary.PCPPNativeNodeLoop
