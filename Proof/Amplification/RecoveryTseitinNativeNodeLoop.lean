import Proof.Amplification.RecoveryTseitinNativeNodeStep
import Proof.Amplification.RecoveryTseitinNativeLoopCore

/-! The actual sentinel-driven loop emits every original node's complete
Tseitin clauses in their original topological order. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loopMachine:=RepeatMachine.machine stepMachine (fun _ _=>true)
def nativeWords {n : Nat} (nodes : List (BooleanNode n)) := nodes.flatMap PCPPRequestNodeSchema.native
def source {n : Nat} (pre tail : List Bool) (nodes : List (BooleanNode n)) := pre++nativeWords nodes++tail
def emitted {n : Nat} (index : Nat) : List (BooleanNode n)→List Bool
  | []=>[]
  | node::nodes=>RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)++emitted (index+1) nodes
def requirements {n : Nat} (index cap : Nat) : List (BooleanNode n)→Prop
  | []=>True
  | node::nodes=>node.WellFormedAt index ∧ coldNodeBudget index node ≤ cap ∧ index+1 ≤ cap ∧ requirements (index+1) cap nodes
noncomputable def configuration (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total driver : Nat) := RepeatMachine.cfg phase (entry n index pos word out cap) total driver

theorem loop_run {n : Nat} (nodes : List (BooleanNode n)) (pre tail out : List Bool)
    (index cap total pos : Nat) (hc : pos+nodes.length=total) (hreq : requirements index cap nodes) :
    ∃ r,runFrom loopMachine (nodes.length*(stepBudget cap+2)+total+3)
      (configuration 0 n index pre.length (source pre tail nodes) out cap total (pos+1))=some r ∧
      r.final=configuration 3 n (index+nodes.length) (pre.length+(nativeWords nodes).length)
        (source pre tail nodes) (out++emitted index nodes) cap total 1 ∧
      r.steps ≤ nodes.length*(stepBudget cap+2)+total+3 := by
  induction nodes generalizing pre out index pos with
  | nil=>
    have hp : pos=total := by simpa only [List.length_nil,Nat.add_zero] using hc
    subst pos
    obtain ⟨r,hr,rf,rs⟩:=exhaust_run stepMachine (entry n index pre.length (source pre tail []) out cap) total
    refine ⟨r,?_,?_,?_⟩
    · simpa only [loopMachine,configuration,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [configuration,nativeWords,List.flatMap_nil,List.length_nil,Nat.add_zero,emitted,List.append_nil] using rf
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
  | cons node nodes ih=>
    rcases hreq with ⟨hw,hcap,hindex,hrest⟩
    have firstSource : source pre tail (node::nodes)=pre++PCPPRequestNodeSchema.native node++(nativeWords nodes++tail) := by
      simp only [source,nativeWords,List.flatMap_cons,List.append_assoc]
    have nextSource : source (pre++PCPPRequestNodeSchema.native node) tail nodes=source pre tail (node::nodes) := by
      simp only [source,nativeWords,List.flatMap_cons,List.append_assoc]
    obtain ⟨a,ha,ah,atapes,asteps⟩:=step_run index node hw pre (nativeWords nodes++tail) out cap hcap hindex
    rw [←firstSource] at ha atapes
    let next:=entry n (index+1) (pre++PCPPRequestNodeSchema.native node).length
      (source (pre++PCPPRequestNodeSchema.native node) tail nodes)
      (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)) cap
    have iteration:=iteration_data stepMachine
      (entry n index pre.length (source pre tail (node::nodes)) out cap) next total pos a rfl
      (by simp only [List.length_cons] at hc; omega) ha ah
      (by simpa only [next,entry,nextSource] using atapes)
    change Timed loopMachine (a.steps+2)
      (configuration 0 n index pre.length (source pre tail (node::nodes)) out cap total (pos+1))
      (configuration 0 n (index+1) (pre++PCPPRequestNodeSchema.native node).length
        (source (pre++PCPPRequestNodeSchema.native node) tail nodes)
        (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node)) cap total (pos+2)) at iteration
    obtain ⟨b,hb,bf,bs⟩:=ih (pre++PCPPRequestNodeSchema.native node)
      (out++RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodeClauses index node))
      (index+1) (pos+1) (by simp only [List.length_cons] at hc; omega) hrest
    have he : pos+2=(pos+1)+1 := by omega
    rw [he] at iteration
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨result,hr,rf,rs,_peak⟩:=hprefix.followedBy b hb
    have htime : (a.steps+2)+(nodes.length*(stepBudget cap+2)+total+3) ≤
        (node::nodes).length*(stepBudget cap+2)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hm:=runFrom_moreFuel loopMachine _
      ((node::nodes).length*(stepBudget cap+2)+total+3-((a.steps+2)+(nodes.length*(stepBudget cap+2)+total+3))) _ result hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,hm,?_,?_⟩
    · have hfinal:=rf.trans bf
      simpa only [configuration,source,nativeWords,List.flatMap_cons,emitted,List.length_cons,
        List.length_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hfinal
    · rw [rs]
      omega

theorem emitted_original {n : Nat} (index : Nat) (nodes : List (BooleanNode n)) :
    emitted index nodes=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodesClausesFrom index nodes) := by
  induction nodes generalizing index with
  | nil=>rfl
  | cons node nodes ih=>
    simp only [emitted,CircuitInputCNF.circuitInputNodesClausesFrom,ih,
      RecoveryFormulaPayload.input,RecoveryFormulaPayload.fields,List.map_append,
      ProjectionNormalization.FieldList.stream,List.flatten_append]

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
