import Proof.Amplification.RecoveryTseitinNativeFormulaLayout
import Proof.Amplification.RecoveryTseitinNativeAssertion

/-! Every original node clause and the original final assertion execute on
one append cursor. The incoming tautology prefix yields the exact original
free-input circuit formula, with every witness position retained. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Formula
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem writer_view (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) : ∀ j,
    (state phase n index pos word out cap total output).heads (Assertion.wordSlots j)=0 ∧
    (state phase n index pos word out cap total output).tapes (Assertion.wordSlots j)=[] := by
  intro j
  fin_cases j
  · exact ⟨extra_heads phase n index pos word out cap total output 1,
      extra_tapes phase n index pos word out cap total output 1⟩
  · exact ⟨extra_heads phase n index pos word out cap total output 2,
      extra_tapes phase n index pos word out cap total output 2⟩
theorem assertion_heads (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) (i : Fin 1338) :
    (state phase n index pos word out cap total output).heads (Assertion.slots i)=Reuse.heads 0 out.length i := by
  by_cases hi : i=1
  · subst i
    exact extra_heads phase n index pos word out cap total output 0
  by_cases hs : i=1062
  · subst i
    exact extra_heads phase n index pos word out cap total output 1
  rw [Assertion.slots,if_neg hi,if_neg hs,old_heads]
  simp only [Reuse.heads,if_neg hs]
theorem assertion_tapes (phase : Fin 5) (n index pos : Nat) (word out : List Bool)
    (cap total output : Nat) (i : Fin 1338) (hs : i≠1062) :
    (state phase n index pos word out cap total output).tapes (Assertion.slots i)=
      Reuse.data n output Assertion.bits out cap i := by
  by_cases hi : i=1
  · subst i
    exact extra_tapes phase n index pos word out cap total output 0
  rw [Assertion.slots,if_neg hi,if_neg hs,old_tapes]
  simp only [Reuse.data,if_neg hi,if_neg hs]

noncomputable def first := TapeEmbedding.machine 3 Reuse.loopMachine
noncomputable def machine := Composition.machine first Assertion.machine
def budget (n count : Nat) :=
  count*(Reuse.stepBudget (Reuse.capacity n count)+2)+count+3+1+Assertion.budget (Reuse.capacity n count)
theorem loop_start {t e s : Nat} (p : Machine t s) (accepted : Fin s→(Fin t→Bool)→Bool)
    (c : Configuration t s) (h : Fin e→Nat) (d : Fin e→List Bool) (total driver : Nat) :
    (TapeEmbedding.config h d (RepeatMachine.cfg 0 c total driver)).control=
      (TapeEmbedding.machine e (RepeatMachine.machine p accepted)).start := rfl
theorem formula_input_append (a b : EncodedCNF) :
    RecoveryFormulaPayload.input (a++b)=RecoveryFormulaPayload.input a++RecoveryFormulaPayload.input b := by
  simp only [RecoveryFormulaPayload.input,RecoveryFormulaPayload.fields,List.map_append,
    FieldList.stream,List.flatten_append]

theorem formula_run {n : Nat} (circuit : BooleanCircuit n) (pre tail : List Bool) : ∃ r,
    runFrom machine (budget n circuit.nodes.length)
      ⟨machine.start,
        (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes)
          (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n))
          (Reuse.capacity n circuit.nodes.length) circuit.nodes.length circuit.output.val).heads,
        (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes)
          (RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n))
          (Reuse.capacity n circuit.nodes.length) circuit.nodes.length circuit.output.val).tapes⟩=some r ∧
      r.final.heads 1333=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit)).length ∧
      r.final.tapes 1333=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit) ∧
      r.steps ≤ budget n circuit.nodes.length := by
  let out:=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)
  let cap:=Reuse.capacity n circuit.nodes.length
  let clauses:=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputNodesClausesFrom 0 circuit.nodes)
  obtain ⟨base,hbase,bf,bs⟩:=Reuse.circuit_run circuit pre tail out
  let a:=TapeEmbedding.receipt (fun _ : Fin 3=>0) (extraData circuit.output.val) base
  have ha:=TapeEmbedding.run_embed Reuse.loopMachine (fun _ : Fin 3=>0)
    (extraData circuit.output.val) _ _ base hbase
  have af : a.final=state 3 n circuit.nodes.length (pre.length+(Reuse.nativeWords circuit.nodes).length)
      (Reuse.source pre tail circuit.nodes) (out++clauses) cap circuit.nodes.length circuit.output.val := by
    change TapeEmbedding.config _ _ base.final=_
    rw [bf]
    rfl
  have hc:=Reuse.node_budget_bound circuit.nodes.length circuit.output.val circuit.output.isLt.le
    (.const true : BooleanNode n) (by trivial)
  obtain ⟨b,hb,bh,bt,bstep⟩:=Assertion.assertion_run n circuit.output.val (out++clauses) cap
    a.final.heads a.final.tapes hc
    (by rw [af]; exact writer_view _ _ _ _ _ _ _ _ _)
    (by rw [af]; exact assertion_heads _ _ _ _ _ _ _ _ _)
    (by rw [af]; exact assertion_tapes _ _ _ _ _ _ _ _ _)
  obtain ⟨r,hr,rh,rt,rs⟩:=join_two first Assertion.machine _ _ _ a b ha hb
  have hc0 : (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes) out cap
      circuit.nodes.length circuit.output.val).control=first.start :=
    loop_start Reuse.stepMachine (fun _ _=>true) _ _ _ _ _
  have hstart : Composition.leftConfig _
      (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes) out cap
        circuit.nodes.length circuit.output.val)=
      (⟨machine.start,
        (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes) out cap
          circuit.nodes.length circuit.output.val).heads,
        (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes) out cap
          circuit.nodes.length circuit.output.val).tapes⟩ : Configuration 1342 _) := by
    apply configuration_ext
    · change Fin.castAdd _ _=Fin.castAdd _ _
      exact congrArg (Fin.castAdd _) hc0
    · rfl
    · rfl
  change runFrom machine (budget n circuit.nodes.length)
    (Composition.leftConfig _ (state 0 n 0 pre.length (Reuse.source pre tail circuit.nodes)
      out cap circuit.nodes.length circuit.output.val))=some r at hr
  rw [hstart] at hr
  have he : (out++clauses)++RecoveryFormulaPayload.input
      [TseitinCNF.positiveUnit (CircuitInputCNF.circuitInputGateVariable n circuit.output.val)]=
      RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputFormula circuit) := by
    simp only [CircuitInputCNF.circuitInputFormula,formula_input_append,out,clauses,List.append_assoc]
  refine ⟨r,hr,?_,?_,?_⟩
  · exact (congrFun rh 1333).trans (bh.trans (congrArg List.length he))
  · exact (congrFun rt 1333).trans (bt.trans he)
  · rw [rs]
    change base.steps+1+b.steps ≤ _
    unfold budget
    change b.steps ≤ Assertion.budget (Reuse.capacity n circuit.nodes.length) at bstep
    omega

theorem output_forward : CursorRestore.NoLeft machine (1333 : Fin 1342) :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.embedded_forward 3 Reuse.loopMachine 1333 Reuse.loop_forward)
    Assertion.output_forward

end NearCubicWires.RepairSource.RecoveryTseitinNative.Formula
