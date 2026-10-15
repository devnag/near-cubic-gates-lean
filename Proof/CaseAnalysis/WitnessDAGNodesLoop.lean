import Proof.CaseAnalysis.WitnessDAGNodesPrefix

/-! The cold bank and native header feed the counted node loop directly.
The literal count sentinel is crossed by one paid transition. No native
descriptor prefix or local workspace is supplied by the theorem caller. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGNodes
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem repeat_heads_old {t s : ℕ} (phase : Fin 5) (c : Configuration t s) (total pos : ℕ) (i : Fin t) :
    (RepeatMachine.cfg phase c total pos).heads (i.castAdd 1)=c.heads i:=by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
private theorem repeat_tapes_old {t s : ℕ} (phase : Fin 5) (c : Configuration t s) (total pos : ℕ) (i : Fin t) :
    (RepeatMachine.cfg phase c total pos).tapes (i.castAdd 1)=c.tapes i:=by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left]
private theorem repeat_heads_driver {t s : ℕ} (phase : Fin 5) (c : Configuration t s) (total pos : ℕ) :
    (RepeatMachine.cfg phase c total pos).heads ((0 : Fin 1).natAdd t)=pos:=by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_right]
private theorem repeat_tapes_driver {t s : ℕ} (phase : Fin 5) (c : Configuration t s) (total pos : ℕ) :
    (RepeatMachine.cfg phase c total pos).tapes ((0 : Fin 1).natAdd t)=CompareMachine.word total:=by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_right]
private theorem repeat_entry {t s : ℕ} (body : Machine t s) (c : Configuration t s) (total pos : ℕ) :
    RepeatMachine.cfg 0 c total pos=
      (⟨(CloseoutRowsDegreeLoop.machine body).start,(RepeatMachine.cfg 0 c total pos).heads,
        (RepeatMachine.cfg 0 c total pos).tapes⟩ : Configuration (t+1) _):=by
  rfl

def enter : Machine 805 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun _ _=>some ⟨1,fun _=>none,fun i=>if i=766 then .right else .stay⟩
def enteredHeads (heads : Fin 805→ℕ) : Fin 805→ℕ:=
  fun i=>if i=766 then heads i+1 else heads i
noncomputable def loop:=RecoveryFocus.machine loopSlots NodeLoop.machine
noncomputable def tailMachine:=Composition.machine enter loop
noncomputable def machine:=Composition.machine prefixMachine tailMachine
def budget (w : ℕ) (arityBits : List Bool) (count : ℕ):=
  prefixBudget w arityBits count+1+(1+1+NodeLoop.budget w count)

theorem enter_run (heads : Fin 805→ℕ) (tapes : Fin 805→List Bool) : ∃ r,
    runFrom enter 1 ⟨0,heads,tapes⟩=some r ∧ r.final=⟨1,enteredHeads heads,tapes⟩ ∧ r.steps=1:=by
  have hs:step enter ⟨0,heads,tapes⟩=some ⟨1,enteredHeads heads,tapes⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi:i=766 <;> simp [applyAction,enteredHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem loop_old (i : Fin 755) : loopSlots (i.castAdd 1)=coreSlots i:=by
  simp only [loopSlots,Fin.val_castAdd,i.isLt,if_true,coreSlots]
  rfl
theorem entry_initial (w : ℕ) (left : List Bool) (flag : Bool) (words : List (List Bool)) (out : List Bool) :
    NodeLoop.entry w left flag words [] [] 0 out=
      NodeRound.cfg NodeRound.machine.start (NodeReady.capacity w) w 0 left (binary w 0)
        [] out (words.flatMap frame) flag:=by
  simp only [NodeLoop.entry,List.length_nil,List.take_zero,List.flatMap_nil,List.nil_append,List.append_nil,
    Nat.add_zero,NodeLoop.validity,List.range_zero,List.all_nil,Bool.and_true]

theorem nodes_run (w : ℕ) (arityBits : List Bool) (flag : Bool) (words : List (List Bool))
    (hw : 1≤w) (hb : arityBits.length≤w) (hwords : ∀ bits∈words,bits.length+1≤w)
    (hcount : words.length<2^w) : ∃ actual,
    run machine (budget w arityBits words.length) (input w arityBits (words.flatMap frame) flag words.length)=some actual ∧
      actual.steps≤budget w arityBits words.length ∧
      (∀ i,actual.final.heads (coreSlots i)=
        (NodeLoop.entry w (binary w (value arityBits)) flag words [] [] words.length
          (nativeHeader arityBits words.length++words.flatMap DAGMeaning.emitted)).heads i) ∧
      (∀ i,actual.final.tapes (coreSlots i)=
        (NodeLoop.entry w (binary w (value arityBits)) flag words [] [] words.length
          (nativeHeader arityBits words.length++words.flatMap DAGMeaning.emitted)).tapes i) ∧
      actual.final.tapes 766=CompareMachine.word words.length ∧ actual.final.heads 766=1:=by
  obtain ⟨p,hp,ps,ph,pt,pc,pch⟩:=prefix_run w arityBits (words.flatMap frame) flag words.length hw hb
  obtain ⟨e,he,ef,es⟩:=enter_run p.final.heads p.final.tapes
  obtain ⟨base,hbase,bf,bs⟩:=NodeLoop.nodes_run w (binary w (value arityBits)) flag words
    (nativeHeader arityBits words.length) [] [] (binary_length _ _) hwords hcount
  have local_heads : ∀ i,e.final.heads (loopSlots i)=
      (RepeatMachine.cfg 0 (NodeLoop.entry w (binary w (value arityBits)) flag words [] [] 0
        (nativeHeader arityBits words.length)) words.length 1).heads i:=by
    intro i
    refine Fin.addCases (m:=755) (n:=1) ?_ ?_ i
    · intro j
      rw [loop_old,ef]
      have hn:coreSlots j≠766:=by apply Fin.ne_of_val_ne;dsimp [coreSlots];omega
      simp only [enteredHeads,if_neg hn]
      rw [ph,repeat_heads_old,entry_initial]
      rfl
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rw [ef]
      change enteredHeads p.final.heads 766=1
      simp [enteredHeads,pch]
  have local_tapes : ∀ i,e.final.tapes (loopSlots i)=
      (RepeatMachine.cfg 0 (NodeLoop.entry w (binary w (value arityBits)) flag words [] [] 0
        (nativeHeader arityBits words.length)) words.length 1).tapes i:=by
    intro i
    refine Fin.addCases (m:=755) (n:=1) ?_ ?_ i
    · intro j
      rw [loop_old,ef,pt,repeat_tapes_old,entry_initial]
      rfl
    · intro j
      have hj:j=0:=Fin.eq_zero j
      subst j
      rw [ef]
      rw [repeat_tapes_driver]
      exact pc
  have baseRun:=hbase
  rw [repeat_entry NodeRound.machine] at baseRun
  obtain ⟨b,hb,_,bt,bheads,btapes,_⟩:=RecoveryFocus.dock loopSlots loop_injective NodeLoop.machine _
    e.final.heads e.final.tapes _ local_heads local_tapes base baseRun
  have ht:=Composition.run_join enter loop _ _ _ e b he hb
  let tail:=Composition.joinedReceipt e b
  have htail:runFrom tailMachine (1+1+NodeLoop.budget w words.length)
      (Composition.restart p.final tailMachine.start)=some tail:=ht
  have hall:=Composition.run_join prefixMachine tailMachine _ _ _ p tail hp htail
  refine ⟨Composition.joinedReceipt p tail,hall,?_,?_,?_,?_,?_⟩
  · change p.steps+1+(e.steps+1+b.steps)≤budget w arityBits words.length
    unfold budget
    omega
  · intro i
    change b.final.heads (coreSlots i)=_
    rw [←loop_old,bheads,bf,repeat_heads_old]
  · intro i
    change b.final.tapes (coreSlots i)=_
    rw [←loop_old,btapes,bf,repeat_tapes_old]
  · change b.final.tapes (loopSlots 755)=_
    rw [btapes,bf]
    exact repeat_tapes_driver _ _ _ _
  · change b.final.heads (loopSlots 755)=_
    rw [bheads,bf]
    exact repeat_heads_driver _ _ _ _

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGNodes
