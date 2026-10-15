import Proof.CaseAnalysis.RecoveryClauseListMeaning

/-! The paid finite clause driver. The postcondition exposes a contiguous
extension of the original builder and exactly the outputs saved for its
original deferred ANDs; it does not define another graph compiler. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseList
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryExecution RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedClauseCollect (old pushed)
open RecoveryBoundedLiteral (references)
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Finish {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clauses : List (Fin 3→Literal q)) (W C L : ℕ) (out pre source stack : List Bool) where
  next : BooleanDAGBuilder n
  extension : BooleanDAGExtension b next
  refs : List ℕ
  H : Fin 72→ℕ
  A : Fin 72→List Bool
  left : ℕ
  right : ℕ
  refs_length : refs.length=clauses.length
  refs_bound : ∀ ref∈refs,ref ≤ W
  left_bound : left ≤ W
  right_bound : right ≤ W
  state : RecoveryBoundedClauseState.State (H∘old) (A∘old) next.nodes.length left right C L
    (out++extension.suffix.flatMap PCPPRequestNodeSchema.native) (pre++word clauses) source (sourceWord (references values))
  stackH : H 71=(stack++stackWord refs).length
  stackA : A 71=stack++stackWord refs
  nodes : (compileClauses b values hv clauses).final.nodes=next.nodes++allSuffix next.nodes.length refs
  output : (compileClauses b values hv clauses).output.val=next.nodes.length+refs.length

noncomputable def forwardMachine:=RepeatMachine.machine RecoveryBoundedClauseBody.machine (fun _ _=>true)
noncomputable def configuration (phase : Fin 5) (H : Fin 72→ℕ) (A : Fin 72→List Bool) (total driver : ℕ):=
  RepeatMachine.cfg phase (⟨RecoveryBoundedClauseBody.machine.start,H,A⟩ : Configuration 72 _) total driver

theorem forward_run {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b)) (hv : values.length=q)
    (clauses : List (Fin 3→Literal q)) (W C L total pos : ℕ)
    (H : Fin 72→ℕ) (A : Fin 72→List Bool) (left right : ℕ) (out pre source tail stack : List Bool)
    (h : RecoveryBoundedClauseState.State (H∘old) (A∘old) b.nodes.length left right C L out pre source (sourceWord (references values)))
    (hSH : H 71=stack.length) (hSA : A 71=stack)
    (hSource : source=pre++word clauses++tail) (hpos : pos+clauses.length=total)
    (hFinal : (compileClauses b values hv clauses).final.nodes.length ≤ W)
    (hq : q ≤ W) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (hL : C+5*W+7 ≤ L) :
    ∃ f : Finish b values hv clauses W C L out pre source stack, ∃ r,
      runFrom forwardMachine (clauses.length*(RecoveryBoundedClauseBody.budget W C+2)+total+3)
        (configuration 0 H A total (pos+1))=some r ∧
      r.final=configuration 3 f.H f.A total 1 ∧
      r.steps ≤ clauses.length*(RecoveryBoundedClauseBody.budget W C+2)+total+3 := by
  induction clauses generalizing b pos H A left right out pre stack with
  | nil=>
    have hoff : pos=total:=by simpa only [List.length_nil,Nat.add_zero] using hpos
    let f : Finish b values hv [] W C L out pre source stack := {
      next:=b,extension:=BooleanDAGExtension.refl b,refs:=[],H:=H,A:=A,left:=left,right:=right
      refs_length:=rfl,refs_bound:=by simp,left_bound:=hl,right_bound:=hr
      state:=by simpa only [BooleanDAGExtension.refl,word,List.flatMap_nil,List.append_nil] using h
      stackH:=by simpa only [stackWord,List.flatMap_nil,List.append_nil] using hSH
      stackA:=by simpa only [stackWord,List.flatMap_nil,List.append_nil] using hSA
      nodes:=nil_nodes b values hv
      output:=by simpa only [List.length_nil,Nat.add_zero] using nil_output b values hv }
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust RecoveryBoundedClauseBody.machine (fun _ _=>true)
      (⟨RecoveryBoundedClauseBody.machine.start,H,A⟩ : Configuration 72 _) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨f,r,?_,rf,?_⟩
    · simpa only [forwardMachine,configuration,hoff,List.length_nil,Nat.zero_mul,Nat.zero_add] using rr
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using rs.le
  | cons clause clauses ih=>
    let head:=compileClause b values hv clause
    let lifted:=liftLiveWires head.compiled.extension values
    have lifted_length : lifted.length=q:=by rw [liftLiveWires_length];exact hv
    let nextOut:=out++head.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let nextPre:=pre++RecoveryBoundedClauseRun.word clause
    let nextStack:=pushed head.compiled.output.val stack
    have hh : head.compiled.final.nodes.length ≤ W:=head_bound b values hv clause clauses W hFinal
    have hs : source=pre++RecoveryBoundedClauseRun.word clause++(word clauses++tail) := by
      simpa only [word,List.flatMap_cons,List.append_assoc] using hSource
    obtain ⟨first,fr,fs,fstate,fsH,fsA⟩:=RecoveryBoundedClauseBody.body_run b values hv clause H A left right W C L
      out pre source (word clauses++tail) stack h hSH hSA hs hh hq hl hr hC hL
    have hp : pos < total:=by simp only [List.length_cons] at hpos;omega
    have hiteration:=RepeatMachine.iteration RecoveryBoundedClauseBody.machine (fun _ _=>true)
      (⟨RecoveryBoundedClauseBody.machine.start,H,A⟩ : Configuration 72 _) total pos first rfl hp fr
    change Timed forwardMachine (first.steps+2) (configuration 0 H A total (pos+1))
      (RepeatMachine.cfg 0 first.final total (pos+2)) at hiteration
    have fi : RecoveryBoundedClauseState.State (first.final.heads∘old) (first.final.tapes∘old)
        head.compiled.final.nodes.length head.compiled.output.val
        (RecoveryBoundedClauseMeaning.third b values hv clause).compiled.output.val C L
        nextOut nextPre source (sourceWord (references lifted)) := by
      rw [RecoveryBoundedClauseMeaning.references_lift]
      exact fstate
    have hnSource : source=nextPre++word clauses++tail := by
      simpa only [nextPre,List.append_assoc] using hs
    obtain ⟨f,last,lr,lf,ls⟩:=ih head.compiled.final lifted lifted_length (pos+1) first.final.heads first.final.tapes
      head.compiled.output.val (RecoveryBoundedClauseMeaning.third b values hv clause).compiled.output.val
      nextOut nextPre nextStack fi fsH fsA hnSource (by simp only [List.length_cons] at hpos;omega)
      (tail_bound b values hv clause clauses W hFinal) (head.compiled.output.isLt.le.trans hh)
      (third_bound b values hv clause W hh)
    have hi : RepeatMachine.cfg 0 first.final total (pos+2)=
        configuration 0 first.final.heads first.final.tapes total (pos+1+1) := by
      apply configuration_ext
      · rfl
      · rfl
      · rfl
    rw [hi] at hiteration
    rcases hiteration with ⟨space,hprefix⟩
    obtain ⟨r,rr,rf,rs,_⟩:=hprefix.followedBy last lr
    have hb : first.steps+2+(clauses.length*(RecoveryBoundedClauseBody.budget W C+2)+total+3) ≤
        (clause::clauses).length*(RecoveryBoundedClauseBody.budget W C+2)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel forwardMachine _
      ((clause::clauses).length*(RecoveryBoundedClauseBody.budget W C+2)+total+3-
        (first.steps+2+(clauses.length*(RecoveryBoundedClauseBody.budget W C+2)+total+3))) _ r rr
    rw [Nat.add_sub_of_le hb] at more
    let finished : Finish b values hv (clause::clauses) W C L out pre source stack := {
      next:=f.next,extension:=head.compiled.extension.trans f.extension,refs:=head.compiled.output.val::f.refs
      H:=f.H,A:=f.A,left:=f.left,right:=f.right
      refs_length:=by simp only [List.length_cons,f.refs_length]
      refs_bound:=by
        intro ref href
        rcases List.mem_cons.mp href with he|he
        · exact he ▸ (head.compiled.output.isLt.le.trans hh)
        · exact f.refs_bound ref he
      left_bound:=f.left_bound,right_bound:=f.right_bound
      state:=by
        simpa only [BooleanDAGExtension.trans,word,List.flatMap_cons,List.flatMap_append,List.append_assoc,
          nextOut,nextPre,lifted,RecoveryBoundedClauseMeaning.references_lift] using f.state
      stackH:=by simpa only [nextStack,pushed,stackWord,List.flatMap_cons,List.append_assoc] using f.stackH
      stackA:=by simpa only [nextStack,pushed,stackWord,List.flatMap_cons,List.append_assoc] using f.stackA
      nodes:=by
        rw [cons_nodes]
        change (compileClauses head.compiled.final lifted lifted_length clauses).final.nodes++
          [.and head.compiled.output.val (compileClauses head.compiled.final lifted lifted_length clauses).output.val]=_
        rw [f.output,f.nodes]
        simp only [allSuffix,List.append_assoc]
      output:=by
        rw [cons_output]
        change (compileClauses head.compiled.final lifted lifted_length clauses).final.nodes.length=_
        rw [f.nodes,List.length_append,allSuffix_length,List.length_cons] }
    refine ⟨finished,r,more,rf.trans lf,?_⟩
    rw [rs]
    omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseList
