import Proof.CaseAnalysis.RecoveryCountStep

/-! The original ascending count cases run on their own exact full-bound
driver. The opaque whole-count worker is reused, saving the original references
in order for the existing terminal false and reverse OR fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage RecoveryExecution
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n}

private theorem counts_cons (k : ℕ) (hk : k<bound) :
    (List.finRange bound).drop k=(⟨k,hk⟩ : Fin bound)::(List.finRange bound).drop (k+1) := by
  have h : k<(List.finRange bound).length:=by simpa using hk
  rw [List.drop_eq_getElem_cons h]
  congr 1
  simp

structure Forward (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (counts : List (Fin bound)) where
  next : BooleanDAGBuilder (descriptionWidth R bound)
  extension : BooleanDAGExtension b next
  refs : List ℕ
  spine : RecoveryBoundedCounts.Spine (compactProjectionPCP (p.normalized R Q hr hq)) x b counts next refs
  refs_length : refs.length=counts.length
  refs_bound : ∀ ref∈refs,ref≤z.base.W
  next_bound : next.nodes.length≤z.base.G

noncomputable def Forward.prepend (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (hk : k<bound)
    (f : Forward z (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b ⟨k,hk⟩).final
      ((List.finRange bound).drop (k+1)))
    (hg : (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b ⟨k,hk⟩).final.nodes.length≤z.base.G) :
    Forward z b ((List.finRange bound).drop k) := by
  let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b ⟨k,hk⟩
  refine {
    next:=f.next
    extension:=original.extension.trans f.extension
    refs:=original.output.val::f.refs
    spine:=?_
    refs_length:=?_
    refs_bound:=?_
    next_bound:=f.next_bound}
  · rw [counts_cons k hk]
    exact RecoveryBoundedCounts.Spine.cons (pcp:=compactProjectionPCP (p.normalized R Q hr hq)) (x:=x)
      b ⟨k,hk⟩ ((List.finRange bound).drop (k+1)) f.next f.refs f.spine
  · rw [counts_cons k hk,List.length_cons,List.length_cons,f.refs_length]
  · intro ref href
    rcases List.mem_cons.mp href with he|he
    · exact he ▸ original.output.isLt.le.trans (hg.trans z.base.graph_bound)
    · exact f.refs_bound ref he

private theorem saved_room (stack : List Bool) (ref W remaining extra S : ℕ)
    (href : ref≤W) (hs : stack.length+(remaining+1+extra)*(2*W+1)≤S) :
    (RecoveryBoundedAddress.pushed ref stack).length+(remaining+extra)*(2*W+1)≤S := by
  have hp : (RecoveryBoundedAddress.pushed ref stack).length ≤ stack.length+(2*W+1) := by
    simp only [RecoveryBoundedAddress.pushed,List.length_append,List.length_reverse,frame_length,List.length_replicate]
    omega
  calc
    _ ≤ (stack.length+(2*W+1))+(remaining+extra)*(2*W+1) := Nat.add_le_add_right hp _
    _ = stack.length+(remaining+1+extra)*(2*W+1) := by ring
    _ ≤ S := hs

namespace Driver
variable {s : ℕ}
noncomputable def machine (worker : Machine 152 s):=RepeatMachine.machine worker (fun _ _=>true)
noncomputable def configuration (worker : Machine 152 s) (phase : Fin 5)
    (z : Resources p R Q hr hq (bound:=bound) x)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool)
    (extra : Fin 12→List Bool) (driver : ℕ):=
  RepeatMachine.cfg phase (⟨worker.start,z.heads b stack,z.bank b k stack extra⟩ : Configuration 152 s) bound driver

private theorem followed {t s : ℕ} (m : Machine t s) (u v : ℕ) (c d : Configuration t s)
    (h : Timed m u c d) (last : ExecutionReceipt t s) (hr : runFrom m v d=some last) :
    ∃ r,runFrom m (u+v) c=some r ∧ r.final=last.final ∧ r.steps=u+last.steps := by
  rcases h with ⟨space,hprefix⟩
  obtain ⟨r,rr,rf,rs,_⟩:=hprefix.followedBy last hr
  exact ⟨r,rr,rf,rs⟩

theorem forward_run (worker : Machine 152 s) (z : Resources p R Q hr hq (bound:=bound) x)
    (extra : Fin 12→List Bool)
    (supplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (count : Fin bound) (stack : List Bool),
      stack.length+z.base.W*(2*z.base.W+1)≤z.base.S →
      (compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count).final.nodes.length≤z.base.G →
      stack.length+(2^R+1)*(2*z.base.W+1)≤z.P →
      let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
      let saved:=RecoveryBoundedAddress.pushed original.output.val stack
      ∃ r,runFrom worker (bodyBudget z.base.B z.base.W R)
        ⟨worker.start,z.heads b stack,z.bank b count.val stack extra⟩=some r ∧
        r.steps≤bodyBudget z.base.B z.base.W R ∧ r.final.heads=z.heads original.final saved ∧
        r.final.tapes=z.bank original.final (count.val+1) saved extra)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (remaining k : ℕ) (stack : List Bool)
    (hk : k+remaining=bound)
    (hS : stack.length+(remaining+z.base.W)*(2*z.base.W+1)≤z.base.S)
    (hP : stack.length+(remaining+2^R+1)*(2*z.base.W+1)≤z.P)
    (hFinal : (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b
      ((List.finRange bound).drop k)).final.nodes.length≤z.base.G) :
    ∃ f : Forward z b ((List.finRange bound).drop k), ∃ r,
      runFrom (machine worker) (remaining*(bodyBudget z.base.B z.base.W R+2)+bound+3)
        (configuration worker 0 z b k stack extra (k+1))=some r ∧
      r.final=configuration worker 3 z f.next bound (stack++stackWord f.refs) extra 1 ∧
      r.steps≤remaining*(bodyBudget z.base.B z.base.W R+2)+bound+3 := by
  induction remaining generalizing b k stack with
  | zero=>
    have he : k=bound:=by omega
    have hn : (List.finRange bound).drop k=[]:=by simp [he]
    have hb : b.nodes.length≤z.base.G:=
      (compileCountCases (compactProjectionPCP (p.normalized R Q hr hq)) x b _).extension.length_le.trans hFinal
    let f : Forward z b ((List.finRange bound).drop k):={
      next:=b,extension:=BooleanDAGExtension.refl b,refs:=[],spine:=by
        rw [hn]
        exact RecoveryBoundedCounts.Spine.nil _
      refs_length:=by rw [hn]
                      rfl
      refs_bound:=by simp,next_bound:=hb}
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust worker (fun _ _=>true)
      (⟨worker.start,z.heads b stack,z.bank b k stack extra⟩ : Configuration 152 _) bound).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨f,r,?_,?_,?_⟩
    · simpa only [machine,configuration,he,Nat.zero_mul,Nat.zero_add] using rr
    · simpa only [configuration,f,stackWord,List.flatMap_nil,List.append_nil,he] using rf
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
  | succ remaining ih=>
    have hlt : k<bound:=by omega
    rw [counts_cons k hlt] at hFinal
    let count : Fin bound:=⟨k,hlt⟩
    let original:=compileFixedCount (compactProjectionPCP (p.normalized R Q hr hq)) x b count
    let saved:=RecoveryBoundedAddress.pushed original.output.val stack
    have hg : original.final.nodes.length≤z.base.G:=RecoveryBoundedCounts.head_bound
      (compactProjectionPCP (p.normalized R Q hr hq)) x b count ((List.finRange bound).drop (k+1)) z.base.G hFinal
    have hrowS : stack.length+z.base.W*(2*z.base.W+1)≤z.base.S := by
      have hm:=Nat.mul_le_mul_right (2*z.base.W+1) (Nat.le_add_left z.base.W (remaining+1))
      omega
    have hrowP : stack.length+(2^R+1)*(2*z.base.W+1)≤z.P := by
      have hm:=Nat.mul_le_mul_right (2*z.base.W+1) (Nat.le_add_left (2^R+1) (remaining+1))
      rw [←Nat.add_assoc] at hm
      omega
    obtain ⟨first,fr,fs,fh,ft⟩:=supplier b count stack hrowS hg hrowP
    change first.final.heads=z.heads original.final saved at fh
    change first.final.tapes=z.bank original.final (k+1) saved extra at ft
    have step:=RepeatMachine.iteration worker (fun _ _=>true)
      (⟨worker.start,z.heads b stack,z.bank b k stack extra⟩ : Configuration 152 _) bound k first rfl hlt fr
    change Timed (machine worker) (first.steps+2) (configuration worker 0 z b k stack extra (k+1))
      (RepeatMachine.cfg 0 first.final bound (k+2)) at step
    have hm : RepeatMachine.cfg 0 first.final bound (k+2)=
        configuration worker 0 z original.final (k+1) saved extra (k+1+1) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,configuration,controlConfig,TapeEmbedding.config,fh]
      · simp only [RepeatMachine.cfg,configuration,controlConfig,TapeEmbedding.config,ft]
    rw [hm] at step
    have href : original.output.val≤z.base.W:=original.output.isLt.le.trans (hg.trans z.base.graph_bound)
    have hS':=saved_room stack original.output.val z.base.W remaining z.base.W z.base.S href hS
    have hP':=saved_room stack original.output.val z.base.W remaining (2^R+1) z.P href
      (by simpa only [Nat.add_assoc] using hP)
    simp only [←Nat.add_assoc] at hP'
    obtain ⟨f,last,lr,lf,ls⟩:=ih original.final (k+1) saved (by omega) hS' hP'
      (RecoveryBoundedCounts.tail_bound (compactProjectionPCP (p.normalized R Q hr hq)) x b count
        ((List.finRange bound).drop (k+1)) z.base.G hFinal)
    obtain ⟨r,rr,rf,rs⟩:=followed (machine worker) (first.steps+2)
      (remaining*(bodyBudget z.base.B z.base.W R+2)+bound+3) _ _ step last lr
    have hb : first.steps+2+(remaining*(bodyBudget z.base.B z.base.W R+2)+bound+3)≤
        (remaining+1)*(bodyBudget z.base.B z.base.W R+2)+bound+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel (machine worker) _
      ((remaining+1)*(bodyBudget z.base.B z.base.W R+2)+bound+3-
        (first.steps+2+(remaining*(bodyBudget z.base.B z.base.W R+2)+bound+3))) _ r rr
    rw [Nat.add_sub_of_le hb] at more
    let finished:=Forward.prepend z b k hlt f hg
    refine ⟨finished,r,more,?_,?_⟩
    · rw [rf,lf]
      simp only [finished,Forward.prepend,saved,original,count,RecoveryBoundedAddress.pushed,stackWord,List.flatMap_cons,List.append_assoc]
    · rw [rs]
      omega

end Driver

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountUniform
