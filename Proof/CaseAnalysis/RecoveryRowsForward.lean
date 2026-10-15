import Proof.CaseAnalysis.RecoveryRowsPrepared

/-! The original finite nonterminal randomness driver. Its result retains
the exact original builder and the physically saved references, ready for
the terminal row and the already checked reverse AND fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape SourceInterfaces RepairSource CanonicalRecoveryLanguage RecoveryExecution
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedClauseList (stackWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {p : RawProjectionPCP} {R Q : ℕ} {hr : p.width≤R} {hq : p.queries≤Q}
variable {n bound : ℕ} {x : BitInput n} {count : ℕ} {hc : count≤bound}

private theorem followed {t s : ℕ} (m : Machine t s) (u v : ℕ) (c d : Configuration t s)
    (h : Timed m u c d) (last : ExecutionReceipt t s) (hr : runFrom m v d=some last) :
    ∃ r,runFrom m (u+v) c=some r ∧ r.final=last.final ∧ r.steps=u+last.steps := by
  rcases h with ⟨space,hprefix⟩
  obtain ⟨r,rr,rf,rs,_⟩:=hprefix.followedBy last hr
  exact ⟨r,rr,rf,rs⟩

theorem Resources.body_original (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool) (hk : k+1<2^R)
    (hg : (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)).compiled.final.nodes.length≤z.G) :
    let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
    let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
    ∃ r,runFrom bodyMachine (bodyBudget z.B)
      ⟨bodyMachine.start,z.heads b stack,z.bank b k stack⟩=some r ∧ r.steps≤bodyBudget z.B ∧
      r.final.heads=z.heads row.compiled.final saved ∧ r.final.tapes=z.bank row.compiled.final (k+1) saved := by
  obtain ⟨a,ar,as,ah,aT⟩:=z.finish_original b k stack hg
  have hWB : z.W≤z.B := by
    have h:=z.backing_capacity
    unfold RecoveryBoundedSelectorLoop.capacity at h
    nlinarith only [h,Nat.zero_le (z.W^2)]
  exact body_run p R Q k z.B hk (z.native_bound.trans hWB) (z.heads b stack) (z.bank b k stack)
    _ _ a ar as ah aT

structure Forward (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (rows : List (BitInput R)) where
  next : BooleanDAGBuilder (descriptionWidth R bound)
  extension : BooleanDAGExtension b next
  refs : List ℕ
  spine : Spine (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b rows next refs
  refs_length : refs.length=rows.length
  refs_bound : ∀ ref∈refs,ref≤z.W
  next_bound : next.nodes.length≤z.G

namespace Driver
variable {s : ℕ}
noncomputable def machine (worker : Machine 115 s):=RepeatMachine.machine worker (fun _ _=>true)
noncomputable def configuration (worker : Machine 115 s) (phase : Fin 5) (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool) (total driver : ℕ):=
  RepeatMachine.cfg phase (⟨worker.start,z.heads b stack,z.bank b k stack⟩ : Configuration 115 s) total driver

theorem forward_run (worker : Machine 115 s) (z : Resources p R Q hr hq x count hc)
    (supplier : ∀ (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool), k+1<2^R →
      (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)).compiled.final.nodes.length≤z.G →
      let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
      let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
      ∃ r,runFrom worker (bodyBudget z.B) ⟨worker.start,z.heads b stack,z.bank b k stack⟩=some r ∧
        r.steps≤bodyBudget z.B ∧ r.final.heads=z.heads row.compiled.final saved ∧
        r.final.tapes=z.bank row.compiled.final (k+1) saved)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (remaining k : ℕ) (rest : List (BitInput R))
    (stack : List Bool) (total pos : ℕ) (hpos : pos+remaining=total) (hk : k+remaining<2^R)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R k remaining++rest)).final.nodes.length≤z.G) :
    ∃ f : Forward z b (randomnesses R k remaining), ∃ r,
      runFrom (machine worker) (remaining*(bodyBudget z.B+2)+total+3)
        (configuration worker 0 z b k stack total (pos+1))=some r ∧
      r.final=configuration worker 3 z f.next (k+remaining) (stack++stackWord f.refs) total 1 ∧
      r.steps≤remaining*(bodyBudget z.B+2)+total+3 := by
  induction remaining generalizing b k stack pos with
  | zero=>
    have hoff : pos=total:=by omega
    have hb : b.nodes.length≤z.G:=
      (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b _).extension.length_le.trans hFinal
    let f : Forward z b (randomnesses R k 0):={
      next:=b,extension:=BooleanDAGExtension.refl b,refs:=[],spine:=by
        simp only [randomnesses,List.range'_zero,List.map_nil]
        exact Spine.nil (pcp:=compactProjectionPCP (p.normalized R Q hr hq)) (x:=x) (count:=count) (hc:=hc) b
      refs_length:=by simp only [randomnesses,List.range'_zero,List.map_nil];rfl
      refs_bound:=by simp,next_bound:=hb }
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust worker (fun _ _=>true)
      (⟨worker.start,z.heads b stack,z.bank b k stack⟩ : Configuration 115 _) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨f,r,?_,?_,?_⟩
    · simpa only [machine,configuration,hoff,Nat.zero_mul,Nat.zero_add] using rr
    · simpa only [configuration,f,stackWord,List.flatMap_nil,List.append_nil,Nat.add_zero] using rf
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
  | succ remaining ih=>
    rw [randomnesses_cons,List.cons_append] at hFinal
    let row:=compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc (bitInputOfCode R k)
    let saved:=RecoveryBoundedClauseCollect.pushed row.compiled.output.val stack
    have hg : row.compiled.final.nodes.length≤z.G:=head_bound
      (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (bitInputOfCode R k)
      (randomnesses R (k+1) remaining++rest) z.G hFinal
    obtain ⟨first,fr,fs,fh,ft⟩:=supplier b k stack (by omega) hg
    change first.final.heads=z.heads row.compiled.final saved at fh
    change first.final.tapes=z.bank row.compiled.final (k+1) saved at ft
    have step:=RepeatMachine.iteration worker (fun _ _=>true)
      (⟨worker.start,z.heads b stack,z.bank b k stack⟩ : Configuration 115 _) total pos first rfl (by omega) fr
    change Timed (machine worker) (first.steps+2) (configuration worker 0 z b k stack total (pos+1))
      (RepeatMachine.cfg 0 first.final total (pos+2)) at step
    have hm : RepeatMachine.cfg 0 first.final total (pos+2)=
        configuration worker 0 z row.compiled.final (k+1) saved total (pos+1+1) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,configuration,controlConfig,TapeEmbedding.config,fh]
      · simp only [RepeatMachine.cfg,configuration,controlConfig,TapeEmbedding.config,ft]
    rw [hm] at step
    obtain ⟨f,last,lr,lf,ls⟩:=ih row.compiled.final (k+1) saved (pos+1) (by omega) (by omega)
      (tail_bound (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b (bitInputOfCode R k)
        (randomnesses R (k+1) remaining++rest) z.G hFinal)
    obtain ⟨r,rr,rf,rs⟩:=followed (machine worker) (first.steps+2)
      (remaining*(bodyBudget z.B+2)+total+3) _ _ step last lr
    have hb : first.steps+2+(remaining*(bodyBudget z.B+2)+total+3)≤
        (remaining+1)*(bodyBudget z.B+2)+total+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel (machine worker) _
      ((remaining+1)*(bodyBudget z.B+2)+total+3-(first.steps+2+(remaining*(bodyBudget z.B+2)+total+3))) _ r rr
    rw [Nat.add_sub_of_le hb] at more
    let finished : Forward z b (randomnesses R k (remaining+1)):={
      next:=f.next,extension:=row.compiled.extension.trans f.extension,refs:=row.compiled.output.val::f.refs
      spine:=by
        rw [randomnesses_cons]
        exact Spine.cons (pcp:=compactProjectionPCP (p.normalized R Q hr hq)) (x:=x) (count:=count) (hc:=hc)
          b (bitInputOfCode R k) (randomnesses R (k+1) remaining) f.next f.refs f.spine
      refs_length:=by rw [randomnesses_cons,List.length_cons,List.length_cons,f.refs_length]
      refs_bound:=by
        intro ref href
        rcases List.mem_cons.mp href with he|he
        · exact he ▸ row.compiled.output.isLt.le.trans (hg.trans z.graph_bound)
        · exact f.refs_bound ref he
      next_bound:=f.next_bound }
    refine ⟨finished,r,more,?_,?_⟩
    · rw [rf,lf]
      simp only [finished,saved,RecoveryBoundedClauseCollect.pushed,stackWord,List.flatMap_cons,List.append_assoc,
        Nat.add_assoc,Nat.add_comm 1 remaining]
    · rw [rs]
      omega

end Driver

noncomputable def forwardMachine:=Driver.machine bodyMachine
noncomputable def configuration (phase : Fin 5) (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (k : ℕ) (stack : List Bool) (total driver : ℕ):=
  Driver.configuration bodyMachine phase z b k stack total driver

theorem forward_run (z : Resources p R Q hr hq x count hc)
    (b : BooleanDAGBuilder (descriptionWidth R bound)) (remaining k : ℕ) (rest : List (BitInput R))
    (stack : List Bool) (total pos : ℕ) (hpos : pos+remaining=total) (hk : k+remaining<2^R)
    (hFinal : (compileVerifierRows (compactProjectionPCP (p.normalized R Q hr hq)) x count hc b
      (randomnesses R k remaining++rest)).final.nodes.length≤z.G) :
    ∃ f : Forward z b (randomnesses R k remaining), ∃ r,
      runFrom forwardMachine (remaining*(bodyBudget z.B+2)+total+3)
        (configuration 0 z b k stack total (pos+1))=some r ∧
      r.final=configuration 3 z f.next (k+remaining) (stack++stackWord f.refs) total 1 ∧
      r.steps≤remaining*(bodyBudget z.B+2)+total+3 := by
  exact Driver.forward_run bodyMachine z z.body_original b remaining k rest stack total pos hpos hk hFinal

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
