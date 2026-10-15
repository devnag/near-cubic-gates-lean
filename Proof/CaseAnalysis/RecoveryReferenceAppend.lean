import Proof.CaseAnalysis.RecoveryReferenceRead

/-! One complete original-selector head starts by consuming its live wire
reference from the actual framed stream, then emits the unary guard and AND.
The stream cursor advances once; the previous native graph is appended to. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceAppend
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open FinitePredicateCircuit BoundedOracleStructuralCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots : Fin 3→Fin 39:=![37,36,38]
def appendSlots (j : Fin 37) : Fin 39:=j.castAdd 2
def caps (C : ℕ) (j : Fin 37) : ℕ:=if j=36 then C else 0
noncomputable def first:=RecoveryFocus.machine readSlots RecoveryBoundedReferenceRead.machine
noncomputable def last:=RecoveryFocus.machine appendSlots RecoveryBoundedNativeGuarded.machine
noncomputable def machine:=Composition.machine first last
def budget (ref limit C : ℕ):=(4*ref+4)+1+RecoveryBoundedNativeGuarded.budget limit C
noncomputable def bank {n bound : ℕ} (row : Fin (bound+1))
    (start base C value limit ref : ℕ) (out pre : List Bool) :=
  ZeroPadding.config (caps C)
    (RecoveryBoundedNativeGuarded.entry (n:=n) row start base C value limit ref out pre)
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1))
    (start base C value limit ref : ℕ) (out pre skipped tail : List Bool) :=
  restart (TapeEmbedding.config (![skipped.length,0] : Fin 2→ℕ)
    ![skipped++frame (List.replicate ref true)++tail,List.replicate C false]
    (bank (n:=n) row start base C value limit 0 out pre)) machine.start

noncomputable def completeState {n bound : ℕ}
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (row : Fin (bound+1))
    (start limit value C ref : ℕ) (out pre skipped tail : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  TapeEmbedding.config (![skipped.length+2*ref+1,0] : Fin 2→ℕ)
    ![skipped++frame (List.replicate ref true)++tail,List.replicate C false]
    (ZeroPadding.config (caps C)
      (RecoveryBoundedNativeGuarded.completeState b row start limit value C ref out pre hblock))

theorem append_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C : ℕ) (out pre skipped tail : List Bool)
    (wire : LiveWire b) (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (budget wire.output.val limit C)
      (entry (n:=n) row start b.nodes.length C value limit wire.output.val out pre skipped tail)=some r ∧
      r.steps ≤ budget wire.output.val limit C ∧
      r.final.heads 37=skipped.length+2*wire.output.val+1 ∧
      r.final.tapes 37=skipped++frame (List.replicate wire.output.val true)++tail ∧
      r.final.tapes 20=out++
        ((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
          PCPPRequestNodeSchema.native++
        PCPPRequestNodeSchema.native (n:=descriptionWidth n bound) (BooleanNode.and
          (compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val wire.output.val) ∧
      r.final.heads 20=(r.final.tapes 20).length ∧
      r.final.heads=(completeState b row start limit value C wire.output.val out pre skipped tail hblock).heads ∧
      r.final.tapes=(completeState b row start limit value C wire.output.val out pre skipped tail hblock).tapes := by
  let before:=entry (n:=n) row start b.nodes.length C value limit wire.output.val out pre skipped tail
  let after:=bank (n:=n) row start b.nodes.length C value limit wire.output.val out pre
  have href : wire.output.val ≤ W := by have h:=wire.output.isLt; omega
  have small : 2*wire.output.val+1 ≤ C := by nlinarith [Nat.zero_le (W*W)]
  obtain ⟨rd,hrd,rdh,rdt,rds⟩:=RecoveryBoundedReferenceRead.read_run skipped tail wire.output.val C small
  obtain ⟨a,ha,_ac,ast,ah,ad,ak⟩:=RecoveryFocus.dock readSlots (by decide)
    RecoveryBoundedReferenceRead.machine _ before.heads before.tapes
    (RecoveryBoundedReferenceRead.entry skipped tail wire.output.val C)
    (by intro j; fin_cases j <;> rfl)
    (by
      intro j
      fin_cases j
      · exact (ZeroPadding.pad_zero _).symm
      · rfl
      · rfl) rd hrd
  obtain ⟨wr,hwr,wrs,wrt,wrh,wrhFull,wrtFull⟩:=RecoveryBoundedNativeGuarded.append_run
    b row start limit value W C out pre wire hblock hi hp hC
  obtain ⟨pd,hpd,pf,ps,_pp⟩:=ZeroPadding.run_config RecoveryBoundedNativeGuarded.machine (caps C) _ _ wr hwr
  have ahead (j : Fin 37) : a.final.heads (appendSlots j)=after.heads j := by
    by_cases hj : j=36
    · subst j
      have h:=ah 1
      rw [rdh] at h
      exact h
    · have away : ∀ i,readSlots i≠appendSlots j := by
        intro i he
        have hv:=congrArg Fin.val he
        have hbound:=j.isLt
        have hn : j.val≠36:=fun h=>hj (Fin.ext h)
        fin_cases i <;> dsimp [readSlots,appendSlots] at hv <;> omega
      rw [(ak _ away).1]
      simp only [before,entry,restart,TapeEmbedding.config,appendSlots,Fin.addCases_left,
        after,bank,ZeroPadding.config,RecoveryBoundedNativeGuarded.entry]
  have adata (j : Fin 37) : a.final.tapes (appendSlots j)=after.tapes j := by
    by_cases hj : j=36
    · subst j
      have h:=ad 1
      rw [rdt] at h
      exact h
    · have away : ∀ i,readSlots i≠appendSlots j := by
        intro i he
        have hv:=congrArg Fin.val he
        have hbound:=j.isLt
        have hn : j.val≠36:=fun h=>hj (Fin.ext h)
        fin_cases i <;> dsimp [readSlots,appendSlots] at hv <;> omega
      rw [(ak _ away).2]
      have hn : j.val<36 := by
        have hbound:=j.isLt
        have ne : j.val≠36:=fun h=>hj (Fin.ext h)
        omega
      let k : Fin 36:=⟨j.val,hn⟩
      have je : j=k.castAdd 1 := Fin.ext rfl
      rw [je]
      simp only [before,entry,restart,appendSlots,TapeEmbedding.config,Fin.addCases_left,
        after,bank,ZeroPadding.config]
      change ZeroPadding.pad (caps C (k.castAdd 1))
        ((RecoveryBoundedNativeGuarded.entry (n:=n) row start b.nodes.length C value limit 0 out pre).tapes (k.castAdd 1))=
          ZeroPadding.pad (caps C (k.castAdd 1))
        ((RecoveryBoundedNativeGuarded.entry (n:=n) row start b.nodes.length C value limit wire.output.val out pre).tapes (k.castAdd 1))
      simp only [RecoveryBoundedNativeGuarded.entry,restart,TapeEmbedding.config,Fin.addCases_left]
  obtain ⟨z,hz,_zc,zs,zh,zt,zk⟩:=RecoveryFocus.dock appendSlots
    (by intro i j h; have hv:=congrArg Fin.val h; exact Fin.ext hv) RecoveryBoundedNativeGuarded.machine _
    a.final.heads a.final.tapes after ahead adata pd hpd
  have full:=Composition.run_join first last _ _ _ a z ha hz
  refine ⟨joinedReceipt a z,full,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+z.steps ≤ budget wire.output.val limit C
    rw [ast,rds,zs,ps]
    unfold budget
    omega
  · change z.final.heads 37=_
    rw [(zk 37 (by intro j he; have h:=congrArg Fin.val he; have hj:=j.isLt; dsimp [appendSlots] at h; omega)).1]
    have h:=ah 0
    rw [rdh] at h
    exact h
  · change z.final.tapes 37=_
    rw [(zk 37 (by intro j he; have h:=congrArg Fin.val he; have hj:=j.isLt; dsimp [appendSlots] at h; omega)).2]
    have h:=ad 0
    rw [rdt] at h
    exact h
  · change z.final.tapes 20=_
    have h:=zt 20
    rw [pf] at h
    change z.final.tapes 20=ZeroPadding.pad 0 (wr.final.tapes 20) at h
    rw [ZeroPadding.pad_zero,wrt] at h
    exact h
  · change z.final.heads 20=(z.final.tapes 20).length
    have h:=zh 20
    have t:=zt 20
    rw [pf] at h t
    change z.final.heads 20=wr.final.heads 20 at h
    change z.final.tapes 20=ZeroPadding.pad 0 (wr.final.tapes 20) at t
    rw [ZeroPadding.pad_zero] at t
    rw [t]
    exact h.trans wrh
  · change z.final.heads=_
    funext i
    refine Fin.addCases (m:=37) (n:=2) (motive:=fun i=>z.final.heads i=
      (completeState b row start limit value C wire.output.val out pre skipped tail hblock).heads i) ?_ ?_ i
    · intro j
      have h:=zh j
      rw [pf] at h
      change z.final.heads (j.castAdd 2)=wr.final.heads j at h
      rw [wrhFull] at h
      simpa only [completeState,TapeEmbedding.config,Fin.addCases_left,ZeroPadding.config] using h
    · intro j
      have away : ∀ k,appendSlots k≠j.natAdd 37 := by
        intro k he
        have hv:=congrArg Fin.val he
        have hk:=k.isLt
        dsimp only [appendSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
      rw [(zk _ away).1]
      fin_cases j
      · have h:=ah 0
        rw [rdh] at h
        exact h
      · have h:=ah 2
        rw [rdh] at h
        exact h
  · change z.final.tapes=_
    funext i
    refine Fin.addCases (m:=37) (n:=2) (motive:=fun i=>z.final.tapes i=
      (completeState b row start limit value C wire.output.val out pre skipped tail hblock).tapes i) ?_ ?_ i
    · intro j
      have h:=zt j
      rw [pf] at h
      change z.final.tapes (j.castAdd 2)=ZeroPadding.pad (caps C j) (wr.final.tapes j) at h
      rw [wrtFull] at h
      simpa only [completeState,TapeEmbedding.config,Fin.addCases_left,ZeroPadding.config] using h
    · intro j
      have away : ∀ k,appendSlots k≠j.natAdd 37 := by
        intro k he
        have hv:=congrArg Fin.val he
        have hk:=k.isLt
        dsimp only [appendSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
      rw [(zk _ away).2]
      fin_cases j
      · have h:=ad 0
        rw [rdt] at h
        exact h
      · have h:=ad 2
        rw [rdt] at h
        exact h

end NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceAppend
