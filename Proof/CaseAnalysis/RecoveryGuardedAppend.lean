import Proof.CaseAnalysis.RecoveryUnaryComplete
import Proof.Amplification.RecoveryBoundedUniversalSchedule

/-! The original guarded selector emits its unary condition and then the
AND with the retained described-node reference, on the same physical bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeGuarded
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open FinitePredicateCircuit BoundedOracleStructuralCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 29) : Fin 37 := if j=1 then 36 else j.castAdd 8
theorem slots_injective : Function.Injective slots := by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> have hi:=i.isLt <;> have hj:=j.isLt <;> omega
noncomputable def first:=TapeEmbedding.machine 1 RecoveryBoundedNativeUnaryJoin.machine
noncomputable def last:=RecoveryFocus.machine slots (PCPPNativeClauseBank.nodeMachine 3 0 3 0 1)
noncomputable def machine:=Composition.machine first last
def budget (limit C : ℕ):=RecoveryBoundedNativeUnaryJoin.budget limit C+1+(8*C+20)
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1))
    (start base C value limit reference : ℕ) (out pre : List Bool) :=
  restart (TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate reference true)
    (RecoveryBoundedNativeUnaryJoin.entry (n:=n) row start base C value limit out pre)) machine.start

noncomputable def completeState {n bound : ℕ}
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (row : Fin (bound+1))
    (start limit value C reference : ℕ) (out pre : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  let before:=TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate reference true)
    (RecoveryBoundedNativeUnaryJoin.completeState row start b.nodes.length C value limit out pre hblock)
  let bits:=((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
    PCPPRequestNodeSchema.native
  let acc:=b.nodes.length+prefixCount (unaryItems row start limit value hblock)+limit
  let vals:=RecoveryBoundedNativeFold.values reference acc
  RecoveryFocus.config slots before.heads before.tapes
    (PCPPNativeClauseBank.entry (PCPPNativeClauseBank.nodeMachine 3 0 3 0 1) vals C
      (out++bits++PCPPNativeClauseBank.nodeBits 3 0 3 0 1 vals))

theorem append_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C : ℕ) (out pre : List Bool)
    (wire : LiveWire b) (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (budget limit C)
      (entry (n:=n) row start b.nodes.length C value limit wire.output.val out pre)=some r ∧
      r.steps ≤ budget limit C ∧
      r.final.tapes 20=out++
        ((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
          PCPPRequestNodeSchema.native++
        PCPPRequestNodeSchema.native (n:=descriptionWidth n bound) (BooleanNode.and
          (compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val wire.output.val) ∧
      r.final.heads 20=(r.final.tapes 20).length ∧
      r.final.heads=(completeState b row start limit value C wire.output.val out pre hblock).heads ∧
      r.final.tapes=(completeState b row start limit value C wire.output.val out pre hblock).tapes := by
  let bits:=((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
    PCPPRequestNodeSchema.native
  let acc:=b.nodes.length+prefixCount (unaryItems row start limit value hblock)+limit
  let vals:=RecoveryBoundedNativeFold.values wire.output.val acc
  have ha : acc ≤ W := by
    have h:=prefixCount_bound (unaryItems row start limit value hblock)
    have hlen : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
    rw [hlen] at h
    dsimp only [acc]
    omega
  have href : wire.output.val ≤ W := by have h:=wire.output.isLt; omega
  have cap1:=PCPPNativeClauseCapacity.sum_capacity 0 acc W C (by omega) hC
  have cap2:=PCPPNativeClauseCapacity.sum_capacity 0 wire.output.val W C (by omega) hC
  obtain ⟨u,hu,us,_uo,_ua,_uh,_uv,_ug,ub,_ustate,_uvalue⟩:=RecoveryBoundedNativeUnaryJoin.original_run
    b row start limit value W C out pre hblock hi hp hC
  obtain ⟨u',hu',_us',uhFull,utFull⟩:=RecoveryBoundedNativeUnaryJoin.complete_run
    b row start limit value W C out pre hblock hi hp hC
  have same : u'=u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  let a:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>List.replicate wire.output.val true) u
  have ar:=TapeEmbedding.run_embed RecoveryBoundedNativeUnaryJoin.machine
    (fun _ : Fin 1=>0) (fun _=>List.replicate wire.output.val true) _ _ u hu
  obtain ⟨v,hv,vs,vh,vt⟩:=PCPPNativeClauseBank.node_run 3 0 3 0 1 (by decide) (by decide)
    vals C (out++bits) cap1 cap2
  have vbound : PCPPNativeClauseBank.nodeBudget 3 0 3 0 1 vals C ≤ 8*C+20 := by
    have h3 : (natWord 3).length=5 := by decide
    unfold PCPPNativeClauseBank.nodeBudget PCPPNativeSumReusable.budget
    change (natWord 3).length+1+(2*PCPPNativeSumAppend.budget 0 acc+2*C+7)+1+
      (2*PCPPNativeSumAppend.budget 0 wire.output.val+2*C+7) ≤ _
    rw [h3]
    omega
  have more:=runFrom_moreFuel (PCPPNativeClauseBank.nodeMachine 3 0 3 0 1) _
    (8*C+20-PCPPNativeClauseBank.nodeBudget 3 0 3 0 1 vals C) _ v hv
  rw [Nat.add_sub_of_le vbound] at more
  have ah (j : Fin 29) : a.final.heads (slots j)=PCPPNativeClauseBank.heads (out++bits) j := by
    by_cases hj : j=1
    · subst j
      exact TapeEmbedding.receipt_heads_new _ _ _ 0
    · rw [slots,if_neg hj]
      exact (TapeEmbedding.receipt_heads_old _ _ _ (j.castAdd 7)).trans (ub j).1
  have adata (j : Fin 29) : a.final.tapes (slots j)=PCPPNativeClauseBank.data vals C (out++bits) j := by
    by_cases hj : j=1
    · subst j
      exact TapeEmbedding.receipt_tapes_new _ _ _ 0
    · rw [slots,if_neg hj]
      have h:=(TapeEmbedding.receipt_tapes_old (fun _ : Fin 1=>0)
        (fun _=>List.replicate wire.output.val true) u (j.castAdd 7)).trans (ub j).2
      apply h.trans
      change RecoveryBoundedNativeFold.oldData 0 acc C (out++bits) j=_
      rw [RecoveryBoundedNativeFold.oldData,if_neg hj]
      fin_cases j
      all_goals first | exact False.elim (hj rfl) | rfl
  obtain ⟨z,hz,_zc,zs,zh,zt,zk⟩:=RecoveryFocus.dock slots slots_injective
    (PCPPNativeClauseBank.nodeMachine 3 0 3 0 1) (8*C+20) a.final.heads a.final.tapes
    (PCPPNativeClauseBank.entry _ vals C (out++bits)) ah adata v more
  have joined:=Composition.run_join first last _ _ _ a z ar hz
  refine ⟨joinedReceipt a z,joined,?_,?_,?_,?_,?_⟩
  · change u.steps+1+z.steps ≤ budget limit C
    rw [zs]
    unfold budget
    omega
  · change z.final.tapes 20=_
    have output:=(zt 20).trans (congrFun vt 20)
    change z.final.tapes 20=out++bits++PCPPNativeClauseBank.nodeBits 3 0 3 0 1 vals at output
    rw [output]
    have hindex : (compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val=acc := by
      rw [compileExpr_output,unary_expression,all_nodeCount]
      have hlen : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
      rw [hlen]
      dsimp only [acc]
      omega
    rw [hindex]
    congr 1
    simp [PCPPNativeClauseBank.nodeBits,vals,RecoveryBoundedNativeFold.values,
      PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]
  · change z.final.heads 20=(z.final.tapes 20).length
    have h:=(zh 20).trans (congrFun vh 20)
    have t:=(zt 20).trans (congrFun vt 20)
    change z.final.heads 20=(out++bits++PCPPNativeClauseBank.nodeBits 3 0 3 0 1 vals).length at h
    change z.final.tapes 20=out++bits++PCPPNativeClauseBank.nodeBits 3 0 3 0 1 vals at t
    rw [t]
    exact h
  · change z.final.heads=_
    funext i
    cases hpick : RecoveryFocus.pick slots i with
    | some j=>
      have he:=RecoveryFocus.slot_of_pick slots hpick
      rw [←he]
      simp only [completeState,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact (zh j).trans (congrFun vh j)
    | none=>
      have away : ∀ j,slots j≠i := by
        intro j he
        have h:=RecoveryFocus.pick_slot slots slots_injective j
        rw [he,hpick] at h
        contradiction
      rw [(zk i away).1]
      simp only [completeState,RecoveryFocus.config,hpick]
      change (Fin.addCases (m:=36) (n:=1) (motive:=fun _=>ℕ) u.final.heads (fun _=>0)) i=_
      rw [uhFull]
      rfl
  · change z.final.tapes=_
    funext i
    cases hpick : RecoveryFocus.pick slots i with
    | some j=>
      have he:=RecoveryFocus.slot_of_pick slots hpick
      rw [←he]
      simp only [completeState,RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
      exact (zt j).trans (congrFun vt j)
    | none=>
      have away : ∀ j,slots j≠i := by
        intro j he
        have h:=RecoveryFocus.pick_slot slots slots_injective j
        rw [he,hpick] at h
        contradiction
      rw [(zk i away).2]
      simp only [completeState,RecoveryFocus.config,hpick]
      change (Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool) u.final.tapes
        (fun _=>List.replicate wire.output.val true)) i=_
      rw [utFull]
      rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeGuarded
