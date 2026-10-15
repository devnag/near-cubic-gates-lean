import Proof.Amplification.RecoveryTseitinNativeArgs

/-! Execute the original native reader and both operand conversions. The
result is exactly the cold reference producer's actual unary input bank. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def referenceSlots (i : Fin 1062) : Fin 1099 := i.castAdd 37
theorem reference_injective : Function.Injective referenceSlots := by
  intro i j he
  have h:=congrArg Fin.val he
  exact Fin.ext h
theorem arg_away (right : Bool) (i : Fin 1062) (h2 : i≠2) (h3 : i≠3) :
    ∀ j,argSlots right j≠referenceSlots i := by
  intro j he
  have h:=congrArg Fin.val he
  have hi:=i.isLt
  have hi2 : i.val≠2 := by intro he; exact h2 (Fin.ext he)
  have hi3 : i.val≠3 := by intro he; exact h3 (Fin.ext he)
  cases right <;> fin_cases j <;> dsimp [argSlots,referenceSlots] at h <;> omega

theorem low_input (arity index : Nat) (word : List Bool) (i : Fin 1062) :
    input arity index word (referenceSlots i)=RecoveryTseitinReferences.coldInput arity index 0 0 i := by
  have hi:=i.isLt
  have hn : referenceSlots i≠1062 := by intro he; have h:=congrArg Fin.val he; change i.val=1062 at h; omega
  simp only [input,if_neg hn]
  simp only [referenceSlots,Fin.val_castAdd,dif_pos hi]

theorem input_other (arity index a b : Nat) (i : Fin 1062) (h2 : i≠2) (h3 : i≠3) :
    RecoveryTseitinReferences.coldInput arity index 0 0 i=RecoveryTseitinReferences.coldInput arity index a b i := by
  have generic (j : Fin 10) (hj2 : j≠2) (hj3 : j≠3) :
      RecoveryTseitinReferences.input arity index 0 0 j=RecoveryTseitinReferences.input arity index a b j := by
    fin_cases j <;> simp_all [RecoveryTseitinReferences.input]
  unfold RecoveryTseitinReferences.coldInput
  split_ifs with h
  · apply generic
    · intro he
      have hv:=congrArg Fin.val he
      exact h2 (Fin.ext hv)
    · intro he
      have hv:=congrArg Fin.val he
      exact h3 (Fin.ext hv)
  · rfl

noncomputable def operandsMachine := Composition.machine (Composition.machine readMachine (argMachine false)) (argMachine true)
def operandsBudget (tag a b : Nat) := (PCPPNativeNodeRead.budget tag a b+1+(4*a+16))+1+(4*b+16)

theorem operands_run (arity index : Nat) (pre tail : List Bool) (tag a b : Nat) :
    ∃ r,runFrom operandsMachine (operandsBudget tag a b)
      ⟨operandsMachine.start,heads pre.length,input arity index (PCPPNativeNodeRead.source pre tail tag a b)⟩=some r ∧
      r.steps≤operandsBudget tag a b ∧
      (∀ i : Fin 1062,r.final.tapes (referenceSlots i)=RecoveryTseitinReferences.coldInput arity index a b i ∧
        r.final.heads (referenceSlots i)=0) ∧
      r.final.tapes 1062=PCPPNativeNodeRead.source pre tail tag a b ∧
      r.final.heads 1062=pre.length+(natWord tag).length+(natWord a).length+(natWord b).length ∧
      r.final.tapes 1072=UnaryTemplate.tape tag ∧ r.final.heads 1072=1 ∧
      r.final.tapes 1082=UnaryTemplate.tape a ∧ r.final.heads 1082=1 := by
  obtain ⟨reader,hr,rs,r0,rh,rt,rkeep⟩:=read_run arity index pre tail tag a b
  have fresh (right : Bool) (j : Fin 5) (hj : j≠0) :
      reader.final.tapes (argSlots right j)=[] ∧ reader.final.heads (argSlots right j)=0 := by
    have hi : (argSlots right j).val < 1062 ∨ 1093 ≤ (argSlots right j).val := by
      cases right <;> fin_cases j <;> simp_all [argSlots]
    have h:=rkeep (argSlots right j) hi
    cases right <;> fin_cases j <;> first
      | exact False.elim (hj rfl)
      | exact h
  obtain ⟨left,hl,ls,l0,l1,lh,lkeep⟩:=arg_run false a reader.final (rt 1).1 (rt 1).2 (fresh false)
  obtain ⟨right,hg,gs,g0,g1,gh,gkeep⟩:=arg_run true b left.final
    ((lkeep _ (by intro i; exact arg_disjoint false i 0)).1.trans (rt 2).1)
    ((lkeep _ (by intro i; exact arg_disjoint false i 0)).2.trans (rt 2).2)
    (by
      intro j hj
      have h:=lkeep _ (by intro i; exact arg_disjoint false i j)
      exact ⟨h.1.trans (fresh true j hj).1,h.2.trans (fresh true j hj).2⟩)
  obtain ⟨result,hresult,hheads,htapes,hsteps⟩:=PCPPRequestNodeFields.join_three_run
    readMachine (argMachine false) (argMachine true) _ _ _ _ reader left right hr hl hg
  refine ⟨result,hresult,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hsteps]
    unfold operandsBudget
    omega
  · intro i
    rw [htapes,hheads]
    by_cases h2 : i=2
    · subst i
      have h:=gkeep 2 (by decide)
      exact ⟨h.1.trans l1,h.2.trans (lh 1)⟩
    by_cases h3 : i=3
    · subst i
      exact ⟨g1,gh 1⟩
    have g:=gkeep _ (arg_away true i h2 h3)
    have l:=lkeep _ (arg_away false i h2 h3)
    have r:=rkeep (referenceSlots i) (Or.inl i.isLt)
    refine ⟨g.1.trans (l.1.trans (r.1.trans ?_)),g.2.trans (l.2.trans (r.2.trans ?_))⟩
    · exact (low_input arity index _ i).trans (input_other arity index a b i h2 h3)
    · have hn : referenceSlots i≠1062 := by intro he; have hv:=congrArg Fin.val he; have hi:=i.isLt; change i.val=1062 at hv; omega
      simp only [heads,if_neg hn]
  · rw [htapes]
    exact (gkeep 1062 (by decide)).1.trans ((lkeep 1062 (by decide)).1.trans r0)
  · rw [hheads]
    exact (gkeep 1062 (by decide)).2.trans ((lkeep 1062 (by decide)).2.trans rh)
  · rw [htapes]
    exact (gkeep 1072 (by decide)).1.trans ((lkeep 1072 (by decide)).1.trans (rt 0).1)
  · rw [hheads]
    exact (gkeep 1072 (by decide)).2.trans ((lkeep 1072 (by decide)).2.trans (rt 0).2)
  · rw [htapes]
    exact (gkeep 1082 (by decide)).1.trans l0
  · rw [hheads]
    exact (gkeep 1082 (by decide)).2.trans (lh 0)

end NearCubicWires.RepairSource.RecoveryTseitinNative
