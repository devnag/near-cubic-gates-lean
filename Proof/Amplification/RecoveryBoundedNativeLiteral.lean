import Proof.Amplification.RecoveryBoundedNativeLiteralRun

/-! Actual bounded-compiler literal emission starts with blank scratch.
The one retained capacity is supplied by the enclosing compiler allocator;
its size dominates every native-field printing bound uniformly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
open LocalBitMultitape RepairRepresentation RecoveryExecution PCPPNativeClauseBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev retained (i : Fin 30) : Prop := i=0 ∨ i=1 ∨ i=20 ∨ i=22 ∨ 24 ≤ i.val
def padding (C : ℕ) (i : Fin 30) : ℕ := if retained i then 0 else if i=23 then C+1 else C
noncomputable def coldInput (index position C : ℕ) (negative : Bool) (out : List Bool) :=
  {entry index position C negative out with tapes:=fun i=>if retained i then data index position C negative out i else []}

theorem padded_input (index position C : ℕ) (negative : Bool) (out : List Bool) :
    ZeroPadding.config (padding C) (coldInput index position C negative out)=entry index position C negative out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : retained i
    · change ZeroPadding.pad (padding C i) (if retained i then _ else [])=_
      simp only [padding,hi,ite_true,ZeroPadding.pad_zero]
      rfl
    · have he : data index position C negative out i=List.replicate (padding C i) false := by
        fin_cases i
        all_goals first | exact False.elim (hi (by decide)) | rfl
      change ZeroPadding.pad (padding C i) (if retained i then _ else [])=_
      rw [if_neg hi]
      change ZeroPadding.pad (padding C i) []=data index position C negative out i
      rw [he]
      rfl

theorem budget_bound (index position C : ℕ)
    (hi : PCPPNativeSumAppend.budget 0 index+1≤C) (hp : PCPPNativeSumAppend.budget 0 position+1≤C)
    (hz : PCPPNativeSumAppend.budget 0 0+1≤C) : budget index position C≤16*C+34 := by
  have h1 : (natWord 1).length=3 := by decide
  have h2 : (natWord 2).length=5 := by decide
  unfold budget firstBudget secondBudget nodeBudget PCPPNativeSumReusable.budget
  simp only [values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,h1,h2]
  omega

theorem cold_run (index position W C : ℕ) (negative : Bool) (out : List Bool)
    (hi : index≤W) (hp : position≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ r,runFrom machine (16*C+34) (coldInput index position C negative out)=some r ∧
      r.steps≤16*C+34 ∧ r.final.heads=heads (out++emitted index position negative) ∧
      (∀ i,retained i → r.final.tapes i=data index position C negative (out++emitted index position negative) i) := by
  have capi:=PCPPNativeClauseCapacity.sum_capacity 0 index W C (by omega) hC
  have capp:=PCPPNativeClauseCapacity.sum_capacity 0 position W C (by omega) hC
  have capz:=PCPPNativeClauseCapacity.sum_capacity 0 0 W C (by omega) hC
  obtain ⟨a,ha,as,ah,atapes⟩:=literal_run index position C negative out capi capp capz
  rw [←padded_input] at ha
  obtain ⟨b,hb,bf,bs,_⟩:=ZeroPadding.run_unpad machine (padding C) _ _ a ha
  have cap:=budget_bound index position C capi capp capz
  have more:=runFrom_moreFuel machine _ (16*C+34-budget index position C) _ b hb
  rw [Nat.add_sub_of_le cap] at more
  refine ⟨b,more,bs.le.trans (as.trans cap),?_,?_⟩
  · exact (congrArg Configuration.heads bf).trans ah
  · intro i hi
    have ht:=congrArg (fun c=>c.tapes i) bf
    simpa only [ZeroPadding.config,padding,hi,ite_true,ZeroPadding.pad_zero,atapes] using ht

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
