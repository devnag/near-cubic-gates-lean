import Proof.CaseAnalysis.RecoveryGrammarLess

/-! The original terminal constant and reverse AND/OR fold use the same
grammar bank. The saved-reference stack is consumed in its original order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFoldRun
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open RecoveryBoundedGrammarWorker (positioned paddedData resultData resultHeads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 35) : Fin 78:=if j=31 then 74 else if j=34 then 35 else j.castAdd 43
theorem slots_injective : Function.Injective slots:=by decide
def driver (i : Fin 78):=decide (i=35)
noncomputable def body (conjunction : Bool):=
  RecoveryFocus.machine slots (RecoveryBoundedGrammarFold.machine conjunction)
noncomputable def machine (conjunction : Bool):=
  RecoveryBoundedGrammarWorker.machine (body conjunction) driver

theorem input_heads (out pre : List Bool) (refs : List ℕ) :
    ∀ j,positioned driver out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) (slots j)=
      RecoveryBoundedGrammarFold.heads out pre refs j := by
  intro j;fin_cases j <;> rfl

theorem final_heads (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ) :
    let last:=RecoveryBoundedGrammarFold.finalConfiguration conjunction base C out pre refs
    last.heads 20=(last.tapes 20).length ∧ last.heads 31=pre.length := by
  constructor
  · rfl
  · change (RecoveryBoundedNativeFoldLoop.stack pre []).length=pre.length
    simp only [RecoveryBoundedNativeFoldLoop.stack,List.reverse_nil,
      RecoveryBoundedNativeUnaryLoop.stackWords,List.flatMap_nil,List.append_nil]

theorem raw_run (conjunction : Bool) (base W C : ℕ) (out pre : List Bool) (refs : List ℕ)
    (A : Fin 78→List Bool) (href : ∀ ref∈refs,ref≤W) (ha : base+refs.length≤W)
    (hC : 16384*(W+1)^2≤C)
    (hA : ∀ j,A (slots j)=RecoveryBoundedGrammarFold.data base C out pre refs j) :
    let last:=RecoveryBoundedGrammarFold.finalConfiguration conjunction base C out pre refs
    ∃ r,runFrom (body conjunction) (RecoveryBoundedGrammarFold.budget conjunction refs.length C)
      ⟨(body conjunction).start,positioned driver out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs),A⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarFold.budget conjunction refs.length C ∧
      r.final.heads 20=(last.tapes 20).length ∧ r.final.heads 74=pre.length ∧
      r.final.tapes=install slots A last.tapes := by
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedGrammarFold.fold_run conjunction base W C out pre refs href ha hC
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slots slots_injective
    (RecoveryBoundedGrammarFold.machine conjunction) _
    (positioned driver out (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs)) A
    (RecoveryBoundedGrammarFold.entry conjunction base C out pre refs) (input_heads out pre refs) hA p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_,?_⟩
  · change r.final.heads (slots 20)=_
    rw [rh 20,ph]
    exact (final_heads conjunction base C out pre refs).1
  · change r.final.heads (slots 31)=_
    rw [rh 31,ph]
    exact (final_heads conjunction base C out pre refs).2
  · exact (HierarchyWidth.install_eq slots slots_injective A r.final.tapes _
      (by intro j;rw [rt j,pt]) (by intro i h;exact (rkeep i h).2)).symm

theorem fold_run (conjunction : Bool) (base W C S B : ℕ) (out pre : List Bool) (refs : List ℕ)
    (A : Fin 78→List Bool) (href : ∀ ref∈refs,ref≤W) (ha : base+refs.length≤W)
    (hC : 16384*(W+1)^2≤C)
    (hA : ∀ j,A (slots j)=RecoveryBoundedGrammarFold.data base C out pre refs j)
    (hS : 1≤S) (ho : out.length≤S)
    (hk : (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length≤S)
    (hAB : ∀ i,(A i).length≤B)
    (hB : S+RecoveryBoundedGrammarFold.budget conjunction refs.length C+3≤B) :
    let last:=RecoveryBoundedGrammarFold.finalConfiguration conjunction base C out pre refs
    let next:=install slots A last.tapes
    ∃ r,runFrom (machine conjunction) (2*(RecoveryBoundedGrammarFold.budget conjunction refs.length C+2)+2)
      (RecoveryBoundedGrammarWorker.entry (body conjunction) driver out
        (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) (paddedData B A) B)=some r ∧
      r.steps≤2*(RecoveryBoundedGrammarFold.budget conjunction refs.length C+2)+2 ∧
      r.final.heads=resultHeads (last.tapes 20).length pre.length ∧
      r.final.tapes=resultData (paddedData B next) B ∧
      (∀ i,i.val<73 → (paddedData B next i).length≤B) := by
  obtain ⟨p,pr,ps,ph,pk,pt⟩:=raw_run conjunction base W C out pre refs A href ha hC hA
  obtain ⟨r,rr,rs,rh,rt,rb⟩:=RecoveryBoundedGrammarWorker.padded_reset_run (body conjunction) driver out
    (pre++RecoveryBoundedNativeUnaryLoop.stackWords refs) A
    (RecoveryBoundedGrammarFold.budget conjunction refs.length C) S B (by decide) (by decide)
    p pr ps hS ho hk hAB hB
  rw [ph,pk] at rh
  rw [pt] at rt rb
  exact ⟨r,rr,rs,rh,rt,rb⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFoldRun
