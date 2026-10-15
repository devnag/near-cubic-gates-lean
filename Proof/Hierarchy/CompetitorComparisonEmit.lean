import Proof.Hierarchy.CompetitorRecordEmit

/-! The actual six-field comparison-record emitter feeding the accepted
C.10 validity/midpoint consumer, in its exact word order and denominator ABI. -/
namespace NearCubicWires.RepairOrdinary.CompetitorComparisonEmit
open LocalBitMultitape RecoveryExecution
open CompetitorValidity CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sources : List (Fin 8) := [0,1,2,3,4,5]
def fields (b : ℕ) (a : Comparison) (i : Fin 8) :=
  if h : i.val<6 then a.fields b ⟨i.val,h⟩ else []
def input (b : ℕ) (a : Comparison) (out : List Bool) : Fin 8 → List Bool := fun i =>
  if h : i.val<6 then ZeroPadding.pad (capacity b) (frame (a.fields b ⟨i.val,h⟩))
  else if i.val=6 then out else List.replicate (capacity b) false
def heads (out : List Bool) : Fin 8 → ℕ := fun i => if i.val=6 then out.length else 0
noncomputable def machine := CompetitorFieldEmit.listProgram (6 : Fin 8) 7 sources

theorem stream_eq (b : ℕ) (a : Comparison) : CompetitorFieldEmit.stream (fields b a) sources=a.word b := rfl
theorem cost_eq (b : ℕ) (a : Comparison) : CompetitorFieldEmit.listCost (fields b a) sources=40*b+56 := by
  change fieldCost (a.fields b) targets=40*b+56
  exact record_cost b a

theorem emit_run (b : ℕ) (a : Comparison) (out : List Bool) :
    ∃ r : ExecutionReceipt 8 (CompetitorFieldEmit.states sources),
      runFrom machine (40*b+56) (RecoveryCalls.restarted machine (heads out) (input b a out))=some r ∧
      r.final.heads=heads (out++a.word b) ∧ r.final.tapes=input b a (out++a.word b) ∧
      r.steps=40*b+56 := by
  have hlt (j : Fin 8) (hj : j∈sources) : j.val<6 := by
    simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj | hj | hj | hj <;> subst j <;> decide
  have ht : ∀ j∈sources,j≠(6 : Fin 8) := by
    intro j hj he
    have hv := congrArg Fin.val he
    have hl := hlt j hj
    omega
  have hc : ∀ j∈sources,j≠(7 : Fin 8) := by
    intro j hj he
    have hv := congrArg Fin.val he
    have hl := hlt j hj
    omega
  obtain ⟨r,hr,hh,htapes,hs⟩ := CompetitorFieldEmit.list_run (6 : Fin 8) 7 sources (fields b a) (by decide) ht hc
    out (capacity b) (heads out) (input b a out)
    (by intro j hj; simp [heads,show j.val≠6 by have hl := hlt j hj; omega]) rfl rfl
    (by intro j hj; simp [input,fields,hlt j hj]) rfl rfl
    (by intro j hj; simpa only [fields,hlt j hj,↓reduceDIte] using field_capacity b a ⟨j.val,hlt j hj⟩)
  rw [cost_eq] at hr hs
  rw [stream_eq] at hh htapes
  refine ⟨r,hr,?_,?_,hs⟩
  · rw [hh]
    funext i
    by_cases hi : i=6
    · subst i
      simp [heads]
    · have hv : i.val≠6 := fun he => hi (Fin.ext he)
      simp [Function.update_of_ne hi,heads,hv]
  · rw [htapes]
    funext i
    by_cases hi : i=6
    · subst i
      simp [input]
    · have hv : i.val≠6 := fun he => hi (Fin.ext he)
      simp [Function.update_of_ne hi,input,hv]

end NearCubicWires.RepairOrdinary.CompetitorComparisonEmit
