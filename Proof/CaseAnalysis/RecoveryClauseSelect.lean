import Proof.CaseAnalysis.RecoveryClauseRead

/-! Lookup and decode one actual query reference in the retained61-bank.
Only its two lookup scratch fields and selected raw operand change. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseSelect
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def target (second : Bool) : Fin 61:=if second then 47 else 45
def lookupSlots : Fin 5→Fin 61:=![59,37,49,30,43]
def readSlots (second : Bool) : Fin 3→Fin 61:=![30,target second,43]
theorem read_injective (second : Bool) : Function.Injective (readSlots second) := by cases second <;> decide
noncomputable def lookup:=RecoveryFocus.machine lookupSlots RecoveryBoundedClauseLookup.machine
noncomputable def read (second : Bool):=RecoveryFocus.machine (readSlots second) RecoveryBoundedClauseLookup.readMachine
noncomputable def machine (second : Bool):=Composition.machine lookup (read second)
def lookupOutput (A : Fin 61→List Bool) (before : List ℕ) (node C : ℕ) (i : Fin 61):=
  if i=37 then ZeroPadding.pad C (sourceWord before)
  else if i=30 then ZeroPadding.pad C (frame (List.replicate node true)) else A i
def output (A : Fin 61→List Bool) (second : Bool) (before : List ℕ) (node C : ℕ):=
  Function.update (lookupOutput A before node C) (target second) (ZeroPadding.pad C (List.replicate node true))
def budget (before : List ℕ) (node : ℕ):=RecoveryBoundedClauseLookup.budget before node+1+(4*node+4)

theorem lookup_run (H : Fin 61→ℕ) (A : Fin 61→List Bool) (before : List ℕ)
    (node C L : ℕ) (tail : List Bool)
    (hH : ∀ j,H (lookupSlots j)=0)
    (hA : ∀ j,A (lookupSlots j)=RecoveryBoundedClauseLookup.input before node C L tail j)
    (hL : RecoveryBoundedClauseLookup.rawBudget before node ≤ L) :
    ∃ r,runFrom lookup (RecoveryBoundedClauseLookup.budget before node) ⟨lookup.start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedClauseLookup.budget before node ∧ r.final.heads=H ∧
      r.final.tapes=lookupOutput A before node C := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedClauseLookup.lookup_ready before node C L tail hL).focus_at
    lookupSlots (by decide) H A hA hH
  have he : install lookupSlots A (RecoveryBoundedClauseLookup.output before node C L tail)=lookupOutput A before node C := by
    apply HierarchyWidth.install_eq lookupSlots (by decide)
    · intro j
      have h:=hA j
      fin_cases j <;> first | rfl | exact h
    · intro i hi
      have h37 : i≠37:=fun h=>hi 1 h.symm
      have h30 : i≠30:=fun h=>hi 3 h.symm
      simp only [lookupOutput,if_neg h37,if_neg h30]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

theorem read_run (second : Bool) (H : Fin 61→ℕ) (A : Fin 61→List Bool) (node C L : ℕ)
    (hH : ∀ j,H (readSlots second j)=0)
    (hA : ∀ j,A (readSlots second j)=
      (![ZeroPadding.pad C (frame (List.replicate node true)),List.replicate C false,List.replicate L false] : Fin 3→List Bool) j)
    (hL : 2*node+1 ≤ L) :
    ∃ r,runFrom (read second) (4*node+4) ⟨(read second).start,H,A⟩=some r ∧
      r.steps ≤ 4*node+4 ∧ r.final.heads=H ∧
      r.final.tapes=Function.update A (target second) (ZeroPadding.pad C (List.replicate node true)) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedClauseLookup.read_ready node C L hL).focus_at
    (readSlots second) (read_injective second) H A hA hH
  have he : install (readSlots second) A
      ![ZeroPadding.pad C (frame (List.replicate node true)),ZeroPadding.pad C (List.replicate node true),List.replicate L false]=
      Function.update A (target second) (ZeroPadding.pad C (List.replicate node true)) := by
    apply HierarchyWidth.install_eq (readSlots second) (read_injective second)
    · intro j
      have h:=hA j
      fin_cases j
      · cases second <;> exact h
      · cases second <;> rfl
      · cases second <;> exact h
    · intro i hi
      have ht : i≠target second:=fun h=>hi 1 h.symm
      simp only [Function.update_of_ne ht]
  exact ⟨r,hr,rs,rh,rt.trans he⟩

theorem select_run (second : Bool) (H : Fin 61→ℕ) (A : Fin 61→List Bool) (before : List ℕ)
    (node C L : ℕ) (tail : List Bool)
    (hH : ∀ j,H (lookupSlots j)=0) (ht : H (target second)=0)
    (hA : ∀ j,A (lookupSlots j)=RecoveryBoundedClauseLookup.input before node C L tail j)
    (aTarget : A (target second)=List.replicate C false)
    (hL : RecoveryBoundedClauseLookup.rawBudget before node ≤ L) :
    ∃ r,runFrom (machine second) (budget before node) ⟨(machine second).start,H,A⟩=some r ∧
      r.steps ≤ budget before node ∧ r.final.heads=H ∧ r.final.tapes=output A second before node C := by
  obtain ⟨p,pr,ps,ph,pt⟩:=lookup_run H A before node C L tail hH hA hL
  have hl : 2*node+1 ≤ L := by unfold RecoveryBoundedClauseLookup.rawBudget at hL;omega
  obtain ⟨q,qr,qs,qh,qt⟩:=read_run second H (lookupOutput A before node C) node C L
    (by intro j;fin_cases j;exact hH 3;exact ht;exact hH 4)
    (by intro j;fin_cases j
        · rfl
        · cases second <;> exact aTarget
        · exact hA 4) hl
  have qr' : runFrom (read second) (4*node+4) (restart p.final (read second).start)=some q := by
    change runFrom _ _ ⟨_,p.final.heads,p.final.tapes⟩=some q
    rw [ph,pt]
    exact qr
  have full:=Composition.run_join lookup (read second) _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,qh,qt⟩
  change p.steps+1+q.steps ≤ budget before node
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseSelect
