import Proof.CaseAnalysis.RowsOriginalPairReset
import Proof.PCP.PCPPQueryClauseErase

/-! The original clause packet produces two reusable index/sign pairs and
clears every parser/return cell at one common paid capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalPair
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateSlot (i : Fin 21) : Fin 26 := ⟨if i.val < 10 then i.val+1 else if i.val < 20 then i.val+3 else 25,by split_ifs <;> omega⟩
def eraseSlots : Fin 23 → Fin 28 :=
  Fin.addCases (m:=21) (n:=2) (motive:=fun _=>Fin 28) (fun j=>(privateSlot j).castAdd 2) (fun j=>Fin.natAdd 26 j)
theorem erase_injective : Function.Injective eraseSlots := by decide
def extra (C : ℕ) : Fin 2 → List Bool := ![List.replicate C true,List.replicate (C+1) false]
noncomputable def erased := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 21)
noncomputable def clean := Composition.machine (TapeEmbedding.machine 2 reset) erased
def cleanBudget (a b C : ℕ) (sa sb : Bool) := resetBudget a b sa sb+2*C+5
def cleanInput (C : ℕ) (source : List Bool) : Fin 28 → List Bool :=
  Fin.addCases (m:=26) (n:=2) (motive:=fun _=>List Bool) (resetInput C source) (extra C)
def cleanOutput (a b C : ℕ) (sa sb : Bool) (i : Fin 28) : List Bool :=
  if i=11 then ZeroPadding.pad C (List.replicate a true)
  else if i=12 then ZeroPadding.pad C [sa]
  else if i=23 then ZeroPadding.pad C (List.replicate b true)
  else if i=24 then ZeroPadding.pad C [sb]
  else cleanInput C (word a b sa sb) i

theorem clean_run (a b C : ℕ) (sa sb : Bool) (hc : budget a b sa sb+1 ≤ C) :
    Step clean (cleanBudget a b C sa sb) (fun _=>0) (cleanInput C (word a b sa sb))
      (fun _=>0) (cleanOutput a b C sa sb) := by
  obtain ⟨r,hr,rh,t0,t11,t12,t23,t24,small,_,_⟩:=reset_run a b C sa sb hc
  have first:=(Step.of_run hr rh rfl).embed (fun _ : Fin 2=>0) (extra C)
  let A : Fin 28 → List Bool:=Fin.addCases (m:=26) (n:=2) (motive:=fun _=>List Bool) r.final.tapes (extra C)
  have old (i : Fin 26) : A (i.castAdd 2)=r.final.tapes i := Fin.addCases_left i
  have bound : ∀ i,(A ((privateSlot i).castAdd 2)).length ≤ C := by
    intro i
    rw [old,small _ (by fin_cases i <;> decide)]
  have raw:=Step.of_ready (RecoveryScratchErase.erase_ready C (C+1)
    (fun i=>A ((privateSlot i).castAdd 2)) bound)
  have last:=raw.dock eraseSlots erase_injective (fun _=>0) A (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl)
  have hout : dockH eraseSlots (fun _=>0) (fun _=>0)=(fun _=>0) :=
    dockH_existing _ _ _ (by intro i;rfl)
  have tout : install eraseSlots A (PCPTraversal.clearedLocal 21 C (C+1))=cleanOutput a b C sa sb := by
    apply HierarchyWidth.install_eq eraseSlots erase_injective
    · intro j;fin_cases j <;> first | rfl | (change List.replicate (C+1) false=List.replicate (max (C+1) (C+1)) false;rw [max_self])
    · intro i hi
      fin_cases i
      · exact t0.symm
      all_goals first
      | exact t11.symm
      | exact t12.symm
      | exact t23.symm
      | exact t24.symm
      | exact False.elim (hi 0 rfl)
      | exact False.elim (hi 1 rfl)
      | exact False.elim (hi 2 rfl)
      | exact False.elim (hi 3 rfl)
      | exact False.elim (hi 4 rfl)
      | exact False.elim (hi 5 rfl)
      | exact False.elim (hi 6 rfl)
      | exact False.elim (hi 7 rfl)
      | exact False.elim (hi 8 rfl)
      | exact False.elim (hi 9 rfl)
      | exact False.elim (hi 10 rfl)
      | exact False.elim (hi 11 rfl)
      | exact False.elim (hi 12 rfl)
      | exact False.elim (hi 13 rfl)
      | exact False.elim (hi 14 rfl)
      | exact False.elim (hi 15 rfl)
      | exact False.elim (hi 16 rfl)
      | exact False.elim (hi 17 rfl)
      | exact False.elim (hi 18 rfl)
      | exact False.elim (hi 19 rfl)
      | exact False.elim (hi 20 rfl)
      | exact False.elim (hi 21 rfl)
      | exact False.elim (hi 22 rfl)
  have hz : (Fin.addCases (m:=26) (n:=2) (motive:=fun _=>ℕ)
      (fun _=>0) (fun _=>0))=(fun _=>0) := by funext i;fin_cases i <;> rfl
  have first' := (first.congr_in hz rfl).congr hz rfl
  have all:=first'.seq (last.congr hout tout)
  have time : resetBudget a b sa sb+1+(2*C+4)=cleanBudget a b C sa sb := by unfold cleanBudget;omega
  rw [time] at all
  exact all.congr_in (by funext i;fin_cases i <;> rfl) rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalPair
