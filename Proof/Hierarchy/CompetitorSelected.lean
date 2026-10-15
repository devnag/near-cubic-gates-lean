import Proof.Hierarchy.CompetitorSelectedPadding

/-! Cold zero-head entry to the actual selected-total machine. The five
sentinel cursors move right in one physical transition before the scan. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open LocalBitMultitape RecoveryExecution CompetitorCountMask SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bootHeads : Fin 20 → ℕ := ![1,0,0,1,1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0]
def boot : Machine 20 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if bootHeads i=1 then .right else .stay⟩ else none
noncomputable def coldMachine := Composition.machine boot machine
def coldBudget (b w N : ℕ) := 1+1+budget b w N

theorem boot_run (tapes : Fin 20 → List Bool) : ∃ r,
    run boot 1 tapes=some r ∧ r.final=⟨1,bootHeads,tapes⟩ ∧ r.steps=1 := by
  have hs : step boot (initialConfiguration boot tapes)=some ⟨1,bootHeads,tapes⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem cold_run (b w N : ℕ) (xs : List (Bool × ℕ)) (hn : xs.length≤N)
    (hw : b≤w) (hx : ∀ x∈selected xs,x<2^b) (hfit : (selected xs).sum<2^w) :
    ∃ actual,run coldMachine (coldBudget b w N) (shortTapes b w N xs)=some actual ∧
      actual.steps≤coldBudget b w N ∧ actual.final.heads=finalHeads b N ∧
      actual.final.tapes 15=frame (binary w (selected xs).sum) ∧
      actual.final.tapes 12=List.replicate w true := by
  obtain ⟨first,hf,ff,fs⟩ := boot_run (shortTapes b w N xs)
  obtain ⟨last,hl,ls,lh,l15,l12⟩ := short_run b w N xs hn hw hx hfit
  have hi : Composition.restart first.final machine.start=shortInput b w N xs := by
    rw [ff]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · rfl
  rw [←hi] at hl
  have hj := Composition.run_join boot machine _ _ _ first last hf hl
  refine ⟨Composition.joinedReceipt first last,hj,?_,lh,l15,l12⟩
  change first.steps+1+last.steps≤coldBudget b w N
  unfold coldBudget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSelectedCount
