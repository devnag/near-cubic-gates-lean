import Proof.PCP.PCPOuterCopy

namespace NearCubicWires.RepairOrdinary.PCPOuter
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftFour : Machine 1 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q _ => if h : q.val<4 then
    some ⟨⟨q.val+1,by omega⟩,fun _ => none,fun _ => .left⟩ else none
def countLocal := Composition.machine (HierarchyFixedWord.raw (CompareMachine.word 4)) leftFour
def countReceipt : ExecutionReceipt 1 11 := ⟨⟨10,fun _ => 1,fun _ => CompareMachine.word 4⟩,10,5⟩

theorem count_local : runFrom countLocal 10 ⟨countLocal.start,fun _ => 0,fun _ => []⟩=
    some countReceipt := by rfl

noncomputable def countMachine {t : ℕ} (o : Fin t) :=
  RecoveryFocus.machine (fun _ : Fin 1 => o) countLocal

theorem count_run {t : ℕ} (o : Fin t) (h : Fin t → ℕ) (d : Fin t → List Bool)
    (hh : h o=0) (ht : d o=[]) :
    Exact (countMachine o) 10 h d (Function.update h o 1)
      (Function.update d o (CompareMachine.word 4)) := by
  classical
  have inj : Function.Injective (fun _ : Fin 1 => o) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config (fun _ : Fin 1 => o) inj countLocal h d _ _
    countReceipt count_local
  rw [focused_existing (fun _ : Fin 1 => o) h d _ (fun _ => hh) (fun _ => ht)] at hr
  have hp : RecoveryFocus.pick (fun _ : Fin 1 => o) o=some 0 := RecoveryFocus.pick_slot _ inj 0
  refine ⟨r,hr,?_,?_,rs⟩
  · funext i
    by_cases hi : i=o
    · subst i
      simp [rf,RecoveryFocus.config,hp,countReceipt]
    · have hn : RecoveryFocus.pick (fun _ : Fin 1 => o) i=none := by
        unfold RecoveryFocus.pick
        exact dif_neg (by rintro ⟨j,hj⟩; exact hi hj.symm)
      simp [rf,RecoveryFocus.config,hn,hi]
  · funext i
    by_cases hi : i=o
    · subst i
      simp [rf,RecoveryFocus.config,hp,countReceipt]
    · have hn : RecoveryFocus.pick (fun _ : Fin 1 => o) i=none := by
        unfold RecoveryFocus.pick
        exact dif_neg (by rintro ⟨j,hj⟩; exact hi hj.symm)
      simp [rf,RecoveryFocus.config,hn,hi]

end NearCubicWires.RepairOrdinary.PCPOuter
