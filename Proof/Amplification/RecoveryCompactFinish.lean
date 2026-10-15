import Proof.Amplification.RecoveryCompactBank

/-! Paid positioning of the four new streaming/count heads and the two
empty prior-prefix drivers, after every substantive tape has been copied. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finishing (i : Fin 493) : Prop := i=387 ∨ i=406 ∨ i=456 ∨ i=491
instance finishingDecidable (i : Fin 493) : Decidable (finishing i) := by
  unfold finishing
  infer_instance
def finishHeads (h : Fin 493→Nat) (i : Fin 493) := if finishing i then 1 else h i
def finishTapes (a : Fin 493→List Bool) := Function.update (Function.update a 404 [false]) 473 [false]
def finish : Machine 493 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=404 ∨ i=473 then some false else none,
    fun i=>if finishing i then .right else .stay⟩ else none

theorem finish_run (h : Fin 493→Nat) (a : Fin 493→List Bool)
    (hh : ∀ (i : Fin 493),338 ≤ i.val → h i=0) (ha : a 404=[]) (hb : a 473=[]) :
    ∃ r,runFrom finish 1 ⟨finish.start,h,a⟩=some r ∧
      r.final.heads=finishHeads h ∧ r.final.tapes=finishTapes a ∧ r.steps=1 := by
  let out : Configuration 493 2 := ⟨1,finishHeads h,finishTapes a⟩
  have hs : step finish ⟨finish.start,h,a⟩=some out := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : finishing i
      · have hlarge : 338 ≤ i.val := by
          rcases hi with rfl|rfl|rfl|rfl <;> decide
        simp [applyAction,finishHeads,HeadMove.apply,hi,hh i hlarge,out]
      · simp [applyAction,finishHeads,HeadMove.apply,hi,out]
    · funext i
      by_cases hi : i=404
      · subst i
        simp [applyAction,finishTapes,ha,hh 404 (by decide),out]
        rfl
      · by_cases hj : i=473
        · subst i
          simp [applyAction,finishTapes,hb,hh 473 (by decide),out]
          rfl
        · simp [applyAction,finishTapes,hi,hj,out]
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],ht⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
