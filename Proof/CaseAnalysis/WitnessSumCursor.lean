import Proof.CaseAnalysis.WitnessSumReader
import Proof.Circuits.DecompositionCountPosition
import Proof.CaseAnalysis.RowsCircuitCounterReturn

/-! The actual term counter enters and leaves its sentinel position with
one paid step. The consumed field stream returns with the existing H
rewind driver/log before the successful sum-bank clear. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCursor
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions (direction : HeadMove) (i : Fin 3061) := if i=2532 then direction else .stay
def move (direction : HeadMove) := DecompositionCountPosition.move (directions direction)
def rewindSlots : Fin 3 → Fin 3061 := ![722,2530,2531]
noncomputable def rewind := RecoveryFocus.machine rewindSlots CompetitorRecordRewind.machine

theorem move_run (direction : HeadMove) (heads : Fin 3061 → ℕ) (input : Fin 3061 → List Bool) :
    ∃ r,runFrom (move direction) 1 ⟨0,heads,input⟩=some r ∧ r.steps=1 ∧
      r.final.heads=Function.update heads 2532 (direction.apply (heads 2532)) ∧ r.final.tapes=input := by
  obtain ⟨r,hr,rf,rs⟩ := DecompositionCountPosition.move_run (directions direction) heads input
  refine ⟨r,hr,rs,?_,by rw [rf]⟩
  rw [rf]
  funext i
  by_cases hi : i=2532
  · subst i;simp only [directions,ite_true,Function.update_self]
  · simp only [directions,if_neg hi,HeadMove.apply,Function.update_of_ne hi]

theorem rewind_run (H pos : ℕ) (heads : Fin 3061 → ℕ) (input : Fin 3061 → List Bool)
    (hp : pos ≤ H) (h722 : heads 722=pos) (h2530 : heads 2530=0) (h2531 : heads 2531=0)
    (hdriver : input 2530=List.replicate H true) (hlog : input 2531=List.replicate (H+1) false) :
    ∃ r,runFrom rewind (2*H+2) ⟨rewind.start,heads,input⟩=some r ∧ r.steps=2*H+2 ∧
      r.final.heads=Function.update heads 722 0 ∧ r.final.tapes=input := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := CloseoutRowsCircuitCounterReturn.return_run H pos (input 722) hp
  obtain ⟨r,run,_rf,rs,rh,rt,keep⟩ := RecoveryFocus.dock rewindSlots (by decide)
    CompetitorRecordRewind.machine _ heads input _
    (by intro i;fin_cases i <;> assumption)
    (by intro i;fin_cases i
        · rfl
        · exact hdriver
        · exact hlog) base hbase
  refine ⟨r,run,rs.trans bs,?_,?_⟩
  · funext i
    by_cases hi : i=722
    · subst i;rw [Function.update_self];exact (rh 0).trans (congrFun bh 0)
    rw [Function.update_of_ne hi]
    by_cases h0 : i=2530
    · subst i;exact ((rh 1).trans (congrFun bh 1)).trans h2530.symm
    by_cases h1 : i=2531
    · subst i;exact ((rh 2).trans (congrFun bh 2)).trans h2531.symm
    exact (keep i (by intro j;fin_cases j <;> first | exact Ne.symm hi | exact Ne.symm h0 | exact Ne.symm h1)).1
  · funext i
    by_cases hi : i=722
    · subst i;exact (rt 0).trans (congrFun bt 0)
    by_cases h0 : i=2530
    · subst i;exact ((rt 1).trans (congrFun bt 1)).trans hdriver.symm
    by_cases h1 : i=2531
    · subst i;exact ((rt 2).trans (congrFun bt 2)).trans hlog.symm
    exact (keep i (by intro j;fin_cases j <;> first | exact Ne.symm hi | exact Ne.symm h0 | exact Ne.symm h1)).2

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCursor
