import Proof.Hierarchy.CompetitorWitnessCapLoop

/-! Cold whole-witness cap, with the rewind physically paid. The bound is
linear in the actual input length for every witness, including an overlong
one; only a true result licenses the subsequent nested decoder. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def guard := Rewind.machine machine
def input (x w : List Bool) : Fin 4→List Bool := ![frame x,frame w,[],[]]
def output (x w : List Bool) (scratch : ℕ) : Fin 4→List Bool :=
  ![frame x,frame w,[decide (16*w.length≤x.length)],List.replicate scratch false]

theorem cap_ready (x w : List Bool) :
    ∃ scratch,scratch≤3*x.length+2 ∧
      ReadyRun guard (2*scratch+2) (input x w) (output x w scratch) := by
  obtain ⟨base,hbase,hbt,hbs⟩ := raw_run x w
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace machine
    (3*x.length+2) ![frame x,frame w,[]] base hbase 0
  have hin : (Fin.addCases (m:=3) (n:=1) (motive:=fun _ : Fin 4=>List Bool)
      ![frame x,frame w,[]] (fun _ : Fin 1=>List.replicate 0 false))=input x w := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨base.steps,hbs,r,hr,?_,hh,hsteps⟩
  funext i
  fin_cases i
  · exact (ht 0).trans (congrFun hbt 0)
  · exact (ht 1).trans (congrFun hbt 1)
  · exact (ht 2).trans (congrFun hbt 2)
  · simpa [output] using hcounter

theorem cap_iff (x w : List Bool) (scratch : ℕ) :
    output x w scratch 2=[true] ↔ w.length≤x.length/16 := by
  change [decide (16*w.length≤x.length)]=[true] ↔ _
  simp only [List.cons.injEq,and_true,decide_eq_true_eq]
  omega

theorem cap_run (x w : List Bool) :
    ∃ scratch,scratch≤3*x.length+2 ∧ ∃ r,
      run guard (6*x.length+6) (input x w)=some r ∧
      r.final.tapes=output x w scratch ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤6*x.length+6 := by
  obtain ⟨scratch,hsc,r,hr,ht,hh,hs⟩ := cap_ready x w
  have hb : 2*scratch+2≤6*x.length+6 := by omega
  have hm := run_moreFuel guard (2*scratch+2) (6*x.length+6-(2*scratch+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨scratch,hsc,r,hm,ht,hh,hs.le.trans hb⟩

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
