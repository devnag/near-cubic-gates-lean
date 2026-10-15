import Proof.CaseAnalysis.RecoveryTableStep

/-! The actual unary repeat driver executes the literal original universal
table. Its extra count tape is retained and rewound, not a free loop bound. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTable
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding RecoveryExecution
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RepeatMachine.machine RecoveryBoundedTableNode.machine (fun _ _=>true)
def budget (total W : ℕ):=total*(RecoveryBoundedTableNode.budget W+2)+total+3
def Fits {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W : ℕ) (ht : total ≤ bound) : Prop :=
  ∀ (k : ℕ) (hk : k < total),StepFits b address k (by omega) W
noncomputable def configuration {n bound : ℕ} (phase : Fin 5)
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (address : BitInput n)
    (W D L : ℕ) (out addressTail : List Bool) (k : ℕ) (hk : k ≤ bound) (total driver : ℕ):=
  RepeatMachine.cfg phase (entry b address W D L out addressTail k hk) total driver

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

theorem repeat_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (W D L : ℕ) (out addressTail : List Bool)
    (remaining total pos : ℕ) (ht : total ≤ bound) (hpos : pos+remaining=total)
    (hfits : Fits b address total W ht) (hD : 8388608*(W+1)^3 ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    ∃ r,runFrom machine (remaining*(RecoveryBoundedTableNode.budget W+2)+total+3)
      (configuration 0 b address W D L out addressTail pos (by omega) total (pos+1))=some r ∧
      r.final=configuration 3 b address W D L out addressTail total ht total 1 ∧
      r.steps ≤ remaining*(RecoveryBoundedTableNode.budget W+2)+total+3 := by
  induction remaining generalizing pos with
  | zero=>
    have hoff : pos=total:=by omega
    subst pos
    obtain ⟨r,hr,rf,rs⟩:=(RepeatMachine.exhaust RecoveryBoundedTableNode.machine (fun _ _=>true)
      (entry b address W D L out addressTail total ht) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,rf,?_⟩
    · simpa only [machine,configuration,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
  | succ remaining ih=>
    have hp : pos < total:=by omega
    obtain ⟨first,hr,hs,hh,hdata⟩:=step_run b address W D L out addressTail pos (by omega)
      (hfits pos hp) hD hL
    have hiteration:=RepeatMachine.iteration RecoveryBoundedTableNode.machine (fun _ _=>true)
      (entry b address W D L out addressTail pos (by omega)) total pos first rfl hp hr
    change Timed machine (first.steps+2)
      (configuration 0 b address W D L out addressTail pos (by omega) total (pos+1))
      (RepeatMachine.cfg 0 first.final total (pos+2)) at hiteration
    rw [cfg_data 0 first.final (entry b address W D L out addressTail (pos+1) (by omega)) total (pos+2) hh hdata] at hiteration
    obtain ⟨last,hl,lf,ls⟩:=ih (pos+1) (by omega)
    rcases hiteration with ⟨space,hprefix⟩
    obtain ⟨r,hrun,rf,rs,_⟩:=hprefix.followedBy last hl
    have hbudget : first.steps+2+(remaining*(RecoveryBoundedTableNode.budget W+2)+total+3) ≤
        (remaining+1)*(RecoveryBoundedTableNode.budget W+2)+total+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel machine _
      ((remaining+1)*(RecoveryBoundedTableNode.budget W+2)+total+3-
        (first.steps+2+(remaining*(RecoveryBoundedTableNode.budget W+2)+total+3))) _ r hrun
    rw [Nat.add_sub_of_le hbudget] at more
    refine ⟨r,more,rf.trans lf,?_⟩
    rw [rs]
    omega

theorem table_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total W D L : ℕ) (out addressTail : List Bool) (ht : total ≤ bound)
    (hfits : Fits b address total W ht) (hD : 8388608*(W+1)^3 ≤ D)
    (hL : RecoveryBoundedSelectorFinish.logCapacity W ≤ L) :
    ∃ r,runFrom machine (budget total W)
      (configuration 0 b address W D L out addressTail 0 (by omega) total 1)=some r ∧
      r.final=configuration 3 b address W D L out addressTail total ht total 1 ∧
      r.steps ≤ budget total W := by
  exact repeat_run b address W D L out addressTail total total 0 ht (by omega) hfits hD hL

end NearCubicWires.RepairOrdinary.RecoveryBoundedTable
