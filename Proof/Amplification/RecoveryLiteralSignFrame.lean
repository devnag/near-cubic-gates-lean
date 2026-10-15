import Proof.Amplification.RecoveryFormulaValueFields

/-! The source's negative flag is complemented and physically written as
one binary Bool code field for the original CNF positive-sign convention. -/
namespace NearCubicWires.RepairSource.RecoveryLiteralSignFrame
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=3
  rule := fun q scan=>if q.val=0 then some ⟨1,![none,some true],![.stay,.right]⟩
    else if q.val=1 then some ⟨2,![none,some (!(scan 0))],![.stay,.right]⟩
    else if q.val=2 then some ⟨3,![none,some false],fun _=>.stay⟩ else none

def machine := Rewind.machine raw

theorem raw_run (negative : Bool) : ∃ r,
    run raw 3 ![[negative],[]]=some r ∧
      r.final.tapes=![[negative],RepairOrdinary.frame [!negative]] ∧ r.steps=3 := by
  let first : Configuration 2 4 := ⟨1,![0,1],![[negative],[true]]⟩
  let next : Configuration 2 4 := ⟨2,![0,2],![[negative],[true,!negative]]⟩
  let last : Configuration 2 4 := ⟨3,![0,2],![[negative],RepairOrdinary.frame [!negative]]⟩
  have h0 : step raw (initialConfiguration raw ![[negative],[]])=some first := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h1 : step raw first=some next := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h2 : step raw next=some last := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := ((Timed.single (by rfl) h0).trans
    ((Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2))).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.tapes hf,hs⟩

theorem sign_ready (negative : Bool) :
    ClockJoin.ReadyRun machine 8 ![[negative],[],[]]
      ![[negative],RepairOrdinary.frame [!negative],List.replicate 3 false] := by
  obtain ⟨base,hbase,bt,bs⟩ := raw_run negative
  obtain ⟨r,hr,rt,rc,rh,rs,_peak⟩ := Rewind.Workspace.reset_workspace raw 3 _ base hbase 0
  rw [bs] at hr rc rs
  refine ⟨r,?_,?_,rh,rs.le⟩
  · convert hr using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · exact (rt 0).trans (congrFun bt 0)
    · exact (rt 1).trans (congrFun bt 1)
    · exact rc

end NearCubicWires.RepairSource.RecoveryLiteralSignFrame
