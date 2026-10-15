import Proof.Amplification.RecoveryRawCountPadded

/-! The raw clause reuses the physical padded counter produced by the
count parser. Only that counter tape is padded; every payload stays exact. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RecoveryRawLiteralBound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverCaps (capacity : Nat) (i : Fin 36) := if i=35 then capacity else 0
def paddedCfg {s : Nat} (capacity : Nat) (x : State) (total : Nat) (q : Fin s) :=
  ZeroPadding.config (driverCaps capacity) (cfg x total q)

theorem padded_clause_run (width total capacity : Nat) (x : State)
    (hx : RecoveryRawLiteralLoop.Inv width x) :
    ∃ r,runFrom machine (budget width total) (paddedCfg capacity x total machine.start)=some r ∧
      r.steps ≤ budget width total ∧ r.final.heads 28=0 ∧
      r.final.tapes 28=[answer total x] ∧
      (answer total x=true → r.final=paddedCfg capacity
        (inverted (output (out total x).2)) total r.final.control) := by
  have hrun := clause_run width total x hx
  obtain ⟨base,hr,hb,hh,ht,hf⟩ := hrun
  obtain ⟨r,h,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine (driverCaps capacity) _ _ base hr
  refine ⟨r,h,hsteps.le.trans hb,?_,?_,?_⟩
  · rw [hfinal]; exact hh
  · rw [hfinal]
    change ZeroPadding.pad 0 (base.final.tapes 28)=_
    rw [ZeroPadding.pad_zero,ht]
  · intro ha
    rw [hfinal,hf ha]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryRawClause
