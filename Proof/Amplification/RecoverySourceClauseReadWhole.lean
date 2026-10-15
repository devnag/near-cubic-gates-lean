import Proof.Amplification.RecoverySourceClauseRead

/-! The three consecutive source-field reads compose at their actual source
cursors, including both physical control handoffs. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseRead
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (bits : Fin 3→List Bool) := 4*((bits 0).length+(bits 1).length+(bits 2).length)+14

theorem read_run (pre : List Bool) (bits : Fin 3→List Bool) (suffix : List Bool) : ∃ r,
    runFrom machine (budget bits) (cfg machine.start pre bits suffix 0)=some r ∧
      r.final=cfg r.final.control pre bits suffix 3 ∧ r.steps=budget bits := by
  obtain ⟨a,ha,af,as⟩ := phase_run pre bits suffix 0
  obtain ⟨b,hb,bf,bs⟩ := phase_run pre bits suffix 1
  obtain ⟨c,hc,cf,cs⟩ := phase_run pre bits suffix 2
  have he1 : Composition.restart a.final (phase 1).start=cfg (phase 1).start pre bits suffix 1 := by
    rw [af]; rfl
  have hab := Composition.run_join (phase 0) (phase 1) _ _ _ a b ha (by rw [he1]; exact hb)
  let ab := Composition.joinedReceipt a b
  have abf : ab.final=cfg ab.final.control pre bits suffix 2 := by
    dsimp only [ab,Composition.joinedReceipt]
    rw [bf]
    rfl
  have he2 : Composition.restart ab.final (phase 2).start=cfg (phase 2).start pre bits suffix 2 := by
    rw [abf]; rfl
  have hall := Composition.run_join (Composition.machine (phase 0) (phase 1)) (phase 2) _ _ _ ab c hab (by rw [he2]; exact hc)
  have hf : ((4*(bits 0).length+4)+1+(4*(bits 1).length+4))+1+(4*(bits 2).length+4)=budget bits := by
    unfold budget; ring
  rw [hf] at hall
  refine ⟨_,hall,?_,?_⟩
  · dsimp only [Composition.joinedReceipt]
    rw [cf]
    rfl
  · change (a.steps+1+b.steps)+1+c.steps=budget bits
    rw [as,bs,cs]
    exact hf

end NearCubicWires.RepairSource.RecoverySourceClauseRead
