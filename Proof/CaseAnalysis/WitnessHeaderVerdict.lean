import Proof.CaseAnalysis.WitnessHeaderSwitch

/-! Project the selected physical verdict while controller state counts
remain symbolic. This is the existing switch receipt, with the same fuel. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderSwitch
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem accepted_flag {t a b c : ℕ} (p : Machine t a) (q : Machine t b) (r : Machine t c)
    (good mode : (Fin t→Bool)→Bool) (j : Fin 3) (hj:j=1 ∨ j=2) (pfuel fuel : ℕ)
    (heads : Fin t→ℕ) (data : Fin t→List Bool) (prior : ExecutionReceipt t a)
    (last : ExecutionReceipt t (sizes a b c j))
    (hp:runFrom p pfuel ⟨p.start,heads,data⟩=some prior)
    (hl:runFrom (programs p q r j) fuel
      (RecoveryCalls.restarted (programs p q r j) prior.final.heads prior.final.tapes)=some last)
    (hg:good prior.final.scanned=true) (hm:j=if mode prior.final.scanned then 1 else 2)
    (v : Fin t) (value : Bool) (hh:last.final.heads v=0) (ht:readTapeBit (last.final.tapes v) 0=value) :
    ∃ actual,runFrom (machine p q r good mode) (pfuel+1+fuel+1)
      ⟨(machine p q r good mode).start,heads,data⟩=some actual ∧
      actual.steps ≤ pfuel+1+fuel+1 ∧ actual.final.heads v=0 ∧
      readTapeBit (actual.final.tapes v) 0=value := by
  obtain ⟨actual,hr,hs,ah,tapes⟩:=accepted p q r good mode j hj pfuel fuel heads data prior last hp hl hg hm
  exact ⟨actual,hr,hs,(congrFun ah v).trans hh,
    (congrArg (fun ts=>readTapeBit (ts v) 0) tapes).trans ht⟩

theorem rejected_flag {t a b c : ℕ} (p : Machine t a) (q : Machine t b) (r : Machine t c)
    (good mode : (Fin t→Bool)→Bool) (fuel : ℕ) (heads : Fin t→ℕ) (data : Fin t→List Bool)
    (prior : ExecutionReceipt t a) (hp:runFrom p fuel ⟨p.start,heads,data⟩=some prior)
    (hg:good prior.final.scanned=false) (v : Fin t) (value : Bool)
    (hh:prior.final.heads v=0) (ht:readTapeBit (prior.final.tapes v) 0=value) :
    ∃ actual,runFrom (machine p q r good mode) (fuel+1)
      ⟨(machine p q r good mode).start,heads,data⟩=some actual ∧
      actual.steps ≤ fuel+1 ∧ actual.final.heads v=0 ∧
      readTapeBit (actual.final.tapes v) 0=value := by
  obtain ⟨actual,hr,hs,ah,tapes⟩:=rejected p q r good mode fuel heads data prior hp hg
  exact ⟨actual,hr,hs,(congrFun ah v).trans hh,
    (congrArg (fun ts=>readTapeBit (ts v) 0) tapes).trans ht⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.HeaderSwitch
