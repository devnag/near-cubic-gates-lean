import Proof.PCP.PCPPNativeClauseRetained

/-! Execute one original literal, retain its raw reference, then physically
erase the entire field workspace. The returned bank is ready for reuse. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseReusable
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem coverage (i : Fin 23) :
    (i=4 ∨ i=5 ∨ i=6 ∨ i=13 ∨ i=19 ∨ i=20) ∨ ∃ j,eraseSlots j=i := by
  fin_cases i <;> decide

def budget (bits : List Bool) (index stride : ℕ) (sign : Bool) (p n C : ℕ) :=
  prefixBudget bits index stride sign p n+2*C+5

theorem field_run (pre bits tail : List Bool) (index : ℕ) (sign : Bool)
    (stride p n C : ℕ) (hv : value bits=2*index+sign.toNat)
    (hC : PCPPNativeClauseField.budget bits index sign stride p n+1 ≤ C) : ∃ r,
    runFrom machine (budget bits index stride sign p n C)
      (entry machine pre.length (data (pre++frame bits++tail) stride p n C []))=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes=data (pre++frame bits++tail) stride p n C
        (List.replicate (reference index stride sign p n) true) ∧
      r.steps ≤ budget bits index stride sign p n C := by
  obtain ⟨a,ha,ah,aret,awork,astep⟩ := prefix_run pre bits tail index sign stride p n C hv hC
  let backing : Fin 15→List Bool := fun j=>a.final.tapes (fieldSlots (workSlots j))
  have hin (j : Fin 17) : a.final.tapes (eraseSlots j)=
      (Fin.addCases (m:=16) (n:=1) (motive:=fun _ : Fin 17=>List Bool)
        (Fin.addCases (m:=15) (n:=1) (motive:=fun _ : Fin 16=>List Bool)
          backing (fun _=>List.replicate C true))
        (fun _=>List.replicate (C+1) false)) j := by
    fin_cases j
    all_goals first | rfl | exact aret 21 (by decide) | exact aret 22 (by decide)
  have hheads (j : Fin 17) : a.final.heads (eraseSlots j)=0 := by
    rw [ah]
    fin_cases j <;> rfl
  have ready := RecoveryScratchErase.erase_ready C (C+1) backing awork
  obtain ⟨b,hb,bh,bt,bs⟩ := ready.focus_at eraseSlots erase_injective a.final.heads a.final.tapes hin hheads
  have hall := Composition.run_join (Composition.machine first copyMachine) last _ _ _ a b ha hb
  have htime : prefixBudget bits index stride sign p n+1+(2*C+4)=budget bits index stride sign p n C := by
    unfold budget
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt a b,hall,bh.trans ah,?_,?_⟩
  · change b.final.tapes=_
    rw [bt]
    funext i
    rcases coverage i with hi|⟨j,rfl⟩
    · rw [install_other eraseSlots _ _ _ (erase_away i hi)]
      exact aret i (by rcases hi with h|h|h|h|h|h <;> subst i <;> decide)
    · rw [install_slot eraseSlots erase_injective]
      fin_cases j <;> simp only [max_self] <;> rfl
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.PCPPNativeClauseReusable
