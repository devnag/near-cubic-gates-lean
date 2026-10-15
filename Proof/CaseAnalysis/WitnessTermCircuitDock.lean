import Proof.CaseAnalysis.WitnessTermCircuitReset

/-! The circuit reader directly aliases the retained term payload and
shared internal driver. Every other term/mass field remains outside its
bank; the supplied receipt is the actual circuit call, not a new parser. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1703) : Fin 2532 :=
  ⟨if i.val=1 then 78 else if i.val=1694 then 720 else 827+i.val,by split_ifs <;> omega⟩

theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem term_away (i : Fin 827) (hi : i.val≠78 ∧ i.val≠720) :
    ∀ j,slots j≠i.castAdd 1705 := by
  intro j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  dsimp only [slots,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega

theorem reset_away (i : Fin 2) : ∀ j,slots j≠i.natAdd 2530 := by
  intro j h
  have hv := congrArg (fun k : Fin 2532=>k.val) h
  dsimp only [slots,Fin.val_natAdd] at hv
  split_ifs at hv <;> omega

theorem call_run {s : ℕ} (worker : Machine 1703 s) (fuel : ℕ)
    (heads : Fin 2532 → ℕ) (input : Fin 2532 → List Bool)
    (entry : Configuration 1703 s) (base : ExecutionReceipt 1703 s)
    (hh : ∀ i,heads (slots i)=entry.heads i)
    (ht : ∀ i,input (slots i)=entry.tapes i)
    (hr : runFrom worker fuel entry=some base)
    (hraw : base.final.heads 1=entry.heads 1 ∧ base.final.tapes 1=entry.tapes 1)
    (hdriver : base.final.heads 1694=entry.heads 1694 ∧ base.final.tapes 1694=entry.tapes 1694) :
    ∃ result,runFrom (RecoveryFocus.machine slots worker) fuel ⟨entry.control,heads,input⟩=some result ∧
      result.steps=base.steps ∧ result.final.control=base.final.control ∧
      (∀ i,result.final.heads (slots i)=base.final.heads i ∧
        result.final.tapes (slots i)=base.final.tapes i) ∧
      (∀ i : Fin 827,result.final.heads (i.castAdd 1705)=heads (i.castAdd 1705) ∧
        result.final.tapes (i.castAdd 1705)=input (i.castAdd 1705)) ∧
      (∀ i : Fin 2,result.final.heads (i.natAdd 2530)=heads (i.natAdd 2530) ∧
        result.final.tapes (i.natAdd 2530)=input (i.natAdd 2530)) := by
  obtain ⟨r,run,control,steps,rheads,rtapes,keep⟩ :=
    RecoveryFocus.dock slots slots_injective worker fuel heads input entry hh ht base hr
  refine ⟨r,run,steps,control,fun i=>⟨rheads i,rtapes i⟩,?_,fun i=>keep _ (reset_away i)⟩
  intro i
  by_cases h78 : i.val=78
  · have he : i.castAdd 1705=slots 1 := Fin.ext (by change i.val=78;exact h78)
    rw [he]
    exact ⟨(rheads 1).trans (hraw.1.trans (hh 1).symm),
      (rtapes 1).trans (hraw.2.trans (ht 1).symm)⟩
  by_cases h720 : i.val=720
  · have he : i.castAdd 1705=slots 1694 := Fin.ext (by change i.val=720;exact h720)
    rw [he]
    exact ⟨(rheads 1694).trans (hdriver.1.trans (hh 1694).symm),
      (rtapes 1694).trans (hdriver.2.trans (ht 1694).symm)⟩
  exact keep _ (term_away i ⟨h78,h720⟩)

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitDock
