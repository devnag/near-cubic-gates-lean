import Proof.CaseAnalysis.RowsCircuitPadding
import Proof.CaseAnalysis.WitnessTermLoopDriver

/-! Literal existing term/circuit port identities. The raw circuit and
paid parser capacity are aliases; logical native output stays in its bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermPorts
open LocalBitMultitape CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (i : Fin 1703) : Fin 2532:=(i.castAdd 2).natAdd 827
theorem slot_extra (i : Fin 1703) (h1 : i≠1) (hC : i≠1694) : TermCircuitDock.slots i=extra i:=by
  apply Fin.ext
  have hn1:i.val≠1:=fun h=>h1 (Fin.ext h)
  have hnC:i.val≠1694:=fun h=>hC (Fin.ext h)
  simp only [TermCircuitDock.slots,extra,Fin.val_natAdd,Fin.val_castAdd,hn1,hnC,ite_false]

theorem holes_away (i : Fin 1703) (hi : i=1 ∨ i=1694) : ∀ j,TermCircuitDock.slots j≠extra i:=by
  intro j he
  have hv:=congrArg Fin.val he
  dsimp only [TermCircuitDock.slots,extra,Fin.val_natAdd,Fin.val_castAdd] at hv
  rcases hi with rfl|rfl <;> dsimp at hv
  all_goals split_ifs at hv <;> omega

theorem heads (pos : ℕ) (out native : List Bool) (i : Fin 1703) :
    TermRound.heads pos out (TermEnvironment.heads native) (TermCircuitDock.slots i)=
      CloseoutRowsCircuitColdEntry.heads native i:=by
  by_cases h1:i=1
  · subst i
    exact TermCommit.heads_core pos out 78
  by_cases hC:i=1694
  · subst i
    exact TermCommit.heads_core pos out 720
  rw [slot_extra i h1 hC]
  have eqval (a : Fin 1703) : i=a ↔ i.val=a.val:=Fin.ext_iff
  simp only [extra,TermRound.heads,Fin.addCases_right,TermEnvironment.heads,Fin.val_castAdd,
    CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads,eqval]
  split_ifs <;> first | rfl | omega

theorem tapes (P H core W L : ℕ) (bits out native : List Bool)
    (terms : Fin 725 → List Bool) (ambient : Fin 94 → List Bool)
    (hr : terms 78=ZeroPadding.pad P (frame bits)) (hc : terms 720=List.replicate P true)
    (i : Fin 1703) :
    TermRound.data P terms ambient out (TermEnvironment.tapes H core W L native) (TermCircuitDock.slots i)=
      CloseoutRowsCircuitPadding.input P H core W L bits native i:=by
  by_cases h1:i=1
  · subst i
    exact (TermCommit.data_core P terms ambient out 78).trans hr
  by_cases hC:i=1694
  · subst i
    exact (TermCommit.data_core P terms ambient out 720).trans hc
  rw [slot_extra i h1 hC]
  have eqval (a : Fin 1703) : i=a ↔ i.val=a.val:=Fin.ext_iff
  have hn1:i.val≠1:=fun h=>h1 (Fin.ext h)
  have hnC:i.val≠1694:=fun h=>hC (Fin.ext h)
  have hi:=i.isLt
  simp only [extra,TermRound.data,Fin.addCases_right,TermEnvironment.tapes,Fin.val_castAdd,
    CloseoutRowsCircuitPadding.input,eqval]
  split_ifs <;> first | rfl | omega

theorem environment_heads (native : List Bool) (i : Fin 1703) :
    TermEnvironment.heads native (i.castAdd 2)=CloseoutRowsCircuitColdEntry.heads native i:=by
  have eqval (a : Fin 1703) : i=a ↔ i.val=a.val:=Fin.ext_iff
  simp only [TermEnvironment.heads,Fin.val_castAdd,CloseoutRowsCircuitColdEntry.heads,
    CloseoutRowsCircuit.heads,eqval]
  split_ifs <;> first | rfl | omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermPorts
