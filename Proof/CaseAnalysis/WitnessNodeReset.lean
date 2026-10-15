import Proof.CaseAnalysis.WitnessNodeReadyLayout
import Proof.CaseAnalysis.WitnessPaddedReset

/-! The complete node reader now reuses one padded workspace and one recorded
reset, while preserving its forward native-descriptor cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeReady
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pads_eq (cap : ℕ) : PaddedReset.pads selected cap=pads cap:=by
  funext i
  by_cases hi:i=747 <;> simp [PaddedReset.pads,selected,pads,hi]

theorem node_run (w : ℕ) (left right bits out : List Bool)
    (hl : left.length=w) (hr : right.length=w) (hw : bits.length+1 ≤ w) : ∃ result,
    runFrom machine (budget w bits) (entry (capacity w) w left right bits out)=some result ∧
      result.steps ≤ budget w bits ∧
      result.final.tapes 747=NodeBody.appended bits out ∧
      result.final.heads 747=(NodeBody.appended bits out).length ∧
      (∀ i : Fin 749,i≠747 → result.final.heads i=0 ∧ (result.final.tapes i).length ≤ capacity w) ∧
      (readTapeBit (result.final.tapes 745) 0=true ↔ NodeMeaning.valid (value left) (value right) bits) ∧
      (∀ i,result.final.tapes ((NodeGuard.common i).castAdd 3)=
        ZeroPadding.pad (capacity w) (NodeGuard.shared w left right i)):=by
  obtain ⟨r,hrun,rs,rt,rh,rf,rc⟩:=NodeBody.raw_run w left right bits [] out hl hr hw
  have hb:=budget_bound w bits hw
  have hcap:NodeBody.budget w bits+1 ≤ capacity w:=by unfold budget at hb;omega
  obtain ⟨z,hz,zs,zh,zt,zl,zc,zct⟩:=PaddedReset.reset_run NodeBody.machine selected _ (capacity w) _ r hrun
    (by intro i hi;exact NodeBody.entry_heads _ _ _ _ _ _ i (of_decide_eq_true hi))
    (by
      intro i hi
      have h:=input_length w left right bits out hl hr hw i (of_decide_eq_true hi)
      have hp:w ≤ w^24:=Nat.le_self_pow (by decide) _
      unfold capacity
      omega)
    (by omega)
  simp only [PaddedReset.entry,pads_eq] at hz
  have htime:2*r.steps+2 ≤ budget w bits:=by unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget w bits-(2*r.steps+2))
    (entry (capacity w) w left right bits out) z hz
  rw [Nat.add_sub_of_le htime] at more
  have outSlot:(747 : Fin 748).castAdd 1=(747 : Fin 749):=by decide
  have lastSlot:(0 : Fin 1).natAdd 748=(748 : Fin 749):=by decide
  refine ⟨z,more,by omega,?_,?_,?_,?_,?_⟩
  · simpa only [PaddedReset.pads,selected,decide_false,ne_eq,not_true_eq_false,
      Bool.false_eq_true,if_false,ZeroPadding.pad_zero,rt,outSlot] using zt 747
  · simpa only [selected,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,if_false,rh,outSlot] using zh 747
  · intro i
    refine Fin.addCases (m:=748) (n:=1) ?_ ?_ i
    · intro j hj
      have hj':j≠747:=by intro he;subst j;exact hj rfl
      exact ⟨by simpa only [selected,decide_eq_true hj',if_true] using zh j,
        zl j (decide_eq_true hj')⟩
    · intro j _
      have hj:j=0:=Fin.eq_zero j
      subst j
      rw [lastSlot]
      exact ⟨by simpa only [lastSlot] using zc,
        by simpa only [lastSlot,List.length_replicate] using (congrArg List.length zct).le⟩
  · change readTapeBit (z.final.tapes ((745 : Fin 748).castAdd 1)) 0=true ↔ _
    rw [zt,ZeroPadding.read_pad]
    exact rf
  · intro i
    change z.final.tapes (((NodeGuard.common i).castAdd 2).castAdd 1)=_
    rw [zt,pads_eq,pads,if_neg (by fin_cases i <;> decide),(rc i).2]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeReady
