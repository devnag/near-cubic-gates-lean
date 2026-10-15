import Proof.CaseAnalysis.RowsCheckedInteger
import Proof.CaseAnalysis.WitnessPaddedReset

/-! Reuse one checked integer workspace while retaining the forward native
output cursor. The same polynomial capacity pays every touched work tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerReady
open LocalBitMultitape RadixSemantics CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 214):=decide (i≠213)
def capacity (w : ℕ):=1000000000000000000000*(w+1)^24
def budget (bits : List Bool):=2*CloseoutRowsCheckedInteger.budget bits+2
noncomputable def machine:=MaskedReset.machine CloseoutRowsCheckedInteger.machine selected
noncomputable def entry (w : ℕ) (bits out : List Bool):=
  PaddedReset.entry selected (capacity w) (CloseoutRowsCheckedInteger.entry bits [] out)

theorem raw_heads (bits out : List Bool) (i : Fin 214) (hi : i≠213) :
    (CloseoutRowsCheckedInteger.entry bits [] out).heads i=0:=by
  revert hi
  refine Fin.addCases (m:=212) (n:=2) ?_ ?_ i
  · intro j _
    simp only [CloseoutRowsCheckedInteger.entry,Composition.leftConfig,TapeEmbedding.config,
      Fin.addCases_left,initialConfiguration]
  · intro j hj
    fin_cases j
    · rfl
    · exact False.elim (hj rfl)

theorem field_input (bits : List Bool) (i : Fin 203) :
    CloseoutRowsIntegerFields.input bits i=if i.val=0 then frame bits else []:=by
  fin_cases i <;> rfl
theorem guard_input (bits : List Bool) (i : Fin 212) :
    CloseoutRowsIntegerGuard.input bits i=if i.val=0 then frame bits else []:=by
  fin_cases i <;> rfl

theorem input_length (bits out : List Bool) (i : Fin 214) (hi : i≠213) :
    ((CloseoutRowsCheckedInteger.entry bits [] out).tapes i).length ≤ 2*bits.length+1:=by
  revert hi
  refine Fin.addCases (m:=212) (n:=2) ?_ ?_ i
  · intro j _
    simp only [CloseoutRowsCheckedInteger.entry,Composition.leftConfig,TapeEmbedding.config,
      Fin.addCases_left,initialConfiguration]
    rw [guard_input]
    split_ifs <;> simp [frame_length]
  · intro j hj
    fin_cases j
    · change ((CloseoutRowsCheckedInteger.entry bits [] out).tapes ((0 : Fin 2).natAdd 212)).length ≤ _
      simp only [CloseoutRowsCheckedInteger.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_right]
      change 0 ≤ 2*bits.length+1
      omega
    · exact False.elim (hj rfl)

theorem budget_bound (w : ℕ) (bits : List Bool) (hw : bits.length ≤ w) :
    budget bits+2*bits.length+2 ≤ capacity w:=by
  have hp:=Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 24
  have hlin:w+1 ≤ (w+1)^24:=Nat.le_self_pow (by decide) _
  have hpos:1 ≤ (w+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold budget capacity CloseoutRowsCheckedInteger.budget CloseoutRowsIntegerGuard.budget
    CloseoutRowsIntegerFields.budget
  omega

theorem integer_run (w : ℕ) (bits out : List Bool) (hw : bits.length ≤ w) : ∃ r,
    runFrom machine (budget bits) (entry w bits out)=some r ∧ r.steps ≤ budget bits ∧
      r.final.tapes 213=out++CloseoutRowsCheckedInteger.produced bits ∧
      r.final.heads 213=(out++CloseoutRowsCheckedInteger.produced bits).length ∧
      (readTapeBit (r.final.tapes 211) 0=true ↔ (CanonicalBinary.decodeInt (value bits)).isSome) ∧
      (∀ i : Fin 215,i≠213 → r.final.heads i=0 ∧ (r.final.tapes i).length ≤ capacity w):=by
  obtain ⟨raw,hr,rs,rt,rh,_,_,rf,_⟩:=CloseoutRowsCheckedInteger.native_run bits [] out
  have hb:=budget_bound w bits hw
  obtain ⟨r,hrun,rsteps,rheads,rtapes,rlength,lastHead,lastTape⟩:=PaddedReset.reset_run
    CloseoutRowsCheckedInteger.machine selected _ (capacity w) _ raw hr
    (by intro i hi;exact raw_heads bits out i (of_decide_eq_true hi))
    (by intro i hi;exact (input_length bits out i (of_decide_eq_true hi)).trans (by omega))
    (by unfold budget at hb;omega)
  have ht:2*raw.steps+2 ≤ budget bits:=by unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget bits-(2*raw.steps+2)) (entry w bits out) r hrun
  rw [Nat.add_sub_of_le ht] at more
  have outSlot:(213 : Fin 214).castAdd 1=(213 : Fin 215):=by decide
  refine ⟨r,more,rsteps.le.trans ht,?_,?_,?_,?_⟩
  · simpa only [PaddedReset.pads,selected,ne_eq,not_true_eq_false,decide_false,if_false,
      ZeroPadding.pad_zero,outSlot] using (rtapes 213).trans (congrArg (ZeroPadding.pad 0) rt)
  · simpa only [selected,ne_eq,not_true_eq_false,decide_false,if_false,outSlot] using (rheads 213).trans rh
  · change readTapeBit (r.final.tapes ((211 : Fin 214).castAdd 1)) 0=true ↔ _
    rw [rtapes,ZeroPadding.read_pad]
    exact rf
  · intro i
    refine Fin.addCases (m:=214) (n:=1) ?_ ?_ i
    · intro j hj
      have h:j≠213:=by intro he;subst j;exact hj rfl
      exact ⟨by simpa only [selected,decide_eq_true h,if_true] using rheads j,
        rlength j (decide_eq_true h)⟩
    · intro j _
      have hj:j=0:=Fin.eq_zero j
      subst j
      exact ⟨lastHead,by simpa only [lastTape,List.length_replicate] using (Nat.le_refl (capacity w))⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerReady
