import Proof.Hierarchy.CompetitorBankMergePadding
import Proof.Hierarchy.CompetitorBankMergeReplace

/-! Actual native35 merge boundary. W is physically copied from padded9;
the real padded n driver27 controls the pass. Native rawD30/reset31 then
clear/copy the temporary raw result back into bank19, preserving cursor32. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMergeDock
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorBankMerge
open CompetitorPlaneStream (oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 48) : Fin 87 :=
  if i=19 then 19 else if i=23 then 35 else if i=27 then 27 else if i=9 then 36
  else ⟨i.val+37,by omega⟩
def widthSlots : Fin 4 → Fin 87 := ![9,85,36,86]
def input (ambient : Fin 35 → List Bool) (second : List Bool) : Fin 87 → List Bool :=
  Fin.addCases (m := 35) (n := 52) (motive := fun _ => List Bool) ambient (fun i => if i=0 then second else [])
def heads (pos : ℕ) : Fin 87 → ℕ := fun i => if i=32 then pos else 0
noncomputable def widthProgram := RecoveryFocus.machine widthSlots ClockUnarySum.machine
noncomputable def tableProgram := RecoveryFocus.machine nativeSlots CompetitorBankMerge.machine
noncomputable def passProgram := Composition.machine widthProgram tableProgram
noncomputable def replaceProgram := CompetitorBankMergeReplace.program (45 : Fin 87) 19 30 31
noncomputable def machine := Composition.machine passProgram replaceProgram
def capacity := CompetitorPlanePacketPass.capacity
def passBudget (w n : ℕ) := 2*w+7+CompetitorBankMerge.budget w n
def budget (w n : ℕ) := passBudget w n+4*capacity w n+10

theorem native_injective : Function.Injective nativeSlots := by decide
theorem native_avoids (j : Fin 35) (h19 : j≠19) (h27 : j≠27) :
    ∀ i,nativeSlots i≠j.castAdd 52 := by
  exact (show ∀ j : Fin 35,j≠19 → j≠27 → ∀ i,nativeSlots i≠j.castAdd 52 by decide) j h19 h27

theorem pass_run (d w pos : ℕ) (xs : List Pair) (ambient : Fin 35 → List Bool)
    (hw : ambient 9=ZeroPadding.pad d (List.replicate w true))
    (hn : ambient 27=ZeroPadding.pad d (CompareMachine.word xs.length))
    (hsource : ambient 19=ZeroPadding.pad d (leftWords w xs)) (hv : ∀ a∈xs,Valid w a.1 a.2) :
    ∃ r,runFrom passProgram (passBudget w xs.length)
      (RecoveryCalls.restarted passProgram (heads pos) (input ambient (rightWords w xs)))=some r ∧
      r.steps≤passBudget w xs.length ∧ r.final.heads=heads pos ∧
      r.final.tapes 45=mergedWords w xs ∧ r.final.tapes 35=rightWords w xs ∧
      (∀ i : Fin 35,r.final.tapes (i.castAdd 52)=ambient i) := by
  have hwi : ∀ i,input ambient (rightWords w xs) (widthSlots i)=CompetitorResidueTable.widthInput d w i := by
    intro i
    fin_cases i
    · exact hw
    · rfl
    · rfl
    · rfl
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorReusableDecision.bounded_focused_run widthSlots (by decide)
    _ _ _ (CompetitorResidueTable.width_copy_run d w) (heads pos) (input ambient (rightWords w xs))
    (by intro i; fin_cases i <;> rfl) hwi
  let middle := install widthSlots (input ambient (rightWords w xs)) (CompetitorResidueTable.widthOutput d w)
  have middleOriginal (i : Fin 35) : middle (i.castAdd 52)=ambient i := by
    by_cases hi : i=9
    · subst i
      exact (install_slot widthSlots (by decide) _ (CompetitorResidueTable.widthOutput d w) 0).trans hw.symm
    · have hn9 : i.val≠9 := fun h => hi (Fin.ext h)
      have hk : ∀ j,widthSlots j≠i.castAdd 52 := by
        intro j hj
        have hv' := congrArg (fun a : Fin 87 => a.val) hj
        fin_cases j <;> simp [widthSlots] at hv' <;> omega
      have he := install_other widthSlots (input ambient (rightWords w xs)) (CompetitorResidueTable.widthOutput d w) (i.castAdd 52) hk
      simpa only [middle,input,Fin.addCases_left] using he
  have middleLocal (i : Fin 48) : middle (nativeSlots i)=
      if i=9 then List.replicate w true else input ambient (rightWords w xs) (nativeSlots i) := by
    by_cases hi : i=9
    · subst i
      exact install_slot widthSlots (by decide) _ (CompetitorResidueTable.widthOutput d w) 2
    · rw [if_neg hi]
      apply install_other
      intro j hj
      fin_cases j
      · exact (show ∀ i,nativeSlots i≠9 by decide) i hj.symm
      · exact (show ∀ i,nativeSlots i≠85 by decide) i hj.symm
      · exact hi ((show ∀ i,nativeSlots i=36 → i=9 by decide) i hj.symm)
      · exact (show ∀ i,nativeSlots i≠86 by decide) i hj.symm
  let suffixA := List.replicate (d-(leftWords w xs).length) false
  obtain ⟨produced,hready,h8,h19,h23,h9,h27⟩ := padded_run d w xs suffixA [] hv
  have hti : ∀ i,middle (nativeSlots i)=paddedInput d w xs.length (leftWords w xs++suffixA) (rightWords w xs++[]) i := by
    intro i
    rw [middleLocal]
    fin_cases i <;> simp [nativeSlots,input,paddedInput,driverPadding,readyInput,
      CompetitorBankMerge.input,Fin.addCases,hn,hsource,ZeroPadding.pad,suffixA]
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorReusableDecision.bounded_focused_run nativeSlots native_injective
    _ _ _ hready (heads pos) middle (by
      intro i
      have hn32 : nativeSlots i≠32 := (show ∀ i,nativeSlots i≠32 by decide) i
      simp [heads,hn32]) hti
  have he : Composition.restart first.final tableProgram.start=
      RecoveryCalls.restarted tableProgram (heads pos) middle := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom tableProgram (CompetitorBankMerge.budget w xs.length)
      (Composition.restart first.final tableProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join widthProgram tableProgram _ _ _ first last hfirst hl'
  have hc : (2*w+6)+1+CompetitorBankMerge.budget w xs.length=passBudget w xs.length := by unfold passBudget; omega
  rw [hc] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,?_,?_,?_⟩
  · change first.steps+1+last.steps≤passBudget w xs.length
    omega
  · change last.final.tapes 45=mergedWords w xs
    rw [hlt]
    exact (install_slot nativeSlots native_injective middle produced 8).trans h8
  · change last.final.tapes 35=rightWords w xs
    rw [hlt]
    exact (install_slot nativeSlots native_injective middle produced 23).trans (by simpa using h23)
  · intro i
    change last.final.tapes (i.castAdd 52)=ambient i
    rw [hlt]
    by_cases hi : i=19
    · subst i
      exact (install_slot nativeSlots native_injective middle produced 19).trans (h19.trans hsource.symm)
    · by_cases hj : i=27
      · subst i
        exact (install_slot nativeSlots native_injective middle produced 27).trans (h27.trans hn.symm)
      · exact (install_other nativeSlots middle produced (i.castAdd 52) (native_avoids i hi hj)).trans (middleOriginal i)

theorem dock_run (w pos : ℕ) (xs : List Pair) (ambient : Fin 35 → List Bool)
    (hw : ambient 9=ZeroPadding.pad (capacity w xs.length) (List.replicate w true))
    (hn : ambient 27=ZeroPadding.pad (capacity w xs.length) (CompareMachine.word xs.length))
    (hsource : ambient 19=ZeroPadding.pad (capacity w xs.length) (leftWords w xs))
    (hd : ambient 30=List.replicate (capacity w xs.length) true)
    (hreset : ambient 31=List.replicate (capacity w xs.length+1) false)
    (hv : ∀ a∈xs,Valid w a.1 a.2) :
    ∃ r,runFrom machine (budget w xs.length)
      (RecoveryCalls.restarted machine (heads pos) (input ambient (rightWords w xs)))=some r ∧
      r.steps≤budget w xs.length ∧ r.final.heads=heads pos ∧
      r.final.tapes 19=ZeroPadding.pad (capacity w xs.length) (mergedWords w xs) ∧
      r.final.tapes 35=rightWords w xs ∧
      (∀ i : Fin 35,i≠19 → r.final.tapes (i.castAdd 52)=ambient i) := by
  obtain ⟨first,hfirst,hfs,hfh,h45,h35,hkeep⟩ := pass_run (capacity w xs.length) w pos xs ambient hw hn hsource hv
  have hcapacity : xs.length*(2*w)≤capacity w xs.length :=
    (CompetitorPlanePaddedEntry.capacity_bounds w xs.length).2.1
  have hlen : (mergedWords w xs).length≤capacity w xs.length := by
    simpa [mergedWords,mergedCells,CompetitorPlanePaddedEntry.old_length] using
      hcapacity
  have hleft : (leftWords w xs).length≤capacity w xs.length := by
    simpa [leftWords,CompetitorPlanePaddedEntry.old_length] using
      hcapacity
  have hback : (ZeroPadding.pad (capacity w xs.length) (leftWords w xs)).length≤capacity w xs.length := by
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl hleft
  have hti : ∀ i,first.final.tapes (CompetitorBankMergeReplace.copySlots (45 : Fin 87) 19 30 31 i)=
      ![mergedWords w xs,ZeroPadding.pad (capacity w xs.length) (leftWords w xs),
        List.replicate (capacity w xs.length) true,List.replicate (capacity w xs.length+1) false] i := by
    intro i
    fin_cases i
    · exact h45
    · exact (hkeep 19).trans hsource
    · exact (hkeep 30).trans hd
    · exact (hkeep 31).trans hreset
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorBankMergeReplace.replace_run (45 : Fin 87) 19 30 31
    (by decide) (mergedWords w xs) (ZeroPadding.pad (capacity w xs.length) (leftWords w xs))
    (capacity w xs.length) (heads pos) first.final.tapes hlen hback (by intro i; fin_cases i <;> rfl) hti
  have he : Composition.restart first.final replaceProgram.start=
      RecoveryCalls.restarted replaceProgram (heads pos) first.final.tapes := by
    apply configuration_ext
    · rfl
    · exact hfh
    · rfl
  have hl' : runFrom replaceProgram (4*capacity w xs.length+9)
      (Composition.restart first.final replaceProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join passProgram replaceProgram _ _ _ first last hfirst hl'
  have htime : passBudget w xs.length+1+(4*capacity w xs.length+9)=budget w xs.length := by unfold budget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget w xs.length
    omega
  · change last.final.tapes 19=_
    rw [hlt]
    exact Function.update_self ..
  · change last.final.tapes 35=_
    rw [hlt,Function.update_of_ne (by decide : (35 : Fin 87)≠19)]
    exact h35
  · intro i hi
    change last.final.tapes (i.castAdd 52)=_
    rw [hlt,Function.update_of_ne (show i.castAdd 52≠19 from fun h => hi (Fin.ext (congrArg (fun j : Fin 87 => j.val) h)))]
    exact hkeep i

theorem budget_bound (w n : ℕ) : budget w n≤500000*(n+1)*(w+1)^2 := by
  have hb := CompetitorBankMerge.budget_bound w n
  have hw : w≤(w+1)^2 := by nlinarith
  have hu : 1≤(w+1)^2 := by nlinarith
  have hn := Nat.mul_le_mul_left n hu
  unfold budget passBudget capacity CompetitorPlanePacketPass.capacity CompetitorPlaneReusable.capacity
    CompetitorPlanePaddedEntry.capacity CompetitorPlaneSign.budget CompetitorPlaneEntry.readyBudget
    CompetitorPlaneEntry.budget CompetitorPlaneStream.planeBudget CompetitorPlaneStream.bodyBudget CompetitorPlane.capacity
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorBankMergeDock
