import Proof.Hierarchy.CompetitorMonomialPrepare

/-! Exact docking of the paid monomial-record preparation to the accepted
native multiplication/widening/append run, retaining both ambient cursors
and the next iteration's physical scratch-support bound. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlot (i : Fin 79) : Fin 88 := i.castAdd 9
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlot CompetitorMonomialTarget.machine

theorem native_injective : Function.Injective nativeSlot := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 88 => a.val) h)
theorem native_other (j : Fin 79) (i : Fin 88) (hi : 79 ≤ i.val) : nativeSlot j≠i := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=i.val at hv
  omega

def inputValues (b t : ℕ) (q : ℚ) (count denominator : ℕ) (output : List Bool) (i : Fin 79) : List Bool :=
  if i.val=5 then ZeroPadding.pad (capacity t) (frame (binary b count))
  else if i.val=4 then ZeroPadding.pad (capacity t) (frame (binary b denominator))
  else if i.val=3 then ZeroPadding.pad (capacity t) (frame (binary (width b) 0))
  else if i.val=2 then ZeroPadding.pad (capacity t) (frame (binary (width b) q.den))
  else if i.val=1 then ZeroPadding.pad (capacity t) (frame (binary (width b) (negative q)))
  else if i.val=0 then ZeroPadding.pad (capacity t) (frame (binary (width b) (positive q)))
  else if i.val=75 then ZeroPadding.pad (capacity t) (List.replicate t true)
  else if i.val=67 then ZeroPadding.pad (capacity t) (List.replicate (width t) true)
  else if i.val=6 then ZeroPadding.pad (capacity t) (List.replicate (width b) true)
  else if i.val=74 then output else List.replicate (capacity t) false

theorem native_input_cases (b t : ℕ) (q : ℚ) (count denominator : ℕ) (output : List Bool) (i : Fin 79) :
    CompetitorMonomialTarget.paddedInput b t q count denominator output i=inputValues b t q count denominator output i := by
  fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _

theorem prepared_native (b t : ℕ) (q : ℚ) (count denominator : ℕ) (output : List Bool)
    (ambient : Fin 88 → List Bool) (hout : ambient 74=output) (i : Fin 79) :
    prepared b t q count denominator ambient (nativeSlot i)=CompetitorMonomialTarget.paddedInput b t q count denominator output i := by
  rw [native_input_cases,prepared_cases,widened_cases]
  have hclean : clean t ambient (nativeSlot i)=if i.val=74 then output else List.replicate (capacity t) false := by
    by_cases he : i.val=74
    · have hi : nativeSlot i=74 := Fin.ext he
      rw [if_pos he,hi]
      exact (clear_keep t ambient 74 (by simp)).trans hout
    · rw [if_neg he]
      apply clear_cell
      left
      exact ⟨i.isLt,fun h => he (congrArg Fin.val h)⟩
  rw [hclean]
  simp only [nativeSlot,Fin.val_castAdd,inputValues]
  rfl

theorem prepared_reset (b t : ℕ) (q : ℚ) (count denominator : ℕ) (ambient : Fin 88 → List Bool)
    (i : Fin 88) (hi : i=80 ∨ i=86 ∨ i=87) :
    prepared b t q count denominator ambient i=List.replicate (capacity t) false := by
  rw [prepared_cases,widened_cases]
  have hv : i.val=80 ∨ i.val=86 ∨ i.val=87 := by rcases hi with rfl|rfl|rfl <;> decide
  simp only [show i.val≠5 by omega,show i.val≠4 by omega,show i.val≠3 by omega,
    show i.val≠2 by omega,show i.val≠1 by omega,show i.val≠0 by omega,
    show i.val≠75 by omega,show i.val≠67 by omega,show i.val≠6 by omega,if_false]
  apply clear_cell
  exact Or.inr hi

theorem native_heads {s : ℕ} (q : Fin s) (oldOutput output : List Bool) (pos : ℕ)
    (ambient : Fin 88 → List Bool) (localTapes : Fin 79 → List Bool) :
    (RecoveryFocus.config nativeSlot (heads oldOutput.length pos) ambient
      (⟨q,CompetitorMonomialTarget.targetHeads output,localTapes⟩ : Configuration 79 s)).heads=heads output.length pos := by
  funext i
  by_cases hi : i.val<79
  · let j : Fin 79 := ⟨i.val,hi⟩
    have he : nativeSlot j=i := Fin.ext rfl
    have hp : RecoveryFocus.pick nativeSlot i=some j := he ▸ RecoveryFocus.pick_slot nativeSlot native_injective j
    simp only [RecoveryFocus.config,hp]
    change (if j.val=74 then output.length else 0)=heads output.length pos i
    have hn79 : i.val≠79 := by omega
    simp [heads,hn79,j]
  · have hn : ¬∃ j,nativeSlot j=i := by rintro ⟨j,hj⟩; exact native_other j i (by omega) hj
    simp only [RecoveryFocus.config,RecoveryFocus.pick,hn,↓reduceDIte]
    simp [heads,show i.val≠74 by omega]

theorem native_run (b t pos : ℕ) (q : ℚ) (count denominator : ℕ) (source output : List Bool)
    (ambient : Fin 88 → List Bool) (h : Store b t source output ambient)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t)
    (hout : output.length≤100*(t+1)^2) :
    ∃ r,runFrom nativeProgram (CompetitorMonomialTarget.budget b t)
        (cfg output.length nativeProgram.start pos (prepared b t q count denominator ambient))=some r ∧
      r.steps≤CompetitorMonomialTarget.budget b t ∧
      r.final.heads=heads (output++CompetitorSumFold.termWord t (contribution q count denominator)).length pos ∧
      Store b t source (output++CompetitorSumFold.termWord t (contribution q count denominator)) r.final.tapes := by
  obtain ⟨base,out,hr,hs,hbt,hbh,hbo,hbound⟩ := CompetitorMonomialTarget.padded_record_run b t q count denominator output
    hp hn hq hc hd htarget hout
  let ready := prepared b t q count denominator ambient
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config nativeSlot native_injective CompetitorMonomialTarget.machine
    (heads output.length pos) ready _ _ base hr
  have hi : RecoveryFocus.config nativeSlot (heads output.length pos) ready
      (RecoveryCalls.restarted CompetitorMonomialTarget.machine (CompetitorMonomialTarget.targetHeads output)
        (CompetitorMonomialTarget.paddedInput b t q count denominator output))=
      cfg output.length nativeProgram.start pos ready := by
    apply configuration_ext
    · rfl
    · exact native_heads _ _ _ _ _ _
    · exact install_existing nativeSlot ready _ (prepared_native b t q count denominator output ambient h.output)
  rw [hi] at hrun
  have ht : r.final.tapes=install nativeSlot ready out := by rw [hfinal]; change install nativeSlot ready base.final.tapes=_; rw [hbt]
  have keep (i : Fin 88) (hval : 79 ≤ i.val) : r.final.tapes i=ready i := by
    rw [ht]
    exact install_other nativeSlot ready out i (fun j => native_other j i hval)
  have hpreserve (i : Fin 88) (hval : 79 ≤ i.val)
      (hkeep : i=79 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85) : r.final.tapes i=ambient i :=
    (keep i hval).trans (prepared_keep b t q count denominator ambient i (Or.inr hkeep))
  refine ⟨r,hrun,hsteps.trans_le hs,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hfinal]
    have hbconfig : base.final=⟨base.final.control,CompetitorMonomialTarget.targetHeads
        (output++CompetitorSumFold.termWord t (contribution q count denominator)),out⟩ := by
      apply configuration_ext
      · rfl
      · exact hbh
      · exact hbt
    rw [hbconfig]
    exact native_heads _ _ _ _ _ _
  · exact (hpreserve 79 (by decide) (by simp)).trans h.source
  · rw [ht]
    exact (install_slot nativeSlot native_injective ready out 74).trans hbo
  · exact (hpreserve 81 (by decide) (by simp)).trans h.inputWidth
  · exact (hpreserve 82 (by decide) (by simp)).trans h.targetWidth
  · exact (hpreserve 83 (by decide) (by simp)).trans h.shortWidth
  · exact (hpreserve 84 (by decide) (by simp)).trans h.eraseDriver
  · exact (hpreserve 85 (by decide) (by simp)).trans h.eraseReset
  · intro j
    rcases work_range j with ⟨hj,_⟩|he|he|he
    · let i : Fin 79 := ⟨(workSlot j).val,hj⟩
      have he : nativeSlot i=workSlot j := Fin.ext rfl
      rw [ht,← he,install_slot nativeSlot native_injective]
      exact hbound i
    all_goals
      rw [he,keep _ (by omega)]
      dsimp only [ready]
      rw [prepared_reset b t q count denominator ambient _ (by simp),List.length_replicate]

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
