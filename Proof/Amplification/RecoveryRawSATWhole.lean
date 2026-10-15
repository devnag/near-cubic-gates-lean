import Proof.Amplification.RecoveryRawSATLeaf

/-! Whole raw-SAT clause body. The initial clear and outer-presence gate
are executed, and every accepting return contains the actual reusable
clause evaluator output paired with the consumed outer-code bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cell_cost (x : State) (word : List Bool) (hx : x.Valid word) :
    RecoveryStoredListCell.time x.outer.bits ≤ 262144*(x.width+1)^2 := by
  have h := RecoveryStoredListCell.time_bound x.outer.bits
  unfold RecoveryStoredListCell.budget at h
  rw [hx.2.2.2] at h
  exact h

theorem body_trace (x : State) (word : List Bool) (hx : x.Valid word) :
    ∃ n output,n ≤ budget x.width ∧ output 27=[answer x word] ∧
      Timed machine n (initialConfiguration machine x.tapes)
        (RecoveryCalls.stopped sizes (fun _=>0) output) ∧
      (answer x word=true → ∃ out : AcceptedResult x word,output=out.data.tapes) := by
  have hclear := (clear_ready x).call sizes programs 0 next 0 1 (by intro q; rfl)
  have houter := outer_ready (cleared x) hx.2.2.1
  have hcell := cell_cost x word hx
  by_cases hz : RadixSemantics.value x.outer.bits=0
  · have hstop := houter.stop sizes programs 0 next 1 (by
      intro q
      change (if (x.outer.after 0).flag then some (2 : Fin 4) else none)=none
      rw [RecoveryThreeCellReader.after_flag]
      simp [hz])
    have h := hclear.trans hstop
    have hanswer : answer x word=false := by simp [answer,hz]
    refine ⟨2+(RecoveryStoredListCell.time x.outer.bits+1),(outerStep (cleared x)).tapes,?_,?_,h,?_⟩
    · unfold budget
      nlinarith only [hcell,show 0<(x.width+1)^2 by positivity]
    · rw [hanswer]
      rfl
    · simp only [hanswer,Bool.false_eq_true,IsEmpty.forall_iff]
  · have hread := houter.call sizes programs 0 next 1 2 (by
      intro q
      change (if (x.outer.after 0).flag then some (2 : Fin 4) else none)=some 2
      rw [RecoveryThreeCellReader.after_flag]
      simp [hz])
    have hcopy := (copy_ready (outerStep (cleared x)) (headWord x) (head_width x word hx)
      (prepared_field x hz)).call sizes programs 0 next 2 3 (by intro q; rfl)
    obtain ⟨n,output,hn,ht,hcheck,hreturn⟩ := leaf_trace x word hx hz
    have h := (hclear.trans hread).trans (hcopy.trans hcheck)
    have hanswer : answer x word=leafAnswer x word := by simp [answer,hz]
    refine ⟨(2+(RecoveryStoredListCell.time x.outer.bits+1))+(8*(headWord x).length+8+1+n),
      output,?_,ht.trans (congrArg (fun bit : Bool=>[bit]) hanswer.symm),h,?_⟩
    · rw [head_width x word hx]
      unfold budget
      nlinarith only [hcell,hn,show 0<(x.width+1)^2 by positivity]
    · intro ha
      exact hreturn (hanswer.symm.trans ha)

theorem body_run (x : State) (word : List Bool) (hx : x.Valid word) :
    ∃ r,run machine (budget x.width) x.tapes=some r ∧ r.steps ≤ budget x.width ∧
      (∀ i,r.final.heads i=0) ∧ r.final.tapes 27=[answer x word] ∧
      (answer x word=true → ∃ out : AcceptedResult x word,r.final.tapes=out.data.tapes) := by
  obtain ⟨n,output,hn,ht,h,hreturn⟩ := body_trace x word hx
  obtain ⟨r,hr,hf,hsteps⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := run_moreFuel machine n (budget x.width-n) x.tapes r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,?_,?_,?_⟩
  · intro i; rw [hf]; rfl
  · rw [hf]; exact ht
  · intro ha
    obtain ⟨out,he⟩ := hreturn ha
    exact ⟨out,by rw [hf]; exact he⟩

end NearCubicWires.RepairOrdinary.RecoveryRawSAT
