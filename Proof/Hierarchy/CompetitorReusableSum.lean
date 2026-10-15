import Proof.Hierarchy.CompetitorRationalSum

/-! Reusable bounded workspace for the literal rational fold. The native
addition runs on physically retained zero padding, and copying a result back
to a cleared accumulator uses an actual framed copy with both resets paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorReusableSum
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (b : ℕ) (i : Fin 88) := if i.val=6 ∨ i.val=84 then 0 else capacity b
def paddedInput (b : ℕ) (a c : CompetitorValidity.Estimate) : Fin 88 → List Bool :=
  fun i => ZeroPadding.pad (padding b i) (CompetitorRationalSum.input b a c i)

theorem input_support (b : ℕ) (a c : CompetitorValidity.Estimate) (i : Fin 88) :
    (CompetitorRationalSum.input b a c i).length≤capacity b := by
  unfold CompetitorRationalSum.input
  split
  · exact CompetitorReusableDecision.input_support b _ _ _ _
  · split
    · simp only [List.length_replicate]
      unfold capacity
      nlinarith
    · simp

theorem padded_sum_run (b : ℕ) (a c : CompetitorValidity.Estimate)
    (ha : a.Valid b) (hc : c.Valid b) :
    ∃ out,ClockJoin.ReadyRun CompetitorRationalSum.machine (3000*(b+1)^2)
      (paddedInput b a c) out ∧
      (∀ i,(out i).length≤capacity b) ∧
      out 63=ZeroPadding.pad (capacity b) (frame (binary (width b) (CompetitorRationalNumerators.add a c).positive)) ∧
      out 64=ZeroPadding.pad (capacity b) (frame (binary (width b) (CompetitorRationalNumerators.add a c).negative)) ∧
      out 85=ZeroPadding.pad (capacity b) (frame (binary b (CompetitorRationalNumerators.add a c).denominator)) ∧
      out 6=List.replicate (width b) true ∧ out 84=List.replicate b true := by
  obtain ⟨raw,hraw,h63,h64,h85,h6,h84⟩ := CompetitorRationalSum.rational_sum_run b a c ha hc
  obtain ⟨base,hr,ht,hh,hs⟩ := hraw
  have hsupport := RecoveryTapeSupport.run_support CompetitorRationalSum.machine _ _ base hr (capacity b) 0
    (by intro i; exact Nat.zero_le _) (by
      intro i
      exact (input_support b a c i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 88) : (base.final.tapes i).length≤capacity b := by
    have hm : base.steps+1≤capacity b := by
      have hp : 0<(b+1)^2 := by positivity
      unfold capacity
      omega
    simpa only [Nat.zero_add,max_eq_left hm] using hsupport i
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config CompetitorRationalSum.machine (padding b) _ _ base hr
  have hi : ZeroPadding.config (padding b)
      (initialConfiguration CompetitorRationalSum.machine (CompetitorRationalSum.input b a c))=
      initialConfiguration CompetitorRationalSum.machine (paddedInput b a c) := rfl
  rw [hi] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold padding; split <;> omega) (hbound i)
  · simpa only [hf,ZeroPadding.config,padding,show ¬((63 : Fin 88).val=6 ∨ (63 : Fin 88).val=84) by decide,
      if_false,ht] using congrArg (ZeroPadding.pad (capacity b)) h63
  · simpa only [hf,ZeroPadding.config,padding,show ¬((64 : Fin 88).val=6 ∨ (64 : Fin 88).val=84) by decide,
      if_false,ht] using congrArg (ZeroPadding.pad (capacity b)) h64
  · simpa only [hf,ZeroPadding.config,padding,show ¬((85 : Fin 88).val=6 ∨ (85 : Fin 88).val=84) by decide,
      if_false,ht] using congrArg (ZeroPadding.pad (capacity b)) h85
  · simpa [hf,ZeroPadding.config,padding,ht] using h6
  · simpa [hf,ZeroPadding.config,padding,ht] using h84

theorem padded_copy_run (bits : List Bool) (cap : ℕ) (hc : 4*bits.length+3≤cap) :
    ClockJoin.ReadyRun copyMachine (8*bits.length+8)
      ![ZeroPadding.pad cap (frame bits),List.replicate cap false,
        List.replicate cap false,List.replicate cap false]
      ![ZeroPadding.pad cap (frame bits),ZeroPadding.pad cap (frame bits),
        List.replicate cap false,List.replicate cap false] := by
  obtain ⟨base,hr,ht,hh,hs⟩ := copy_ready bits [] cap cap (by simp)
  have hc' : 2*bits.length+1≤cap := by omega
  simp only [max_eq_left hc',max_eq_left hc] at ht
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config copyMachine (fun _ => cap) _ _ base hr
  have hi : ZeroPadding.config (fun _ : Fin 4 => cap)
      (initialConfiguration copyMachine ![frame bits,[],List.replicate cap false,List.replicate cap false])=
      initialConfiguration copyMachine ![ZeroPadding.pad cap (frame bits),List.replicate cap false,
        List.replicate cap false,List.replicate cap false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs.le⟩
  · rw [hf]
    change (fun i => ZeroPadding.pad cap (base.final.tapes i))=_
    rw [ht]
    funext i
    fin_cases i <;> simp [pad_zeros]
  · intro i
    rw [hf]
    exact hh i

end NearCubicWires.RepairOrdinary.CompetitorReusableSum
