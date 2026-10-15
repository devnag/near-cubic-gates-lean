import Proof.Hierarchy.CompetitorSumClear

/-! Cold initial accumulator producer. Physical clearing provides every
retained zero cell consumed by the subsequent constant writers and fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def constantInput (b : ℕ) : Fin 88 → List Bool := fun i =>
  ZeroPadding.pad (CompetitorReusableSum.padding b i) (CompetitorSumConstants.input b i)

theorem constant_support (b : ℕ) (i : Fin 88) : (CompetitorSumConstants.input b i).length≤capacity b := by
  unfold CompetitorSumConstants.input
  split
  · simp only [List.length_replicate,width,capacity]
    nlinarith
  · split
    · simp only [List.length_replicate,capacity]
      nlinarith
    · simp

theorem padded_constants_run (b : ℕ) (hb : 1≤b) :
    ∃ out,ClockJoin.ReadyRun CompetitorSumConstants.machine (20*b+53) (constantInput b) out ∧
      (∀ i,(out i).length≤capacity b) ∧
      out 0=ZeroPadding.pad (capacity b) (frame (binary (width b) 0)) ∧
      out 1=ZeroPadding.pad (capacity b) (frame (binary (width b) 0)) ∧
      out 4=ZeroPadding.pad (capacity b) (frame (binary b 1)) ∧
      out 6=List.replicate (width b) true ∧ out 84=List.replicate b true := by
  obtain ⟨raw,hraw,h0,h1,h4,h6,h84⟩ := CompetitorSumConstants.constants_run b hb
  obtain ⟨base,hr,ht,hh,hs⟩ := hraw
  have hsupport := RecoveryTapeSupport.run_support CompetitorSumConstants.machine _ _ base hr (capacity b) 0
    (by intro i; exact Nat.zero_le _) (by intro i; exact (constant_support b i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 88) : (base.final.tapes i).length≤capacity b := by
    have hm : base.steps+1≤capacity b := by unfold capacity; nlinarith
    simpa only [Nat.zero_add,max_eq_left hm] using hsupport i
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config CompetitorSumConstants.machine
    (CompetitorReusableSum.padding b) _ _ base hr
  have hi : ZeroPadding.config (CompetitorReusableSum.padding b)
      (initialConfiguration CompetitorSumConstants.machine (CompetitorSumConstants.input b))=
      initialConfiguration CompetitorSumConstants.machine (constantInput b) := rfl
  rw [hi] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold CompetitorReusableSum.padding; split <;> omega) (hbound i)
  · simpa [hf,ZeroPadding.config,CompetitorReusableSum.padding,ht] using congrArg (ZeroPadding.pad (capacity b)) h0
  · simpa [hf,ZeroPadding.config,CompetitorReusableSum.padding,ht] using congrArg (ZeroPadding.pad (capacity b)) h1
  · simpa [hf,ZeroPadding.config,CompetitorReusableSum.padding,ht] using congrArg (ZeroPadding.pad (capacity b)) h4
  · simpa [hf,ZeroPadding.config,CompetitorReusableSum.padding,ht] using h6
  · simpa [hf,ZeroPadding.config,CompetitorReusableSum.padding,ht] using h84

noncomputable def constantsProgram := RecoveryFocus.machine nativeSlots CompetitorSumConstants.machine
noncomputable def bootstrapProgram := Composition.machine coldClearProgram constantsProgram
def bootstrapBudget (b : ℕ) := 2*capacity b+20*b+58

theorem bootstrap_run (b : ℕ) (source : List Bool) (hb : 1≤b) :
    ∃ out,ClockJoin.ReadyRun bootstrapProgram (bootstrapBudget b) (coldInput b source) out ∧
      Store b CompetitorSumWidth.zero source out := by
  obtain ⟨out,hrun,hbound,h0,h1,h4,h6,h84⟩ := padded_constants_run b hb
  have hin : ∀ j,zeroed b source (nativeSlots j)=constantInput b j := by
    intro j
    fin_cases j <;> first | rfl | exact (ZeroPadding.pad_zero _).symm
  have hf := CompetitorRationalProducts.bounded_focus nativeSlots native_injective _ _ _ hrun (zeroed b source) hin
  have hall := ClockJoin.join coldClearProgram constantsProgram _ _ _ _ _ (cold_clear_run b source) hf
  have hc : (2*capacity b+4)+1+(20*b+53)=bootstrapBudget b := by unfold bootstrapBudget; omega
  rw [hc] at hall
  refine ⟨install nativeSlots (zeroed b source) out,hall,?_⟩
  constructor
  · exact (install_slot nativeSlots native_injective _ out 0).trans h0
  · exact (install_slot nativeSlots native_injective _ out 1).trans h1
  · exact (install_slot nativeSlots native_injective _ out 4).trans h4
  · exact (install_slot nativeSlots native_injective _ out 6).trans h6
  · exact (install_slot nativeSlots native_injective _ out 84).trans h84
  · exact install_other nativeSlots _ _ 88 (fun j => native_outside j 88 (by decide))
  · exact install_other nativeSlots _ _ 89 (fun j => native_outside j 89 (by decide))
  · exact install_other nativeSlots _ _ 90 (fun j => native_outside j 90 (by decide))
  · exact install_other nativeSlots _ _ 91 (fun j => native_outside j 91 (by decide))
  · exact install_other nativeSlots _ _ 92 (fun j => native_outside j 92 (by decide))
  · exact install_other nativeSlots _ _ 93 (fun j => native_outside j 93 (by decide))
  · intro i
    rw [show i.castAdd 6=nativeSlots i by rfl,install_slot nativeSlots native_injective]
    exact hbound i

end NearCubicWires.RepairOrdinary.CompetitorSumFold
