import Proof.Hierarchy.CompetitorBankMergeWorkspace

/-! The existing binary adder and raw appender on actual cleared scratch.
The sum-fit premise concerns natural P/P or N/N addition, before signed
subtraction. Global source and result cursors are preserved by arithmetic. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addSlots : Fin 4 → Fin 27 := ![0,1,2,3]
def addInput (w a b : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad (capacity w) (frame (binary w a)),ZeroPadding.pad (capacity w) (frame (binary w b)),
    List.replicate (capacity w) false,List.replicate (capacity w) false]
def addOutput (w a b : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad (capacity w) (frame (binary w a)),ZeroPadding.pad (capacity w) (frame (binary w b)),
    ZeroPadding.pad (capacity w) (frame (binary w (a+b))),List.replicate (capacity w) false]
noncomputable def addProgram := RecoveryFocus.machine addSlots BoundaryAdvance.machine
noncomputable def emitProgram := CompetitorRawScalarPaddedField.program (2 : Fin 27) 8 3
noncomputable def kernelProgram := Composition.machine addProgram emitProgram

theorem word_fits (w : ℕ) : 2*w+1≤capacity w := by
  unfold capacity CompetitorResidueTable.capacity CompetitorReusableDecision.capacity
  nlinarith

theorem padded_add_ready (w a b : ℕ) (hfit : a+b<2^w) :
    ClockJoin.ReadyRun BoundaryAdvance.machine (4*w+4) (addInput w a b) (addOutput w a b) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := HierarchyBinary.add_ready w a b 0 [] hfit (by simp)
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config BoundaryAdvance.machine (fun _ => capacity w) _ _ base hr
  have hin : ZeroPadding.config (fun _ => capacity w)
      (initialConfiguration BoundaryAdvance.machine ![frame (binary w a),frame (binary w b),[],List.replicate 0 false])=
      initialConfiguration BoundaryAdvance.machine (addInput w a b) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,addInput,ZeroPadding.pad]
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs.le⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,ht,addOutput,CompetitorReusableDecision.pad_zeros,max_eq_left (word_fits w)]
  · intro i
    rw [hf]
    exact hh i

theorem add_support (w a b : ℕ) (i : Fin 4) : (addOutput w a b i).length≤capacity w := by
  have hc := word_fits w
  fin_cases i <;> simp [addOutput,ZeroPadding.pad_length] <;> omega

theorem Store.add {w : ℕ} {left right out : List Bool} {ambient : Fin 27 → List Bool}
    (h : Store w left right out ambient) (a b : ℕ) :
    Store w left right out (install addSlots ambient (addOutput w a b)) := by
  have keep (i : Fin 27) (hi : ∀ j,addSlots j≠i) : install addSlots ambient (addOutput w a b) i=ambient i :=
    install_other addSlots ambient (addOutput w a b) i hi
  constructor
  · exact (keep 9 (by decide)).trans h.width
  · exact (keep 20 (by decide)).trans h.widthCopy
  · exact (keep 19 (by decide)).trans h.sourceLeft
  · exact (keep 23 (by decide)).trans h.sourceRight
  · exact (keep 8 (by decide)).trans h.output
  · exact (keep 21 (by decide)).trans h.erase
  · exact (keep 22 (by decide)).trans h.reset
  · intro i
    fin_cases i
    all_goals first
      | (change (install addSlots ambient (addOutput w a b) (addSlots 0)).length≤_; rw [install_slot addSlots (by decide)]; exact add_support w a b 0)
      | (change (install addSlots ambient (addOutput w a b) (addSlots 1)).length≤_; rw [install_slot addSlots (by decide)]; exact add_support w a b 1)
      | (change (install addSlots ambient (addOutput w a b) (addSlots 2)).length≤_; rw [install_slot addSlots (by decide)]; exact add_support w a b 2)
      | (change (install addSlots ambient (addOutput w a b) (addSlots 3)).length≤_; rw [install_slot addSlots (by decide)]; exact add_support w a b 3)
      | (change (install addSlots ambient (addOutput w a b) 5).length≤_; rw [keep 5 (by decide)]; exact h.support 4)
      | (change (install addSlots ambient (addOutput w a b) 6).length≤_; rw [keep 6 (by decide)]; exact h.support 5)
      | (change (install addSlots ambient (addOutput w a b) 7).length≤_; rw [keep 7 (by decide)]; exact h.support 6)
      | (change (install addSlots ambient (addOutput w a b) 10).length≤_; rw [keep 10 (by decide)]; exact h.support 7)

theorem kernel_run (w a b pa pb : ℕ) (left right out : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w left right out ambient) (hfit : a+b<2^w)
    (hloaded : ∀ i,ambient (addSlots i)=addInput w a b i) :
    ∃ r,runFrom kernelProgram (8*w+8) (cfg kernelProgram.start pa pb out.length ambient)=some r ∧
      r.steps≤8*w+8 ∧ r.final.heads=heads pa pb (out++binary w (a+b)).length ∧
      Store w left right (out++binary w (a+b)) r.final.tapes := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorReusableDecision.bounded_focused_run addSlots (by decide)
    _ _ _ (padded_add_ready w a b hfit) (heads pa pb out.length) ambient
    (by intro i; fin_cases i <;> rfl) hloaded
  let middle := install addSlots ambient (addOutput w a b)
  have hm2 : middle 2=ZeroPadding.pad (capacity w) (frame (binary w (a+b))) := install_slot addSlots (by decide) ambient _ 2
  have hm3 : middle 3=List.replicate (capacity w) false := install_slot addSlots (by decide) ambient _ 3
  have hm8 : middle 8=out := (install_other addSlots ambient _ 8 (by decide)).trans h.output
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := CompetitorRawScalarPaddedField.field_run (2 : Fin 27) 8 3
    (by decide) (by decide) (by decide) (binary w (a+b)) out (capacity w) (heads pa pb out.length) middle
    rfl rfl rfl hm2 hm8 hm3 (by simpa using word_fits w)
  have he : Composition.restart first.final emitProgram.start=cfg emitProgram.start pa pb out.length middle := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom emitProgram (4*w+3) (Composition.restart first.final emitProgram.start)=some last := by
    rw [he]
    simpa only [binary_length,emitProgram,cfg,RecoveryCalls.restarted] using hlast
  have hall := Composition.run_join addProgram emitProgram _ _ _ first last hfirst hl'
  have htime : (4*w+4)+1+(4*w+3)=8*w+8 := by omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤8*w+8
    simp only [binary_length] at hls
    omega
  · change last.final.heads=_
    rw [hlh]
    funext i
    by_cases hi : i=8 <;> simp [heads,hi]
  · change Store w left right (out++binary w (a+b)) last.final.tapes
    rw [hlt]
    exact (h.add a b).emit _

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
