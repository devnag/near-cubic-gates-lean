import Proof.PCP.VerifierLookupWalk

/-! Read a fixed field while preserving the exact retained source cursor.
The return is driven by the same physical width, including on witness tapes. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRetainField
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (target : List Bool) (width : ℕ) : Configuration 3 s :=
  ⟨q,![pos,0,1],![source,target,CompareMachine.word width]⟩
def slots : Fin 2 → Fin 3 := ![0,2]
noncomputable def returnProgram := RecoveryFocus.machine slots (LookupWalk.machine .left)
noncomputable def machine := Composition.machine FieldMachine.machine returnProgram

theorem place (q : Fin 4) (source target : List Bool) (pos nextPos width : ℕ) :
    RecoveryFocus.config slots (cfg q source pos target width).heads (cfg q source pos target width).tapes
      (LookupWalk.cfg q source nextPos width 1)=cfg q source nextPos target width := by
  apply TransitionEvent.focused_eq slots (by decide) (cfg q source pos target width)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl
  · intro i h; fin_cases i <;> rfl

theorem return_run (source target : List Bool) (pos width : ℕ) :
    ∃ r,runFrom returnProgram (3*width+2) (cfg 0 source pos target width)=some r ∧
      r.final=cfg 3 source (pos-2*width) target width ∧ r.steps=3*width+2 := by
  obtain ⟨base,hb,hf,hs⟩ := LookupWalk.walk_run .left source pos width
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config slots (by decide) _
    (cfg (0 : Fin 4) source pos target width).heads (cfg (0 : Fin 4) source pos target width).tapes _ _ base hb
  rw [place] at hr
  refine ⟨r,hr,?_,hrs.trans hs⟩
  rw [hrf,hf]
  exact place 3 source target pos _ width

theorem field_run (pre bits tail backing : List Bool) (hb : backing.length≤2*bits.length+1) :
    let source := pre++Streaming.marks bits++tail
    ∃ r,runFrom machine (7*bits.length+5) (cfg machine.start source pre.length backing bits.length)=some r ∧
      r.final=cfg 9 source pre.length (frame bits) bits.length ∧ r.steps=7*bits.length+5 := by
  dsimp only
  let source := pre++Streaming.marks bits++tail
  obtain ⟨first,hfirst,hff,hfs,_⟩ := FieldMachine.field_run pre bits tail backing hb
  have hi : FieldMachine.scan 0 source pre.length bits.length 0 [] backing=
      cfg 0 source pre.length backing bits.length := by
    apply configuration_ext
    · rfl
    · rfl
    · simp [FieldMachine.scan,cfg,StablePartition.Workspace.overlay]
  rw [hi] at hfirst
  obtain ⟨last,hlast,hlf,hls⟩ := return_run source (frame bits) (pre.length+2*bits.length) bits.length
  have hmid : Composition.restart first.final returnProgram.start=
      cfg 0 source (pre.length+2*bits.length) (frame bits) bits.length := by
    rw [hff]
    rfl
  rw [←hmid] at hlast
  have hj := Composition.run_join FieldMachine.machine returnProgram (4*bits.length+2) (3*bits.length+2)
    (cfg 0 source pre.length backing bits.length) first last hfirst hlast
  have htime : (4*bits.length+2)+1+(3*bits.length+2)=7*bits.length+5 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · simp only [Composition.joinedReceipt,hlf,Nat.add_sub_cancel]
    rfl
  · simp only [Composition.joinedReceipt,hfs,hls]
    omega

end NearCubicWires.RepairSource.VerifierDecoding.LookupRetainField
