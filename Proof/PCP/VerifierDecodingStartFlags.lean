import Proof.PCP.VerifierDecodingFlagsLayout

/-! Start-state and state-flag controller. A malformed start rejects before
the flags loop; truncated flags physically clear the shared result bit. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.StartFlags
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejectProgram : Machine 14 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=12 then some false else none,fun _ => .stay⟩ else none
def sizes : Fin 3 → ℕ := ![StartLayout.states,FlagsLayout.states,2]
noncomputable def programs : (j : Fin 3) → Machine 14 (sizes j)
  | ⟨0,_⟩ => StartLayout.machine
  | ⟨1,_⟩ => FlagsLayout.machine
  | ⟨2,_⟩ => rejectProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
noncomputable def next : (j : Fin 3) → Fin (sizes j) → (Fin 14 → Bool) → Option (Fin 3)
  | ⟨0,_⟩,_,bits => if bits 12 then some 1 else none
  | ⟨1,_⟩,q,_ => if q=RepeatMachine.phaseCode FlagsLayout.tagStates 3 then none else some 2
  | ⟨2,_⟩,_,_ => none
  | ⟨n+3,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_prefix (node dest : Fin 3) (fuel : ℕ)
    (input : Configuration 14 (sizes node)) (r : ExecutionReceipt 14 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
theorem stop_prefix (node : Fin 3) (fuel : ℕ)
    (input : Configuration 14 (sizes node)) (r : ExecutionReceipt 14 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

noncomputable def rejected (heads : Fin 14 → ℕ) (tapes : Fin 14 → List Bool) :=
  RecoveryCalls.stopped sizes heads
    (fun i => if i=12 then writeTapeBit (tapes i) (heads i) false else tapes i)
theorem rejected_scanned (heads : Fin 14 → ℕ) (tapes : Fin 14 → List Bool) :
    (rejected heads tapes).scanned 12=false := by
  simp [rejected,RecoveryCalls.stopped,Configuration.scanned,MemoryTransition.read_write]
theorem reject_tail (heads : Fin 14 → ℕ) (tapes : Fin 14 → List Bool) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 2) ⟨(programs 2).start,heads,tapes⟩)
      (rejected heads tapes) := by
  let final : Configuration 14 2 := ⟨1,heads,
    fun i => if i=12 then writeTapeBit (tapes i) (heads i) false else tapes i⟩
  have hstep : step rejectProgram ⟨0,heads,tapes⟩=some final := by
    simp [step,rejectProgram]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,final]
    · funext i; by_cases h : i=12 <;> simp [applyAction,final,h]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single
    (by rfl : rejectProgram.halted (0 : Fin 2)=false) hstep).run (by rfl)
  have hp := stop_prefix 2 1 _ r hr (by rfl)
  rw [hf,hs] at hp
  exact hp

theorem reject_ne_accept : RepeatMachine.phaseCode FlagsLayout.tagStates 4 ≠
    RepeatMachine.phaseCode FlagsLayout.tagStates 3 := by
  intro h
  have he := (RepeatMachine.code FlagsLayout.tagStates).injective h
  exact (by decide : (4 : Fin 5)≠3) (Sum.inr.inj he)

theorem flags_tail {a : ℕ} (base : Configuration 14 a) (pre bits : List Bool) (c s : ℕ)
    (h : FlagsLayout.Entry base pre bits c s) (hflag : base.scanned 12=true) :
    ∃ n final, n≤8*s+7 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (FlagsLayout.input base)) final ∧
      machine.halted final.control=true ∧ final.scanned 12=decide (2*s≤bits.length) ∧
      (2*s≤bits.length → final=RecoveryCalls.stopped sizes
        (FlagsLayout.output base pre s).heads (FlagsLayout.output base pre s).tapes) := by
  obtain ⟨r,hr,hs,hresult⟩ := FlagsLayout.flags_layout base pre bits c s h
  by_cases hlen : 2*s≤bits.length
  · simp only [if_pos hlen] at hresult
    have hp := stop_prefix 1 (8*s+3) _ r hr (by simp [next,hresult,FlagsLayout.output])
    rw [hresult] at hp
    refine ⟨_,_,by omega,hp,?_,?_,by intro _; rfl⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simpa [hlen,RecoveryCalls.stopped,FlagsLayout.output,Configuration.scanned] using hflag
  · simp only [if_neg hlen] at hresult
    have hp := call_prefix 1 2 (8*s+3) _ r hr (by
      simp [next,hresult]
      exact reject_ne_accept)
    have hall := hp.trans (reject_tail r.final.heads r.final.tapes)
    refine ⟨_,_,by omega,hall,?_,?_,by intro h; exact (hlen h).elim⟩
    · simp [machine,RecoveryCalls.machine,rejected,RecoveryCalls.stopped]
    · simpa [hlen] using rejected_scanned r.final.heads r.final.tapes

end NearCubicWires.RepairSource.VerifierDecoding.StartFlags
