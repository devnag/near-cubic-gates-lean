import Proof.MachineModel.OrdinaryTransitionArrayReset

/-! Physical array-buffer reuse and physical zeroing of the framed tape id.
Both calls preserve the accumulating event stream and witness cursors. -/
namespace NearCubicWires.RepairOrdinary.TransitionArrayReuse
open LocalBitMultitape RecoveryExecution SignedSortKey RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def moveSlots : Fin 4 → Fin 20 := ![17,16,19,18]
def zeroSlots : Fin 2 → Fin 20 := ![15,10]
noncomputable def moveProgram := RecoveryFocus.machine moveSlots TransitionArrayMove.machine
noncomputable def zeroProgram := RecoveryFocus.machine zeroSlots TransitionTapeZero.machine

theorem move_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap C : ℕ)
    (source out nextSource nextOut : List Bool) :
    RecoveryFocus.config moveSlots (cfg q d w cap C source out).heads (cfg q d w cap C source out).tapes
      (⟨q,fun _ => 0,![nextOut,nextSource,List.replicate C true,List.replicate (C+1) false]⟩ : Configuration 4 s)=
      cfg q d w cap C nextSource nextOut := by
  apply TransitionEvent.focused_eq moveSlots (by decide) (cfg q d w cap C source out)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | exact False.elim (h 1 rfl) | rfl

theorem move_run (d : TransitionTape.Store) (w cap C : ℕ) (source out : List Bool)
    (hs : source.length≤C) (ho : out.length=C) :
    ∃ r,runFrom moveProgram (2*C+4) (cfg moveProgram.start d w cap C source out)=some r ∧
      r.final=cfg 3 d w cap C out (List.replicate C false) := by
  obtain ⟨base,hb,hf,hh,_⟩ := TransitionArrayMove.move_ready out source (C+1) (by omega) (by omega)
  rw [ho] at hb hf
  have hc : base.final.control=3 := by
    have halted := (prefix_of_run TransitionArrayMove.machine _ _ base hb).2
    exact (by decide : ∀ q : Fin 4,TransitionArrayMove.machine.halted q=true → q=3) _ halted
  have hfinal : base.final=(⟨3,fun _ => 0,
      ![List.replicate C false,out,List.replicate C true,List.replicate (C+1) false]⟩ : Configuration 4 4) :=
    configuration_ext hc (funext hh) hf
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config moveSlots (by decide) _
    (cfg (0 : Fin 4) d w cap C source out).heads (cfg (0 : Fin 4) d w cap C source out).tapes _ _ base hb
  have hi : RecoveryFocus.config moveSlots (cfg (0 : Fin 4) d w cap C source out).heads
      (cfg (0 : Fin 4) d w cap C source out).tapes
      (initialConfiguration TransitionArrayMove.machine
        ![out,source,List.replicate C true,List.replicate (C+1) false])=cfg 0 d w cap C source out :=
    move_place 0 d w cap C source out source out
  rw [hi] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hfinal]
  exact move_place 3 d w cap C source out out (List.replicate C false)

theorem zero_place {s : ℕ} (q : Fin s) (d : TransitionTape.Store) (w cap C : ℕ)
    (source out : List Bool) (tape : ℕ) :
    RecoveryFocus.config zeroSlots (cfg q d w cap C source out).heads (cfg q d w cap C source out).tapes
      (⟨q,fun _ => 0,![frame (binary w tape),List.replicate cap false]⟩ : Configuration 2 s)=
      cfg q {d with tape:=tape} w cap C source out := by
  apply TransitionEvent.focused_eq zeroSlots (by decide) (cfg q d w cap C source out)
  · rfl
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro i h; fin_cases i <;> rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl

theorem zero_run (d : TransitionTape.Store) (w cap C : ℕ) (source out : List Bool) (hc : 2*w+1≤cap) :
    ∃ r,runFrom zeroProgram (4*w+4) (cfg zeroProgram.start d w cap C source out)=some r ∧
      r.final=cfg 4 {d with tape:=0} w cap C source out := by
  obtain ⟨base,hb,hf,hh,_⟩ := TransitionTapeZero.zero_ready (binary w d.tape) cap (by simpa using hc)
  simp only [binary_length] at hb hf
  have hzall : ∀ n,binary n 0=List.replicate n false := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa [binary,List.replicate_succ] using congrArg (List.cons false) ih
  have hz := hzall w
  rw [←hz] at hf
  have hcontrol : base.final.control=4 := by
    have halted := (prefix_of_run TransitionTapeZero.machine _ _ base hb).2
    exact (by decide : ∀ q : Fin 5,TransitionTapeZero.machine.halted q=true → q=4) _ halted
  have hfinal : base.final=(⟨4,fun _ => 0,![frame (binary w 0),List.replicate cap false]⟩ : Configuration 2 5) :=
    configuration_ext hcontrol (funext hh) hf
  obtain ⟨r,hr,hrf,_⟩ := RecoveryFocus.run_config zeroSlots (by decide) _
    (cfg (0 : Fin 5) d w cap C source out).heads (cfg (0 : Fin 5) d w cap C source out).tapes _ _ base hb
  have hi : RecoveryFocus.config zeroSlots (cfg (0 : Fin 5) d w cap C source out).heads
      (cfg (0 : Fin 5) d w cap C source out).tapes
      (initialConfiguration TransitionTapeZero.machine ![frame (binary w d.tape),List.replicate cap false])=
      cfg 0 d w cap C source out := zero_place 0 d w cap C source out d.tape
  rw [hi] at hr
  refine ⟨r,hr,?_⟩
  rw [hrf,hfinal]
  exact zero_place 4 d w cap C source out 0

end NearCubicWires.RepairOrdinary.TransitionArrayReuse
