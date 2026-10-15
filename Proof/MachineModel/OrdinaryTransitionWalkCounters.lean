import Proof.MachineModel.OrdinaryTransitionWalkStore

/-! Paid arithmetic on the actual binary m and iteration fields. All source,
head-array and event-stream cursors survive these local short operations. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ready_lift {t s time : ℕ} (slot : Fin t→Fin 42) (hi : Function.Injective slot)
    (p : Machine t s) (input output : Fin t→List Bool) (d e : Store)
    (h : ReadyRun p time input output)
    (hin : ∀ i,(cfg p.start d).tapes (slot i)=input i)
    (hh : ∀ i,(cfg p.start d).heads (slot i)=0)
    (hout : ∀ i,(cfg p.start e).tapes (slot i)=output i)
    (he : ∀ i,(cfg p.start e).heads (slot i)=0)
    (oh : ∀ i,(∀ j,slot j≠i) → (cfg p.start d).heads i=(cfg p.start e).heads i)
    (ot : ∀ i,(∀ j,slot j≠i) → (cfg p.start d).tapes i=(cfg p.start e).tapes i) :
    ∃ r,runFrom (RecoveryFocus.machine slot p) time (cfg p.start d)=some r ∧
      r.final=cfg r.final.control e ∧ r.steps=time := by
  obtain ⟨base,hb,hbt,hbh,hbs⟩ := h
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config slot hi p (cfg p.start d).heads (cfg p.start d).tapes _ _ base hb
  have hinput : RecoveryFocus.config slot (cfg p.start d).heads (cfg p.start d).tapes
      (initialConfiguration p input)=cfg p.start d := by
    apply TransitionEvent.focused_eq slot hi (cfg p.start d)
    · rfl
    · intro i; exact (hh i).symm
    · intro i; exact (hin i).symm
    · intro i _; rfl
    · intro i _; rfl
  rw [hinput] at hr
  have houtput : RecoveryFocus.config slot (cfg p.start d).heads (cfg p.start d).tapes base.final=
      cfg base.final.control e := by
    apply TransitionEvent.focused_eq slot hi (cfg p.start d)
    · rfl
    · intro i; exact (hbh i).trans (he i).symm
    · intro i; rw [hbt]; exact (hout i).symm
    · exact oh
    · exact ot
  exact ⟨r,hr,by rw [hrf,houtput]; rfl,hrs.trans hbs⟩

def clearSlots : Fin 1→Fin 42 := fun _=>41
def compareSlots : Fin 4→Fin 42 := ![39,40,41,29]
def incrementSlots : Fin 2→Fin 42 := ![40,29]
noncomputable def clearProgram := RecoveryFocus.machine clearSlots LookupReadBit.clear
noncomputable def compareProgram := RecoveryFocus.machine compareSlots compareMachine
noncomputable def incrementProgram := RecoveryFocus.machine incrementSlots FramedIncrement.machine

theorem clear_run (d : Store) :
    ∃ r,runFrom clearProgram 1 (cfg clearProgram.start d)=some r ∧
      r.final=cfg r.final.control {d with countFlag:=false} ∧ r.steps=1 := by
  apply ready_lift clearSlots (by decide) LookupReadBit.clear (fun _=>[d.countFlag]) (fun _=>[false])
    d {d with countFlag:=false} (LookupReadBit.clear_ready d.countFlag)
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i; rfl
  · intro i; fin_cases i; rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl

theorem compare_run (d : Store) (hm : d.m<2^d.w) (hi : d.index<2^d.w)
    (hf : d.countFlag=false) (hc : 2*d.w+1≤d.cap) :
    ∃ r,runFrom compareProgram (4*d.w+4) (cfg compareProgram.start d)=some r ∧
      r.final=cfg r.final.control {d with countFlag:=decide (d.m≤d.index)} ∧ r.steps=4*d.w+4 := by
  have h := compare_ready (binary d.w d.m) (binary d.w d.index) d.cap (by simp)
  simp only [binary_length,binary_value d.w d.m hm,binary_value d.w d.index hi,max_eq_left hc] at h
  apply ready_lift compareSlots (by decide) compareMachine _ _ d {d with countFlag:=decide (d.m≤d.index)} h
  · intro i; fin_cases i <;> first | rfl | (change [d.countFlag]=[false]; rw [hf])
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 2 rfl) | rfl

theorem increment_place {s : ℕ} (q : Fin s) (d : Store) (index : ℕ) :
    RecoveryFocus.config incrementSlots (cfg q d).heads (cfg q d).tapes
      (⟨q,fun _=>0,![frame (binary d.w index),List.replicate d.cap false]⟩ : Configuration 2 s)=
      cfg q {d with index:=index} := by
  apply TransitionEvent.focused_eq incrementSlots (by decide) (cfg q d)
  · rfl
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  · intro i _; rfl
  · intro i h; fin_cases i <;> first | exact False.elim (h 0 rfl) | rfl

theorem increment_run (d : Store) (hi : d.index+1<2^d.w) (hc : 2*d.w≤d.cap) :
    ∃ r,runFrom incrementProgram (4*d.w+2) (cfg incrementProgram.start d)=some r ∧
      r.final=cfg (4 : Fin 5) {d with index:=d.index+1} ∧ r.steps≤4*d.w+2 := by
  obtain ⟨base,hb,ht0,ht1,hh,_,_⟩ := FramedIncrement.increment_run d.w d.index d.cap hi hc
  have hf : base.final=(⟨4,fun _=>0,![frame (binary d.w (d.index+1)),List.replicate d.cap false]⟩ : Configuration 2 5) := by
    apply configuration_ext
    · have halted := (prefix_of_run FramedIncrement.machine (4*d.w+2) _ base hb).2
      exact (by decide : ∀ q : Fin 5,FramedIncrement.machine.halted q=true→q=4) _ halted
    · exact funext hh
    · funext i; fin_cases i
      · exact ht0
      · exact ht1
  obtain ⟨r,hr,hrf,hrs⟩ := RecoveryFocus.run_config incrementSlots (by decide) FramedIncrement.machine
    (cfg (0 : Fin 5) d).heads (cfg (0 : Fin 5) d).tapes _ _ base hb
  have hin : initialConfiguration FramedIncrement.machine
      (Fin.addCases (motive:=fun _ : Fin (1+1)=>List Bool) (fun _ : Fin 1=>frame (binary d.w d.index))
        (fun _ : Fin 1=>List.replicate d.cap false))=
      (⟨0,fun _=>0,![frame (binary d.w d.index),List.replicate d.cap false]⟩ : Configuration 2 5) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [hin,increment_place] at hr
  refine ⟨r,hr,?_,?_⟩
  · rw [hrf,hf]
    exact increment_place 4 d _
  · rw [hrs]
    exact runFrom_steps_le FramedIncrement.machine _ _ base hb

end NearCubicWires.RepairOrdinary.TransitionWalk
