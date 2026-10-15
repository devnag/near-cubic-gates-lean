import Proof.PCP.PCPPNativeCanonicalStackMarker
import Proof.PCP.PCPSerializerReuseCopy

/-! Literal29-tape DFS state: the checked reusable tree decoder, the live
pending stack, the ordered field stream, and its physically growing count.
The original code and cold resource producers dock outside these ports. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  core : PCPPNativeCanonicalTree.Data
  stack : List Bool
  out : List Bool
  count : ℕ
  capacity : ℕ

def State.tapes (x : State) : Fin 29→List Bool := Fin.addCases
  (m:=26) (n:=3) (motive:=fun _=>List Bool) x.core.tapes
  ![ZeroPadding.pad x.capacity x.stack,x.out,List.replicate x.count true]
def State.heads (x : State) (i : Fin 29) : ℕ :=
  if i.val=26 then x.stack.length else if i.val=27 then x.out.length else if i.val=28 then x.count else 0
def State.cfg {s : ℕ} (x : State) (q : Fin s) : Configuration 29 s := ⟨q,x.heads,x.tapes⟩
def State.withCore (x : State) (d : PCPPNativeCanonicalTree.Data) : State := {x with core:=d}
def State.Valid (x : State) := x.core.Valid ∧
  x.capacity=RecoveryReusableUnpair.capacity x.core.bits ∧
  x.capacity+1≤x.core.reset ∧ x.stack.length≤x.capacity

def coreSlots (i : Fin 26) : Fin 29 := i.castAdd 3
theorem core_injective : Function.Injective coreSlots := by
  intro i j h;exact Fin.ext (congrArg (fun q:Fin 29=>q.val) h)
noncomputable def coreMachine := RecoveryFocus.machine coreSlots PCPPNativeCanonicalTree.stepMachine

theorem core_install (x : State) (d : PCPPNativeCanonicalTree.Data) :
    install coreSlots x.tapes d.tapes=(x.withCore d).tapes := by
  funext i
  refine Fin.addCases (m:=26) (n:=3) ?_ ?_ i
  · intro j
    change install coreSlots x.tapes d.tapes (coreSlots j)=_
    exact (install_slot coreSlots core_injective _ _ j).trans (by rw [State.tapes,Fin.addCases_left];rfl)
  · intro j
    rw [install_other coreSlots _ _ _ (by
      intro k he
      have hv:=congrArg Fin.val he
      simp only [coreSlots,Fin.val_castAdd,Fin.val_natAdd] at hv
      omega)]
    rw [State.tapes,State.tapes,Fin.addCases_right,Fin.addCases_right]
    rfl

theorem core_run (x : State) (hx:x.core.Valid) :
    ∃ r,runFrom coreMachine (PCPPNativeCanonicalTree.stepTime x.core)
      (x.cfg coreMachine.start)=some r ∧
      r.final=(x.withCore (PCPPNativeCanonicalTree.stepped x.core)).cfg r.final.control ∧
      r.steps=PCPPNativeCanonicalTree.stepTime x.core := by
  obtain ⟨r,hr,hh,ht,hs⟩:=
    (PCPPNativeCanonicalTree.step_ready x.core hx).focus_at coreSlots core_injective x.heads x.tapes
      (by intro j;rw [coreSlots,State.tapes,Fin.addCases_left])
      (by intro j;simp only [State.heads,coreSlots,Fin.val_castAdd];split_ifs <;> omega)
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · exact hh
  · rw [ht,core_install]
    rfl

theorem core_valid (x : State) (hx:x.Valid) :
    (x.withCore (PCPPNativeCanonicalTree.stepped x.core)).Valid := by
  refine ⟨PCPPNativeCanonicalTree.stepped_valid x.core,?_,?_,hx.2.2.2⟩
  · dsimp only [State.withCore]
    rw [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,PCPPNativeCanonicalTree.stepped_width]
    exact hx.2.1
  · have hreset:x.core.reset≤(PCPPNativeCanonicalTree.stepped x.core).reset:=by
      unfold PCPPNativeCanonicalTree.stepped
      split <;> dsimp [PCPPNativeCanonicalTree.decoded,PCPPNativeCanonicalTree.classified]
      · exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      · exact Nat.le_max_left _ _
    exact hx.2.2.1.trans hreset

def leaf (x : State) : State := {x with out:=x.out++frame x.core.bits}
def copySlots : Fin 3→Fin 29 := ![0,27,22]
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots PCPSerializerReuse.copyMachine

theorem leaf_copy (x : State) (hx:x.Valid) :
    ∃ r,runFrom copyMachine (4*x.core.bits.length+4) (x.cfg copyMachine.start)=some r ∧
      r.final=(leaf x).cfg r.final.control ∧ r.steps≤4*x.core.bits.length+4 := by
  have hR:2*x.core.bits.length+1≤x.core.reset:=
    (PCPPNativeCanonicalTree.capacity_frame x.core.bits).trans (by
      rw [←hx.2.1]
      exact (Nat.le_succ _).trans hx.2.2.1)
  obtain ⟨base,hl,lh,lt,ls⟩:=PCPSerializerReuse.copy_run [] x.core.bits [] x.out x.core.reset hR
  simp only [List.nil_append,List.append_nil] at lt
  have hi:∀ j,x.tapes (copySlots j)=(PCPSerializerReuse.copyEntry [] x.core.bits [] x.out x.core.reset).tapes j:=by
    intro j;fin_cases j
    · change frame x.core.bits=[]++frame x.core.bits++[]
      simp only [List.nil_append,List.append_nil]
    · rfl
    · rfl
  have hh:∀ j,x.heads (copySlots j)=(PCPSerializerReuse.copyEntry [] x.core.bits [] x.out x.core.reset).heads j:=by
    intro j;fin_cases j <;> rfl
  obtain ⟨r,hr,_,hs,rh,rt,ro⟩:=RecoveryFocus.dock copySlots copy_injective PCPSerializerReuse.copyMachine
    _ x.heads x.tapes _ hh hi base hl
  refine ⟨r,hr,?_,hs.le.trans ls⟩
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi0:i=0
    · subst i;exact (rh 0).trans (by rw [lh];rfl)
    by_cases hi27:i=27
    · subst i;exact (rh 1).trans (by rw [lh];rfl)
    by_cases hi22:i=22
    · subst i;exact (rh 2).trans (by rw [lh];rfl)
    have hother:=ro i (by intro j;fin_cases j <;> simp [copySlots,Ne.symm hi0,Ne.symm hi27,Ne.symm hi22])
    rw [hother.1]
    simp only [State.cfg,State.heads,leaf]
    have hv:i.val≠27:=by intro he;exact hi27 (Fin.ext he)
    simp only [if_neg hv]
  · funext i
    by_cases hi0:i=0
    · subst i;exact (rt 0).trans (by rw [lt];rfl)
    by_cases hi27:i=27
    · subst i;exact (rt 1).trans (by rw [lt];rfl)
    by_cases hi22:i=22
    · subst i;exact (rt 2).trans (by rw [lt];rfl)
    have hother:=ro i (by intro j;fin_cases j <;> simp [copySlots,Ne.symm hi0,Ne.symm hi27,Ne.symm hi22])
    rw [hother.2]
    fin_cases i <;> first
      | rfl
      | exact False.elim (hi27 rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
