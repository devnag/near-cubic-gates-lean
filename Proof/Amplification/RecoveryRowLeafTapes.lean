import Proof.Amplification.RecoveryRowKind

namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem RecoveryRootRound.ReadyRun.embed {t e s n : Nat} {p : Machine t s}
    {input output : Fin t→List Bool} (h : ReadyRun p n input output) (extra : Fin e→List Bool) :
    ReadyRun (TapeEmbedding.machine e p) n (Fin.addCases input extra) (Fin.addCases output extra) := by
  obtain ⟨r,hr,ht,hh,hsteps⟩ := h
  have he := TapeEmbedding.run_embed p (fun _ : Fin e=>0) extra n _ r hr
  have hi : TapeEmbedding.config (fun _ : Fin e=>0) extra (initialConfiguration p input)=
      initialConfiguration (TapeEmbedding.machine e p) (Fin.addCases input extra) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=t) (n:=e) (fun _=>?_) (fun _=>?_) i
      all_goals simp [TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hi] at he
  refine ⟨TapeEmbedding.receipt (fun _ : Fin e=>0) extra r,he,?_,?_,hsteps⟩
  · simp only [TapeEmbedding.receipt,TapeEmbedding.config,ht]
  · intro i
    refine Fin.addCases (m:=t) (n:=e) (motive:=fun j=>
      (TapeEmbedding.receipt (fun _ : Fin e=>0) extra r).final.heads j=0) ?_ ?_ i
    · intro j; simpa [TapeEmbedding.receipt,TapeEmbedding.config] using hh j
    · intro j; simp [TapeEmbedding.receipt,TapeEmbedding.config]

namespace RecoveryRowLeaf
open RecoveryClauseState RecoveryClauseEvaluation

def extra (kind : List Bool) (flags : Fin 3→Bool) : Fin 4→List Bool :=
  ![frame kind,[flags 0],[flags 1],[flags 2]]
def tapes (core : Fin 42→List Bool) (kind : List Bool) (flags : Fin 3→Bool) : Fin 46→List Bool :=
  fun i=>Fin.addCases core (extra kind flags) i
def kindSlots : Fin 5→Fin 46 := ![42,43,44,45,22]
theorem kindSlots_injective : Function.Injective kindSlots := by decide
noncomputable def kindMachine := RecoveryFocus.machine kindSlots RecoveryRowKind.machine
noncomputable def clauseMachine := TapeEmbedding.machine 4 RecoveryClauseEvaluation.machine

theorem kind_input (core : Fin 42→List Bool) (kind : List Bool) (flags : Fin 3→Bool) (capacity : Nat)
    (hc : core 22=List.replicate capacity false) (j : Fin 5) :
    tapes core kind flags (kindSlots j)=RecoveryRowKind.tapes kind flags capacity j := by
  fin_cases j
  all_goals first | rfl | exact hc

theorem kind_install (core : Fin 42→List Bool) (kind nextKind : List Bool)
    (flags nextFlags : Fin 3→Bool) (capacity : Nat) (hc : core 22=List.replicate capacity false) :
    install kindSlots (tapes core kind flags) (RecoveryRowKind.tapes nextKind nextFlags capacity)=
      tapes core nextKind nextFlags := by
  funext i
  by_cases hi : ∃ j,kindSlots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot kindSlots kindSlots_injective]
    exact (kind_input core nextKind nextFlags capacity hc j).symm
  · rw [install_other kindSlots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    refine Fin.addCases (m:=42) (n:=4) (motive:=fun k=>(¬∃ j,kindSlots j=k) →
      tapes core kind flags k=tapes core nextKind nextFlags k) ?_ ?_ i hi
    · intro j _; simp [tapes]
    · intro j hj
      fin_cases j
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
      · exact False.elim (hj ⟨2,rfl⟩)
      · exact False.elim (hj ⟨3,rfl⟩)

theorem kind_ready (s : State) (e : Extra) (word kind : List Bool) (flags : Fin 3→Bool)
    (he : e.Valid s word) (hk : kind.length ≤ s.bits.length) :
    ReadyRun kindMachine (RecoveryRowKind.time kind)
      (tapes (RecoveryClauseEvaluation.tapes s e) kind flags)
      (tapes (RecoveryClauseEvaluation.tapes s e) (RecoveryRowKind.after kind)
        (fun i=>decide (RadixSemantics.value kind=i.val))) := by
  have hc : 2*kind.length+1 ≤ s.capacity := by
    have h := he.reset
    change 8192*(s.bits.length+1)^2+1 ≤ s.capacity at h
    nlinarith only [h,hk]
  have h := (RecoveryRowKind.kind_ready kind flags s.capacity).focus kindSlots kindSlots_injective
    (tapes (RecoveryClauseEvaluation.tapes s e) kind flags)
    (kind_input _ kind flags s.capacity rfl)
  rw [Nat.max_eq_left hc,kind_install _ kind (RecoveryRowKind.after kind) flags _ s.capacity rfl] at h
  exact h

def force : Machine 46 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun i=>if i=27 then some true else none,fun _=>.stay⟩ else none

theorem force_ready (input : Fin 46→List Bool) (old : Bool) (ht : input 27=[old]) :
    ReadyRun force 1 input (Function.update input 27 [true]) := by
  let final : Configuration 46 2 := ⟨1,fun _=>0,Function.update input 27 [true]⟩
  have hs : step force (initialConfiguration force input)=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=27
      · subst i; simp [applyAction,force,initialConfiguration,ht,writeTapeBit,final]
      · simp [applyAction,force,initialConfiguration,hi,final]
  obtain ⟨r,hr,hf,hsteps⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hsteps⟩

end RecoveryRowLeaf
end NearCubicWires.RepairOrdinary
