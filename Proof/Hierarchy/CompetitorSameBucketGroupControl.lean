import Proof.Hierarchy.CompetitorSameBucketGroupAccumulate
import Proof.Hierarchy.CompetitorSameBucketGroupMemory
import Proof.Hierarchy.CompetitorSameBucketGroupEmit

/-! The literal finite controller for the sorted signed-key scan. It reads
presence, both-ID equality and sign from executed tape operations. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagTape (same : Bool) : Fin 24 := if same then 12 else 11
def marked (s : Store) (same : Bool) : Store :=
  if same then {s with same:=true} else {s with present:=true}
def markProgram (same : Bool) : Machine 24 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=flagTape same then some true else none,fun _=>.stay⟩ else none

theorem marked_tapes (s : Store) (same : Bool) (cap w p m : ℕ) (source out : List Bool) :
    (marked s same).tapes cap w p m source out=
      Function.update (s.tapes cap w p m source out) (flagTape same) [true] := by
  funext i
  cases same <;> fin_cases i <;> simp only [Store.tapes_at] <;> rfl

theorem mark_run (same : Bool) (s : Store) (cap w p m pos : ℕ) (source out : List Bool) :
    Run (markProgram same) 1 cap w p m pos pos source out out s (marked s same) := by
  let before : Configuration 24 2:=⟨0,heads pos out.length,s.tapes cap w p m source out⟩
  let after : Configuration 24 2:=⟨1,heads pos out.length,(marked s same).tapes cap w p m source out⟩
  have h : step (markProgram same) before=some after := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      rfl
    · change _=(marked s same).tapes cap w p m source out
      rw [marked_tapes]
      funext i
      by_cases hi : i=flagTape same
      · subst i
        cases same <;> rfl
      · simp only [applyAction,if_neg hi,Function.update_of_ne hi]
        rfl
  obtain ⟨r,hr,hf,hs⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs⟩

def idleProgram : Machine 24 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def sizes : Fin 10 → ℕ :=
  ![1,stateCount readProgram,2,stateCount compareProgram,stateCount emitProgram,
    stateCount copyProgram,2,stateCount (arithmeticProgram false),
    stateCount (arithmeticProgram true),stateCount emitProgram]
noncomputable def programs : (j : Fin 10) → Machine 24 (sizes j)
  | ⟨0,_⟩=>idleProgram
  | ⟨1,_⟩=>readProgram
  | ⟨2,_⟩=>markProgram true
  | ⟨3,_⟩=>compareProgram
  | ⟨4,_⟩=>emitProgram
  | ⟨5,_⟩=>copyProgram
  | ⟨6,_⟩=>markProgram false
  | ⟨7,_⟩=>arithmeticProgram false
  | ⟨8,_⟩=>arithmeticProgram true
  | ⟨9,_⟩=>emitProgram
  | ⟨n+10,h⟩=>False.elim (by omega)
def next (j : Fin 10) (_ : Fin (sizes j)) (bits : Fin 24 → Bool) : Option (Fin 10) :=
  match j.val with
  | 0=>if bits 0 then some 1 else if bits 11 then some 9 else none
  | 1=>if bits 11 then some 2 else some 5
  | 2=>some 3
  | 3=>if bits 12 then some 5 else some 4
  | 4=>some 5
  | 5=>some 6
  | 6=>if bits 10 then some 8 else some 7
  | 7=>some 0
  | 8=>some 0
  | _=>none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
