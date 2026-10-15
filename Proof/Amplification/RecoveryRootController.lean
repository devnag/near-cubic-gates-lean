import Proof.Amplification.RecoveryReadyCalls

namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  root : List Bool
  remainder : List Bool
  lowCandidate : List Bool
  highCandidate : List Bool
  trial : List Bool
  shifted : List Bool
  candidateCapacity : Nat
  flag : Bool
  compareCapacity : Nat
  difference : List Bool
  subtractCapacity : Nat
  copyCapacity : Nat
  resetCapacity : Nat

def Store.tapes (s : Store) (i : Fin 13) : List Bool :=
  match i.val with
  | 0 => frame s.root
  | 1 => frame s.remainder
  | 2 => s.lowCandidate
  | 3 => s.highCandidate
  | 4 => s.trial
  | 5 => s.shifted
  | 6 => List.replicate s.candidateCapacity false
  | 7 => [s.flag]
  | 8 => List.replicate s.compareCapacity false
  | 9 => s.difference
  | 10 => List.replicate s.subtractCapacity false
  | 11 => List.replicate s.copyCapacity false
  | 12 => List.replicate s.resetCapacity false
  | _ => []

def Store.candidates (s : Store) (lo hi : Bool) : Store :=
  {s with lowCandidate := frame (RecoveryRootCandidates.words lo hi s.root s.remainder 0)
          highCandidate := frame (RecoveryRootCandidates.words lo hi s.root s.remainder 1)
          trial := frame (RecoveryRootCandidates.words lo hi s.root s.remainder 2)
          shifted := frame (RecoveryRootCandidates.words lo hi s.root s.remainder 3)
          candidateCapacity := max s.candidateCapacity (2 * s.root.length + 7)}

def Store.clear (s : Store) : Store := {s with flag := false}

def clearMachine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some false, fun _ => .stay⟩ else none

theorem clear_ready (flag : Bool) : ReadyRun clearMachine 1 (fun _ => [flag]) (fun _ => [false]) := by
  let final : Configuration 1 2 := ⟨1, fun _ => 0, fun _ => [false]⟩
  have hstep : step clearMachine (initialConfiguration clearMachine (fun _ => [flag])) = some final := by rfl
  obtain ⟨r, hr, hf, hs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  exact ⟨r, hr, congrArg Configuration.tapes hf, by intro i; simp [hf, final], hs⟩

def candidateSlots : Fin 7 → Fin 13 := ![0, 1, 2, 3, 4, 5, 6]
def clearSlots : Fin 1 → Fin 13 := fun _ => 7
def compareSlots : Fin 4 → Fin 13 := ![4, 5, 7, 8]
def subtractSlots : Fin 4 → Fin 13 := ![5, 4, 9, 10]
def highCopySlots : Fin 4 → Fin 13 := ![3, 0, 11, 12]
def lowCopySlots : Fin 4 → Fin 13 := ![2, 0, 11, 12]
def differenceCopySlots : Fin 4 → Fin 13 := ![9, 1, 11, 12]
def shiftedCopySlots : Fin 4 → Fin 13 := ![5, 1, 11, 12]

theorem candidateSlots_injective : Function.Injective candidateSlots := by decide
theorem clearSlots_injective : Function.Injective clearSlots := by decide
theorem compareSlots_injective : Function.Injective compareSlots := by decide
theorem subtractSlots_injective : Function.Injective subtractSlots := by decide
theorem highCopySlots_injective : Function.Injective highCopySlots := by decide
theorem lowCopySlots_injective : Function.Injective lowCopySlots := by decide
theorem differenceCopySlots_injective : Function.Injective differenceCopySlots := by decide
theorem shiftedCopySlots_injective : Function.Injective shiftedCopySlots := by decide

def sizes : Fin 8 → Nat := ![11, 2, 7, 7, 6, 6, 6, 6]
noncomputable def programs (lo hi : Bool) : (j : Fin 8) → Machine 13 (sizes j)
  | ⟨0, _⟩ => RecoveryFocus.machine candidateSlots (candidateMachine lo hi)
  | ⟨1, _⟩ => RecoveryFocus.machine clearSlots clearMachine
  | ⟨2, _⟩ => RecoveryFocus.machine compareSlots compareMachine
  | ⟨3, _⟩ => RecoveryFocus.machine subtractSlots subtractMachine
  | ⟨4, _⟩ => RecoveryFocus.machine highCopySlots copyMachine
  | ⟨5, _⟩ => RecoveryFocus.machine lowCopySlots copyMachine
  | ⟨6, _⟩ => RecoveryFocus.machine differenceCopySlots copyMachine
  | ⟨7, _⟩ => RecoveryFocus.machine shiftedCopySlots copyMachine
  | ⟨n + 8, h⟩ => False.elim (by omega)

def next (j : Fin 8) (_ : Fin (sizes j)) (scanned : Fin 13 → Bool) : Option (Fin 8) :=
  if j.val = 0 then some 1
  else if j.val = 1 then some 2
  else if j.val = 2 then if scanned 7 then some 3 else some 5
  else if j.val = 3 then some 4
  else if j.val = 4 then some 6
  else if j.val = 5 then some 7
  else none

noncomputable def roundMachine (lo hi : Bool) := RecoveryCalls.machine sizes (programs lo hi) 0 next

theorem candidates_layout (lo hi : Bool) (s : Store)
    (hw : s.root.length = s.remainder.length)
    (hb : ∀ i : Fin 4, (![s.lowCandidate, s.highCandidate, s.trial, s.shifted] i).length ≤
      2 * (s.root.length + 2) + 1) :
    ReadyRun (programs lo hi 0) (4 * s.root.length + 16) s.tapes (s.candidates lo hi).tapes := by
  have h := (candidate_ready lo hi s.root s.remainder
    ![s.lowCandidate, s.highCandidate, s.trial, s.shifted] s.candidateCapacity hw hb).focus
      candidateSlots candidateSlots_injective s.tapes (by intro j; fin_cases j <;> rfl)
  have he : install candidateSlots s.tapes (candidateOutput lo hi s.root s.remainder s.candidateCapacity) =
      (s.candidates lo hi).tapes := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot candidateSlots candidateSlots_injective _ _ 0
      | exact install_slot candidateSlots candidateSlots_injective _ _ 1
      | exact install_slot candidateSlots candidateSlots_injective _ _ 2
      | exact install_slot candidateSlots candidateSlots_injective _ _ 3
      | exact install_slot candidateSlots candidateSlots_injective _ _ 4
      | exact install_slot candidateSlots candidateSlots_injective _ _ 5
      | exact install_slot candidateSlots candidateSlots_injective _ _ 6
      | exact install_other candidateSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem clear_layout (lo hi : Bool) (s : Store) :
    ReadyRun (programs lo hi 1) 1 s.tapes s.clear.tapes := by
  have h := (clear_ready s.flag).focus clearSlots clearSlots_injective s.tapes (by intro j; fin_cases j; rfl)
  have he : install clearSlots s.tapes (fun _ => [false]) = s.clear.tapes := by
    funext i
    by_cases hi : i = 7
    · subst i
      exact install_slot clearSlots clearSlots_injective _ _ 0
    · have hn : ∀ j, clearSlots j ≠ i := by intro j; simpa [clearSlots] using Ne.symm hi
      rw [install_other clearSlots _ _ i hn]
      fin_cases i <;> simp_all [Store.tapes, Store.clear]
  rw [he] at h
  exact h

theorem candidates_clear_call (lo hi : Bool) (s : Store)
    (hw : s.root.length = s.remainder.length)
    (hb : ∀ i : Fin 4, (![s.lowCandidate, s.highCandidate, s.trial, s.shifted] i).length ≤
      2 * (s.root.length + 2) + 1) :
    Timed (roundMachine lo hi) (4 * s.root.length + 19)
      (initialConfiguration (roundMachine lo hi) s.tapes)
      (controlConfig (RecoveryCalls.code sizes 2)
        (initialConfiguration (programs lo hi 2) (s.candidates lo hi).clear.tapes)) := by
  have ha := (candidates_layout lo hi s hw hb).call sizes (programs lo hi) 0 next 0 1 (by intro q; rfl)
  have hb := (clear_layout lo hi (s.candidates lo hi)).call sizes (programs lo hi) 0 next 1 2 (by intro q; rfl)
  have h := ha.trans hb
  have he : (4 * s.root.length + 16 + 1) + (1 + 1) = 4 * s.root.length + 19 := by omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryRootRound
