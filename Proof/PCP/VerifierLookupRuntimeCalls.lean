import Proof.PCP.VerifierLookupRuntimeSlices

/-! One fixed fourteen-call lookup program. All calls and returns are
ordinary transitions; dimensions and selected addresses never enter control. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev navigationStates := Fintype.card (RecoveryCalls.Control LookupNavigation.sizes)
abbrev flagsStates := Fintype.card (RecoveryCalls.Control (LookupSelect.sizes 6))
abbrev tableStates := Fintype.card (RecoveryCalls.Control
  (LookupSelect.sizes (Fintype.card (RecoveryCalls.Control LookupSkip.sizes))))
def sizes : Fin 14 → ℕ := ![2,7,navigationStates,flagsStates,3,3,10,7,2,navigationStates,tableStates,3,6,6]
noncomputable def programs : (i : Fin 14) → Machine 21 (sizes i)
  | 0=>clearProgram
  | 1=>flagsQueryProgram
  | 2=>flagsNavigationProgram
  | 3=>flagsSelectProgram
  | 4=>scalarProgram 0
  | 5=>scalarProgram 1
  | 6=>claimedProgram
  | 7=>tableQueryProgram
  | 8=>clearProgram
  | 9=>tableNavigationProgram
  | 10=>tableSelectProgram
  | 11=>scalarProgram 2
  | 12=>fieldProgram false
  | 13=>fieldProgram true

def next (j : Fin 14) (_ : Fin (sizes j)) (_ : Fin 21 → Bool) : Option (Fin 14) :=
  if h:j.val<13 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 14) (d e : Store) (fuel : ℕ) (r : ExecutionReceipt 21 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg r.final.control e) (hn : ∀ c bits,next j c bits=some k) :
    ∃ time≤fuel+1,Timed machine time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh (hn _ _)
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem stop_phase (j : Fin 14) (d e : Store) (fuel : ℕ) (r : ExecutionReceipt 21 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg r.final.control e) (hn : ∀ c bits,next j c bits=none) :
    ∃ time≤fuel+1,Timed machine time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh (hn _ _)
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem binary_zero (n : ℕ) : binary n 0=List.replicate n false := by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa [binary,List.replicate_succ] using congrArg (List.cons false) ih

def flagOffset (d : Store) : ℕ := d.t+d.s+d.j+2+2*value d.state
def tableOffset (d : Store) (bits : List Bool) : ℕ :=
  d.t+3*d.s+d.j+2+value (bits++d.state)*(1+d.j+4*d.t)
def flagsPrepared (d : Store) : Store := flagsInitialized (cleared d)
def flagsStarted (d : Store) : Store := positioned (flagsPrepared d) (2*(d.t+d.s+d.j+2))
def flagsChosen (d : Store) : Store := selectionOut (flagsStarted d) false
  ((flagsStarted d).codePos+value d.state*4) (binary d.state.length (value d.state)) true
def afterHalt (d : Store) : Store := scalarOut (flagsChosen d) 0 ((flagsChosen d).codePos+2)
  (d.code.getD (flagOffset d) false)
def afterFlags (d : Store) : Store := scalarOut (afterHalt d) 1 ((afterHalt d).codePos+2)
  (d.code.getD (flagOffset d+1) false)

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
