import Proof.MachineModel.OrdinaryTransitionWalkLift

/-! A single finite call graph for binary-counted claimed execution. The
terminal branch reads only flags; continuation checks a complete vector,
rejects halted or absent rules, emits the entire tape array, and advances i. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def decisionProgram : Machine 42 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then some ⟨1,
    fun i=>if i.val=41 then some (bits 8 && bits 9) else none,fun _=>.stay⟩ else none

theorem decision_run (d : Store) :
    ∃ r,runFrom decisionProgram 1 (cfg decisionProgram.start d)=some r ∧
      r.final=cfg (1 : Fin 2) {d with countFlag:=d.lookup.halt && d.lookup.accept} ∧ r.steps=1 := by
  have hs : step decisionProgram (cfg (0 : Fin 2) d)=
      some (cfg (1 : Fin 2) {d with countFlag:=d.lookup.halt && d.lookup.accept}) := by
    simp only [step,decisionProgram]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl : decisionProgram.halted (0 : Fin 2)=false) hs).run (by rfl)

abbrev lookupStates := Fintype.card (RecoveryCalls.Control LookupRuntime.sizes)
abbrev arrayStates := Fintype.card (RecoveryCalls.Control TransitionArrayReuse.sizes)
def sizes : Fin 12→ℕ := ![2,7,lookupStates,2,6,4,lookupStates,arrayStates,4,10,5,2]
noncomputable def programs : (j : Fin 12)→Machine 42 (sizes j)
  | 0=>clearProgram
  | 1=>compareProgram
  | 2=>terminalProgram
  | 3=>decisionProgram
  | 4=>guardProgram
  | 5=>returnProgram
  | 6=>lookupProgram
  | 7=>arrayProgram
  | 8=>resetTagsProgram
  | 9=>promoteProgram
  | 10=>incrementProgram
  | 11=>clearProgram

def next (j : Fin 12) (q : Fin (sizes j)) (bits : Fin 42→Bool) : Option (Fin 12) :=
  match j.val with
  | 0=>some 1
  | 1=>if bits 41 then some 2 else some 4
  | 2=>some 3
  | 3=>none
  | 4=>if q.val=4 then some 5 else some 11
  | 5=>some 6
  | 6=>if bits 8 || !bits 10 then some 11 else some 7
  | 7=>some 8
  | 8=>some 9
  | 9=>some 10
  | 10=>some 0
  | _=>none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 12) (d e : Store) (fuel : ℕ) (r : ExecutionReceipt 42 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg r.final.control e) (hn : next j r.final.control r.final.scanned=some k) :
    ∃ time≤fuel+1,Timed machine time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh hn
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem stop_phase (j : Fin 12) (d e : Store) (fuel : ℕ) (r : ExecutionReceipt 42 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg r.final.control e) (hn : next j r.final.control r.final.scanned=none) :
    ∃ time≤fuel+1,Timed machine time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh hn
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

end NearCubicWires.RepairOrdinary.TransitionWalk
