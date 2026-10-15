import Proof.MachineModel.UInputEntryLayout

/-! The single total U-input program: syntax scan, a physical branch on its
flag, then paid extraction/scalars. Malformed or truncated fields stop before
the valid-input phase; no witness tape is consulted. -/
namespace NearCubicWires.RepairOrdinary.UInputEntry
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 2 → ℕ := ![17,139]
noncomputable def programs : (j : Fin 2) → Machine 49 (sizes j)
  | ⟨0,_⟩ => scanPhase
  | ⟨1,_⟩ => validMachine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (scan : Fin 49 → Bool) : Option (Fin 2) :=
  if j.val=0 && scan 1 then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def budget (raw : List Bool) := 400*(raw.length+1)*PCPResourceLedger.q raw.length^2

theorem raw_length (code x bound padding : List Bool) :
    3 ≤ (VerifierInputFields.source code x bound padding).length ∧
    x.length ≤ (VerifierInputFields.source code x bound padding).length := by
  simp only [VerifierInputFields.source,List.length_append,frame_length]
  omega

theorem valid_budget (code x bound padding : List Bool) :
    let raw := VerifierInputFields.source code x bound padding
    (4*raw.length+4)+1+(validBudget raw x+1) ≤ budget raw := by
  let raw := VerifierInputFields.source code x bound padding
  have hx : x.length ≤ raw.length := (raw_length code x bound padding).2
  have hb := UInputScalars.budget_bound raw x hx
  have hq : 1 ≤ PCPResourceLedger.q raw.length^2 := by
    apply Nat.one_le_pow
    simp [PCPResourceLedger.q]
  have hn : raw.length+1 ≤ (raw.length+1)*PCPResourceLedger.q raw.length^2 := by nlinarith
  change _ ≤ budget raw
  dsimp only [validBudget,budget] at *
  nlinarith

theorem valid_shape_run (code x bound padding : List Bool) :
    let raw := VerifierInputFields.source code x bound padding
    ∃ g carry reset degree cap scratch r,
      run machine (budget raw) (input raw)=some r ∧
      r.final.tapes=endpoint raw code x bound g carry reset degree cap scratch ∧
      r.final.heads=heads ∧ r.steps ≤ budget raw := by
  let raw := VerifierInputFields.source code x bound padding
  obtain ⟨first,hfirst,ht,hh,hs⟩ := scan_ready raw
  have hsyntax : UInputSyntax.accepts 0 raw=true :=
    (UInputSyntax.accepts_iff raw).mpr ⟨code,x,bound,padding,rfl⟩
  have hn : next 0 first.final.control first.final.scanned=some 1 := by
    simp [next,Configuration.scanned,ht,hh,afterScan,hsyntax,readTapeBit]
  obtain ⟨n,hncost,hcall⟩ := call_receipt sizes programs 0 next 0 1 (4*raw.length+4)
    _ first hfirst hn
  have hre : RecoveryCalls.restarted (programs 1) first.final.heads first.final.tapes=
      initialConfiguration (programs 1) (afterScan raw) := by
    apply configuration_ext
    · rfl
    · exact funext hh
    · exact ht
  rw [hre] at hcall
  obtain ⟨g,carry,reset,degree,cap,scratch,last,hlast,hlt,hlh,hls⟩ := valid_run code x bound padding
  obtain ⟨m,hmcost,hstop⟩ := stop_receipt sizes programs 0 next 1 (validBudget raw x)
    _ last hlast (by simp [next])
  have hall := hcall.trans hstop
  change Timed machine (n+m) (initialConfiguration machine (input raw)) _ at hall
  obtain ⟨r,hr,hf,hrs⟩ := hall.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hbudget : (4*raw.length+4)+1+(validBudget raw x+1) ≤ budget raw :=
    valid_budget code x bound padding
  have hb : n+m ≤ budget raw := by omega
  have hmore := run_moreFuel machine (n+m) (budget raw-(n+m)) _ r hr
  rw [Nat.add_sub_of_le hb] at hmore
  refine ⟨g,carry,reset,degree,cap,scratch,r,hmore,?_,?_,?_⟩
  · simpa [hf,RecoveryCalls.stopped] using hlt
  · simpa [hf,RecoveryCalls.stopped] using hlh
  · change r.steps ≤ budget raw
    omega

theorem invalid_shape_run (raw : List Bool) (hbad : ¬UInputSyntax.Fields raw) :
    ∃ r,run machine (budget raw) (input raw)=some r ∧
      r.final.tapes=afterScan raw ∧ (∀ i,r.final.heads i=0) ∧ r.steps ≤ 4*raw.length+5 := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := scan_ready raw
  have hsyntax : UInputSyntax.accepts 0 raw=false := by
    cases h : UInputSyntax.accepts 0 raw
    · rfl
    · exact False.elim (hbad ((UInputSyntax.accepts_iff raw).mp h))
  have hn : next 0 first.final.control first.final.scanned=none := by
    simp [next,Configuration.scanned,ht,hh,afterScan,hsyntax,readTapeBit]
  obtain ⟨n,hncost,hstop⟩ := stop_receipt sizes programs 0 next 0 (4*raw.length+4)
    _ first hfirst hn
  change Timed machine n (initialConfiguration machine (input raw)) _ at hstop
  obtain ⟨r,hr,hf,hrs⟩ := hstop.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hq : 1 ≤ PCPResourceLedger.q raw.length^2 := by
    apply Nat.one_le_pow
    simp [PCPResourceLedger.q]
  have hb : n ≤ budget raw := by dsimp [budget]; nlinarith
  have hmore := run_moreFuel machine n (budget raw-n) _ r hr
  rw [Nat.add_sub_of_le hb] at hmore
  exact ⟨r,hmore,by simpa [hf,RecoveryCalls.stopped] using ht,
    by intro i; simpa [hf,RecoveryCalls.stopped] using hh i,by omega⟩

end NearCubicWires.RepairOrdinary.UInputEntry
