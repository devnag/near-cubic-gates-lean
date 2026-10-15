import Proof.PCP.VerifierLookupSkipSteps

/-! This one fixed finite program skips one encoded record: presence,
actual unary j next-state bits, and four traversals of actual capped t. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupSkip
open LocalBitMultitape RepairOrdinary RecoveryExecution LookupSelect
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sizes : Fin 6 → ℕ := ![3,4,4,4,4,4]
noncomputable def programs : (j : Fin 6) → Machine 7 (sizes j)
  | 0 => two
  | 1 => walkProgram false
  | 2 => walkProgram true
  | 3 => walkProgram true
  | 4 => walkProgram true
  | 5 => walkProgram true

def next (j : Fin 6) (_ : Fin (sizes j)) (_ : Fin 7 → Bool) : Option (Fin 6) :=
  if h:j.val<5 then some ⟨j.val+1,by omega⟩ else none
noncomputable def record := RecoveryCalls.machine sizes programs 0 next

theorem call_phase (j k : Fin 6) (d e : Store) (fuel : ℕ) (q : Fin (sizes j))
    (r : ExecutionReceipt 7 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : ∀ c bits,next j c bits=some k) :
    ∃ time≤fuel+1,Timed record time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.code sizes k (programs k).start) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next j k r.final hh (hn _ _)
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem stop_phase (j : Fin 6) (d e : Store) (fuel : ℕ) (q : Fin (sizes j))
    (r : ExecutionReceipt 7 (sizes j))
    (hr : runFrom (programs j) fuel (cfg (programs j).start d)=some r)
    (hf : r.final=cfg q e) (hn : ∀ c bits,next j c bits=none) :
    ∃ time≤fuel+1,Timed record time
      (cfg (RecoveryCalls.code sizes j (programs j).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) e) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs j) fuel _ r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next j r.final hh (hn _ _)
  have hj := hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)
  rw [hf] at hj
  have hs := runFrom_steps_le (programs j) fuel _ r hr
  exact ⟨r.steps+1,by omega,hj⟩

theorem record_run (d : Store) (j t c : ℕ)
    (hj : d.driverA=CompareMachine.word j) (ht : d.driverB=CapMachine.counter c t) :
    ∃ r,runFrom record (3*j+12*t+18) (cfg record.start d)=some r ∧
      r.final=cfg r.final.control (advance d (2*(1+j+4*t))) ∧ r.steps≤3*j+12*t+18 := by
  let d0 := advance d 2
  let d1 := advance d0 (2*j)
  let d2 := advance d1 (2*t)
  let d3 := advance d2 (2*t)
  let d4 := advance d3 (2*t)
  let d5 := advance d4 (2*t)
  obtain ⟨r0,hr0,hf0,_⟩ := two_run d
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d d0 _ _ r0 hr0 hf0 (by intro q bits; rfl)
  obtain ⟨r1,hr1,hf1,_⟩ := walk_run false d0 j 0 (by
    change d.driverA=ZeroPadding.pad 0 (CompareMachine.word j)
    simpa only [ZeroPadding.pad_zero] using hj)
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 2 d0 d1 _ _ r1 hr1 hf1 (by intro q bits; rfl)
  obtain ⟨r2,hr2,hf2,_⟩ := walk_run true d1 t (c+2) ht
  obtain ⟨n2,hn2,hp2⟩ := call_phase 2 3 d1 d2 _ _ r2 hr2 hf2 (by intro q bits; rfl)
  obtain ⟨r3,hr3,hf3,_⟩ := walk_run true d2 t (c+2) ht
  obtain ⟨n3,hn3,hp3⟩ := call_phase 3 4 d2 d3 _ _ r3 hr3 hf3 (by intro q bits; rfl)
  obtain ⟨r4,hr4,hf4,_⟩ := walk_run true d3 t (c+2) ht
  obtain ⟨n4,hn4,hp4⟩ := call_phase 4 5 d3 d4 _ _ r4 hr4 hf4 (by intro q bits; rfl)
  obtain ⟨r5,hr5,hf5,_⟩ := walk_run true d4 t (c+2) ht
  obtain ⟨n5,hn5,hp5⟩ := stop_phase 5 d4 d5 _ _ r5 hr5 hf5 (by intro q bits; rfl)
  have hp := ((((hp0.trans hp1).trans hp2).trans hp3).trans hp4).trans hp5
  have hout : d5=advance d (2*(1+j+4*t)) := by
    dsimp only [d5,d4,d3,d2,d1,d0,advance]
    congr 1
    omega
  rw [hout] at hp
  obtain ⟨r,hr,hrf,hrs⟩ := hp.run (by simp [record,RecoveryCalls.machine,cfg])
  have htime : ((((n0+n1)+n2)+n3)+n4)+n5≤3*j+12*t+18 := by omega
  have hm := runFrom_moreFuel record _ ((3*j+12*t+18)-(((((n0+n1)+n2)+n3)+n4)+n5)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  exact ⟨r,hm,by rw [hrf]; rfl,hrs.trans_le htime⟩

noncomputable def flagPair := Composition.machine two two

theorem flagPair_run (d : Store) :
    ∃ r,runFrom flagPair 5 (cfg flagPair.start d)=some r ∧
      r.final=cfg r.final.control (advance d 4) := by
  obtain ⟨a,ha,haf,_⟩ := two_run d
  obtain ⟨b,hb,hbf,_⟩ := two_run (advance d 2)
  have he : Composition.restart a.final two.start=cfg 0 (advance d 2) := by rw [haf]; rfl
  rw [←he] at hb
  have hj := Composition.run_join two two 2 2 (cfg 0 d) a b ha hb
  refine ⟨Composition.joinedReceipt a b,hj,?_⟩
  simp only [Composition.joinedReceipt,hbf]
  have hp : advance (advance d 2) 2=advance d 4 := by simp [advance,Nat.add_assoc]
  rw [hp]
  rfl

end NearCubicWires.RepairSource.VerifierDecoding.LookupSkip
