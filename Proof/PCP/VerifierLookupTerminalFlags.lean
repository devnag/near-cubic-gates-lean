import Proof.PCP.VerifierLookupDecoded

/-! Terminal-state lookup executes only the paid flag prefix. It never reads
any claimed vector, including for a zero-step certificate. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime.TerminalFlags
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next (j : Fin 14) (_ : Fin (sizes j)) (_ : Fin 21 → Bool) : Option (Fin 14) :=
  if h:j.val<5 then some ⟨j.val+1,by omega⟩ else none
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

theorem flags_run (d : Store) (hp : d.codePos≤2*d.code.length+1)
    (hw : d.state.length=d.j) (hcap : 2*d.j+2≤d.cap)
    (hq : d.flagQuery.length≤2*d.j+1) (hz : d.flagCounter.length≤2*d.j+1)
    (hflags : flagOffset d+2≤d.code.length) :
    ∃ r,runFrom machine (flagsBudget d) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (afterFlags d) ∧ r.steps≤flagsBudget d := by
  obtain ⟨r0,hr0,hf0,_⟩ := clear_run d
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d (cleared d) _ r0 hr0 hf0 (by intro q bits; rfl)
  obtain ⟨r1,hr1,hf1,_⟩ := flags_query_run (cleared d) rfl
    (by change d.flagQuery.length≤2*d.state.length+1; omega)
    (by change d.flagCounter.length≤2*d.state.length+1; omega)
    (by change 2*d.state.length+2≤d.cap; omega)
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 2 (cleared d) (flagsPrepared d) _ r1 hr1 hf1 (by intro q bits; rfl)
  obtain ⟨r2,hr2,hf2,_⟩ := flags_navigation_run (flagsPrepared d) hp
  obtain ⟨n2,hn2,hp2⟩ := call_phase 2 3 (flagsPrepared d) (flagsStarted d) _ r2 hr2 hf2 (by intro q bits; rfl)
  obtain ⟨r3,hr3,hf3,_⟩ := flags_select_run (flagsStarted d) d.state rfl
    (by change frame (List.replicate d.state.length false)=frame (binary d.state.length 0); rw [binary_zero])
    rfl (by change 2*d.state.length+1≤d.cap; omega)
  obtain ⟨n3,hn3,hp3⟩ := call_phase 3 4 (flagsStarted d) (flagsChosen d) _ r3 hr3 hf3 (by intro q bits; rfl)
  have hflagpos : (flagsChosen d).codePos=2*flagOffset d := by
    change 2*(d.t+d.s+d.j+2)+value d.state*4=2*(d.t+d.s+d.j+2+2*value d.state)
    ring
  obtain ⟨r4,hr4,hf4,_⟩ := scalar_slice_run 0 (flagsChosen d) (flagOffset d) hflagpos (by change flagOffset d<d.code.length; omega)
  obtain ⟨n4,hn4,hp4⟩ := call_phase 4 5 (flagsChosen d) (afterHalt d) _ r4 hr4 hf4 (by intro q bits; rfl)
  have hacceptpos : (afterHalt d).codePos=2*(flagOffset d+1) := by
    change (flagsChosen d).codePos+2=2*(flagOffset d+1)
    rw [hflagpos]
    omega
  obtain ⟨r5,hr5,hf5,_⟩ := scalar_slice_run 1 (afterHalt d) (flagOffset d+1) hacceptpos
    (by change flagOffset d+1<d.code.length; omega)
  obtain ⟨n5,hn5,hp5⟩ := stop_phase 5 (afterHalt d) (afterFlags d) _ r5 hr5 hf5 (by intro q bits; rfl)
  have h := ((((hp0.trans hp1).trans hp2).trans hp3).trans hp4).trans hp5
  change n1≤4*d.state.length+6+1 at hn1
  change n2≤3*d.code.length+3*d.t+3*d.s+3*d.j+20+1 at hn2
  rw [hw] at hn1 hn3
  have hn : ((((n0+n1)+n2)+n3)+n4)+n5≤flagsBudget d := by
    unfold flagsBudget
    omega
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg])
  have hm := runFrom_moreFuel machine _ (flagsBudget d-(((((n0+n1)+n2)+n3)+n4)+n5)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hf,by omega⟩

theorem canonical_flags_run (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (hc : Canonical d v q) (hp : d.codePos≤2*d.code.length+1)
    (hcap : 2*d.j+2≤d.cap) (hq : d.flagQuery.length≤2*d.j+1)
    (hz : d.flagCounter.length≤2*d.j+1) :
    ∃ r,runFrom machine (128*(d.code.length+1)^2) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (afterFlags d) ∧
      r.steps≤128*(d.code.length+1)^2 ∧
      r.final.tapes 8=[v.machine.halted q] ∧ r.final.tapes 9=[v.accepting q] := by
  obtain ⟨r,hr,hf,hs⟩ := flags_run d hp hc.state_length hcap hq hz hc.flag_fit
  have hb : flagsBudget d≤128*(d.code.length+1)^2 := by
    have h := hc.budget_le (fun _=>false)
    unfold budget at h
    omega
  have hm := runFrom_moreFuel machine _ (128*(d.code.length+1)^2-flagsBudget d) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r,hm,hf,hs.trans hb,?_,?_⟩
  · rw [hf]
    exact congrArg (fun b=>[b]) hc.halt_bit
  · rw [hf]
    exact congrArg (fun b=>[b]) hc.accept_bit

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime.TerminalFlags
