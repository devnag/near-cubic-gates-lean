import Proof.PCP.VerifierLookupRuntimeCalls

/-! The lookup's complete flag prefix: actual query initialization, paid
navigation, ordinal search and physical halted/accepting payload reads. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagsBudget (d : Store) : ℕ :=
  3*d.code.length+3*d.t+3*d.s+7*d.j+37+(value d.state+1)*(8*d.j+14)

theorem flags_prefix (d : Store) (hp : d.codePos≤2*d.code.length+1)
    (hw : d.state.length=d.j) (hcap : 2*d.j+2≤d.cap)
    (hq : d.flagQuery.length≤2*d.j+1) (hz : d.flagCounter.length≤2*d.j+1)
    (hflags : flagOffset d+2≤d.code.length) :
    ∃ time≤flagsBudget d,Timed machine time (cfg machine.start d)
      (cfg (RecoveryCalls.code sizes 6 (programs 6).start) (afterFlags d)) := by
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
  obtain ⟨n5,hn5,hp5⟩ := call_phase 5 6 (afterHalt d) (afterFlags d) _ r5 hr5 hf5 (by intro q bits; rfl)
  have h := ((((hp0.trans hp1).trans hp2).trans hp3).trans hp4).trans hp5
  refine ⟨((((n0+n1)+n2)+n3)+n4)+n5,?_,h⟩
  change n1≤4*d.state.length+6+1 at hn1
  change n2≤3*d.code.length+3*d.t+3*d.s+3*d.j+20+1 at hn2
  rw [hw] at hn1 hn3
  unfold flagsBudget
  omega

theorem afterFlags_position (d : Store) : (afterFlags d).codePos=2*(flagOffset d+2) := by
  change 2*(d.t+d.s+d.j+2)+value d.state*4+2+2=2*(d.t+d.s+d.j+2+2*value d.state+2)
  ring

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
