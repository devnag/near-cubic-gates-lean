import Proof.MachineModel.OrdinaryTransitionWalkEvents

/-! The actual binary loop test and final-state branch. Final flags are
selected by paid code navigation without inspecting any remaining witness. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compared (d : Store) : Store := {d with countFlag:=decide (d.m≤d.index)}
def testNode (d : Store) : Fin 12 := if d.m≤d.index then 2 else 4

theorem test_prefix (d : Store) (hm : d.m<2^d.w) (hi : d.index<2^d.w)
    (hc : 2*d.w+1≤d.cap) :
    ∃ time≤4*d.w+7,Timed machine time (cfg machine.start d)
      (cfg (RecoveryCalls.code sizes (testNode d) (programs (testNode d)).start) (compared d)) := by
  obtain ⟨r0,hr0,hf0,_⟩ := clear_run d
  obtain ⟨n0,hn0,hp0⟩ := call_phase 0 1 d {d with countFlag:=false} _ r0 hr0 hf0 rfl
  obtain ⟨r1,hr1,hf1,_⟩ := compare_run {d with countFlag:=false} hm hi rfl hc
  have hnext : next 1 r1.final.control r1.final.scanned=some (testNode d) := by
    rw [hf1]
    change (if decide (d.m≤d.index) then some 2 else some 4)=some (testNode d)
    by_cases h:d.m≤d.index <;> simp [testNode,h]
  obtain ⟨n1,hn1,hp1⟩ := call_phase 1 (testNode d) {d with countFlag:=false} (compared d) _ r1 hr1 hf1 hnext
  change n1≤4*d.w+4+1 at hn1
  exact ⟨n0+n1,by omega,hp0.trans hp1⟩

def terminalOut (d : Store) : Store :=
  {d with
    lookup:=LookupRuntime.afterFlags d.lookup,
    tagPos:=0,
    countFlag:=d.lookup.code.getD (LookupRuntime.flagOffset d.lookup) false &&
      d.lookup.code.getD (LookupRuntime.flagOffset d.lookup+1) false}

theorem terminal_tail (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (hcanonical : LookupRuntime.Canonical d.lookup v q) (htag : d.tagPos=0)
    (hp : d.lookup.codePos≤2*d.lookup.code.length+1)
    (hcap : 2*d.lookup.j+2≤d.lookup.cap)
    (hq : d.lookup.flagQuery.length≤2*d.lookup.j+1)
    (hz : d.lookup.flagCounter.length≤2*d.lookup.j+1) :
    ∃ time≤128*(d.lookup.code.length+1)^2+3,Timed machine time
      (cfg (RecoveryCalls.code sizes 2 (programs 2).start) d)
      (cfg (RecoveryCalls.controlCode sizes none) (terminalOut d)) := by
  obtain ⟨base,hbase,hbf,_,_,_⟩ := LookupRuntime.TerminalFlags.canonical_flags_run d.lookup v q
    hcanonical hp hcap hq hz
  have hbf' : base.final=LookupRuntime.cfg base.final.control (LookupRuntime.afterFlags d.lookup) := by rw [hbf]; rfl
  obtain ⟨r0,hr0,hf0,_⟩ := lift_lookup LookupRuntime.TerminalFlags.machine d
    (LookupRuntime.afterFlags d.lookup) _ base htag hbase hbf'
  let d1 : Store := {d with lookup:=LookupRuntime.afterFlags d.lookup,tagPos:=0}
  obtain ⟨n0,hn0,hp0⟩ := call_phase 2 3 d d1 _ r0 hr0 hf0 rfl
  obtain ⟨r1,hr1,hf1,_⟩ := decision_run d1
  have hfinal : r1.final=cfg r1.final.control (terminalOut d) := by rw [hf1]; rfl
  obtain ⟨n1,hn1,hp1⟩ := stop_phase 3 d1 (terminalOut d) _ r1 hr1 hfinal rfl
  exact ⟨n0+n1,by omega,hp0.trans hp1⟩

theorem terminal_run (d : Store) (v : OrdinaryVerifier) (q : Fin v.stateCount)
    (hcanonical : LookupRuntime.Canonical d.lookup v q) (htag : d.tagPos=0)
    (hm : d.m<2^d.w) (hi : d.index=d.m) (hc : 2*d.w+1≤d.cap)
    (hp : d.lookup.codePos≤2*d.lookup.code.length+1)
    (hcap : 2*d.lookup.j+2≤d.lookup.cap)
    (hq : d.lookup.flagQuery.length≤2*d.lookup.j+1)
    (hz : d.lookup.flagCounter.length≤2*d.lookup.j+1) :
    ∃ r,runFrom machine (128*(d.lookup.code.length+1)^2+4*d.w+10) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (terminalOut (compared d)) ∧
      r.steps≤128*(d.lookup.code.length+1)^2+4*d.w+10 ∧
      r.final.tapes 41=[v.machine.halted q && v.accepting q] := by
  obtain ⟨n0,hn0,hp0⟩ := test_prefix d hm (by omega) hc
  have hnode : testNode d=2 := by simp [testNode,hi]
  rw [hnode] at hp0
  obtain ⟨n1,hn1,hp1⟩ := terminal_tail (compared d) v q hcanonical htag hp hcap hq hz
  change n1≤128*(d.lookup.code.length+1)^2+3 at hn1
  have h := hp0.trans hp1
  have hn : n0+n1≤128*(d.lookup.code.length+1)^2+4*d.w+10 := by omega
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg])
  have hm := runFrom_moreFuel machine _ (128*(d.lookup.code.length+1)^2+4*d.w+10-(n0+n1)) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hf,by omega,?_⟩
  rw [hf]
  change [d.lookup.code.getD (LookupRuntime.flagOffset d.lookup) false &&
    d.lookup.code.getD (LookupRuntime.flagOffset d.lookup+1) false]=_
  rw [hcanonical.halt_bit,hcanonical.accept_bit]

end NearCubicWires.RepairOrdinary.TransitionWalk
