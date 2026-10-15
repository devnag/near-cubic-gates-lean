import Proof.PCP.VerifierLookupRuntimeTable

/-! The complete fixed runtime lookup, with literal reusable endpoints.
All cursor/address/query production and field extraction are in its run. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (d : Store) (bits : List Bool) : ℕ := flagsBudget d+tableBudget d bits

theorem lookup_run (d : Store) (pre bits tail : List Bool)
    (hpos : d.codePos≤2*d.code.length+1)
    (hs : d.scans=pre++Streaming.marks bits++tail) (hp : d.scanPos=pre.length)
    (hl : bits.length=d.t) (hw : d.state.length=d.j) (hcap : 2*(d.t+d.j)+2≤d.cap)
    (hsc : d.scanCopy.length≤2*d.t+1)
    (hfq : d.flagQuery.length≤2*d.j+1) (hfz : d.flagCounter.length≤2*d.j+1)
    (hq : d.query.length≤2*(d.t+d.j)+1) (hz : d.counter.length≤2*(d.t+d.j)+1)
    (hn : d.nextState.length≤2*d.j+1) (htags : d.tags.length≤8*d.t+1)
    (hflags : flagOffset d+2≤d.code.length)
    (htable : tableOffset d bits+1+d.j+4*d.t≤d.code.length) :
    ∃ r,runFrom machine (budget d bits) (cfg machine.start d)=some r ∧
      r.final=cfg (RecoveryCalls.controlCode sizes none) (finished d bits) ∧ r.steps≤budget d bits := by
  obtain ⟨n,hnTime,hp0⟩ := flags_prefix d hpos hw (by omega) hfq hfz hflags
  obtain ⟨m,hmTime,hp1⟩ := table_suffix d pre bits tail hs hp hl hw hcap hsc hq hz hn htags hflags htable
  obtain ⟨r,hr,hrf,hrs⟩ := (hp0.trans hp1).run (by simp [machine,RecoveryCalls.machine,cfg])
  have htime : n+m≤budget d bits := by unfold budget; omega
  have hm := runFrom_moreFuel machine (n+m) (budget d bits-(n+m)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  exact ⟨r,hm,hrf,hrs.trans_le htime⟩

theorem finished_sources (d : Store) (bits : List Bool) :
    (finished d bits).code=d.code ∧ (finished d bits).state=d.state ∧
    (finished d bits).scans=d.scans ∧ (finished d bits).scanPos=d.scanPos := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem finished_fields (d : Store) (bits : List Bool) :
    (finished d bits).halt=d.code.getD (flagOffset d) false ∧
    (finished d bits).accept=d.code.getD (flagOffset d+1) false ∧
    (finished d bits).present=d.code.getD (tableOffset d bits) false ∧
    (finished d bits).nextState=frame (slice d.code (tableOffset d bits+1) d.j) ∧
    (finished d bits).tags=frame (slice d.code (tableOffset d bits+1+d.j) (4*d.t)) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem finished_position (d : Store) (bits : List Bool) :
    (finished d bits).codePos=2*(tableOffset d bits+1+d.j+4*d.t) := by
  change 2*(d.t+3*d.s+d.j+2)+value (bits++d.state)*(2*(1+d.j+4*d.t))+2+2*d.j+8*d.t=
    2*(d.t+3*d.s+d.j+2+value (bits++d.state)*(1+d.j+4*d.t)+1+d.j+4*d.t)
  ring

theorem finished_widths (d : Store) (bits : List Bool)
    (hl : bits.length=d.t) (hw : d.state.length=d.j)
    (htable : tableOffset d bits+1+d.j+4*d.t≤d.code.length) :
    (finished d bits).flagQuery.length=2*d.j+1 ∧
    (finished d bits).flagCounter.length=2*d.j+1 ∧
    (finished d bits).query.length=2*(d.t+d.j)+1 ∧
    (finished d bits).counter.length=2*(d.t+d.j)+1 ∧
    (finished d bits).scanCopy.length=2*d.t+1 ∧
    (finished d bits).nextState.length=2*d.j+1 ∧
    (finished d bits).tags.length=8*d.t+1 := by
  have hn := Sequential.slice_length d.code (tableOffset d bits+1) d.j (by omega)
  have ht := Sequential.slice_length d.code (tableOffset d bits+1+d.j) (4*d.t) htable
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change (frame d.state).length=_
    simp [hw]
  · change (frame (binary d.state.length (value d.state))).length=_
    simp [hw]
  · change (frame (bits++d.state)).length=_
    simp [hl,hw]
  · change (frame (binary (bits++d.state).length (value (bits++d.state)))).length=_
    simp [hl,hw]
  · change (frame bits).length=_
    simp [hl]
  · change (frame (slice d.code (tableOffset d bits+1) d.j)).length=_
    simp [hn]
  · change (frame (slice d.code (tableOffset d bits+1+d.j) (4*d.t))).length=_
    simp [ht]
    omega

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
