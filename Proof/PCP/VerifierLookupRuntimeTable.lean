import Proof.PCP.VerifierLookupRuntimeFlags

/-! The entire transition-table suffix consumes the same retained witness
vector, computes its query, navigates and selects, then extracts actual fields. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
open LocalBitMultitape RepairOrdinary RecoveryExecution SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tablePrepared (d : Store) (bits : List Bool) : Store := tableInitialized (claimed (afterFlags d) bits) bits
def tableCleared (d : Store) (bits : List Bool) : Store := cleared (tablePrepared d bits)
def tableStarted (d : Store) (bits : List Bool) : Store :=
  positioned (tableCleared d bits) (2*(d.t+3*d.s+d.j+2))
def tableChosen (d : Store) (bits : List Bool) : Store :=
  {d with
    codePos:=2*(d.t+3*d.s+d.j+2)+value (bits++d.state)*(2*(1+d.j+4*d.t)),
    halt:=d.code.getD (flagOffset d) false,accept:=d.code.getD (flagOffset d+1) false,
    flag:=true,flagQuery:=frame d.state,flagCounter:=frame (binary d.state.length (value d.state)),
    query:=frame (bits++d.state),counter:=frame (binary (bits++d.state).length (value (bits++d.state))),
    scanCopy:=frame bits}
def afterPresence (d : Store) (bits : List Bool) : Store := scalarOut (tableChosen d bits) 2
  ((tableChosen d bits).codePos+2) (d.code.getD (tableOffset d bits) false)
def afterNext (d : Store) (bits : List Bool) : Store := fieldOut (afterPresence d bits) false
  ((afterPresence d bits).codePos+2*d.j) (frame (slice d.code (tableOffset d bits+1) d.j))
def finished (d : Store) (bits : List Bool) : Store := fieldOut (afterNext d bits) true
  ((afterNext d bits).codePos+8*d.t) (frame (slice d.code (tableOffset d bits+1+d.j) (4*d.t)))
def tableBudget (d : Store) (bits : List Bool) : ℕ :=
  3*d.code.length+30*d.t+9*d.s+11*d.j+52+
    (value (bits++d.state)+1)*(8*(d.t+d.j)+3*d.j+12*d.t+27)

-- reason: Five fixed 21-tape call endpoints require finite store normalization; the
-- selected store is flattened and the extraction suffix is checked separately.
set_option maxHeartbeats 500000 in
theorem table_query_prefix (d : Store) (pre bits tail : List Bool)
    (hs : d.scans=pre++Streaming.marks bits++tail) (hp : d.scanPos=pre.length)
    (hl : bits.length=d.t) (hw : d.state.length=d.j) (hcap : 2*(d.t+d.j)+2≤d.cap)
    (hsc : d.scanCopy.length≤2*d.t+1)
    (hq : d.query.length≤2*(d.t+d.j)+1) (hz : d.counter.length≤2*(d.t+d.j)+1)
    (hflags : flagOffset d+2≤d.code.length) :
    ∃ time≤3*d.code.length+14*d.t+9*d.s+7*d.j+43+
      (value (bits++d.state)+1)*(8*(d.t+d.j)+3*d.j+12*d.t+27),Timed machine time
      (cfg (RecoveryCalls.code sizes 6 (programs 6).start) (afterFlags d))
      (cfg (RecoveryCalls.code sizes 11 (programs 11).start) (tableChosen d bits)) := by
  obtain ⟨r0,hr0,hf0,_⟩ := claimed_run (afterFlags d) pre bits tail hs hp hl hsc
  obtain ⟨n0,hn0,hp0⟩ := call_phase 6 7 (afterFlags d) (claimed (afterFlags d) bits) _ r0 hr0 hf0 (by intro q b; rfl)
  obtain ⟨r1,hr1,hf1,_⟩ := table_query_run (claimed (afterFlags d) bits) bits rfl
    (by change d.query.length≤2*(bits.length+d.state.length)+1; omega)
    (by change d.counter.length≤2*(bits.length+d.state.length)+1; omega)
    (by change 2*(bits.length+d.state.length)+2≤d.cap; omega)
  obtain ⟨n1,hn1,hp1⟩ := call_phase 7 8 (claimed (afterFlags d) bits) (tablePrepared d bits) _ r1 hr1 hf1 (by intro q b; rfl)
  obtain ⟨r2,hr2,hf2,_⟩ := clear_run (tablePrepared d bits)
  obtain ⟨n2,hn2,hp2⟩ := call_phase 8 9 (tablePrepared d bits) (tableCleared d bits) _ r2 hr2 hf2 (by intro q b; rfl)
  have hreset : (tableCleared d bits).codePos≤2*(tableCleared d bits).code.length+1 := by
    change (afterFlags d).codePos≤2*d.code.length+1
    rw [afterFlags_position]
    omega
  obtain ⟨r3,hr3,hf3,_⟩ := table_navigation_run (tableCleared d bits) hreset
  obtain ⟨n3,hn3,hp3⟩ := call_phase 9 10 (tableCleared d bits) (tableStarted d bits) _ r3 hr3 hf3 (by intro q b; rfl)
  obtain ⟨r4,hr4,hf4,_⟩ := table_select_run (tableStarted d bits) (bits++d.state) rfl
    (by change frame (List.replicate (bits.length+d.state.length) false)=frame (binary (bits++d.state).length 0)
        simp only [List.length_append,binary_zero])
    rfl (by change 2*(bits++d.state).length+1≤d.cap; rw [List.length_append,hl,hw]; omega)
  obtain ⟨n4,hn4,hp4⟩ := call_phase 10 11 (tableStarted d bits) (tableChosen d bits) _ r4 hr4 hf4 (by intro q b; rfl)
  have h := (((hp0.trans hp1).trans hp2).trans hp3).trans hp4
  refine ⟨(((n0+n1)+n2)+n3)+n4,?_,h⟩
  change n0≤7*d.t+5+1 at hn0
  change n1≤4*(bits.length+d.state.length)+6+1 at hn1
  change n3≤3*d.code.length+3*d.t+9*d.s+3*d.j+26+1 at hn3
  change n4≤(value (bits++d.state)+1)*(8*(bits++d.state).length+3*d.j+12*d.t+27)+1 at hn4
  rw [hl,hw] at hn1
  rw [List.length_append,hl,hw] at hn4
  omega

theorem table_fields_suffix (d : Store) (bits : List Bool)
    (hn : d.nextState.length≤2*d.j+1) (htags : d.tags.length≤8*d.t+1)
    (htable : tableOffset d bits+1+d.j+4*d.t≤d.code.length) :
    ∃ time≤16*d.t+4*d.j+9,Timed machine time
      (cfg (RecoveryCalls.code sizes 11 (programs 11).start) (tableChosen d bits))
      (cfg (RecoveryCalls.controlCode sizes none) (finished d bits)) := by
  have htablepos : (tableChosen d bits).codePos=2*tableOffset d bits := by
    change 2*(d.t+3*d.s+d.j+2)+value (bits++d.state)*(2*(1+d.j+4*d.t))=
      2*(d.t+3*d.s+d.j+2+value (bits++d.state)*(1+d.j+4*d.t))
    ring
  obtain ⟨r5,hr5,hf5,_⟩ := scalar_slice_run 2 (tableChosen d bits) (tableOffset d bits) htablepos
    (by change tableOffset d bits<d.code.length; omega)
  obtain ⟨n5,hn5,hp5⟩ := call_phase 11 12 (tableChosen d bits) (afterPresence d bits) _ r5 hr5 hf5 (by intro q b; rfl)
  have hnextpos : (afterPresence d bits).codePos=2*(tableOffset d bits+1) := by
    change (tableChosen d bits).codePos+2=2*(tableOffset d bits+1)
    rw [htablepos]
    omega
  obtain ⟨r6,hr6,hf6,_⟩ := field_slice_run false (afterPresence d bits) (tableOffset d bits+1) hnextpos
    (by change tableOffset d bits+1+d.j≤d.code.length; omega) hn
  obtain ⟨n6,hn6,hp6⟩ := call_phase 12 13 (afterPresence d bits) (afterNext d bits) _ r6 hr6 hf6 (by intro q b; rfl)
  have htagpos : (afterNext d bits).codePos=2*(tableOffset d bits+1+d.j) := by
    change (afterPresence d bits).codePos+2*d.j=2*(tableOffset d bits+1+d.j)
    rw [hnextpos]
    omega
  obtain ⟨r7,hr7,hf7,_⟩ := field_slice_run true (afterNext d bits) (tableOffset d bits+1+d.j) htagpos
    htable (by change d.tags.length≤2*(4*d.t)+1; omega)
  have hlast : fieldOut (afterNext d bits) true
      ((afterNext d bits).codePos+2*(fieldWidth (afterNext d bits) true))
      (frame (slice (afterNext d bits).code (tableOffset d bits+1+d.j) (fieldWidth (afterNext d bits) true)))=finished d bits := by
    change fieldOut (afterNext d bits) true ((afterNext d bits).codePos+2*(4*d.t)) _=
      fieldOut (afterNext d bits) true ((afterNext d bits).codePos+8*d.t) _
    congr 2
    omega
  rw [hlast] at hf7
  obtain ⟨n7,hn7,hp7⟩ := stop_phase 13 (afterNext d bits) (finished d bits) _ r7 hr7 hf7 (by intro q b; rfl)
  have h := (hp5.trans hp6).trans hp7
  refine ⟨n5+n6+n7,?_,h⟩
  change n6≤4*d.j+2+1 at hn6
  change n7≤4*(4*d.t)+2+1 at hn7
  omega

theorem table_suffix (d : Store) (pre bits tail : List Bool)
    (hs : d.scans=pre++Streaming.marks bits++tail) (hp : d.scanPos=pre.length)
    (hl : bits.length=d.t) (hw : d.state.length=d.j) (hcap : 2*(d.t+d.j)+2≤d.cap)
    (hsc : d.scanCopy.length≤2*d.t+1)
    (hq : d.query.length≤2*(d.t+d.j)+1) (hz : d.counter.length≤2*(d.t+d.j)+1)
    (hn : d.nextState.length≤2*d.j+1) (htags : d.tags.length≤8*d.t+1)
    (hflags : flagOffset d+2≤d.code.length)
    (htable : tableOffset d bits+1+d.j+4*d.t≤d.code.length) :
    ∃ time≤tableBudget d bits,Timed machine time
      (cfg (RecoveryCalls.code sizes 6 (programs 6).start) (afterFlags d))
      (cfg (RecoveryCalls.controlCode sizes none) (finished d bits)) := by
  obtain ⟨n,hnTime,hp⟩ := table_query_prefix d pre bits tail hs hp hl hw hcap hsc hq hz hflags
  obtain ⟨m,hm,ht⟩ := table_fields_suffix d bits hn htags htable
  exact ⟨n+m,by unfold tableBudget; omega,hp.trans ht⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupRuntime
