import Proof.MachineModel.OrdinaryTransitionWalkAdvance

/-! One complete physical transition cycle, from binary loop test through
claimed-vector check, table lookup, memory emission and iteration increment. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cycleBudget (d : Store) : ℕ := 256*(d.lookup.code.length+1)^2+4*d.C+64*(d.w+d.lookup.code.length+1)

theorem action_suffix (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (reads : Fin v.tapeCount→Bool) (a : Action v.tapeCount v.stateCount)
    (hr : Ready d v view) (hi : d.index<d.m) (haction : v.machine.rule view.control reads=some a)
    (pre tail : List Bool) (hsource : d.lookup.scans=pre++Streaming.marks (List.ofFn reads)++tail)
    (hpos : d.lookup.scanPos=pre.length) :
    ∃ time≤TransitionArrayReuse.budget d.w d.C+12*d.lookup.t+7*d.lookup.j+4*d.w+13,
      Timed machine time (cfg (RecoveryCalls.code sizes 7 (programs 7).start) (looked d (List.ofFn reads)))
        (cfg machine.start (advanced d view reads a)) := by
  let entries := actionItems a view.heads reads
  let d1 := looked d (List.ofFn reads)
  have hfields := hr.canonical.finished_fields reads
  rw [haction] at hfields
  dsimp only at hfields
  rw [action_next_slice,hr.canonical.tapes_eq,action_tags_slice] at hfields
  have hnxt : d1.lookup.nextState=frame (binary d.lookup.j a.nextControl.val) := hfields.2.2.2.1
  have htags : d1.lookup.tags=frame (TransitionArray.tags entries) := by
    rw [actionItems_tags]
    exact hfields.2.2.2.2
  have hserial : d.serial+v.tapeCount<2^(2*d.w) := by
    have hp : v.tapeCount≤(d.m-d.index)*v.tapeCount := by
      exact Nat.le_mul_of_pos_left _ (by omega)
    exact (Nat.add_le_add_left hp d.serial).trans_lt hr.serial_fit
  apply array_suffix d1 entries (binary d.lookup.j a.nextControl.val) pre tail
    (by change (actionItems a view.heads reads).length=d.lookup.t; simp only [actionItems,List.length_ofFn]; exact hr.canonical.tapes_eq.symm)
    rfl (actionItems_valid a view.heads reads)
    (actionItems_heads d.w a view.heads reads (by intro i; have h:=hr.heads_fit i; omega))
    (by change d.serial+entries.length<2^(2*d.w); simpa only [entries,actionItems,List.length_ofFn] using hserial)
    (by change d.tape+entries.length<2^d.w; rw [hr.tape_zero]; simpa only [entries,actionItems,List.length_ofFn,Nat.zero_add] using hr.tape_fit)
    hr.difference hr.capacity
    (by change TransitionArray.loopBudget d.w entries.length≤d.C; simpa only [entries,actionItems,List.length_ofFn] using hr.array_budget)
    (by rw [actionItems_fields]; exact hr.array_eq) hr.array_blank htags
    (by rw [actionItems_scans]; exact hsource) hpos hnxt (by change (binary d.lookup.j a.nextControl.val).length=d.lookup.j; exact binary_length _ _)
    hr.canonical.state_length.le (by change d.index+1<2^d.w; exact (Nat.succ_le_of_lt hi).trans_lt hr.m_fit)

theorem round_prefix (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (reads : Fin v.tapeCount→Bool) (a : Action v.tapeCount v.stateCount)
    (hr : Ready d v view) (hi : d.index<d.m)
    (hhalt : v.machine.halted view.control=false) (haction : v.machine.rule view.control reads=some a)
    (pre tail : List Bool) (hsource : d.lookup.scans=pre++Streaming.marks (List.ofFn reads)++tail)
    (hpos : d.lookup.scanPos=pre.length) :
    ∃ time≤cycleBudget d,Timed machine time (cfg machine.start d) (cfg machine.start (advanced d view reads a)) := by
  obtain ⟨n0,hn0,hp0⟩ := test_prefix d hr.m_fit (hi.trans hr.m_fit) (by have h:=hr.capacity; omega)
  have hnode : testNode d=4 := by simp [testNode,Nat.not_le.mpr hi]
  rw [hnode] at hp0
  have hlen : (List.ofFn reads).length=d.lookup.t := by rw [List.length_ofFn,hr.canonical.tapes_eq]
  obtain ⟨n1,hn1,hp1⟩ := guard_prefix (compared d) pre (List.ofFn reads) tail hr.lookup.tags_zero hsource hpos hlen hr.lookup.scanCopy
  have hc : LookupRuntime.Canonical (guarded (compared d) (List.ofFn reads)).lookup v view.control :=
    ⟨hr.canonical.code_eq,hr.canonical.tapes_eq,hr.canonical.states_eq,hr.canonical.width_eq,hr.canonical.state_eq⟩
  have hg : LookupReady (guarded (compared d) (List.ofFn reads)) :=
    guarded_lookup_ready (compared d) (List.ofFn reads)
      ⟨hr.lookup.tags_zero,hr.lookup.position,hr.lookup.capacity,hr.lookup.scanCopy,hr.lookup.flagQuery,
        hr.lookup.flagCounter,hr.lookup.query,hr.lookup.counter,hr.lookup.nextState,hr.lookup.tags⟩ hlen
  obtain ⟨n2,hn2,hp2⟩ := selected_prefix (guarded (compared d) (List.ofFn reads)) v view.control reads hc hg pre tail hsource hpos
  have hselected : selectedNode (v.machine.halted view.control) (v.machine.rule view.control reads).isSome=7 := by
    rw [hhalt,haction]
    rfl
  rw [hselected] at hp2
  obtain ⟨n3,hn3,hp3⟩ := action_suffix d v view reads a hr hi haction pre tail hsource hpos
  change n1≤7*d.lookup.t+6 at hn1
  change n2≤128*(d.lookup.code.length+1)^2+1 at hn2
  obtain ⟨ht,_,hj,_,_⟩ := hr.canonical.dimensions reads
  have hn : n0+n1+n2+n3≤cycleBudget d := by
    unfold cycleBudget TransitionArrayReuse.budget at *
    nlinarith
  exact ⟨n0+n1+n2+n3,hn,((hp0.trans hp1).trans hp2).trans hp3⟩

end NearCubicWires.RepairOrdinary.TransitionWalk
