import Proof.MachineModel.OrdinaryTransitionWalkRejectHeads

/-! A halted source control or absent selected rule rejects after the paid
literal field guard and lookup, before any transition event is appended. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem failed_round (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (reads : Fin v.tapeCount→Bool) (hr : Ready d v view) (hi : d.index<d.m)
    (hbad : v.machine.halted view.control=true ∨ v.machine.rule view.control reads=none)
    (pre tail : List Bool) (hsource : d.lookup.scans=pre++Streaming.marks (List.ofFn reads)++tail)
    (hpos : d.lookup.scanPos=pre.length) :
    ∃ time≤cycleBudget d,∃ output,Timed machine time (cfg machine.start d) output ∧
      machine.halted output.control=true ∧ output.heads 41=0 ∧ output.tapes 41=[false] := by
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
  have hselected : selectedNode (v.machine.halted view.control) (v.machine.rule view.control reads).isSome=11 := by
    cases hbad with
    | inl h=>rw [h]; rfl
    | inr h=>rw [h]; simp only [selectedNode,Option.isSome,Bool.not_false,Bool.or_true,↓reduceIte]
  rw [hselected] at hp2
  obtain ⟨n3,hn3,hp3⟩ := reject_tail (looked d (List.ofFn reads))
  change n1≤7*d.lookup.t+6 at hn1
  change n2≤128*(d.lookup.code.length+1)^2+1 at hn2
  obtain ⟨ht,_,_,_,_⟩ := hr.canonical.dimensions reads
  have hn : n0+n1+n2+n3≤cycleBudget d := by unfold cycleBudget; nlinarith
  refine ⟨n0+n1+n2+n3,hn,_,((hp0.trans hp1).trans hp2).trans hp3,?_,rfl,rfl⟩
  simp [machine,RecoveryCalls.machine,RecoveryCalls.controlCode,cfg]

end NearCubicWires.RepairOrdinary.TransitionWalk
