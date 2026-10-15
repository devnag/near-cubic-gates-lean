import Proof.MachineModel.OrdinaryTransitionWalkInvariant

/-! A decoded action carries the physical walk invariant to the next
binary iteration, including the remaining head and serial capacity margins. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def looked (d : Store) (bits : List Bool) : Store := selected (guarded (compared d) bits) bits

theorem looked_lookup (d : Store) (bits : List Bool) :
    (looked d bits).lookup=LookupRuntime.finished d.lookup bits := by rfl

def advanced (d : Store) {t s : ℕ} (view : ClaimedTrace.View t s) (reads : Fin t→Bool) (a : Action t s) : Store :=
  roundDone (looked d (List.ofFn reads)) (actionItems a view.heads reads) (binary d.lookup.j a.nextControl.val)

theorem advanced_lookup (d : Store) {t s : ℕ} (view : ClaimedTrace.View t s) (reads : Fin t→Bool) (a : Action t s) :
    (advanced d view reads a).lookup={LookupRuntime.finished d.lookup (List.ofFn reads) with
      state:=binary d.lookup.j a.nextControl.val,scanPos:=d.lookup.scanPos+2*t} := by
  rw [advanced,roundDone_lookup,looked_lookup]
  simp only [actionItems,List.length_ofFn]
  rfl

theorem advanced_counters (d : Store) {t s : ℕ} (view : ClaimedTrace.View t s) (reads : Fin t→Bool) (a : Action t s) :
    (advanced d view reads a).tagPos=0 ∧ (advanced d view reads a).index=d.index+1 ∧
    (advanced d view reads a).serial=d.serial+t ∧ (advanced d view reads a).tape=0 := by
  have h := roundDone_counters (looked d (List.ofFn reads)) (actionItems a view.heads reads)
    (binary d.lookup.j a.nextControl.val)
  have hl : (actionItems a view.heads reads).length=t := by simp [actionItems]
  rw [hl] at h
  exact h

theorem advanced_ready (d : Store) (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (reads : Fin v.tapeCount→Bool) (a : Action v.tapeCount v.stateCount)
    (hr : Ready d v view) (hi : d.index<d.m) : Ready (advanced d view reads a) v (ClaimedTrace.advance view a) := by
  let e := advanced d view reads a
  have he := advanced_lookup d view reads a
  obtain ⟨_,heindex,heserial,hetape⟩ := advanced_counters d view reads a
  have hcanonical : LookupRuntime.Canonical e.lookup v a.nextControl := by
    rw [he]
    exact ⟨hr.canonical.code_eq,hr.canonical.tapes_eq,hr.canonical.states_eq,hr.canonical.width_eq,
      by rw [hr.canonical.width_eq]⟩
  have hready : LookupReady e := by
    apply roundDone_lookup_ready
    change LookupReady (selected (guarded (compared d) (List.ofFn reads)) (List.ofFn reads))
    apply selected_lookup_ready _ v view.control reads
    · exact ⟨hr.canonical.code_eq,hr.canonical.tapes_eq,hr.canonical.states_eq,hr.canonical.width_eq,hr.canonical.state_eq⟩
    · exact hr.lookup.capacity
  refine ⟨hready,hcanonical,hr.m_fit,?_,hetape,hr.tape_fit,?_,?_,?_,hr.capacity,hr.array_budget,?_,rfl⟩
  · change (advanced d view reads a).index≤d.m
    rw [heindex]
    omega
  · change (advanced d view reads a).serial+(d.m-(advanced d view reads a).index)*v.tapeCount<2^(2*d.w)
    rw [heserial,heindex]
    have hsub : d.m-d.index=(d.m-(d.index+1))+1 := by omega
    have h := hr.serial_fit
    rw [hsub,Nat.add_mul] at h
    omega
  · intro i
    change (a.move i).apply (view.heads i)+(d.m-(advanced d view reads a).index)+1<2^d.w
    rw [heindex]
    have h := hr.heads_fit i
    cases hm:a.move i <;> simp only [HeadMove.apply] <;> omega
  · exact roundDone_difference (looked d (List.ofFn reads)) (actionItems a view.heads reads)
      (binary d.lookup.j a.nextControl.val) hr.difference
  · change ZeroPadding.pad d.C (TransitionArray.nextFields d.w (actionItems a view.heads reads))=
      ZeroPadding.pad d.C ((List.ofFn fun i=>frame (binary d.w ((a.move i).apply (view.heads i))))).flatten
    rw [actionItems_nextFields]

end NearCubicWires.RepairOrdinary.TransitionWalk
