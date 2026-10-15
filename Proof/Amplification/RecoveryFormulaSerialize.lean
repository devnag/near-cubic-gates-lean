import Proof.Amplification.RecoveryFormulaSerializePrepare

/-! The original balanced serializer is now callable on just its field
stream from literal external input and blank scratch. Its count is measured
by actual transitions, and its native head1 convention is physically set. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverHeads (i : Fin 131) := if i=3 then 1 else 0
def shift : Machine 131 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val=1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i=3 then .right else .stay⟩ else none

theorem shift_step (t : Fin 131→List Bool) :
    step shift (initialConfiguration shift t)=some ⟨1,driverHeads,t⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi:i=3 <;> simp [applyAction,shift,initialConfiguration,driverHeads,hi,HeadMove.apply]
  · rfl

theorem shift_run (t : Fin 131→List Bool) : ∃ r,
    run shift 1 t=some r ∧ r.final=(⟨1,driverHeads,t⟩ : Configuration 131 2) ∧ r.steps=1 :=
  (Timed.single (by rfl) (shift_step t)).run (by rfl)

theorem native_heads (i : Fin 128) : driverHeads (nativeSlots i)=PCPTraversal.heads 0 i := by
  have he : nativeSlots i=3 ↔ i=2 := by
    constructor
    · intro h; apply Fin.ext; have hv:=congrArg (fun j : Fin 131=>j.val) h; dsimp [nativeSlots] at hv; omega
    · rintro rfl; rfl
  simp only [driverHeads,he,PCPTraversal.heads]
  by_cases hi:i=0
  · subst i; rfl
  · simp [hi]

noncomputable def serializeMachine := RecoveryFocus.machine nativeSlots PCPTraversal.machine
noncomputable def tailMachine := Composition.machine shift serializeMachine
noncomputable def machine := Composition.machine prepareMachine tailMachine
def rawBudget (fields : List (List Bool)) := prepareBudget fields+1+(1+1+PCPTraversal.budget (mass fields))

theorem tail_run (fields : List (List Bool)) : ∃ r,
    run tailMachine (1+1+PCPTraversal.budget (mass fields)) (prepared fields)=some r ∧
      r.final.tapes 79=(PCPTraversal.code fields).bits ∧
      r.steps ≤ 1+1+PCPTraversal.budget (mass fields) := by
  obtain ⟨first,hfirst,hf,hs⟩ := shift_run (prepared fields)
  obtain ⟨last,hlast,_h77,h78,_h0,_h2,_hh,_hother,hsteps⟩ := PCPTraversal.focused_run nativeSlots native_injective
    [] fields [] driverHeads (prepared fields) native_heads (by
      intro j
      simpa only [List.nil_append,List.append_nil] using prepared_native fields j)
  have hrestart : Composition.restart first.final serializeMachine.start=
      (⟨PCPTraversal.machine.start,driverHeads,prepared fields⟩ : Configuration 131 _) := by rw [hf]; rfl
  have hlast' : runFrom serializeMachine (PCPTraversal.budget (mass fields))
      (Composition.restart first.final serializeMachine.start)=some last := by rw [hrestart]; exact hlast
  have hwhole := Composition.run_join shift serializeMachine 1 (PCPTraversal.budget (mass fields))
    _ first last hfirst hlast'
  refine ⟨_,hwhole,h78,?_⟩
  change first.steps+1+last.steps ≤ _
  omega

private theorem restart_of_ready {t a b : Nat} (q : Machine t b)
    (c : Configuration t a) (output : Fin t→List Bool)
    (ht : c.tapes=output) (hh : ∀ i,c.heads i=0) :
    Composition.restart c q.start=initialConfiguration q output := by
  apply configuration_ext
  · rfl
  · exact funext hh
  · exact ht

theorem raw_run (fields : List (List Bool)) : ∃ r,
    run machine (rawBudget fields) (input fields)=some r ∧
      r.final.tapes 79=(PCPTraversal.code fields).bits ∧ r.steps ≤ rawBudget fields := by
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := prepare_ready fields
  obtain ⟨last,hlast,hout,hls⟩ := tail_run fields
  have he := restart_of_ready tailMachine first.final (prepared fields) hft hfh
  have hlast' : runFrom tailMachine (1+1+PCPTraversal.budget (mass fields))
      (Composition.restart first.final tailMachine.start)=some last := by rw [he]; exact hlast
  have hwhole := Composition.run_join prepareMachine tailMachine (prepareBudget fields)
    (1+1+PCPTraversal.budget (mass fields)) _ first last hfirst hlast'
  refine ⟨_,hwhole,hout,?_⟩
  change first.steps+1+last.steps ≤ rawBudget fields
  unfold rawBudget
  omega

def budget (fields : List (List Bool)) := 1000000000016*((FieldList.stream fields).length+1)^12

theorem budget_bound (fields : List (List Bool)) : rawBudget fields ≤ budget fields := by
  have hp : 1 ≤ ((FieldList.stream fields).length+1)^12 := Nat.one_le_pow _ _ (by omega)
  have hl : (FieldList.stream fields).length+1 ≤ ((FieldList.stream fields).length+1)^12 :=
    Nat.le_self_pow (by decide) _
  have hm : mass fields=(FieldList.stream fields).length := (PCPTraversal.stream_mass fields).symm
  simp only [rawBudget,prepareBudget,PCPTraversal.budget,budget,hm]
  omega

noncomputable def program : Program := ⟨131,_,by decide,machine,79,by decide⟩
noncomputable def wordFunction : OrdinaryWordFunction (List (List Bool)) FieldList.stream
    (fun fields=>(PCPTraversal.code fields).bits) budget where
  program := program
  realizes := by
    intro fields
    obtain ⟨r,hr,ht,_hs⟩ := raw_run fields
    have hmore := run_moreFuel machine (rawBudget fields) (budget fields-rawBudget fields) (input fields) r hr
    rw [Nat.add_sub_of_le (budget_bound fields)] at hmore
    exact ⟨r,hmore,ht⟩

end NearCubicWires.RepairSource.RecoveryFormulaSerialize
