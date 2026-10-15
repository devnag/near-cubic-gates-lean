import Proof.Supplier.RowTupleFields

/-! Cold tuple enumeration from actual width, degree and bound metadata.
The program manufactures its binary zero fields, flags and scratch, then
executes the whole binary loop and returns the selected-occurrence stream. -/
namespace NearCubicWires.RepairOrdinary.RowTupleColdEnumeration
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RowTupleEnumeration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 18) : Fin 29 := i.castAdd 11
theorem injective : Function.Injective slots := by
  intro i j h; exact Fin.ext (congrArg (fun a : Fin 29=>a.val) h)
noncomputable def enumeration := RecoveryFocus.machine slots RowTupleColdLogs.machine
noncomputable def machine := Composition.machine RowTupleColdFields.machine enumeration
def budget (w k : ℕ) := RowTupleColdFields.time w k+1+(time w k+2)

theorem prepare_core (w k M : ℕ) (out : Fin 29→List Bool)
    (h0 : out 0=frame (binary (w*k+1) 0)) (h1 : out 1=frame (binary w 0))
    (h6 : out 6=frame (binary w 0))
    (hother : ∀ i : Fin 18,i≠0 → i≠1 → i≠6 → out (slots i)=RowTupleColdFields.input w k M (slots i)) :
    ∀ i,out (slots i)=RowTupleColdLogs.tapes w k M [] i := by
  intro i
  fin_cases i
  all_goals first
    | exact h0
    | exact h1
    | exact h6
    | exact hother _ (by decide) (by decide) (by decide)

theorem enumerate_run (w k M : ℕ) (hM : 0<M) (hMw : M≤2^w) :
    ∃ r,run machine (budget w k) (RowTupleColdFields.input w k M)=some r ∧
      r.final.tapes 0=frame (binary (w*k+1) (2^(w*k))) ∧
      r.final.tapes 17=word w k M ∧ r.final.heads 0=0 ∧
      r.final.heads 17=(word w k M).length ∧ r.steps≤budget w k := by
  obtain ⟨middle,⟨a,ha,atapes,ah,as⟩,a0,a1,a6,aother⟩ := RowTupleColdFields.prepare_run w k M
  obtain ⟨base,hbase,b0,b17,bh,bs⟩ := RowTupleColdLogs.enumerate_run w k M [] hM hMw
  have hcore := prepare_core w k M middle a0 a1 a6 aother
  obtain ⟨b,hb,bf,bsteps⟩ := RecoveryFocus.run_config slots injective RowTupleColdLogs.machine
    (fun _=>0) middle _ _ base hbase
  have hi : RecoveryFocus.config slots (fun _=>0) middle
      (RowTupleColdLogs.input RowTupleColdLogs.machine.start w k M [])=
      Composition.restart a.final enumeration.start := by
    rw [show Composition.restart a.final enumeration.start=initialConfiguration enumeration middle from by
      apply configuration_ext
      · rfl
      · funext i; exact ah i
      · exact atapes]
    apply WilliamsSourceCrop.focus_same slots (initialConfiguration enumeration middle)
    · intro i; simp [RowTupleColdLogs.input,RowTupleColdLogs.heads,initialConfiguration]
    · exact hcore
  rw [hi] at hb
  have hwhole := Composition.run_join RowTupleColdFields.machine enumeration _ _ _ a b ha hb
  have bfield (i : Fin 18) : b.final.tapes (slots i)=base.final.tapes i := by
    rw [bf]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots injective]
  have bhead (i : Fin 18) : b.final.heads (slots i)=base.final.heads i := by
    rw [bf]; simp [RecoveryFocus.config,RecoveryFocus.pick_slot slots injective]
  refine ⟨Composition.joinedReceipt a b,hwhole,(bfield 0).trans b0,?_,?_,?_,?_⟩
  · change b.final.tapes (slots 17)=word w k M
    simpa only [List.nil_append] using (bfield 17).trans b17
  · change b.final.heads 0=0
    rw [show (0 : Fin 29)=slots 0 from rfl,bhead,bh]
    rfl
  · change b.final.heads 17=_
    rw [show (17 : Fin 29)=slots 17 from rfl,bhead,bh]
    rfl
  · change a.steps+1+b.steps≤budget w k
    unfold budget
    rw [bsteps]
    omega

theorem chosen_run (M k : ℕ) (hM : 0<M) :
    ∃ r,run machine (budget (RowTupleSubsets.digitWidth M) k)
      (RowTupleColdFields.input (RowTupleSubsets.digitWidth M) k M)=some r ∧
      r.final.tapes 17=word (RowTupleSubsets.digitWidth M) k M ∧
      r.steps≤budget (RowTupleSubsets.digitWidth M) k := by
  obtain ⟨r,hr,_,hout,_,_,hs⟩ := enumerate_run (RowTupleSubsets.digitWidth M) k M hM
    (RowTupleSubsets.digit_fit M).le
  exact ⟨r,hr,hout,hs⟩

end NearCubicWires.RepairOrdinary.RowTupleColdEnumeration
