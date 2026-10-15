import Proof.MachineModel.UMemoryCloseReset
import Proof.MachineModel.OrdinaryMemoryCheckerEndpoint

/-! Static focus of the existing chronological checker onto the reset event
stream and twenty genuinely fresh tapes. Original emission storage remains
present; the literal result tape and its head-zero endpoint are retained. -/
namespace NearCubicWires.RepairOrdinary.UMemoryClose
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def checkerSlots {t : ℕ} (event : Fin t) : Fin 21 → Fin ((t+1)+20) :=
  Fin.cases (oldSlot event) (scratchSlot t)

theorem checker_injective {t : ℕ} (event : Fin t) : Function.Injective (checkerSlots event) := by
  intro i j h
  have hv := congrArg (fun k : Fin ((t+1)+20) => k.val) h
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      simp only [checkerSlots,Fin.cases_zero,Fin.cases_succ,oldSlot,scratchSlot,
        Fin.val_castAdd,Fin.val_natAdd] at hv
      have hi := event.isLt
      omega
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp only [checkerSlots,Fin.cases_zero,Fin.cases_succ,oldSlot,scratchSlot,
        Fin.val_castAdd,Fin.val_natAdd] at hv
      have hj := event.isLt
      omega
    | succ j =>
      simp only [checkerSlots,Fin.cases_succ,scratchSlot,Fin.val_natAdd] at hv
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

theorem checker_other {t : ℕ} (event i : Fin t) (hi : i ≠ event) :
    ∀ j, checkerSlots event j ≠ oldSlot i := by
  intro j hj
  have hv := congrArg (fun k : Fin ((t+1)+20) => k.val) hj
  cases j using Fin.cases with
  | zero =>
    simp only [checkerSlots,Fin.cases_zero,oldSlot,Fin.val_castAdd] at hv
    exact hi (Fin.ext hv.symm)
  | succ j =>
    simp only [checkerSlots,Fin.cases_succ,oldSlot,scratchSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    have h := i.isLt
    omega

noncomputable def checkerProgram {t : ℕ} (event : Fin t) : Machine ((t+1)+20) 138 :=
  RecoveryFocus.machine (checkerSlots event) MemoryChecker.machine

theorem checker_place {t s : ℕ} (event : Fin t) (req : MemoryChecker.Request)
    (c : Configuration ((t+1)+20) s)
    (hheads : ∀ j, c.heads (checkerSlots event j)=0)
    (htapes : ∀ j, c.tapes (checkerSlots event j)=SourceHandoff.sourceTapes req.input j) :
    RecoveryFocus.config (checkerSlots event) c.heads c.tapes
      (initialConfiguration MemoryChecker.machine (SourceHandoff.sourceTapes req.input)) =
        Composition.restart c (checkerProgram event).start := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick (checkerSlots event) i with
    | none => simp only [RecoveryFocus.config,hp,Composition.restart]
    | some j =>
      have hi := RecoveryFocus.slot_of_pick (checkerSlots event) hp
      simp only [RecoveryFocus.config,hp,initialConfiguration,Composition.restart]
      rw [← hi,hheads]
  · funext i
    cases hp : RecoveryFocus.pick (checkerSlots event) i with
    | none => simp only [RecoveryFocus.config,hp,Composition.restart]
    | some j =>
      have hi := RecoveryFocus.slot_of_pick (checkerSlots event) hp
      simp only [RecoveryFocus.config,hp,initialConfiguration,Composition.restart]
      rw [← hi,htapes]

theorem checker_run {t s : ℕ} (event : Fin t) (req : MemoryChecker.Request)
    (c : Configuration ((t+1)+20) s)
    (hheads : ∀ j, c.heads (checkerSlots event j)=0)
    (htapes : ∀ j, c.tapes (checkerSlots event j)=SourceHandoff.sourceTapes req.input j) :
    ∃ r,runFrom (checkerProgram event) (MemoryChecker.rawBudget req)
      (Composition.restart c (checkerProgram event).start)=some r ∧
      r.final.tapes (resultSlot t)=[req.result] ∧ r.final.heads (resultSlot t)=0 ∧
      (∀ i : Fin t, i ≠ event → r.final.heads (oldSlot i)=c.heads (oldSlot i) ∧
        r.final.tapes (oldSlot i)=c.tapes (oldSlot i)) := by
  obtain ⟨base,hbase,hbt,hbh⟩ := MemoryChecker.raw_run_endpoint req
  obtain ⟨r,hr,hf,_⟩ := RecoveryFocus.run_config (checkerSlots event) (checker_injective event)
    MemoryChecker.machine c.heads c.tapes (MemoryChecker.rawBudget req)
    (initialConfiguration MemoryChecker.machine (SourceHandoff.sourceTapes req.input)) base hbase
  rw [checker_place event req c hheads htapes] at hr
  refine ⟨r,hr,?_,?_,?_⟩
  · change r.final.tapes (checkerSlots event 19)=[req.result]
    rw [hf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot _ (checker_injective event)] using hbt
  · change r.final.heads (checkerSlots event 19)=0
    rw [hf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot _ (checker_injective event)] using hbh
  · intro i hi
    have hn : ¬∃ j,checkerSlots event j=oldSlot i := by
      rintro ⟨j,hj⟩
      exact checker_other event i hi j hj
    rw [hf]
    simp [RecoveryFocus.config,RecoveryFocus.pick,hn]

end NearCubicWires.RepairOrdinary.UMemoryClose
