import Proof.Hierarchy.CompetitorBankMergeContext
import Proof.Hierarchy.CompetitorResidueTableContext
import Proof.Hierarchy.CompetitorOddRowSliceProjection

/-! One literal 159-tape boundary for merge, signed residue and parity
selection. The actual retained parity chooses the residue output routing;
the even branch writes the common output directly. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFinalTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mergeSlots (i : Fin 87) : Fin 159 :=
  if h : i.val<36 then ⟨i.val,by omega⟩ else ⟨i.val+3,by omega⟩
def residueSlots (odd : Bool) (i : Fin 86) : Fin 159 :=
  if h : i.val<35 then ⟨i.val,by omega⟩ else if i=35 then 36
  else if i=45 ∧ odd=false then 141 else ⟨i.val+54,by omega⟩
def sliceSlots (i : Fin 106) : Fin 159 :=
  if h : i.val<86 then residueSlots true ⟨i.val,h⟩ else if i=86 then 37
  else ⟨i.val+53,by omega⟩
def heads (pos : ℕ) : Fin 159 → ℕ := fun i => if i=32 then pos else if i=37 then 1 else 0

def input (ambient : Fin 35 → List Bool) (same : List Bool) (q u : ℕ) (odd : Bool) : Fin 159 → List Bool :=
  Fin.addCases (m := 35) (n := 124) (motive := fun _ => List Bool) ambient
    (fun i => if i=0 then same else if i=1 then List.replicate q true
      else if i=2 then UnaryTemplate.tape u else if i=3 then [odd] else [])
noncomputable def mergeProgram := RecoveryFocus.machine mergeSlots CompetitorBankMergeDock.machine
noncomputable def residueProgram (odd : Bool) := RecoveryFocus.machine (residueSlots odd) CompetitorResidueTableDock.machine
noncomputable def sliceProgram := RecoveryFocus.machine sliceSlots CompetitorOddRowSliceDock.machine
noncomputable def oddProgram := Composition.machine (residueProgram true) sliceProgram

theorem merge_injective : Function.Injective mergeSlots := by decide
theorem residue_injective (odd : Bool) : Function.Injective (residueSlots odd) := by
  cases odd <;> decide
theorem slice_injective : Function.Injective sliceSlots := by decide

/-- Exact finite wiring transport, including nonzero retained source and
U heads. Only selected tapes are changed by the supplied executed run. -/
theorem focus_run {t u s fuel : ℕ} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (p : Machine t s) (lh : Fin t → ℕ) (lt : Fin t → List Bool)
    (ah : Fin u → ℕ) (atapes : Fin u → List Bool) (base : ExecutionReceipt t s)
    (hr : runFrom p fuel (RecoveryCalls.restarted p lh lt)=some base)
    (hb : base.final.heads=lh) (hh : ∀ i,ah (slot i)=lh i) (ht : ∀ i,atapes (slot i)=lt i) :
    ∃ actual,runFrom (RecoveryFocus.machine slot p) fuel
      (RecoveryCalls.restarted (RecoveryFocus.machine slot p) ah atapes)=some actual ∧
      actual.final.heads=ah ∧ actual.final.tapes=install slot atapes base.final.tapes ∧ actual.steps=base.steps := by
  obtain ⟨r,h,hf,hs⟩ := RecoveryFocus.run_config slot hi p ah atapes fuel _ base hr
  have he : RecoveryFocus.config slot ah atapes (RecoveryCalls.restarted p lh lt)=
      RecoveryCalls.restarted (RecoveryFocus.machine slot p) ah atapes := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp,RecoveryCalls.restarted]
      | some j =>
        have hj := RecoveryFocus.slot_of_pick slot hp
        simp only [RecoveryFocus.config,hp,RecoveryCalls.restarted]
        exact (hh j).symm.trans (congrArg ah hj)
    · exact install_existing slot atapes lt ht
  rw [he] at h
  refine ⟨r,h,?_,?_,hs⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have hj := RecoveryFocus.slot_of_pick slot hp
      simp only [RecoveryFocus.config,hp,hb]
      exact (hh j).symm.trans (congrArg ah hj)
  · rw [hf]
    rfl

theorem merge_heads (pos : ℕ) (i : Fin 87) :
    heads pos (mergeSlots i)=CompetitorBankMergeDock.heads pos i := by
  fin_cases i <;> rfl
theorem residue_heads (pos : ℕ) (odd : Bool) (i : Fin 86) :
    heads pos (residueSlots odd i)=CompetitorResidueTableDock.heads pos i := by
  cases odd <;> fin_cases i <;> rfl
theorem slice_heads (pos : ℕ) (i : Fin 106) :
    heads pos (sliceSlots i)=CompetitorOddRowSliceDock.heads pos 1 i := by
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CompetitorFinalTable
