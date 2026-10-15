import Proof.Hierarchy.CompetitorSameBucketBlockLoad

/-! Per-candidate scalar clearing excludes the cached left record, runtime
fields, right-bank cursor and growing contribution stream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 30 → Fin 41 := ![1,2,3,4,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,26,27,28,29,30,35,40]
def eraseSlots : Fin 32 → Fin 41 := ![1,2,3,4,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,26,27,28,29,30,35,40,36,37]
theorem work_injective : Function.Injective workSlots := by decide
theorem erase_injective : Function.Injective eraseSlots := by decide

def heads (sourcePos outPos : ℕ) : Fin 41 → ℕ := fun i =>
  if i=34 then outPos else if i=38 then 1 else if i=39 then sourcePos else 0

def cfg {s : ℕ} (q : Fin s) (sourcePos outPos : ℕ) (ambient : Fin 41 → List Bool) : Configuration 41 s :=
  ⟨q,heads sourcePos outPos,ambient⟩

structure Store (cap : ℕ) (ambient : Fin 41 → List Bool) : Prop where
  driver : ambient 36=List.replicate cap true
  reset : ambient 37=List.replicate (cap+1) false
  support : ∀ i,(ambient (workSlots i)).length≤cap

noncomputable def clear := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 30)
noncomputable def clean (cap : ℕ) (ambient : Fin 41 → List Bool) :=
  install eraseSlots ambient (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 30 => List.replicate cap false))

theorem erase_work (i : Fin 30) : eraseSlots (i.castAdd 2)=workSlots i := by
  fin_cases i <;> rfl

theorem clean_work (cap : ℕ) (ambient : Fin 41 → List Bool) (i : Fin 30) :
    clean cap ambient (workSlots i)=List.replicate cap false := by
  rw [←erase_work]
  have he := install_slot eraseSlots erase_injective ambient
    (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 30 => List.replicate cap false)) (i.castAdd 2)
  apply he.trans
  fin_cases i <;> rfl

theorem clean_other (cap : ℕ) (ambient : Fin 41 → List Bool) (i : Fin 41)
    (hi : ∀ j,eraseSlots j≠i) : clean cap ambient i=ambient i := install_other eraseSlots _ _ i hi

theorem Store.clean {cap : ℕ} {ambient : Fin 41 → List Bool} (_h : Store cap ambient) : Store cap (clean cap ambient) := by
  constructor
  · exact install_slot eraseSlots erase_injective _ _ 30
  · exact install_slot eraseSlots erase_injective _ _ 31
  · intro i
    rw [clean_work]
    simp

theorem clear_run (cap sourcePos outPos : ℕ) (ambient : Fin 41 → List Bool) (h : Store cap ambient) :
    ∃ r,runFrom clear (2*cap+4) (cfg clear.start sourcePos outPos ambient)=some r ∧
      r.final.heads=heads sourcePos outPos ∧ r.final.tapes=clean cap ambient ∧ r.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine 30) (2*cap+4)
      (CompetitorPlaneWorkspace.eraseInput cap (fun i => ambient (workSlots i)))
      (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 30 => List.replicate cap false)) := by
    simpa only [CompetitorPlaneWorkspace.eraseInput,max_self] using RecoveryScratchErase.erase_ready cap (cap+1) _ h.support
  have ht : ∀ i,ambient (eraseSlots i)=CompetitorPlaneWorkspace.eraseInput cap (fun j => ambient (workSlots j)) i := by
    intro i
    fin_cases i <;> first | exact h.driver | exact h.reset | rfl
  have hh : ∀ i,heads sourcePos outPos (eraseSlots i)=0 := by
    intro i
    fin_cases i <;> rfl
  exact HierarchyBinary.focused_run eraseSlots erase_injective _ _ _ ready (heads sourcePos outPos) ambient hh ht

theorem Store.update_work {cap : ℕ} {ambient : Fin 41 → List Bool} (h : Store cap ambient)
    (i : Fin 30) (bits : List Bool) (hb : bits.length≤cap) : Store cap (Function.update ambient (workSlots i) bits) := by
  have ne36 : workSlots i≠36 := by fin_cases i <;> decide
  have ne37 : workSlots i≠37 := by fin_cases i <;> decide
  constructor
  · exact (Function.update_of_ne ne36.symm _ _).trans h.driver
  · exact (Function.update_of_ne ne37.symm _ _).trans h.reset
  · intro j
    by_cases he : workSlots j=workSlots i
    · simp only [he,Function.update_self]
      exact hb
    · rw [Function.update_of_ne he]
      exact h.support j

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
