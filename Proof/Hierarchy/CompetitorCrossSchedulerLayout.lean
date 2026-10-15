import Proof.Hierarchy.CompetitorCrossRequestFieldsBounds
import Proof.MachineModel.OrdinaryMatrixScheduler

/-! Finite routing from original-request fields through the accepted cold
matrix scheduler to the complete native cross-table. No scratch is shared
between the scheduler and the table preparation. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
open LocalBitMultitape RecoveryRootRound
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (p : Program) := 181+p.tapeCount
def input (p : Program) (r : Request) : Fin (tapes p) → List Bool :=
  fun i => if i.val=0 then MatrixScoreBatch.physicalInput r else []
def fieldSlots (p : Program) (i : Fin 61) : Fin (tapes p) := ⟨i.val,by dsimp [tapes];omega⟩
def schedulerSlots (p : Program) (i : Fin p.tapeCount) : Fin (tapes p) :=
  if i.val=0 then ⟨0,by simp [tapes]⟩
  else if i.val=p.outputTape.val then ⟨93,by dsimp [tapes];omega⟩
  else ⟨181+i.val,by dsimp [tapes];omega⟩
def crossSlots (p : Program) (i : Fin 120) : Fin (tapes p) :=
  if i.val=9 then ⟨52,by dsimp [tapes];omega⟩ else if i.val=20 then ⟨48,by dsimp [tapes];omega⟩
  else if i.val=35 then ⟨54,by dsimp [tapes];omega⟩ else if i.val=36 then ⟨28,by dsimp [tapes];omega⟩
  else ⟨61+i.val,by dsimp [tapes];omega⟩
theorem field_injective (p : Program) : Function.Injective (fieldSlots p) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes p) => k.val) h)
theorem scheduler_value (p : Program) (i : Fin p.tapeCount) : (schedulerSlots p i).val=
    if i.val=0 then 0 else if i.val=p.outputTape.val then 93 else 181+i.val := by
  unfold schedulerSlots
  split_ifs <;> rfl
theorem cross_value (p : Program) (i : Fin 120) : (crossSlots p i).val=
    if i.val=9 then 52 else if i.val=20 then 48 else if i.val=35 then 54
    else if i.val=36 then 28 else 61+i.val := by
  unfold crossSlots
  split_ifs <;> rfl
theorem scheduler_injective (p : Program) : Function.Injective (schedulerSlots p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [scheduler_value,scheduler_value] at hv
  split_ifs at hv <;> omega
theorem cross_injective (p : Program) : Function.Injective (crossSlots p) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  rw [cross_value,cross_value] at hv
  split_ifs at hv <;> omega

theorem cross_avoids_zero (p : Program) (i : Fin 120) : crossSlots p i≠fieldSlots p 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [cross_value] at hv
  change (if i.val=9 then 52 else if i.val=20 then 48 else if i.val=35 then 54 else if i.val=36 then 28 else 61+i.val)=0 at hv
  split_ifs at hv
  omega

theorem cross_avoids_u (p : Program) (i : Fin 120) : crossSlots p i≠fieldSlots p 44 := by
  intro h
  have hv := congrArg Fin.val h
  rw [cross_value] at hv
  change (if i.val=9 then 52 else if i.val=20 then 48 else if i.val=35 then 54 else if i.val=36 then 28 else 61+i.val)=44 at hv
  split_ifs at hv <;> omega

theorem field_input (p : Program) (r : Request) :
    ∀ i,input p r (fieldSlots p i)=CompetitorCrossRequestFields.input r i := by
  intro i
  fin_cases i <;> rfl

theorem field_fresh (p : Program) (r : Request) (out : Fin 61 → List Bool)
    (i : Fin (tapes p)) (hi : 61 ≤ i.val) : install (fieldSlots p) (input p r) out i=[] := by
  rw [install_other _ _ _ _ (by
    intro j hj
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    omega)]
  simp [input,show i.val≠0 by omega]

theorem scheduler_input (p : Program) (r : Request) (out : Fin 61 → List Bool)
    (h0 : out 0=MatrixScoreBatch.physicalInput r) :
    ∀ i,install (fieldSlots p) (input p r) out (schedulerSlots p i)=p.inputTapes (MatrixScoreBatch.word r) i := by
  intro i
  by_cases hi : i.val=0
  · have he : schedulerSlots p i=fieldSlots p 0 := by apply Fin.ext;rw [scheduler_value,if_pos hi];rfl
    rw [he,install_slot _ (field_injective p),h0]
    simp [Program.inputTapes,hi,MatrixScoreBatch.physicalInput]
  · rw [field_fresh _ _ _ _ (by rw [scheduler_value,if_neg hi];split_ifs <;> omega)]
    simp [Program.inputTapes,hi]

theorem scheduler_keep (p : Program) (ambient : Fin (tapes p) → List Bool)
    (out : Fin p.tapeCount → List Bool) (i : Fin (tapes p))
    (hi : i.val≠0) (h93 : i.val≠93) (hsmall : i.val<181) :
    install (schedulerSlots p) ambient out i=ambient i := by
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  rw [scheduler_value] at hv
  split_ifs at hv <;> omega

theorem cross_input (p : Program) (r : Request) (fields : Fin 61 → List Bool)
    (out : Fin p.tapeCount → List Bool)
    (hp : fields 28=List.replicate r.p true) (hb : fields 48=List.replicate (natBitLength r.U) true)
    (hw : fields 52=List.replicate (CompetitorPlaneWidth.width (natBitLength r.U) r.p) true)
    (hn : fields 54=List.replicate (r.U*r.U) true) (hstream : out p.outputTape=MatrixScoreBatch.output r) :
    ∀ i,install (schedulerSlots p) (install (fieldSlots p) (input p r) fields) out (crossSlots p i)=
      CompetitorCrossTablePrepare.input (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
        (r.U*r.U) r.p (MatrixScoreBatch.output r) i := by
  intro i
  by_cases h9 : i.val=9
  · have he : i=9 := Fin.ext h9
    subst i
    rw [scheduler_keep _ _ _ _ (by simp [crossSlots]) (by simp [crossSlots]) (by simp [crossSlots])]
    exact (install_slot (fieldSlots p) (field_injective p) _ fields 52).trans hw
  by_cases h20 : i.val=20
  · have he : i=20 := Fin.ext h20
    subst i
    rw [scheduler_keep _ _ _ _ (by simp [crossSlots]) (by simp [crossSlots]) (by simp [crossSlots])]
    exact (install_slot (fieldSlots p) (field_injective p) _ fields 48).trans hb
  by_cases h35 : i.val=35
  · have he : i=35 := Fin.ext h35
    subst i
    rw [scheduler_keep _ _ _ _ (by simp [crossSlots]) (by simp [crossSlots]) (by simp [crossSlots])]
    exact (install_slot (fieldSlots p) (field_injective p) _ fields 54).trans hn
  by_cases h36 : i.val=36
  · have he : i=36 := Fin.ext h36
    subst i
    rw [scheduler_keep _ _ _ _ (by simp [crossSlots]) (by simp [crossSlots]) (by simp [crossSlots])]
    exact (install_slot (fieldSlots p) (field_injective p) _ fields 28).trans hp
  by_cases h32 : i.val=32
  · have he : crossSlots p i=schedulerSlots p p.outputTape := by
      apply Fin.ext
      rw [cross_value,scheduler_value,if_neg p.outputFresh,if_pos rfl]
      simp [h32]
    rw [he,install_slot _ (scheduler_injective p),hstream]
    simp [CompetitorCrossTablePrepare.input,h32]
  · have hv : (crossSlots p i).val=61+i.val := by rw [cross_value,if_neg h9,if_neg h20,if_neg h35,if_neg h36]
    rw [scheduler_keep _ _ _ _ (by rw [hv];omega) (by rw [hv];omega) (by rw [hv];omega)]
    rw [field_fresh _ _ _ _ (by rw [hv];omega)]
    simp [CompetitorCrossTablePrepare.input,h9,h20,h35,h36,h32]

end NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
