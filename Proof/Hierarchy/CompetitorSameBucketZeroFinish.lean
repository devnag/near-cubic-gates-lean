import Proof.Hierarchy.CompetitorSameBucketZeroRow
import Proof.Hierarchy.HierarchyAllocation

/-! Between zero-grid rows, clear the tagged-column field, copy the retained
native U into it, and increment the row field. Both output and U-driver
cursors survive this paid short-word reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroFinish
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 13 → ℕ := fun i => if i=6 then out.length else if i=8 then 1 else 0
def data (p m u left cap : ℕ) (out right : List Bool) : Fin 13 → List Bool :=
  ![ZeroPadding.pad cap (frame (MatrixScoreBatch.signMagnitude p 0)),
    ZeroPadding.pad cap (frame (List.replicate (p+1) false)),right,
    ZeroPadding.pad cap (frame (binary m 0)),ZeroPadding.pad cap (frame (binary m left)),
    ZeroPadding.pad cap (frame (binary m 0)),out,List.replicate cap false,
    UnaryTemplate.tape u,frame (binary m u),List.replicate cap true,List.replicate (cap+1) false,List.replicate cap false]
def cfg {s : ℕ} (q : Fin s) (p m u left cap : ℕ) (out right : List Bool) : Configuration 13 s :=
  ⟨q,heads out,data p m u left cap out right⟩
def clearSlots : Fin 3 → Fin 13 := ![2,10,11]
def copySlots : Fin 4 → Fin 13 := ![9,2,7,12]
def incrementSlots : Fin 2 → Fin 13 := ![4,7]
theorem clear_injective : Function.Injective clearSlots := by decide
theorem copy_injective : Function.Injective copySlots := by decide
theorem increment_injective : Function.Injective incrementSlots := by decide
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copy:=RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def increment:=RecoveryFocus.machine incrementSlots FramedIncrement.machine
noncomputable def tail:=Composition.machine copy increment
noncomputable def machine:=Composition.machine clear tail
def budget (m cap : ℕ):=(2*cap+4)+1+((8*m+8)+1+(4*m+2))

theorem clear_run (p m u left cap : ℕ) (out right : List Bool) (hf : right.length≤cap) :
    ∃ actual,runFrom clear (2*cap+4) (cfg clear.start p m u left cap out right)=some actual ∧
      actual.final.heads=heads out ∧ actual.final.tapes=data p m u left cap out (List.replicate cap false) ∧
      actual.steps≤2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine 1) (2*cap+4)
      (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 1 => right))
      (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 1 => List.replicate cap false)) := by
    simpa only [CompetitorPlaneWorkspace.eraseInput,max_self] using
      RecoveryScratchErase.erase_ready cap (cap+1) (fun _ : Fin 1 => right) (by intro i; exact hf)
  obtain ⟨base,hb,bt,bh,bs⟩:=ready
  obtain ⟨actual,ha,ah,atapes,ast⟩:=CompetitorReusableDecision.bounded_focused_run clearSlots clear_injective
    _ _ _ ⟨base,hb,bt,bh,bs.le⟩ (heads out) (data p m u left cap out right)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  apply HierarchyAllocation.install_eq clearSlots clear_injective
  · intro j; fin_cases j <;> rfl
  · intro i hi
    fin_cases i
    all_goals first | rfl | exact False.elim (hi 0 rfl)

theorem copy_run (p m u left cap : ℕ) (out : List Bool) (hc : 4*m+3≤cap) :
    ∃ actual,runFrom copy (8*m+8) (cfg copy.start p m u left cap out (List.replicate cap false))=some actual ∧
      actual.final.heads=heads out ∧ actual.final.tapes=data p m u left cap out (ZeroPadding.pad cap (frame (binary m u))) ∧
      actual.steps≤8*m+8 := by
  obtain ⟨base,hb,bt,bh,bs⟩:=CompetitorSameBucketColdFrameCopy.copy_ready (binary m u) cap (by simpa using hc)
  simp only [binary_length] at hb bs
  obtain ⟨actual,ha,ah,atapes,ast⟩:=CompetitorReusableDecision.bounded_focused_run copySlots copy_injective
    _ _ _ ⟨base,hb,bt,bh,bs.le⟩ (heads out) (data p m u left cap out (List.replicate cap false))
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  apply HierarchyAllocation.install_eq copySlots copy_injective
  · intro j; fin_cases j <;> rfl
  · intro i hi
    fin_cases i
    all_goals first | rfl | exact False.elim (hi 1 rfl)

theorem increment_run (p m u left cap : ℕ) (out right : List Bool) (hm : 2*m≤cap) (hl : left+1<2^m) :
    ∃ actual,runFrom increment (4*m+2) (cfg increment.start p m u left cap out right)=some actual ∧
      actual.final.heads=heads out ∧ actual.final.tapes=data p m u (left+1) cap out right ∧ actual.steps≤4*m+2 := by
  obtain ⟨actual,ha,ah,atapes,ast⟩:=CompetitorReusableDecision.bounded_focused_run incrementSlots increment_injective
    _ _ _ (CompetitorSameBucketZeroCell.increment_ready m left cap hl hm) (heads out) (data p m u left cap out right)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  refine ⟨actual,ha,ah,?_,ast⟩
  rw [atapes]
  apply HierarchyAllocation.install_eq incrementSlots increment_injective
  · intro j; fin_cases j <;> rfl
  · intro i hi
    fin_cases i
    all_goals first | rfl | exact False.elim (hi 0 rfl)

theorem finish_run (p m u left cap : ℕ) (out right : List Bool)
    (hf : right.length≤cap) (hc : 4*m+3≤cap) (hl : left+1<2^m) :
    ∃ actual,runFrom machine (budget m cap) (cfg machine.start p m u left cap out right)=some actual ∧
      actual.final.heads=heads out ∧
      actual.final.tapes=data p m u (left+1) cap out (ZeroPadding.pad cap (frame (binary m u))) ∧
      actual.steps≤budget m cap := by
  obtain ⟨first,hf,fh,ft,fs⟩:=clear_run p m u left cap out right hf
  obtain ⟨second,hs,sh,st,ss⟩:=copy_run p m u left cap out hc
  obtain ⟨last,hlast,lh,lt,ls⟩:=increment_run p m u left cap out (ZeroPadding.pad cap (frame (binary m u))) (by omega) hl
  have hiLast : Composition.restart second.final increment.start=
      cfg increment.start p m u left cap out (ZeroPadding.pad cap (frame (binary m u))) := configuration_ext rfl sh st
  rw [←hiLast] at hlast
  have joinedTail:=Composition.run_join copy increment _ _ _ second last hs hlast
  have hiTail : Composition.restart first.final tail.start=Composition.leftConfig _
      (cfg copy.start p m u left cap out (List.replicate cap false)) := configuration_ext rfl fh ft
  rw [←hiTail] at joinedTail
  have joined:=Composition.run_join clear tail _ _ _ first (Composition.joinedReceipt second last) hf joinedTail
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt second last),joined,lh,lt,?_⟩
  change first.steps+1+(second.steps+1+last.steps)≤budget m cap
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketZeroFinish
