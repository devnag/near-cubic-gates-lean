import Proof.CaseAnalysis.RecoveryUniversalGateCall
import Proof.Assembly.AppendFrameKernel
import Proof.PCP.PCPSerializerCapacityFocus
import Proof.Hierarchy.CompetitorPaddedAppend

/-! Physically copy an actual unary reference as its length driver, then
frame it in reusable C-backed storage for the original five tag choices. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceFrame
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n P C : ℕ) : Fin 4→List Bool:=
  ![ZeroPadding.pad P (List.replicate n true),List.replicate C false,List.replicate C false,List.replicate C false]
def copied (n P C : ℕ) : Fin 4→List Bool:=
  ![ZeroPadding.pad P (List.replicate n true),ZeroPadding.pad C (List.replicate n true),List.replicate C false,List.replicate C false]
def framed (n P C : ℕ) : Fin 4→List Bool:=
  ![ZeroPadding.pad P (List.replicate n true),ZeroPadding.pad C (List.replicate n true),
    ZeroPadding.pad C (frame (List.replicate n true)),List.replicate C false]
def copySlots : Fin 3→Fin 4:=![0,1,3]
noncomputable def copy:=RecoveryFocus.machine copySlots PCPUnaryCopy.machine
noncomputable def machine:=Composition.machine copy AppendFrameKernel.machine

theorem copy_ready (n P C : ℕ) (hC : n+1 ≤ C) :
    ClockJoin.ReadyRun copy (2*n+4) (input n P C) (copied n P C) := by
  have h:=PCPUnaryCopy.copy_ready n P C C
  rw [max_eq_left hC] at h
  have hf:=h.focus copySlots (by decide) (input n P C) (by intro j;fin_cases j <;> rfl)
  have he : install copySlots (input n P C)
      ![ZeroPadding.pad P (List.replicate n true),ZeroPadding.pad C (List.replicate n true),List.replicate C false]=copied n P C := by
    apply HierarchyWidth.install_eq copySlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  rw [he] at hf
  obtain ⟨r,hr,rt,rh,rs⟩:=hf
  exact ⟨r,hr,rt,rh,rs.le⟩

theorem frame_ready (n P C : ℕ) (hC : 2*n+1 ≤ C) :
    ClockJoin.ReadyRun AppendFrameKernel.machine (4*n+4) (copied n P C) (framed n P C) := by
  obtain ⟨base,hb,bt,bh,bs⟩:=AppendFrameKernel.ready (List.replicate n true)
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config AppendFrameKernel.machine ![P,C,C,C] _ _ base hb
  have hi : ZeroPadding.config ![P,C,C,C] (initialConfiguration AppendFrameKernel.machine (AppendFrameKernel.input (List.replicate n true)))=
      initialConfiguration AppendFrameKernel.machine (copied n P C) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp only [ZeroPadding.config,initialConfiguration,AppendFrameKernel.input,List.length_replicate] <;> rfl
  change runFrom AppendFrameKernel.machine (4*(List.replicate n true).length+4)
    (ZeroPadding.config ![P,C,C,C] (initialConfiguration AppendFrameKernel.machine (AppendFrameKernel.input (List.replicate n true))))=some r at hr
  rw [hi,List.length_replicate] at hr
  refine ⟨r,hr,?_,?_,?_⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad ((![P,C,C,C] : Fin 4→ℕ) i) (base.final.tapes i))=_
    rw [bt]
    funext i
    fin_cases i
    all_goals simp only [AppendFrameKernel.output,List.length_replicate]
    all_goals first | rfl | exact RecoveryBoundedSelectorLoop.pad_erased C (2*n+1) hC
  · intro i
    rw [rf]
    exact bh i
  · rw [rs]
    simpa only [List.length_replicate] using bs

theorem prepare_ready (n P C : ℕ) (hC : 2*n+1 ≤ C) :
    ClockJoin.ReadyRun machine (6*n+9) (input n P C) (framed n P C) := by
  have h:=ClockJoin.join copy AppendFrameKernel.machine _ _ _ _ _
    (copy_ready n P C (by omega)) (frame_ready n P C hC)
  have he : (2*n+4)+1+(4*n+4)=6*n+9 := by omega
  simpa only [machine,he] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceFrame
