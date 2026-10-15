import Proof.MachineModel.CachePrefix
import Proof.Hierarchy.CompetitorRecordRewind

/-! Reuse one paid capacity rewind with the batch's retained driver/log. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheRewind
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem rewind_step (source:List Bool) (C pos:ℕ) (hp:pos≤C) :
    Step CompetitorRecordRewind.machine (2*C+2) ![pos,0,0]
      ![source,List.replicate C true,List.replicate (C+1) false]
      ![0,0,0] ![source,List.replicate C true,List.replicate (C+1) false] := by
  obtain ⟨r,hr,hf,hs⟩:=CompetitorRecordRewind.rewind_run source C pos hp
  have core:Step CompetitorRecordRewind.machine (2*C+2) ![pos,0,0]
      ![source,List.replicate C true,[]] ![0,0,0]
      ![source,List.replicate C true,List.replicate C false]:=
    ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs.le⟩
  let cap:Fin 3 → ℕ:=![0,0,C+1]
  have run:=core.pad cap
  have hi:(fun i=>ZeroPadding.pad (cap i) (![source,List.replicate C true,[]] i))=
      ![source,List.replicate C true,List.replicate (C+1) false]:=by
    funext i;fin_cases i <;> simp [cap,ZeroPadding.pad]
  rw [hi] at run
  apply run.congr rfl
  funext i;fin_cases i <;> simp [cap,ZeroPadding.pad_zero,pad_replicate_false (C+1) C (by omega)]

theorem rewind_dock {t:ℕ} (slots:Fin 3 → Fin t) (hi:Function.Injective slots)
    (H:Fin t → ℕ) (A:Fin t → List Bool) (C:ℕ)
    (hp:H (slots 0)≤C) (h1:H (slots 1)=0) (h2:H (slots 2)=0)
    (a1:A (slots 1)=List.replicate C true) (a2:A (slots 2)=List.replicate (C+1) false) :
    Step (RecoveryFocus.machine slots CompetitorRecordRewind.machine) (2*C+2)
      H A (dockH slots H ![0,0,0]) A := by
  have run:=(rewind_step (A (slots 0)) C (H (slots 0)) hp).dock slots hi H A
    (by intro j;fin_cases j <;> simp [h1,h2])
    (by intro j;fin_cases j <;> simp [a1,a2])
  apply run.congr rfl
  apply install_existing
  intro j;fin_cases j <;> simp [a1,a2]

end NearCubicWires.ExtDecompositionBatch.CacheRewind
