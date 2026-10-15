import Proof.CaseAnalysis.RowsCircuitThreshold
import Proof.Hierarchy.CompetitorRecordRewind

/-! Final resource cursors return with the already paid raw C driver and
erase log. The same existing saturating rewind works from zero as well;
no C-sized template or larger private tape is created. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCounterReturn
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (C : ℕ) (source : List Bool) : Fin 3→List Bool:=
  ![source,List.replicate C true,List.replicate (C+1) false]

theorem return_run (C pos : ℕ) (source : List Bool) (hp : pos ≤ C) :
    PCPOuter.Exact CompetitorRecordRewind.machine (2*C+2) (![pos,0,0] : Fin 3→ℕ)
      (input C source) (fun _=>0) (input C source):=by
  obtain ⟨base,hb,bf,bs⟩:=CompetitorRecordRewind.rewind_run source C pos hp
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config CompetitorRecordRewind.machine
    (![0,0,C+1] : Fin 3→ℕ) _ _ base hb
  have start:ZeroPadding.config (![0,0,C+1] : Fin 3→ℕ)
      (CompetitorRecordRewind.cfg 0 source pos C 0 0 [])=
      (⟨0,![pos,0,0],input C source⟩ : Configuration 3 3):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,CompetitorRecordRewind.cfg,input,ZeroPadding.pad]
  rw [start] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf,bf];funext i;fin_cases i <;> rfl
  · rw [rf,bf];funext i;fin_cases i <;>
      simp [ZeroPadding.config,CompetitorRecordRewind.cfg,input,ZeroPadding.pad]
    exact List.replicate_succ'.symm

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCounterReturn
