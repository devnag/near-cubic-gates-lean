import Proof.PCP.VerifierLookupQuery

/-! Lookup uses the decoder's retained capped dimensions directly. Padding
is preserved by the actual walk and is not reinstalled by the caller. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupWalk
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cappedCfg (q : Fin 4) (source : List Bool) (pos cap total driver : ℕ) : Configuration 2 4 :=
  ⟨q,![pos,driver],![source,CapMachine.counter cap total]⟩

theorem padded_cfg (q : Fin 4) (source : List Bool) (pos cap total driver : ℕ) :
    ZeroPadding.config (![0,cap+2] : Fin 2 → ℕ) (cfg q source pos total driver)=
      cappedCfg q source pos cap total driver := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl

theorem capped_walk_run (move : HeadMove) (source : List Bool) (pos cap n : ℕ) :
    ∃ r,runFrom (machine move) (3*n+2) (cappedCfg 0 source pos cap n 1)=some r ∧
      r.final=cappedCfg 3 source (shift move pos (2*n)) cap n 1 ∧ r.steps=3*n+2 := by
  obtain ⟨base,hb,hbf,hbs⟩ := walk_run move source pos n
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config (machine move) ![0,cap+2] _ _ base hb
  rw [padded_cfg] at hr
  rw [hbf,padded_cfg] at hrf
  exact ⟨r,hr,hrf,hrs.trans hbs⟩

end NearCubicWires.RepairSource.VerifierDecoding.LookupWalk
