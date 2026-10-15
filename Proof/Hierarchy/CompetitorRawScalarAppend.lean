import Proof.Hierarchy.CompetitorRawScalarEmit

/-! Raw appending from an exact scalar frame with a retained paid zero
counter. The source head is restored and the output append head advances. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawScalarAppend
open LocalBitMultitape RecoveryExecution
open CompetitorReusableDecision CompetitorRawScalarEmit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 4) (bits out : List Bool) (cap : ℕ) : Configuration 3 4 :=
  ⟨q,![0,out.length,0],![frame bits,out,List.replicate cap false]⟩

theorem raw_append_run (bits out : List Bool) (cap : ℕ) (hc : 2*bits.length+1≤cap) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom machine (4*bits.length+3) (cfg 0 bits out cap)=some r ∧
      r.final=cfg 3 bits (out++bits) cap ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs⟩ := append_run bits [] out
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config machine ![0,0,cap] _ _ base hr
  have hi : ZeroPadding.config ![0,0,cap] (scan 0 (frame bits++[]) 0 out)=cfg 0 bits out cap := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,scan,cfg,ZeroPadding.pad]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,reset,cfg,pad_zeros,max_eq_left hc]

end NearCubicWires.RepairOrdinary.CompetitorRawScalarAppend
