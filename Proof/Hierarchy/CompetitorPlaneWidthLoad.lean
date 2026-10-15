import Proof.Hierarchy.CompetitorPlaneRawLoad

/-! A native-width driver may have the physically retained zero padding
produced by the local unary-width copier. Its live prefix still controls
exactly the native cell width. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def widthCfg (q : Fin 4) (source : List Bool) (pos b w nativeCap cap : ℕ) (target : List Bool) : Configuration 5 4 :=
  ⟨q,![pos,0,0,0,0],![source,ZeroPadding.pad nativeCap (List.replicate b true),
    List.replicate w true,target,List.replicate cap false]⟩

theorem width_load_run (pre suffix : List Bool) (b w count nativeCap cap : ℕ)
    (hb : b≤w) (hc : count<2^b) (hcap : 2*w+1≤cap) :
    ∃ r,runFrom CompetitorRawCell.machine (4*w+3)
        (widthCfg 0 (pre++binary b count++suffix) pre.length b w nativeCap cap (List.replicate cap false))=some r ∧
      r.final=widthCfg 3 (pre++binary b count++suffix) (pre.length+b) b w nativeCap cap
        (ZeroPadding.pad cap (frame (binary w count))) ∧ r.steps=4*w+3 := by
  obtain ⟨base,hr,hf,hs⟩ := load_run pre suffix b w count cap hb hc hcap
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config CompetitorRawCell.machine ![0,nativeCap,0,0,0] _ _ base hr
  have hcfg (q : Fin 4) (pos : ℕ) (target : List Bool) :
      ZeroPadding.config ![0,nativeCap,0,0,0] (cfg q (pre++binary b count++suffix) pos b w cap target)=
      widthCfg q (pre++binary b count++suffix) pos b w nativeCap cap target := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,cfg,widthCfg]
  rw [hcfg] at hrun
  exact ⟨r,hrun,by rw [hfinal,hf,hcfg],hsteps.trans hs⟩

end NearCubicWires.RepairOrdinary.CompetitorPlaneLoad
