import Proof.Hierarchy.CompetitorRawCount
import Proof.Hierarchy.CompetitorReusableDecision

/-! The native raw plane and retained raw P/N fields load into the same paid
finite workspace. Source/native/target width words are actual retained tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg (q : Fin 4) (source : List Bool) (pos b w cap : ℕ) (target : List Bool) : Configuration 5 4 :=
  ⟨q,![pos,0,0,0,0],![source,List.replicate b true,List.replicate w true,target,List.replicate cap false]⟩

theorem load_run (pre suffix : List Bool) (b w count cap : ℕ)
    (hb : b≤w) (hc : count<2^b) (hcap : 2*w+1≤cap) :
    ∃ r,runFrom CompetitorRawCell.machine (4*w+3)
        (cfg 0 (pre++binary b count++suffix) pre.length b w cap (List.replicate cap false))=some r ∧
      r.final=cfg 3 (pre++binary b count++suffix) (pre.length+b) b w cap
        (ZeroPadding.pad cap (frame (binary w count))) ∧ r.steps=4*w+3 := by
  obtain ⟨base,hr,hf,hs⟩ := CompetitorRawCell.raw_count_run pre suffix [] b w count hb hc (by simp)
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config CompetitorRawCell.machine ![0,0,0,cap,cap] _ _ base hr
  have hi : ZeroPadding.config ![0,0,0,cap,cap]
      (CompetitorRawCell.cfg 0 (pre++binary b count++suffix) pre.length b w [])=
      cfg 0 (pre++binary b count++suffix) pre.length b w cap (List.replicate cap false) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,CompetitorRawCell.cfg,cfg,ZeroPadding.pad,Nat.add_sub_of_le hcap]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,CompetitorRawCell.cfg,cfg,CompetitorReusableDecision.pad_zeros,max_eq_left hcap]

end NearCubicWires.RepairOrdinary.CompetitorPlaneLoad
