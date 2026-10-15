import Proof.MachineModel.OrdinaryTransitionEventRun
import Proof.MachineModel.OrdinaryFrameLoad

/-! Load the next actual head-array field into the reusable local head tape.
The existing reset capacity is retained and the array source keeps streaming. -/
namespace NearCubicWires.RepairOrdinary.TransitionHeadLoad
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (backing : List Bool)
    (cap : ℕ) : Configuration 3 s :=
  ⟨q,![pos,0,0],![source,backing,List.replicate cap false]⟩
def capacities (cap : ℕ) : Fin 3 → ℕ := ![0,0,cap]

theorem load_run (pre bits post backing : List Bool) (cap : ℕ)
    (hb : backing.length≤2*bits.length+1) (hc : 2*bits.length+1≤cap) :
    ∃ r,runFrom FrameLoad.machine (4*bits.length+3)
      (cfg 0 (pre++frame bits++post) pre.length backing cap)=some r ∧
      r.final=cfg 3 (pre++frame bits++post) (pre.length+2*bits.length+1) (frame bits) cap ∧
      r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs,_⟩ := FrameLoad.load_run pre bits post backing hb
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config FrameLoad.machine
    (capacities cap) _ _ base hr
  have hi : ZeroPadding.config (capacities cap)
      (FrameLoad.scan 0 (pre++frame bits++post) pre.length [] backing)=
      cfg 0 (pre++frame bits++post) pre.length backing cap := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,ZeroPadding.pad,capacities,
        FrameLoad.scan,cfg,StablePartition.Workspace.overlay]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,ZeroPadding.pad,capacities,
      FrameLoad.reset,cfg]
    omega

end NearCubicWires.RepairOrdinary.TransitionHeadLoad
