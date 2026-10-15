import Proof.PCP.PCPPRequestNodeDock

/-! Complete cold native Boolean-node coding, preserving the original live
source cursor. Only that source is initially present; all work is blank. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCold
open LocalBitMultitape RepairRepresentation ExecutableInterfaces CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine := PCPPRequestNodeDock.dock PCPPRequestNodePrepare.machine PCPPRequestNodeDispatch.machine
private abbrev states {t s : ℕ} (_ : Machine t s) := s
def entry (source : List Bool) (pos : ℕ) : Configuration 642 (states machine) :=
  Composition.leftConfig _ (PCPPRequestNodeDock.extended (PCPPRequestNodePrepare.entry source pos))
def atom {n : ℕ} (node : BooleanNode n) (j : Fin 3) := encodeNat (PCPPRequestNodeSchema.fields node j)
def budget {n : ℕ} (node : BooleanNode n) :=
  PCPPRequestNodePrepare.budget node+1+
    PCPPRequestNodeDispatch.budget (atom node 0) (atom node 1) (atom node 2) (PCPPRequestNodeSchema.binaryNode node)

theorem cold_run {n : ℕ} (pre tail : List Bool) (node : BooleanNode n) :
    ∃ r,runFrom machine (budget node)
      (entry (pre++PCPPRequestNodeSchema.native node++tail) pre.length)=some r ∧
      r.steps≤budget node ∧
      r.final.tapes 0=pre++PCPPRequestNodeSchema.native node++tail ∧
      r.final.heads 0=pre.length+(PCPPRequestNodeSchema.native node).length ∧
      (∃ padding,r.final.tapes 630=frame (encodeBooleanNode node).bits++List.replicate padding false) ∧
      r.final.heads 630=0 ∧ r.final.tapes 640=(encodeBooleanNode node).bits ∧ r.final.heads 640=0 := by
  obtain ⟨first,hfirst,fs,f0,fh0,fields,fieldHeads,flag,flagHead⟩ := PCPPRequestNodePrepare.cold_run pre tail node
  obtain ⟨pa,ha⟩ := fields 0
  obtain ⟨pb,hb⟩ := fields 1
  obtain ⟨pc,hc⟩ := fields 2
  obtain ⟨out,hout,framed,raw⟩ := PCPPRequestNodeDispatch.dispatch_run
    (atom node 0) (atom node 1) (atom node 2) pa pb pc (PCPPRequestNodeSchema.binaryNode node)
  have hh (i : Fin 4) : first.final.heads (![85,220,355,406] i)=0 := by
    fin_cases i
    · exact fieldHeads 0
    · exact fieldHeads 1
    · exact fieldHeads 2
    · exact flagHead
  obtain ⟨r,hr,rs,r0,rh0,rt,rh⟩ := PCPPRequestNodeDock.dock_run
    PCPPRequestNodePrepare.machine PCPPRequestNodeDispatch.machine _ _ _ first hfirst
    (atom node 0) (atom node 1) (atom node 2) pa pb pc _ ha hb hc flag hh out hout
  have he : PCPPRequestNodeCode.result (atom node 0) (atom node 1) (atom node 2)
      (PCPPRequestNodeSchema.binaryNode node)=encodeBooleanNode node := PCPPRequestNodeDispatch.result_code node
  refine ⟨r,hr,by unfold budget; omega,r0.trans f0,rh0.trans fh0,?_,rh 222,?_,rh 232⟩
  · obtain ⟨padding,hp⟩ := framed
    refine ⟨padding,(rt 222).trans ?_⟩
    rw [he] at hp
    exact hp
  · exact (rt 232).trans (by rw [he] at raw; exact raw)

end
end NearCubicWires.RepairOrdinary.PCPPRequestNodeCold
