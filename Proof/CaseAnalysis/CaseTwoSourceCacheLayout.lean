import Proof.CaseAnalysis.CaseTwoSourceCall
import Proof.PCP.PCPPSourceCachePrepare

/-! The original request frame is outside the shared clause/support bank.
Only the faithful constructor's actual output enters that bank; its size
and arity are the retained physical scalars from the descriptor producer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceCache
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degree (a : PointwisePCPPAlgorithm):=PCPPQueryCachedBounds.degree a
def coldTapes (a : PointwisePCPPAlgorithm):=PCPPQueryCold.tapes (degree a)
def tapes (a : PointwisePCPPAlgorithm):=coldTapes a+SourceCall.tapes a
def coldSlots (a : PointwisePCPPAlgorithm) (j : Fin (coldTapes a)) : Fin (tapes a):=j.castAdd (SourceCall.tapes a)
theorem cold_lower (a : PointwisePCPPAlgorithm) : 38≤coldTapes a:=PCPPSourceCache.cold_lower a
theorem output_positive (a : PointwisePCPPAlgorithm) : 0<(SourceCall.outputSlot a).val:=by
  unfold SourceCall.outputSlot SourceCall.slots
  split_ifs
  all_goals simp only [Fin.val_natAdd]
  all_goals omega
def sourceSlots (a : PointwisePCPPAlgorithm) (j : Fin (SourceCall.tapes a)) : Fin (tapes a):=
  if j.val=(SourceCall.outputSlot a).val then ⟨0,by have h:=cold_lower a;dsimp [tapes];omega⟩
  else j.natAdd (coldTapes a)
theorem source_injective (a : PointwisePCPPAlgorithm) : Function.Injective (sourceSlots a):=by
  intro i j he
  have hv:=congrArg Fin.val he
  have hc:=cold_lower a
  apply Fin.ext
  dsimp only [sourceSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;>omega
theorem cold_injective (a : PointwisePCPPAlgorithm) : Function.Injective (coldSlots a):=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes a)=>k.val) h)
def requestSlot (a : PointwisePCPPAlgorithm) : Fin (tapes a):=
  sourceSlots a ⟨0,by dsimp [SourceCall.tapes];omega⟩
theorem request_val (a : PointwisePCPPAlgorithm) : (requestSlot a).val=coldTapes a:=by
  have h:=output_positive a
  simp [requestSlot,sourceSlots,show (0 : ℕ)≠(SourceCall.outputSlot a).val by omega]
def input (a : PointwisePCPPAlgorithm) (word : List Bool) (size arity : ℕ) : Fin (tapes a)→List Bool:=fun j=>
  if j.val=coldTapes a then frame word else if j.val=21 then List.replicate size true
  else if j.val=19 then List.replicate arity true else []
noncomputable def sourceMachine (a : PointwisePCPPAlgorithm):=RecoveryFocus.machine (sourceSlots a) (SourceCall.machine a)
noncomputable def setupMachine (a : PointwisePCPPAlgorithm):=RecoveryFocus.machine (coldSlots a)
  (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a))
noncomputable def machine (a : PointwisePCPPAlgorithm):=Composition.machine (sourceMachine a) (setupMachine a)
def cacheSlots (a : PointwisePCPPAlgorithm) (j : Fin 19):=coldSlots a (PCPPQueryCold.cacheSlots (degree a) j)
def sizeSlot (a : PointwisePCPPAlgorithm):=coldSlots a (PCPPQueryCold.sizeSlot (degree a))
def budget (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity):=
  SourceCall.budget a request+1+PCPPSourceCache.setupBudget a request

theorem source_input (a : PointwisePCPPAlgorithm) (word : List Bool) (size arity : ℕ)
    (j : Fin (SourceCall.tapes a)) :
    input a word size arity (sourceSlots a j)=SourceCall.input a word j:=by
  have hc:=cold_lower a
  have ho:=output_positive a
  dsimp [input,sourceSlots,SourceCall.input,SourceHandoff.sourceTapes]
  split_ifs <;>simp_all
  all_goals omega
theorem source_output (a : PointwisePCPPAlgorithm) :
    sourceSlots a (SourceCall.outputSlot a)=coldSlots a ⟨0,by have h:=cold_lower a;omega⟩:=by
  apply Fin.ext
  simp [sourceSlots,coldSlots]
theorem source_other (a : PointwisePCPPAlgorithm) (i : Fin (coldTapes a)) (hi : i.val≠0) :
    ∀ j,sourceSlots a j≠coldSlots a i:=by
  intro j he
  have hv:=congrArg Fin.val he
  have hb:=i.isLt
  dsimp only [sourceSlots,coldSlots] at hv
  split_ifs at hv <;>simp only [Fin.val_natAdd,Fin.val_castAdd] at hv <;>omega
theorem cold_away (a : PointwisePCPPAlgorithm) : ∀ j,coldSlots a j≠requestSlot a:=by
  intro j he
  have hv:=congrArg Fin.val he
  rw [request_val] at hv
  change j.val=coldTapes a at hv
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.SourceCache
