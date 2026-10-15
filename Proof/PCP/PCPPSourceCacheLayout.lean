import Proof.PCP.PCPPQueryColdBounds
import Proof.PCP.PCPPRequestSourceRuntime

/-! The one faithful source call is routed directly into the shared query
bank. The native emitter's actual arity and size counters stay outside it. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def degree (a : PointwisePCPPAlgorithm) := PCPPQueryCachedBounds.degree a
def coldTapes (a : PointwisePCPPAlgorithm) := PCPPQueryCold.tapes (degree a)
def tapes (a : PointwisePCPPAlgorithm) := coldTapes a+PCPPRequestSource.tapes a
def coldSlots (a : PointwisePCPPAlgorithm) (j : Fin (coldTapes a)) : Fin (tapes a) := j.castAdd (PCPPRequestSource.tapes a)

theorem cold_lower (a : PointwisePCPPAlgorithm) : 38≤coldTapes a := by
  simp [coldTapes,PCPPQueryCold.tapes,PCPPQueryCapacity.tapes,RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]
  omega

theorem source_output_positive (a : PointwisePCPPAlgorithm) : 0<(PCPPRequestSource.outputSlot a).val := by
  unfold PCPPRequestSource.outputSlot PCPPRequestSource.slots
  split_ifs with h
  · simp [PCPPRequestInput.outputSlot,PCPPRequestInput.slots]
  · simp only [Fin.val_natAdd]
    have ht:= (PCPPRequestSource.program a).outputTape.isLt
    omega

def sourceSlots (a : PointwisePCPPAlgorithm) (j : Fin (PCPPRequestSource.tapes a)) : Fin (tapes a) :=
  if j.val=(PCPPRequestSource.outputSlot a).val then ⟨0,by have h:=cold_lower a; dsimp [tapes]; omega⟩
  else j.natAdd (coldTapes a)
theorem source_injective (a : PointwisePCPPAlgorithm) : Function.Injective (sourceSlots a) := by
  intro i j he
  have hv:=congrArg Fin.val he
  have hc:=cold_lower a
  apply Fin.ext
  dsimp [sourceSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega
theorem cold_injective (a : PointwisePCPPAlgorithm) : Function.Injective (coldSlots a) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin (tapes a)=>k.val) h)

def nativeWord (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  frame (PCPPRequestNodeGlobal.payload r.circuit.nodes (natWord r.circuit.output.val))
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) : Fin (tapes a)→List Bool := fun j=>
  if j.val=coldTapes a then nativeWord a r else if j.val=21 then List.replicate r.circuit.size true
  else if j.val=19 then List.replicate r.arity true else []
noncomputable def sourceMachine (a : PointwisePCPPAlgorithm) := RecoveryFocus.machine (sourceSlots a) (PCPPRequestSource.machine a)
noncomputable def setupMachine (a : PointwisePCPPAlgorithm) := RecoveryFocus.machine (coldSlots a)
  (PCPPQueryCold.machine (degree a) (PCPPQueryCachedBounds.coefficient a))
noncomputable def machine (a : PointwisePCPPAlgorithm) := Composition.machine (sourceMachine a) (setupMachine a)

theorem source_input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (j : Fin (PCPPRequestSource.tapes a)) :
    input a r (sourceSlots a j)=(if j.val=0 then nativeWord a r else []) := by
  have hc:=cold_lower a
  have ho:=source_output_positive a
  dsimp [input,sourceSlots]
  split_ifs <;> simp_all
  all_goals omega

theorem source_output_slot (a : PointwisePCPPAlgorithm) :
    sourceSlots a (PCPPRequestSource.outputSlot a)=coldSlots a ⟨0,by have h:=cold_lower a; omega⟩ := by
  apply Fin.ext
  simp [sourceSlots,coldSlots]

theorem source_other (a : PointwisePCPPAlgorithm) (i : Fin (coldTapes a)) (hi : i.val≠0) :
    ∀ j,sourceSlots a j≠coldSlots a i := by
  intro j he
  have hv:=congrArg Fin.val he
  have hb:=i.isLt
  dsimp [sourceSlots,coldSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega

theorem cold_input_other (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (source : List Bool) (j : Fin (coldTapes a)) (hj : j.val≠0) :
    input a r (coldSlots a j)=PCPPQueryCold.input (degree a) source r.circuit.size r.arity j := by
  have hlt:=j.isLt
  simp [input,coldSlots,PCPPQueryCold.input,hj,show j.val≠coldTapes a by omega]
  rfl

end NearCubicWires.RepairOrdinary.PCPPSourceCache
