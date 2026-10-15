import Proof.CaseAnalysis.WitnessNodeTag
import Proof.MachineModel.ClockScalarFields

/-! Total small-tag guard, using the existing bounded normalizer. The fixed
three-cell driver is retained for the next field; no decoded natural is
expanded. The two output flags must be conjoined by the node decision. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeSmall
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def normSlots : Fin 5 → Fin 11:=Fin.castAdd 6
def tagSlots : Fin 7 → Fin 11:=![2,5,6,7,8,9,10]
theorem norm_injective : Function.Injective normSlots:=by decide
theorem tag_injective : Function.Injective tagSlots:=by decide
def input (bits : List Bool) : Fin 11 → List Bool:=
  Fin.addCases (motive:=fun _ : Fin (5+6) => List Bool) (ClockNormalize.input 3 bits) (fun _=>[])
noncomputable def norm:=RecoveryFocus.machine normSlots ClockNormalize.machine
noncomputable def tag:=RecoveryFocus.machine tagSlots NodeTag.machine
noncomputable def machine:=Composition.machine norm tag

theorem norm_input (bits : List Bool) :
    ∀ i,input bits (normSlots i)=ClockNormalize.input 3 bits i:=by
  intro i
  fin_cases i <;> rfl

theorem tag_input (bits : List Bool) (out : Fin 5 → List Bool)
    (hp : out 2=frame (ClockNormalize.resize 3 bits)) :
    ∀ i,install normSlots (input bits) out (tagSlots i)=
      NodeTag.readyInput (ClockNormalize.resize 3 bits) i:=by
  intro i
  fin_cases i
  · change install normSlots (input bits) out (normSlots 2)=_
    rw [install_slot _ norm_injective,hp]
    rfl
  all_goals
    rw [install_other _ _ _ _ (by decide)]
    rfl

theorem small_run (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine 33 (input bits) out ∧
      out 0=List.replicate 3 true ∧ out 1=frame bits ∧
      out 3=[decide (bits.length ≤ 3)] ∧
      (∀ j : Fin 5,out (tagSlots (j.succ.castAdd 1))=
        [NodeTag.flags (ClockNormalize.resize 3 bits) j]):=by
  obtain ⟨nr,hn,hdriver,hsource,hpayload,hfit,_,hh,hs⟩:=ClockNormalize.normalize_run 3 bits
  have hnready : ClockJoin.ReadyRun ClockNormalize.machine 16 (ClockNormalize.input 3 bits) nr.final.tapes:=
    ⟨nr,hn,rfl,hh,hs.le⟩
  have hnf:=bounded_focus normSlots norm_injective _ _ _ hnready (input bits) (norm_input bits)
  obtain ⟨out,ht,_,hflags⟩:=NodeTag.tag_run (ClockNormalize.resize 3 bits) (ClockNormalize.resize_length 3 bits)
  have htf:=bounded_focus tagSlots tag_injective _ _ _ ht
    (install normSlots (input bits) nr.final.tapes) (tag_input bits _ hpayload)
  have h:=ClockJoin.join norm tag _ _ _ _ _ hnf htf
  refine ⟨_,h,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    exact (install_slot normSlots norm_injective _ _ 0).trans hdriver
  · rw [install_other _ _ _ _ (by decide)]
    exact (install_slot normSlots norm_injective _ _ 1).trans hsource
  · rw [install_other _ _ _ _ (by decide)]
    exact (install_slot normSlots norm_injective _ _ 3).trans hfit
  · intro j
    rw [install_slot _ tag_injective]
    exact hflags j

theorem flags_exact (bits : List Bool) (j : Fin 5) :
    (decide (bits.length ≤ 3) && NodeTag.flags (ClockNormalize.resize 3 bits) j)=
      NodeTag.flags bits j:=by
  by_cases h:bits.length ≤ 3
  · simp [NodeTag.flags,h,ClockScalarFields.resize_value 3 bits h]
  · simp [NodeTag.flags,h]

theorem flags_nat (bits : List Bool) (h : BitFields.passes bits) (j : Fin 5) :
    (decide ((BitFields.payload bits).length ≤ 3) &&
      NodeTag.flags (ClockNormalize.resize 3 (BitFields.payload bits)) j)=
        decide (RadixSemantics.value (BitFields.payload bits)=j.val):=by
  rw [flags_exact,NodeTag.flags_nat bits h j]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeSmall
