import Proof.CaseAnalysis.WitnessCanonicalFields

/-! Exact singleton shape of the retained canonical-list verdict, under
the same original run. This only projects the existing comparison output. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCanonicalFlag
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open CompetitorRationalProducts CanonicalTest
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flag (bits : List Bool):=decide (value bits=value (Reencode.canonical bits).bits)
theorem retained (bits : List Bool) (output : Fin 174→List Bool)
    (houtput : ClockJoin.ReadyRun CanonicalTest.machine (CanonicalTest.budget bits)
      (CanonicalTest.input bits) output) : output 172=[flag bits] ∧ output 0=frame bits:=by
  obtain ⟨out,ho,hframe,_⟩:=Reencode.reencode_ready bits
  have hs:=ClockJoin.join copy boot _ _ _ _ _ (copy_ready bits) (boot_ready bits)
  have hw:=bounded_focus walkSlots walk_injective _ _ _ ho (primed bits) (walk_input bits)
  have hp:=ClockJoin.join start walk _ _ _ _ _ hs hw
  have he:=bounded_focus equalSlots equal_injective _ _ _ (comparison_ready bits)
    (walked bits out) (comparison_input bits out hframe)
  have h:=ClockJoin.join prefixMachine equality _ _ _ _ _ hp he
  obtain ⟨a,ha,atapes,_,_⟩:=ClockJoin.enlarge CanonicalTest.machine (time bits) (CanonicalTest.budget bits)
    _ _ h (time_bound bits)
  obtain ⟨b,hb,btapes,_,_⟩:=houtput
  have hab:a=b:=Option.some.inj (ha.symm.trans hb)
  subst b
  have hout:output=install equalSlots (walked bits out) (compareOutput bits):=btapes.symm.trans atapes
  rw [hout]
  constructor
  · change install equalSlots _ _ (equalSlots 2)=_
    rw [install_slot _ equal_injective]
    rfl
  · change install equalSlots _ _ (equalSlots 0)=_
    rw [install_slot _ equal_injective]
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsCanonicalFlag
