import Proof.CaseAnalysis.RowsCircuitCountBudget
import Proof.Supplier.RowCommonResources

/-! A fixed family tag is checked against its canonical code directly.
The literal printer and binary comparator avoid a second natural decoder. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitMode
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalBinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (threshold : Bool) : List Bool:=if threshold then [true,true] else []
def input (bits : List Bool) : Fin 5→List Bool:=![frame bits,[],[],[],[]]
def literalSlots : Fin 2→Fin 5:=![1,4]
def primeSlots : Fin 1→Fin 5:=fun _=>2
def equalSlots (i : Fin 4) : Fin 5:=i.castAdd 1
noncomputable def literal (threshold : Bool):=
  RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine (frame (word threshold)))
noncomputable def primer:=RecoveryFocus.machine primeSlots CloseoutRowsCircuitCount.prime
noncomputable def equality:=RecoveryFocus.machine equalSlots CloseoutWitness.NumericEquality.readyMachine
noncomputable def prefixMachine (threshold : Bool):=Composition.machine (literal threshold) primer
noncomputable def machine (threshold : Bool):=Composition.machine (prefixMachine threshold) equality
def budget (bits : List Bool):=4*bits.length+30

theorem word_value (threshold : Bool) : value (word threshold)=encodeNat threshold.toNat:=by
  cases threshold
  · exact CompetitorWitnessTriple.encoded_modes.1.symm
  · exact CompetitorWitnessTriple.encoded_modes.2.symm
theorem word_length (threshold : Bool) : (word threshold).length ≤ 2:=by
  cases threshold <;> decide
theorem equal_injective : Function.Injective equalSlots:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 5=>k.val) h)

theorem mode_run (threshold : Bool) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun (machine threshold) (budget bits) (input bits) out ∧
      out 0=frame bits ∧
      (readTapeBit (out 2) 0=true ↔ decodeNat (value bits)=some threshold.toNat):=by
  have hl:=(RowCommonResources.literal_ready (frame (word threshold))).focus literalSlots
    (by decide) (input bits) (by intro i;fin_cases i <;> rfl)
  let one:=install literalSlots (input bits)
    ![frame (word threshold),List.replicate (frame (word threshold)).length false]
  have hp:=CloseoutRowsCircuitCount.prime_run.focus primeSlots (by decide) one (by
    intro i;fin_cases i
    rw [show one=install literalSlots (input bits) _ by rfl,install_other _ _ _ _ (by decide)];rfl)
  let two:=install primeSlots one (fun _=>[true])
  have two_other (i : Fin 5) (hi:i≠2) : two i=one i:=install_other _ _ _ _ (by intro j;exact Ne.symm hi)
  have he:=(CloseoutRowsIntegerTests.equality_run bits (word threshold)).focus equalSlots
    equal_injective two (by
      intro i;fin_cases i
      · rw [two_other _ (by decide),show one=install literalSlots (input bits) _ by rfl,
          install_other _ _ _ _ (by decide)];rfl
      · rw [two_other _ (by decide)]
        exact install_slot literalSlots (by decide) _ _ 0
      · exact install_slot primeSlots (by decide) one (fun _=>[true]) 0
      · rw [two_other _ (by decide),show one=install literalSlots (input bits) _ by rfl,
          install_other _ _ _ _ (by decide)];rfl)
  have hall:=ClockJoin.join (prefixMachine threshold) equality _ _ _ _ _
    (ClockJoin.join (literal threshold) primer _ _ _ _ _ hl hp) he
  have hb:(2*(frame (word threshold)).length+2)+1+1+1+
      (4*max bits.length (word threshold).length+4) ≤ budget bits:=by
    have hw:=word_length threshold
    rw [frame_length]
    unfold budget;omega
  refine ⟨_,ClockJoin.enlarge (machine threshold) _ _ _ _ hall hb,?_,?_⟩
  · exact install_slot equalSlots equal_injective _ _ 0
  · change readTapeBit (install equalSlots _ _ (equalSlots 2)) 0=true ↔_
    rw [install_slot _ equal_injective]
    change decide (value bits=value (word threshold))=true ↔_
    rw [decide_eq_true_eq,word_value]
    constructor
    · intro h;rw [h,decodeNat_encode]
    · intro h;exact (encodeNat_of_decode h).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitMode
