import Proof.CaseAnalysis.RowsCircuitTopCount
import Proof.CaseAnalysis.RowsCircuitLayout

/-! Total symmetric top-table validation on the original raw field. The
same canonical Boolean list, its actual length and the already produced
bottom-count template determine the exact public top condition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymTop
open LocalBitMultitape RecoveryRootRound RadixSemantics CloseoutWitness
open CanonicalBinary RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 178) : Fin 181:=i.castAdd 3
def countSlots : Fin 4→Fin 181:=![41,178,179,180]
def flagSlots : Fin 2→Fin 181:=![176,179]
def input (m : ℕ) (bits : List Bool) : Fin 181→List Bool:=
  Fin.addCases (m:=178) (n:=3) (motive:=fun _=>List Bool) (NatCold.input bits) ![UnaryTemplate.tape m,[],[]]
noncomputable def vector:=RecoveryFocus.machine old CloseoutRowsBooleanVector.machine
noncomputable def counter:=RecoveryFocus.machine countSlots CloseoutRowsCircuitTopCount.machine
noncomputable def finish:=RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
noncomputable def phase:=Composition.machine vector counter
noncomputable def machine:=Composition.machine phase finish
def budget (bits : List Bool):=NatCold.budget bits+2*(BitFields.payload bits).length+13
def valid (m : ℕ) (bits : List Bool):=∃ values,decodeBoolList (value bits)=some values ∧ values.length=m+1

theorem old_injective : Function.Injective old:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 181=>k.val) h)
theorem old_outside (i : Fin 181) (hi:178 ≤ i.val) : ∀ j,old j≠i:=by
  intro j h;have hv:=congrArg (fun k : Fin 181=>k.val) h
  change j.val=i.val at hv;omega

theorem valid_iff (m : ℕ) (bits : List Bool) : valid m bits ↔
    (decodeBoolList (value bits)).isSome ∧ (BitFields.payload bits).length=m+1:=by
  constructor
  · rintro ⟨values,hv,hlen⟩
    have he:BitFields.payload bits=values:=
      (CloseoutRowsBooleanVector.checks_of_typed values bits (encodeBoolList_of_decode hv).symm).2
    exact ⟨Option.isSome_iff_exists.mpr ⟨values,hv⟩,he ▸ hlen⟩
  · rintro ⟨hv,hlen⟩
    obtain ⟨values,hv⟩:=Option.isSome_iff_exists.mp hv
    have he:BitFields.payload bits=values:=
      (CloseoutRowsBooleanVector.checks_of_typed values bits (encodeBoolList_of_decode hv).symm).2
    exact ⟨values,hv,he ▸ hlen⟩

theorem top_run (m : ℕ) (bits : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget bits) (input m bits) out ∧
      out 174=frame (BitFields.payload bits) ∧ out 178=UnaryTemplate.tape m ∧
      (readTapeBit (out 179) 0=true ↔ valid m bits):=by
  obtain ⟨v,hv,table,count,flag,_typed⟩:=CloseoutRowsBooleanVector.vector_run bits
  have hvector:=hv.focus old old_injective (input m bits) (by intro i;simp only [input,old,Fin.addCases_left])
  let one:=install old (input m bits) v
  have one_old (i : Fin 178):one (old i)=v i:=install_slot old old_injective _ _ i
  have one_new (i : Fin 181) (hi:178 ≤ i.val):one i=input m bits i:=install_other _ _ _ _ (old_outside i hi)
  have hc:=(CloseoutRowsCircuitTopCount.count_run (BitFields.payload bits).length m).focus
    countSlots (by decide) one (by
      intro i;fin_cases i
      · exact (one_old 41).trans count
      all_goals rw [one_new _ (by decide)];rfl)
  let checked:=install countSlots one
    (![CompareMachine.word (BitFields.payload bits).length,UnaryTemplate.tape m,
      [decide ((BitFields.payload bits).length=m+1)],
      List.replicate (min (BitFields.payload bits).length (m+1)+2) false] : Fin 4→List Bool)
  have c176:checked 176=v 176:=by
    rw [show checked=install countSlots one _ by rfl,install_other _ _ _ _ (by decide)]
    exact one_old 176
  have c179:checked 179=[decide ((BitFields.payload bits).length=m+1)]:=install_slot countSlots (by decide) _ _ 2
  have hf:=(CloseoutRowsIntegerRound.flag_ready (v 176) (decide ((BitFields.payload bits).length=m+1))).focus_at
    flagSlots (by decide) (fun _=>0) checked
    (by intro i;fin_cases i;exact c176;exact c179) (by intro i;rfl)
  obtain ⟨f,fr,fh,ft,fs⟩:=hf
  have hfinish:ClockJoin.ReadyRun finish 1 checked
      (install flagSlots checked ![v 176,[decide ((BitFields.payload bits).length=m+1) && readTapeBit (v 176) 0]]):=
    ⟨f,fr,ft,by intro i;rw [fh],fs.le⟩
  have first:=ClockJoin.join vector counter _ _ _ _ _ hvector hc
  have all:=ClockJoin.join phase finish _ _ _ _ _ first hfinish
  have hb:NatCold.budget bits+1+CloseoutRowsCircuitTopCount.budget (BitFields.payload bits).length m+1+1≤budget bits:=by
    unfold CloseoutRowsCircuitTopCount.budget budget
    have hmin:=Nat.min_le_left (BitFields.payload bits).length (m+1)
    omega
  have more:=ClockJoin.enlarge machine _ (budget bits) _ _ all hb
  refine ⟨_,more,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    change install countSlots one _ 174=_
    rw [install_other _ _ _ _ (by decide)]
    exact (one_old 174).trans table
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot countSlots (by decide) _ _ 1
  · change readTapeBit (install flagSlots checked _ (flagSlots 1)) 0=true ↔_
    rw [install_slot _ (by decide)]
    change (decide ((BitFields.payload bits).length=m+1) && readTapeBit (v 176) 0)=true ↔_
    rw [Bool.and_eq_true,decide_eq_true_eq,flag,valid_iff,and_comm]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitSymTop
