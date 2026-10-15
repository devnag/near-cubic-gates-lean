import Proof.CaseAnalysis.WitnessOracleCallPrepare

/-! A checked oracle call from the retained source bank. Its only extra raw
input is the guessed circuit frame. The complete old bank survives the
three paid copies and the cold typed decoder unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepared_old {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (hq : base (fields 2)=List.replicate (value arityBits) true)
    (i : Fin t) : prepared fields base bits x arityBits (old i)=base i:=by
  by_cases he:i=fields 2
  · subst i
    change install (rawSlots fields) _ _ (rawSlots fields 0)=_
    rw [install_slot _ (raw_injective fields)]
    exact hq.symm
  rw [prepared,install_other _ _ _ _ (by
    intro j hj
    fin_cases j
    · exact he ((old_injective t) hj.symm)
    · exact old_ne_extra i 1383 hj.symm
    · exact old_ne_extra i 3 hj.symm
    · exact old_ne_extra i 1384 hj.symm),copied_old]

theorem prepared_extra {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (i : Fin 1385) (hi : i.val<1381) :
    prepared fields base bits x arityBits (extra t i)=
      if i=3 then List.replicate (value arityBits) true else copied base bits x arityBits (extra t i):=by
  by_cases h3:i=3
  · subst i
    change install (rawSlots fields) _ _ (rawSlots fields 2)=_
    rw [install_slot _ (raw_injective fields)]
    simp
  rw [if_neg h3,prepared,install_other _ _ _ _ (by
    intro j hj
    fin_cases j
    · exact old_ne_extra (fields 2) i hj
    · have he:=congrArg Fin.val ((extra_injective t) hj)
      change 1383=i.val at he
      omega
    · exact h3 ((extra_injective t) hj.symm)
    · have he:=congrArg Fin.val ((extra_injective t) hj)
      change 1384=i.val at he
      omega)]

theorem parser_input_shape (x bits arityBits : List Bool) (i : Fin (Oracle.tapes+1)) :
    Oracle.coldInput x bits arityBits i=
      if i.val=0 then frame x else if i.val=1 then frame bits
      else if i.val=2 then frame arityBits else if i.val=3 then List.replicate (value arityBits) true else []:=by
  refine Fin.addCases (m:=Oracle.tapes) (n:=1) ?_ ?_ i
  · intro j
    simp only [Oracle.coldInput,Fin.addCases_left,Fin.val_castAdd]
    rfl
  · intro j
    simp only [Oracle.coldInput,Fin.addCases_right,Fin.val_natAdd]
    have hj:j.val=0:=by omega
    simp only [hj,Oracle.tapes,Nat.add_zero,show (1380 : ℕ)≠0 by decide,
      show (1380 : ℕ)≠1 by decide,show (1380 : ℕ)≠2 by decide,show (1380 : ℕ)≠3 by decide,if_false]

theorem prepared_parser {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (i : Fin (Oracle.tapes+1)) :
    prepared fields base bits x arityBits (parserSlots t i)=Oracle.coldInput x bits arityBits i:=by
  change prepared fields base bits x arityBits (extra t (i.castAdd 4))=_
  rw [prepared_extra fields base bits x arityBits _ i.isLt,copied_extra,parser_input_shape]
  have hi:i.val<1381:=i.isLt
  simp only [Fin.ext_iff,Fin.val_castAdd]
  change (if i.val=3 then List.replicate (value arityBits) true else
    if i.val=1382 then List.replicate (2*arityBits.length+1) false else
    if i.val=2 then frame arityBits else if i.val=1381 then List.replicate (2*x.length+1) false else
    if i.val=0 then frame x else if i.val=1 then frame bits else [])=_
  split_ifs <;> first | rfl | omega

theorem parser_outside {t : ℕ} (i : Fin t) : ∀ j,parserSlots t j≠old i:=by
  intro j hj
  have hv:=congrArg Fin.val hj
  simp only [parserSlots,old,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

theorem call_run {t : ℕ} (fields : Fin 3→Fin t) (base : Fin t→List Bool)
    (bits x arityBits : List Bool) (hx : base (fields 0)=frame x)
    (hqb : base (fields 1)=frame arityBits)
    (hqr : base (fields 2)=List.replicate (value arityBits) true)
    (hN : 2  ≤  x.length) (hcap : 16*bits.length  ≤  x.length)
    (hb : arityBits.length  ≤  x.length+1) : ∃ out,
    ClockJoin.ReadyRun (machine fields) (budget x bits arityBits) (input base bits) out ∧
      (∀ i,out (old i)=base i) ∧
      out (parserSlots t Oracle.flagSlot)=[(decodeBooleanCircuit (value arityBits) (value bits)).isSome] ∧
      (∀ c : BooleanCircuit (value arityBits),decodeBooleanCircuit (value arityBits) (value bits)=some c →
        out (parserSlots t Oracle.descriptorSlot)=PCPPNative.descriptor c):=by
  have hp:=prepare_run fields base bits x arityBits hx hqb hqr
  obtain ⟨parsed,hr,hflag,hdesc⟩:=Oracle.cold_run x bits arityBits hN hcap hb
  have hc:=hr.focus (parserSlots t) (parser_injective t) (prepared fields base bits x arityBits)
    (prepared_parser fields base bits x arityBits)
  refine ⟨_,ClockJoin.join (prepare fields) (parser t) _ _ _ _ _ hp hc,?_,?_,?_⟩
  · intro i
    rw [install_other _ _ _ _ (parser_outside i)]
    exact prepared_old fields base bits x arityBits hqr i
  · exact (install_slot _ (parser_injective t) _ _ _).trans hflag
  · intro c hd
    exact (install_slot _ (parser_injective t) _ _ _).trans (hdesc c hd)

end NearCubicWires.RepairOrdinary.CloseoutWitness.OracleCall
