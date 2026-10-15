import Proof.CaseAnalysis.RowsCanonicalFlag
import Proof.CaseAnalysis.RowsGateArityCheck
import Proof.CaseAnalysis.WitnessNodeFlag

/-! The outer balanced payload must contain exactly the SAME source's V
sums. The one canonical traversal retains its field stream and count;
an existing count comparison and one flag fold precede any family loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCount
open LocalBitMultitape RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 174) : Fin 177:=i.castAdd 3
def compareSlots : Fin 4→Fin 177:=![41,174,175,176]
def flagSlots : Fin 2→Fin 177:=![175,172]
def first:=RecoveryFocus.machine old CanonicalTest.machine
def compare:=RecoveryFocus.machine compareSlots CloseoutRowsGateArityCheck.machine
def flag:=RecoveryFocus.machine flagSlots NodeRound.flagMachine
def prefixMachine:=Composition.machine first compare
def machine:=Composition.machine prefixMachine flag
def input (bits : List Bool) (V : ℕ) (i : Fin 177) : List Bool:=
  if i.val=0 then frame bits else if i.val=174 then List.replicate V true else []
def count (bits : List Bool):=(tree (value bits)).atoms.length
def budget (bits : List Bool) (V : ℕ):=CanonicalTest.budget bits+1+(2*min (count bits) V+6)+1+1
def accepted (bits : List Bool) (V : ℕ):=
  CloseoutRowsCanonicalFlag.flag bits && decide (count bits=V)

theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 177=>k.val) h)
theorem outside (i : Fin 177) (hi : 174 ≤ i.val) : ∀ j,old j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 177=>k.val) h
  change j.val=i.val at hv
  omega

theorem count_run (bits : List Bool) (V : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits V) (input bits V) output ∧
      output 0=frame bits ∧ output 174=List.replicate V true ∧
      output 30=atomStream bits.length (tree (value bits)).atoms ∧
      output 41=CompareMachine.word (count bits) ∧ output 172=[accepted bits V]:=by
  obtain ⟨co,hc,cstream,ccount,_⟩:=CanonicalTest.fields_run bits
  obtain ⟨cflag,c0⟩:=CloseoutRowsCanonicalFlag.retained bits co hc
  have hf:=hc.focus old old_injective (input bits V) (by
    intro j
    simp only [input,old,Fin.val_castAdd,if_neg (show j.val≠174 by omega)]
    rfl)
  let middle:=install old (input bits V) co
  have blank (i : Fin 177) (hi : 174 ≤ i.val) : middle i=input bits V i:=
    install_other _ _ _ _ (outside i hi)
  have hcomp:=(CloseoutRowsGateArityCheck.arity_run (count bits) V).focus compareSlots (by decide) middle (by
    intro j;fin_cases j
    · exact (install_slot old old_injective _ co 41).trans ccount
    all_goals rw [blank _ (by decide)];rfl)
  let compared:=install compareSlots middle (CloseoutRowsGateArityCheck.output (count bits) V)
  have cf:compared 172=[CloseoutRowsCanonicalFlag.flag bits]:=by
    rw [show compared=install compareSlots middle _ by rfl,install_other _ _ _ _ (by decide)]
    exact (install_slot old old_injective _ co 172).trans cflag
  have cv:compared 175=[decide (count bits=V)]:=install_slot compareSlots (by decide) _ _ 2
  have hflag:ClockJoin.ReadyRun NodeRound.flagMachine 1
      ![[decide (count bits=V)],[CloseoutRowsCanonicalFlag.flag bits]]
      ![[decide (count bits=V)],[accepted bits V]]:=by
    obtain ⟨r,hr,rt,rh,rs⟩:=NodeRound.flag_ready [decide (count bits=V)] (CloseoutRowsCanonicalFlag.flag bits)
    exact ⟨r,hr,rt,rh,rs.le⟩
  have hff:=hflag.focus flagSlots (by decide) compared (by intro j;fin_cases j <;> assumption)
  have hall:=ClockJoin.join prefixMachine flag _ _ _ _ _
    (ClockJoin.join first compare _ _ _ _ _ hf hcomp) hff
  refine ⟨_,hall,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),show compared=install compareSlots middle _ by rfl,
      install_other _ _ _ _ (by decide)]
    exact (install_slot old old_injective _ co 0).trans c0
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot compareSlots (by decide) _ _ 1
  · rw [install_other _ _ _ _ (by decide),show compared=install compareSlots middle _ by rfl,
      install_other _ _ _ _ (by decide)]
    exact (install_slot old old_injective _ co 30).trans cstream
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot compareSlots (by decide) _ _ 0
  · exact install_slot flagSlots (by decide) _ _ 1

theorem decision_exact (bits : List Bool) (V : ℕ) : accepted bits V=true ↔
    ∃ values,CanonicalBinary.encodeBalancedList values=value bits ∧ values.length=V:=by
  have hc:CloseoutRowsCanonicalFlag.flag bits=true ↔
      ∃ values,CanonicalBinary.encodeBalancedList values=value bits:=by
    unfold CloseoutRowsCanonicalFlag.flag
    rw [decide_eq_true_eq,RecoveryUnpair.bits_value]
    exact eq_comm.trans (tree_canonical_iff (value bits))
  rw [accepted,Bool.and_eq_true,hc,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨values,hv⟩,hn⟩
    refine ⟨values,hv,?_⟩
    simpa only [count,←hv,tree_atoms] using hn
  · rintro ⟨values,hv,hn⟩
    refine ⟨⟨values,hv⟩,?_⟩
    simpa only [count,←hv,tree_atoms] using hn

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCount
