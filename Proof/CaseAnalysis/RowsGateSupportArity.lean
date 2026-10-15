import Proof.CaseAnalysis.RowsGateSupportCount
import Proof.Supplier.EquationNaturalHeader

/-! The actual support bitmap supplies the same retained top's canonical
native arity, including empty support. The whole count-to-header run starts
with only that bitmap and blank work. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportArity
open LocalBitMultitape RecoveryRootRound CloseoutRowsSupportCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlots (i : Fin 3) : Fin 18:=i.castAdd 15
def headerSlots (i : Fin 16) : Fin 18:=if i.val=0 then 1 else ⟨i.val+2,by omega⟩
theorem header_val (i : Fin 16) : (headerSlots i).val=if i.val=0 then 1 else i.val+2:=by
  unfold headerSlots
  split_ifs <;> rfl
theorem count_injective : Function.Injective countSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 18=>k.val) h)
theorem header_injective : Function.Injective headerSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [header_val,header_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
def input (bits : List Bool) (i : Fin 18):=if i.val=0 then frame bits else []
noncomputable def count:=RecoveryFocus.machine countSlots CloseoutRowsSupportCount.readyMachine
noncomputable def header:=RecoveryFocus.machine headerSlots EquationNaturalHeader.machine
noncomputable def machine:=Composition.machine count header
def budget (bits : List Bool):=4*bits.length+4+1+(EquationNaturalHeader.budget (ones bits)+2)

theorem arity_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      output 0=frame bits ∧ output 3=List.replicate (ones bits) true ∧
      output 16=RepairRepresentation.natWord (ones bits):=by
  obtain ⟨c,hc,c0,c1⟩:=count_ready bits
  have h0:=hc.focus countSlots count_injective (input bits) (by intro i;fin_cases i <;> rfl)
  let middle:=install countSlots (input bits) c
  have fresh (i : Fin 18) (hi : 3 ≤ i.val) : middle i=[]:=by
    change install countSlots (input bits) c i=[]
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg Fin.val h
      change j.val=i.val at hv
      omega)]
    simp only [input,if_neg (show i.val≠0 by omega)]
  obtain ⟨h,hh,h1,h14⟩:=EquationNaturalHeader.header_ready (ones bits)
  have hi:∀ i,middle (headerSlots i)=EquationNaturalHeader.input (ones bits) i:=by
    intro i
    by_cases hz:i.val=0
    · have he:i=0:=Fin.ext hz
      subst i
      change install countSlots _ c (countSlots 1)=_
      rw [install_slot _ count_injective]
      exact c1
    · rw [headerSlots,if_neg hz]
      rw [fresh _ (by simp;omega)]
      unfold EquationNaturalHeader.input
      rw [if_neg (show i≠0 by intro h;exact hz (congrArg Fin.val h))]
  have h2:=hh.focus headerSlots header_injective middle hi
  refine ⟨_,ClockJoin.join count header _ _ _ _ _ h0 h2,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i h
      have hv:=congrArg Fin.val h
      rw [header_val] at hv
      change (if i.val=0 then 1 else i.val+2)=0 at hv
      split_ifs at hv)]
    exact (install_slot _ count_injective _ _ 0).trans c0
  · exact (install_slot _ header_injective _ _ 1).trans h1
  · exact (install_slot _ header_injective _ _ 14).trans h14

theorem budget_bound (bits : List Bool) : budget bits≤200*(bits.length+1)^2:=by
  have hc:ones bits≤bits.length:=by
    rw [ones_filter]
    exact List.length_filter_le _ _
  have hsq:ones bits^2≤bits.length^2:=Nat.pow_le_pow_left hc _
  have hlog:natBitLength (ones bits)≤ones bits+1:=by
    have h:=Nat.log_le_self 2 (ones bits)
    unfold natBitLength
    omega
  unfold budget EquationNaturalHeader.budget
  nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportArity
