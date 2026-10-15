import Proof.CaseAnalysis.WitnessDAGVerdict
import Proof.CaseAnalysis.WitnessDAGFooter
import Proof.CaseAnalysis.WitnessDAGNodesLoop
import Proof.CaseAnalysis.WitnessInputPowerFields

/-! The whole cold oracle decoder aliases the actual input-derived capacity,
canonical node stream and literal count into the accepted node loop. Each
bank remains opaque; only selected tape identities are needed at the joins. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev tapes:=1380
def coefficient:=113000000000000000000

def powerSlots (i : Fin (InputPower.tapes 24)) : Fin tapes:=
  if i.val=0 then 0 else ⟨3+i.val,by dsimp [tapes,InputPower.tapes,DimensionPower.tapes];omega⟩
def fieldSlots (i : Fin 488) : Fin tapes:=
  if i.val=0 then 0 else if i.val=1 then 1 else ⟨64+i.val,by dsimp [tapes];omega⟩
def nodeSlots (i : Fin 805) : Fin tapes:=
  if i.val=749 then 63 else if i.val=751 then 231 else if i.val=756 then 11
  else if i.val=759 then 2 else if i.val=766 then 242 else if i.val=767 then 3
  else ⟨552+i.val,by dsimp [tapes];omega⟩
def compareSlots (i : Fin 21) : Fin tapes:=
  if h:i.val<5 then (![1220,1221,1222,1223,548] : Fin 5→Fin tapes) ⟨i.val,h⟩
  else ⟨1352+i.val,by dsimp [tapes];omega⟩
def footerSlots (i : Fin 9) : Fin tapes:=
  if i.val=0 then 548 else if i.val=1 then 415 else if i.val=8 then 1299
  else ⟨1371+i.val,by dsimp [tapes];omega⟩
def verdictSlots : Fin 6→Fin tapes:=![201,373,549,1306,1371,1379]

theorem power_val (i : Fin (InputPower.tapes 24)) :
    (powerSlots i).val=if i.val=0 then 0 else 3+i.val:=by unfold powerSlots;split_ifs <;> rfl
theorem field_val (i : Fin 488) :
    (fieldSlots i).val=if i.val=0 then 0 else if i.val=1 then 1 else 64+i.val:=by
  unfold fieldSlots;split_ifs <;> rfl
theorem node_val (i : Fin 805) : (nodeSlots i).val=
    if i.val=749 then 63 else if i.val=751 then 231 else if i.val=756 then 11
    else if i.val=759 then 2 else if i.val=766 then 242 else if i.val=767 then 3
    else 552+i.val:=by unfold nodeSlots;split_ifs <;> rfl

theorem power_injective : Function.Injective powerSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [power_val,power_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem field_injective : Function.Injective fieldSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [field_val,field_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem node_injective : Function.Injective nodeSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [node_val,node_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem compare_injective : Function.Injective compareSlots:=by decide
theorem footer_injective : Function.Injective footerSlots:=by decide
theorem verdict_injective : Function.Injective verdictSlots:=by decide

def input (x bits arityBits : List Bool) (i : Fin tapes) : List Bool:=
  if i.val=0 then frame x else if i.val=1 then frame bits
  else if i.val=2 then frame arityBits else if i.val=3 then List.replicate (value arityBits) true else []

theorem power_input_shape (x : List Bool) (i : Fin (InputPower.tapes 24)) :
    InputPower.input 24 x i=if i.val=0 then frame x else []:=by
  refine Fin.addCases (m:=10) (n:=2+DimensionPower.tapes 24) ?_ ?_ i
  · intro j
    simp only [InputPower.input,Fin.addCases_left,HierarchyAllocation.input,Fin.val_castAdd]
    rfl
  · intro j
    simp [InputPower.input]

theorem field_input_shape (x bits : List Bool) (i : Fin 488) :
    DAGFields.input x bits i=if i.val=0 then frame x else if i.val=1 then frame bits else []:=by
  refine Fin.addCases (m:=138) (n:=350) ?_ ?_ i
  · intro j
    simp only [DAGFields.input,Fin.addCases_left,PCPPNativeCanonicalGuard.input_eq,Fin.val_castAdd]
    rfl
  · intro j
    have h1:138+j.val≠1:=by omega
    simp [DAGFields.input,h1]

theorem node_input_shape (w : ℕ) (arityBits source : List Bool) (flag : Bool) (count : ℕ)
    (i : Fin 805) : DAGNodes.input w arityBits source flag count i=
      if i.val=749 then List.replicate (NodeReady.capacity w) true else if i.val=751 then source
      else if i.val=754 then [flag] else if i.val=756 then List.replicate w true
      else if i.val=759 then frame arityBits else if i.val=766 then CompareMachine.word count
      else if i.val=767 then List.replicate (value arityBits) true else []:=by
  refine Fin.addCases (m:=766) (n:=39) ?_ ?_ i
  · intro a
    refine Fin.addCases (m:=759) (n:=7) ?_ ?_ a
    · intro b
      refine Fin.addCases (m:=755) (n:=4) ?_ ?_ b
      · intro j
        have h756:j.val≠756:=by omega
        have h759:j.val≠759:=by omega
        have h766:j.val≠766:=by omega
        have h767:j.val≠767:=by omega
        simp only [DAGNodes.input,NodeColdBank.input,NodeBank.input,Fin.addCases_left,
          Fin.val_castAdd,Fin.ext_iff,h756,h759,h766,h767,if_false]
        rfl
      · intro j
        fin_cases j <;> simp [DAGNodes.input,NodeColdBank.input,NodeBank.input,Fin.addCases]
    · intro j
      fin_cases j <;> simp [DAGNodes.input,NodeColdBank.input,Fin.addCases]
  · intro j
    simp only [DAGNodes.input,Fin.addCases_right,Fin.val_natAdd]
    have h749:766+j.val≠749:=by omega
    have h751:766+j.val≠751:=by omega
    have h754:766+j.val≠754:=by omega
    have h756:766+j.val≠756:=by omega
    have h759:766+j.val≠759:=by omega
    simp only [h749,h751,h754,h756,h759,if_false,Fin.ext_iff]
    simp only [Fin.val_zero,Fin.val_one]
    by_cases h0:j.val=0
    · simp [h0]
    by_cases h1:j.val=1
    · simp [h1]
    rw [if_neg h0,if_neg h1,if_neg (show 766+j.val≠766 by omega),
      if_neg (show 766+j.val≠767 by omega)]

noncomputable def power:=RecoveryFocus.machine powerSlots (InputPower.machine 24 coefficient 1)
noncomputable def fields:=RecoveryFocus.machine fieldSlots DAGFields.machine
noncomputable def nodes:=RecoveryFocus.machine nodeSlots DAGNodes.machine
noncomputable def compare:=RecoveryFocus.machine compareSlots NodeScalar.machine
noncomputable def footer:=RecoveryFocus.machine footerSlots DAGFooter.machine
noncomputable def verdict:=RecoveryFocus.machine verdictSlots DAGVerdict.machine

end NearCubicWires.RepairOrdinary.CloseoutWitness.Oracle
