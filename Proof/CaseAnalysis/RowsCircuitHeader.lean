import Proof.Hierarchy.CompetitorWitnessTripleSemantics
import Proof.Hierarchy.CompetitorRationalProducts

/-! The normalized circuit's tagged four-field header reuses the existing
triple extractor on its physically retained tail. This fixed extra work is
polynomial in the original code width, before any row-table scan. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitHeader
open LocalBitMultitape RecoveryRootRound RadixSemantics CompetitorWitnessTriple
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots (i : Fin 122) : Fin 242:=i.castAdd 120
def lastSlots (i : Fin 122) : Fin 242:=
  if i.val=0 then 0 else if i.val=1 then 119 else ⟨i.val+120,by omega⟩
theorem first_injective : Function.Injective firstSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 242=>k.val) h)
theorem last_val (i : Fin 122) :
    (lastSlots i).val=if i.val=0 then 0 else if i.val=1 then 119 else i.val+120:=by
  unfold lastSlots
  split <;> first | rfl | (split <;> rfl)
theorem last_injective : Function.Injective lastSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [last_val,last_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

def input (bits : List Bool) : Fin 242→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (122+120)=>List Bool) (CompetitorWitnessTriple.input [] bits) (fun _=>[])
noncomputable def middle (bits : List Bool):=install firstSlots (input bits) (stage [] bits 6)
noncomputable def first:=RecoveryFocus.machine firstSlots CompetitorWitnessTriple.machine
noncomputable def last:=RecoveryFocus.machine lastSlots CompetitorWitnessTriple.machine
noncomputable def machine:=Composition.machine first last
def codeWord (bits : List Bool) (i : Fin 4):=RecoveryFixedUnpair.leftWord (word bits (2*i.val+1))
def port : Fin 4→Fin 242:=![38,78,118,158]

theorem stage_zero (x bits : List Bool) (k : ℕ) : stage x bits k 0=frame x:=by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [stage]
    split_ifs
    · rw [install_other]
      · exact ih
      · intro j hj
        have hv:=congrArg Fin.val hj
        simp only [slots] at hv
        split_ifs at hv <;> simp_all
    · exact ih

theorem middle_old (bits : List Bool) (i : Fin 122) :
    middle bits (firstSlots i)=stage [] bits 6 i:=install_slot _ first_injective _ _ _
theorem middle_new (bits : List Bool) (i : Fin 242) (hi : 122 ≤ i.val) : middle bits i=[]:=by
  rw [middle,install_other _ _ _ _ (by
    intro j he
    have hv:=congrArg Fin.val he
    change j.val=i.val at hv
    omega)]
  simp [input,Fin.addCases,show ¬i.val<122 by omega]

theorem last_input (bits : List Bool) :
    ∀ i,middle bits (lastSlots i)=CompetitorWitnessTriple.input [] (word bits 6) i:=by
  intro i
  by_cases h0:i.val=0
  · have he:i=0:=Fin.ext h0
    subst i
    exact (middle_old bits 0).trans (stage_zero [] bits 6)
  by_cases h1:i.val=1
  · have he:i=1:=Fin.ext h1
    subst i
    exact (middle_old bits 119).trans (tail_output [] bits)
  · rw [CompetitorWitnessTriple.input,if_neg h0,if_neg h1]
    apply middle_new
    rw [last_val,if_neg h0,if_neg h1]
    omega

def budget (bits : List Bool):=50001*(bits.length+1)^2
theorem header_run (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun machine (budget bits) (input bits) output ∧
      ∀ i,output (port i)=frame (codeWord bits i):=by
  obtain ⟨a,ha,ta,ah,as⟩:=triple_run [] bits
  have hf:=bounded_focus firstSlots first_injective _ _ _ ⟨a,ha,ta,ah,as⟩
    (input bits) (by intro i;simp only [input,firstSlots,Fin.addCases_left])
  obtain ⟨b,hb,bt,bh,bs⟩:=triple_run [] (word bits 6)
  have hl:=bounded_focus lastSlots last_injective _ _ _ ⟨b,hb,bt,bh,bs⟩
    (middle bits) (last_input bits)
  have h:=ClockJoin.join first last _ _ _ _ _ hf hl
  have htime:CompetitorWitnessTriple.budget bits+1+CompetitorWitnessTriple.budget (word bits 6) ≤ budget bits:=by
    unfold CompetitorWitnessTriple.budget budget
    rw [CompetitorWitnessTriple.word_length]
    have hp:1 ≤ (bits.length+1)^2:=Nat.one_le_pow _ _ (by omega)
    omega
  have more:=ClockJoin.enlarge machine _ (budget bits) _ _ h htime
  refine ⟨_,more,?_⟩
  intro i;fin_cases i
  · change install lastSlots _ _ 38=frame (codeWord bits 0)
    rw [install_other _ _ _ _ (by
      intro j he;have hv:=congrArg Fin.val he;rw [last_val] at hv;split_ifs at hv <;> omega)]
    exact (middle_old bits 38).trans (field_output [] bits 1)
  · change install lastSlots _ _ 78=frame (codeWord bits 1)
    rw [install_other _ _ _ _ (by
      intro j he;have hv:=congrArg Fin.val he;rw [last_val] at hv;split_ifs at hv <;> omega)]
    exact (middle_old bits 78).trans (field_output [] bits 3)
  · change install lastSlots _ _ 118=frame (codeWord bits 2)
    rw [install_other _ _ _ _ (by
      intro j he;have hv:=congrArg Fin.val he;rw [last_val] at hv;split_ifs at hv <;> omega)]
    exact (middle_old bits 118).trans (field_output [] bits 5)
  · change install lastSlots _ _ (lastSlots 38)=_
    rw [install_slot _ last_injective]
    exact field_output [] (word bits 6) 1

theorem code_values (a b c d : ℕ) (bits : List Bool)
    (h : value bits=CanonicalBinary.encodeTaggedList [a,b,c,d]) (i : Fin 4) :
    value (codeWord bits i)=![a,b,c,d] i:=by
  change field bits (2*i.val+1)=_
  rw [field_eq]
  fin_cases i <;> simp [nodeCode,h,CanonicalBinary.encodeTaggedList]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitHeader
