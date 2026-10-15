import Proof.CaseAnalysis.WitnessDAGHeader

/-! The same traversal stream and count are retained across cold bank
allocation and native-header production. Only the descriptor cursor enters
the node loop live; all local node work and its bounds start at head zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGNodes
open LocalBitMultitape RecoveryRootRound RadixSemantics SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankSlots (i : Fin 766) : Fin 805:=i.castAdd 39
def coreSlots (i : Fin 755) : Fin 805:=i.castAdd 50
def headerSlots (i : Fin 37) : Fin 805:=
  if i=0 then 767 else if i=1 then 766 else if i=20 then 747 else ⟨768+i.val,by omega⟩
def loopSlots (i : Fin 756) : Fin 805:=
  if i.val<755 then ⟨i.val,by omega⟩ else 766
theorem bank_injective : Function.Injective bankSlots:=by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 805=>i.val) h)
theorem header_injective : Function.Injective headerSlots:=by decide
theorem loop_injective : Function.Injective loopSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  unfold loopSlots at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega
theorem header_core (i : Fin 755) (hi : i≠747) : ∀ j,headerSlots j≠coreSlots i:=by
  intro j h
  have hv:=congrArg Fin.val h
  have hi':i.val≠747:=by intro e;exact hi (Fin.ext e)
  unfold headerSlots at hv
  split_ifs at hv <;> dsimp [coreSlots] at hv <;> omega

def input (w : ℕ) (arityBits source : List Bool) (flag : Bool) (count : ℕ) : Fin 805→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (766+39)=>List Bool)
    (NodeColdBank.input (NodeReady.capacity w) w arityBits source flag)
    (fun i : Fin 39=>if i=0 then CompareMachine.word count
      else if i=1 then List.replicate (value arityBits) true else [])
noncomputable def bank:=RecoveryFocus.machine bankSlots NodeColdBank.machine
noncomputable def header:=RecoveryFocus.machine headerSlots DAGHeader.machine
noncomputable def prefixMachine:=Composition.machine bank header
def prefixBudget (w : ℕ) (arityBits : List Bool) (count : ℕ):=
  10*NodeReady.capacity w+8*w+43+1+DAGHeader.budget (value arityBits) count
def nativeHeader (arityBits : List Bool) (count : ℕ):=
  RepairRepresentation.natWord (value arityBits)++RepairRepresentation.natWord count

theorem capacity_fields (w : ℕ) (arityBits : List Bool) (hw : 1≤w) :
    1≤NodeReady.capacity w ∧
      ∀ j,(NodeGuard.shared w (binary w (value arityBits)) (binary w 0) j).length≤NodeReady.capacity w:=by
  have hp:w≤w^24:=Nat.le_self_pow (by decide) _
  have hpos:1≤w^24:=Nat.one_le_pow _ _ hw
  refine ⟨by unfold NodeReady.capacity;omega,?_⟩
  intro j
  fin_cases j <;> simp [NodeGuard.shared,NodeReady.capacity]
  all_goals omega

theorem bank_fresh (w : ℕ) (arityBits source : List Bool) (flag : Bool) (count : ℕ)
    (out : Fin 766→List Bool) (i : Fin 805) (hi : 766 ≤ i.val) :
    install bankSlots (input w arityBits source flag count) out i=input w arityBits source flag count i:=by
  apply install_other
  intro j h
  have hv:=congrArg Fin.val h
  simp only [bankSlots,Fin.val_castAdd] at hv
  omega

theorem header_input (w : ℕ) (arityBits source : List Bool) (flag : Bool) (count : ℕ)
    (out : Fin 766→List Bool)
    (hout : ∀ i,out (NodeColdBank.loopSlots i)=
      NodeRound.data (NodeReady.capacity w) w (binary w (value arityBits)) (binary w 0) [] [] source flag i) :
    ∀ i,install bankSlots (input w arityBits source flag count) out (headerSlots i)=
      DAGHeader.input (value arityBits) count i:=by
  intro i
  by_cases h0:i=0
  · subst i
    rw [bank_fresh _ _ _ _ _ _ _ (by decide)]
    rfl
  by_cases h1:i=1
  · subst i
    rw [bank_fresh _ _ _ _ _ _ _ (by decide)]
    rfl
  by_cases h20:i=20
  · subst i
    change install bankSlots _ out (bankSlots (NodeColdBank.loopSlots 747))=_
    rw [install_slot _ bank_injective,hout]
    change (NodeReady.entry (NodeReady.capacity w) w _ _ [] []).tapes 747=[]
    exact NodeReady.entry_output _ _ _ _ _ _
  have hv:(headerSlots i).val=768+i.val:=by simp [headerSlots,h0,h1,h20]
  rw [bank_fresh _ _ _ _ _ _ _ (by omega)]
  have he:headerSlots i=(⟨i.val+2,by omega⟩ : Fin 39).natAdd 766:=by
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega
  rw [he]
  simp only [input,Fin.addCases_right]
  simp [DAGHeader.input,h0,h1,Fin.ext_iff]

theorem data_output (cap w : ℕ) (left right bits out source : List Bool) (flag : Bool) :
    NodeRound.data cap w left right bits out source flag 747=out:=
  NodeReady.entry_output cap w left right bits out

theorem data_output_other (cap w : ℕ) (left right bits out out' source : List Bool) (flag : Bool)
    (i : Fin 755) (hi : i≠747) :
    NodeRound.data cap w left right bits out source flag i=
      NodeRound.data cap w left right bits out' source flag i:=by
  revert hi
  refine Fin.addCases (m:=749) (n:=6) ?_ ?_ i
  · intro j hj
    simp only [NodeRound.data,Fin.addCases_left]
    revert hj
    refine Fin.addCases (m:=748) (n:=1) ?_ ?_ j
    · intro k hk
      rw [NodeReady.entry_old,NodeReady.entry_old]
      apply congrArg
      revert hk
      refine Fin.addCases (m:=746) (n:=2) ?_ ?_ k
      · intro a _
        simp only [NodeBody.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left]
      · intro a ha
        fin_cases a
        · rfl
        · exact False.elim (ha rfl)
    · intro k _
      have hk:k=0:=Fin.eq_zero k
      subst k
      exact (NodeReady.entry_clock cap w left right bits out).trans
        (NodeReady.entry_clock cap w left right bits out').symm
  · intro j _
    simp only [NodeRound.data,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGNodes
