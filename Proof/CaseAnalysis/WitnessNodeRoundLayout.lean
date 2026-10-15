import Proof.CaseAnalysis.WitnessNodeStorage
import Proof.MachineModel.OrdinaryFrameLoad
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.Amplification.RecoveryScratchErase

/-! One node round shares its load target, local workspace, arity/index
bounds, and two live stream cursors. Only local scratch is erased. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loadSlots : Fin 3 → Fin 755:=![751,1,752]
def nodeSlots (i : Fin 749) : Fin 755:=i.castAdd 6
def flagSlots : Fin 2 → Fin 755:=![745,754]
def incrementSlots : Fin 2 → Fin 755:=![671,753]
def eraseSlots (i : Fin 746) : Fin 755:=
  if i.val<668 then ⟨i.val,by omega⟩
  else if i.val<743 then ⟨i.val+4,by omega⟩ else ⟨i.val+5,by omega⟩
def scratchSlots (i : Fin 744):=eraseSlots (i.castAdd 2)

theorem erase_val (i : Fin 746) : (eraseSlots i).val=
    if i.val<668 then i.val else if i.val<743 then i.val+4 else i.val+5:=by
  unfold eraseSlots
  split_ifs <;> rfl
theorem erase_injective : Function.Injective eraseSlots:=by
  intro a b h
  have hv:=congrArg Fin.val h
  rw [erase_val,erase_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem scratch_small (i : Fin 744) : (scratchSlots i).val<749:=by
  simp only [scratchSlots,erase_val,Fin.val_castAdd]
  split_ifs <;> omega
theorem scratch_not_output (i : Fin 744) : scratchSlots i≠747:=by
  intro h
  have hv:=congrArg Fin.val h
  simp only [scratchSlots,erase_val,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega
theorem scratch_not_common (i : Fin 744) (j : Fin 4) :
    scratchSlots i≠(NodeGuard.common j).castAdd 9:=by
  intro h
  have hv:=congrArg Fin.val h
  simp only [scratchSlots,erase_val,Fin.val_castAdd,NodeGuard.common] at hv
  split_ifs at hv <;> omega

theorem scratch_covers (i : Fin 749) (hi : i≠747)
    (hc : ∀ j : Fin 4,(NodeGuard.common j).castAdd 3≠i) :
    ∃ j : Fin 744,scratchSlots j=nodeSlots i:=by
  by_cases hlow:i.val<668
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp only [scratchSlots,erase_val,Fin.val_castAdd,nodeSlots,hlow,if_true]
  by_cases hcommon:i.val<672
  · have h:=hc ⟨i.val-668,by omega⟩
    exact False.elim (h (Fin.ext (by simp only [NodeGuard.common,Fin.val_castAdd];omega)))
  by_cases hmid:i.val<747
  · refine ⟨⟨i.val-4,by omega⟩,?_⟩
    apply Fin.ext
    simp only [scratchSlots,erase_val,Fin.val_castAdd,nodeSlots,
      show ¬i.val-4<668 by omega,if_false,show i.val-4<743 by omega,if_true]
    omega
  · have he:i.val=748:=by
      have hne:i.val≠747:=by intro h;exact hi (Fin.ext h)
      omega
    refine ⟨743,Fin.ext ?_⟩
    simpa only [nodeSlots,Fin.val_castAdd,he] using (show (scratchSlots 743).val=748 by decide)

def heads (out : List Bool) (position : ℕ) (i : Fin 755) : ℕ:=
  if i=747 then out.length else if i=751 then position else 0
def extra (cap : ℕ) (source : List Bool) (flag : Bool) : Fin 6 → List Bool:=
  ![List.replicate cap true,List.replicate (cap+1) false,source,
    List.replicate cap false,List.replicate cap false,[flag]]
noncomputable def data (cap w : ℕ) (left right bits out source : List Bool) (flag : Bool) : Fin 755 → List Bool:=
  Fin.addCases (motive:=fun _ : Fin (749+6)=>List Bool)
    (NodeReady.entry cap w left right bits out).tapes (extra cap source flag)
noncomputable def cfg {s : ℕ} (q : Fin s) (cap w position : ℕ)
    (left right bits out source : List Bool) (flag : Bool) : Configuration 755 s:=
  ⟨q,heads out position,data cap w left right bits out source flag⟩

theorem data_node (cap w : ℕ) (left right bits out source : List Bool) (flag : Bool) (i : Fin 749) :
    data cap w left right bits out source flag (nodeSlots i)=(NodeReady.entry cap w left right bits out).tapes i:=by
  simp only [data,nodeSlots,Fin.addCases_left]
theorem data_extra (cap w : ℕ) (left right bits out source : List Bool) (flag : Bool) (i : Fin 6) :
    data cap w left right bits out source flag (i.natAdd 749)=extra cap source flag i:=by
  simp only [data,Fin.addCases_right]
theorem data_bits_other (cap w : ℕ) (left right bits nextBits out source : List Bool) (flag : Bool)
    (i : Fin 755) (hi : i≠1) :
    data cap w left right bits out source flag i=data cap w left right nextBits out source flag i:=by
  revert hi
  refine Fin.addCases (m:=749) (n:=6) ?_ ?_ i
  · intro j hj
    simp only [data,Fin.addCases_left]
    exact NodeReady.entry_bits_other _ _ _ _ _ _ _ j (by intro h;subst j;exact hj rfl)
  · intro j _
    simp only [data,Fin.addCases_right]
theorem heads_node (cap w position : ℕ) (left right bits out : List Bool) (i : Fin 749) :
    heads out position (nodeSlots i)=(NodeReady.entry cap w left right bits out).heads i:=by
  rw [NodeReady.entry_heads]
  have hn:nodeSlots i≠751:=by
    intro h
    have hv:=congrArg Fin.val h
    change i.val=751 at hv
    omega
  unfold heads
  rw [if_neg hn]
  by_cases hi:i=747
  · subst i
    rfl
  · rw [if_neg hi,if_neg (by
      intro h
      apply hi
      exact Fin.ext (congrArg (fun i : Fin 755=>i.val) h))]

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeRound
