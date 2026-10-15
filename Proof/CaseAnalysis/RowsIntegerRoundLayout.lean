import Proof.CaseAnalysis.RowsIntegerTapes
import Proof.MachineModel.OrdinaryFrameLoad
import Proof.Amplification.RecoveryScratchErase

/-! One integer round keeps the raw canonical stream and native output
outside its reusable decoder bank. The literal field count is an outer driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coreSlots (i : Fin 215) : Fin 220:=i.castAdd 5
def loadSlots : Fin 3→Fin 220:=![217,0,218]
def flagSlots : Fin 2→Fin 220:=![211,219]
def eraseSlots (i : Fin 216) : Fin 220:=
  if i.val<213 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def scratchSlots (i : Fin 214):=eraseSlots (i.castAdd 2)
theorem core_injective : Function.Injective coreSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 220=>x.val) h)
theorem erase_val (i : Fin 216) : (eraseSlots i).val=if i.val<213 then i.val else i.val+1:=by
  unfold eraseSlots
  split <;> rfl
theorem erase_injective : Function.Injective eraseSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  rw [erase_val,erase_val] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
theorem scratch_small (i : Fin 214) : (scratchSlots i).val<215:=by
  rw [scratchSlots,erase_val]
  split_ifs <;> simp_all <;> omega
theorem scratch_not_output (i : Fin 214) : scratchSlots i≠213:=by
  intro h
  have hv:=congrArg Fin.val h
  simp only [scratchSlots,erase_val,Fin.val_castAdd] at hv
  split_ifs at hv <;> omega
theorem scratch_covers (i : Fin 215) (hi : i≠213) : ∃ j : Fin 214,scratchSlots j=coreSlots i:=by
  by_cases h:i.val<213
  · refine ⟨⟨i.val,by omega⟩,Fin.ext ?_⟩
    simp only [scratchSlots,erase_val,Fin.val_castAdd,coreSlots,h,if_true]
  · have hv:i.val=214:=by
      have hn:i.val≠213:=by intro he;exact hi (Fin.ext he)
      omega
    refine ⟨213,Fin.ext ?_⟩
    change 214=i.val
    omega

def heads (out : List Bool) (pos : ℕ) (i : Fin 220):=
  if i=213 then out.length else if i=217 then pos else 0
def extra (cap : ℕ) (source : List Bool) (flag : Bool) : Fin 5→List Bool:=
  ![List.replicate cap true,
    List.replicate (cap+1) false,source,
    List.replicate cap false,[flag]]
def coreTapes (cap : ℕ) (bits out : List Bool) (i : Fin 215):=
  if i=213 then out else if i=0 then ZeroPadding.pad cap (frame bits) else List.replicate cap false
noncomputable def data (cap : ℕ) (bits out source : List Bool) (flag : Bool) : Fin 220→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (215+5)=>List Bool)
    (coreTapes cap bits out) (extra cap source flag)
noncomputable def cfg {s : ℕ} (q : Fin s) (cap pos : ℕ) (bits out source : List Bool) (flag : Bool) :
    Configuration 220 s:=⟨q,heads out pos,data cap bits out source flag⟩

theorem data_core (w : ℕ) (bits out source : List Bool) (flag : Bool) (i : Fin 215) :
    data (CloseoutRowsIntegerReady.capacity w) bits out source flag (coreSlots i)=(CloseoutRowsIntegerReady.entry w bits out).tapes i:=by
  simp only [data,coreSlots,Fin.addCases_left]
  exact (CloseoutRowsIntegerReady.entry_tapes w bits out i).symm
theorem data_extra (cap : ℕ) (bits out source : List Bool) (flag : Bool) (i : Fin 5) :
    data cap bits out source flag (i.natAdd 215)=extra cap source flag i:=by
  simp only [data,Fin.addCases_right]
theorem data_bits_other (cap : ℕ) (bits next out source : List Bool) (flag : Bool) (i : Fin 220) (hi : i≠0) :
    data cap bits out source flag i=data cap next out source flag i:=by
  revert hi
  refine Fin.addCases (m:=215) (n:=5) ?_ ?_ i
  · intro j hj
    have h0:j≠0:=by intro he;subst j;exact hj rfl
    simp only [data,Fin.addCases_left,coreTapes,if_neg h0]
  · intro j _
    simp only [data,Fin.addCases_right]
theorem heads_core (w pos : ℕ) (bits out : List Bool) (i : Fin 215) :
    heads out pos (coreSlots i)=(CloseoutRowsIntegerReady.entry w bits out).heads i:=by
  rw [CloseoutRowsIntegerReady.entry_heads]
  have h217:coreSlots i≠217:=by
    intro h
    have hv:=congrArg Fin.val h
    change i.val=217 at hv
    omega
  unfold heads
  rw [if_neg h217]
  by_cases hi:i=213
  · subst i
    rfl
  · rw [if_neg hi,if_neg (by
      intro h
      exact hi (Fin.ext (congrArg (fun i : Fin 220=>i.val) h)))]

structure Stored (cap : ℕ) (out source : List Bool) (flag : Bool) (tapes : Fin 220→List Bool) : Prop where
  scratch : ∀ i,(tapes (scratchSlots i)).length ≤ cap
  output : tapes 213=out
  extra : ∀ i,tapes (i.natAdd 215)=CloseoutRowsIntegerRound.extra cap source flag i

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
