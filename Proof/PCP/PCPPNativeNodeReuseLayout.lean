import Proof.PCP.PCPPNativeNodeReset

/-! Fixed reusable node workspace. A separate actual raw outer capacity F
pays the complete parser/lookup/emitter reset and erase; the retained raw
scalar capacity C continues to pay each inner address/natural append. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeReusable
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resetSlots (i : Fin 120) : Fin 122 := i.castAdd 2
def eraseSlots (i : Fin 116) : Fin 122 := ⟨i.val+6,by omega⟩
theorem erase_injective : Function.Injective eraseSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change i.val+6=j.val+6 at hv
  omega
theorem erase_away (i : Fin 116) : 6 ≤ (eraseSlots i).val := by change 6 ≤ i.val+6; omega
noncomputable def first := RecoveryFocus.machine resetSlots PCPPNativeNodeReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 114)
noncomputable def machine := Composition.machine first last
def data (source queries : List Bool) (base position C F : ℕ) (out : List Bool) (i : Fin 122) : List Bool :=
  if i=0 then source else if i=1 then queries else if i=2 then List.replicate base true
  else if i=3 then List.replicate position true else if i=4 then List.replicate C true
  else if i=5 then out else if i=120 then List.replicate F true
  else if i=121 then List.replicate (F+1) false else List.replicate F false
def heads (pos : ℕ) (out : List Bool) (i : Fin 122) := if i=0 then pos else if i=5 then out.length else 0
noncomputable def entry (source queries : List Bool) (pos base position C F : ℕ) (out : List Bool) :=
  (⟨machine.start,heads pos out,data source queries base position C F out⟩ : Configuration 122 _)

theorem pad_zeros (F n : ℕ) (hn : n ≤ F) : ZeroPadding.pad F (List.replicate n false)=List.replicate F false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hn]

theorem reset_heads (pos : ℕ) (out : List Bool) (i : Fin 119) :
    heads pos out (i.castAdd 3)=initialHeads pos out i := by
  have h0 : i.castAdd 3=0 ↔ i=0 := by
    constructor
    · intro h; apply Fin.ext; exact congrArg (fun j : Fin 122 => j.val) h
    · intro h; subst i; rfl
  have h5 : i.castAdd 3=5 ↔ i=5 := by
    constructor
    · intro h; apply Fin.ext; exact congrArg (fun j : Fin 122 => j.val) h
    · intro h; subst i; rfl
  simp only [heads,initialHeads,h0,h5]

theorem pad_empty (F : ℕ) : ZeroPadding.pad F []=List.replicate F false := by simp [ZeroPadding.pad]

theorem reset_data (source queries : List Bool) (base position C F : ℕ) (out : List Bool)
    (hCF : C+1 ≤ F) (i : Fin 119) :
    data source queries base position C F out (i.castAdd 3)=
      ZeroPadding.pad (if 6 ≤ i.val then F else 0) (initialData source queries base position C out i) := by
  have hc : C ≤ F := by omega
  fin_cases i <;> simp [data,initialData,pad_zeros F C hc,pad_zeros F (C+1) hCF,pad_empty]

theorem reset_input {n r : ℕ} (pre tail : List Bool) (base index C F : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (node : BooleanNode n) (out : List Bool) (hCF : C+1 ≤ F)
    (i : Fin 120) :
    heads pre.length out (resetSlots i)=(PCPPNativeNodeReset.entry pre tail base index C F projection node out).heads i ∧
      data (originalSource pre tail node) (rowCache projection) base (base+2*index) C F out (resetSlots i)=
        (PCPPNativeNodeReset.entry pre tail base index C F projection node out).tapes i := by
  refine Fin.addCases (m := 119) (n := 1) (fun j => ?_) (fun j => ?_) i
  · simp only [PCPPNativeNodeReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
      PCPPNativeNodeMachine.entry,boundary,controlConfig,RecoveryCalls.restarted,Fin.addCases_left,
      PCPPNativeNodeReset.caps,Fin.val_castAdd]
    change heads pre.length out (j.castAdd 3)=initialHeads pre.length out j ∧
      data (originalSource pre tail node) (rowCache projection) base (base+2*index) C F out (j.castAdd 3)=
        ZeroPadding.pad (if 6 ≤ j.val then F else 0)
          (initialData (originalSource pre tail node) (rowCache projection) base (base+2*index) C out j)
    exact ⟨reset_heads pre.length out j,reset_data _ _ base (base+2*index) C F out hCF j⟩
  · fin_cases j
    change 0=0 ∧ List.replicate F false=ZeroPadding.pad F []
    simp [ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.PCPPNativeNodeReusable
