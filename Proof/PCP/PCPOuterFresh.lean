import Proof.PCP.PCPOuterFocused

namespace NearCubicWires.RepairOrdinary.PCPOuterDock
open LocalBitMultitape PCPOuter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {u : ℕ} (source : Fin 4 → Fin u) (i : Fin 133) : Fin (u+129) :=
  Fin.addCases (m:=4) (n:=129) (motive:=fun _ => Fin (u+129))
    (fun j => (source j).castAdd 129) (fun j => j.natAdd u) i

theorem slots_old {u : ℕ} (source : Fin 4 → Fin u) (i : Fin 4) :
    slots source (i.castAdd 129)=(source i).castAdd 129 := by
  simp only [slots,Fin.addCases_left]
theorem slots_new {u : ℕ} (source : Fin 4 → Fin u) (i : Fin 129) :
    slots source (i.natAdd 4)=i.natAdd u := by
  simp only [slots,Fin.addCases_right]

theorem slots_injective {u : ℕ} (source : Fin 4 → Fin u) (hinj : Function.Injective source) :
    Function.Injective (slots source) := by
  intro i j h
  revert h
  refine Fin.addCases (m:=4) (n:=129) (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m:=4) (n:=129) (fun b => ?_) (fun b => ?_) j
  · intro he
    rw [slots_old,slots_old] at he
    have hv := congrArg Fin.val he
    have hab : source a=source b := Fin.ext hv
    rw [hinj hab]
  · intro he
    rw [slots_old,slots_new] at he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro he
    rw [slots_new,slots_old] at he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · intro he
    rw [slots_new,slots_new] at he
    have hab : a=b := by apply Fin.ext; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd] at hv; omega
    rw [hab]

def data (a b c d : List Bool) : Fin 4 → List Bool := ![a,b,c,d]
theorem input_old (a b c d sa sb sc sd : List Bool) (j : Fin 4) :
    PCPOuter.input a b c d sa sb sc sd (j.castAdd 129)=
      frame (data a b c d j)++data sa sb sc sd j := by
  fin_cases j <;> rfl

theorem input_empty (a b c d sa sb sc sd : List Bool) (i : Fin 133) (hi : 4 ≤ i.val) :
    PCPOuter.input a b c d sa sb sc sd i=[] := by
  revert hi
  refine Fin.addCases (m:=132) (n:=1) (fun j => ?_) (fun j => ?_) i
  · intro hj
    simp only [PCPOuter.input,Fin.addCases_left,PCPOuter.sources]
    split_ifs <;> first | rfl | (subst j; norm_num at hj)
  · intro _
    simp only [PCPOuter.input,Fin.addCases_right]

theorem fresh_input {u s : ℕ} (source : Fin 4 → Fin u)
    (a b c d sa sb sc sd : List Bool) (x : Configuration u s)
    (hh : ∀ j,x.heads (source j)=0)
    (ht : ∀ j,x.tapes (source j)=frame (data a b c d j)++data sa sb sc sd j) :
    (∀ j,(TapeEmbedding.config (fun _ : Fin 129 => 0) (fun _ : Fin 129 => []) x).heads
      (slots source j)=0) ∧
    (∀ j,(TapeEmbedding.config (fun _ : Fin 129 => 0) (fun _ : Fin 129 => []) x).tapes
      (slots source j)=PCPOuter.input a b c d sa sb sc sd j) := by
  constructor
  · intro j
    refine Fin.addCases (m:=4) (n:=129) (fun i => ?_) (fun i => ?_) j
    · simpa only [slots_old,TapeEmbedding.config,Fin.addCases_left] using hh i
    · simp only [slots_new,TapeEmbedding.config,Fin.addCases_right]
  · intro j
    refine Fin.addCases (m:=4) (n:=129) (fun i => ?_) (fun i => ?_) j
    · simpa only [slots_old,TapeEmbedding.config,Fin.addCases_left,input_old] using ht i
    · simp only [slots_new,TapeEmbedding.config,Fin.addCases_right]
      exact (input_empty a b c d sa sb sc sd (i.natAdd 4) (by simp)).symm

theorem old_unselected {u : ℕ} (source : Fin 4 → Fin u) (i : Fin u)
    (hi : ∀ j,source j≠i) : ∀ j,slots source j≠i.castAdd 129 := by
  intro j
  refine Fin.addCases (m:=4) (n:=129) (fun k => ?_) (fun k => ?_) j
  · intro he
    rw [slots_old] at he
    have hv := congrArg Fin.val he
    exact hi k (Fin.ext hv)
  · intro he
    rw [slots_new] at he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

end NearCubicWires.RepairOrdinary.PCPOuterDock
