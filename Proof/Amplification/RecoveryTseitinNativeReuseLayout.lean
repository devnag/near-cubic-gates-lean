import Proof.Amplification.RecoveryTseitinNativeMasked

/-! Fixed physical scratch and erase ports for repeated original nodes. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratch (j : Fin 1332) : Fin 1336 :=
  if j.val<1060 then ⟨j.val+2,by omega⟩ else
  if j.val<1330 then ⟨j.val+3,by omega⟩ else ⟨j.val+4,by have hj:=j.isLt; omega⟩
def eraseSlots : Fin 1334→Fin 1338 :=
  Fin.addCases (m:=1332) (n:=2) (motive:=fun _=>Fin 1338) (fun j=>(scratch j).castAdd 2) ![1336,1337]
def heads (pos cursor : Nat) (i : Fin 1338) : Nat := if i=1062 then pos else if i=1333 then cursor else 0
def data (n index : Nat) (word out : List Bool) (cap : Nat) (i : Fin 1338) : List Bool :=
  if i=0 then List.replicate n true else if i=1 then List.replicate index true else
  if i=1062 then word else if i=1333 then out else
  if i=1336 then List.replicate cap true else if i=1337 then List.replicate (cap+1) false else
  List.replicate cap false
noncomputable def prefixMachine := TapeEmbedding.machine 2 maskedMachine
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1332)
noncomputable def machine := Composition.machine prefixMachine eraseMachine

theorem scratch_range (j : Fin 1332) : (scratch j).val≠0 ∧ (scratch j).val≠1 ∧
    (scratch j).val≠1062 ∧ (scratch j).val≠1333 := by
  dsimp only [scratch]
  split_ifs <;> dsimp <;> omega
theorem scratch_injective : Function.Injective scratch := by
  intro i j he
  have h:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [scratch] at h
  split_ifs at h <;> dsimp at h <;> omega
theorem erase_injective : Function.Injective eraseSlots := by
  intro i j
  refine Fin.addCases (m:=1332) (n:=2) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=1332) (n:=2) (fun b=>?_) (fun b=>?_) j
    · intro he
      simp only [eraseSlots,Fin.addCases_left] at he
      have hv:=congrArg Fin.val he
      have he':scratch a=scratch b:=Fin.ext hv
      exact congrArg (Fin.castAdd 2) (scratch_injective he')
    · intro he
      have hv:=congrArg Fin.val he
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at hv
      have ha:=(scratch a).isLt
      fin_cases b <;> dsimp at hv <;> omega
  · refine Fin.addCases (m:=1332) (n:=2) (fun b=>?_) (fun b=>?_) j
    · intro he
      have hv:=congrArg Fin.val he
      simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right] at hv
      have hb:=(scratch b).isLt
      fin_cases a <;> dsimp at hv <;> omega
    · intro he
      simp only [eraseSlots,Fin.addCases_right] at he
      have hab : a=b := (by decide : Function.Injective (![1336,1337] : Fin 2→Fin 1338)) he
      exact congrArg (Fin.natAdd 1332) hab

theorem old_input (n index : Nat) (word out : List Bool) (cap : Nat) (i : Fin 1336) :
    maskedInput n index word out cap i=data n index word out cap (i.castAdd 2) := by
  refine Fin.addCases (m:=1335) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [maskedInput,Fin.addCases_left]
    by_cases hj : work j
    · rw [caps,if_pos hj,input_blank n index word out j hj]
      have h0 : j.val≠0:=fun h=>hj.1 (Fin.ext h)
      have h1 : j.val≠1:=fun h=>hj.2.1 (Fin.ext h)
      have hsrc : j.val≠1062:=fun h=>hj.2.2.1 (Fin.ext h)
      have hout : j.val≠1333:=fun h=>hj.2.2.2 (Fin.ext h)
      have hi:=j.isLt
      simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append,data]
      repeat rw [if_neg (by intro he; have hv:=congrArg Fin.val he; dsimp at hv; omega)]
    · have h : j=0 ∨ j=1 ∨ j=1062 ∨ j=1333 := by
        simpa only [work,not_and_or,not_not] using hj
      rw [caps,if_neg hj,ZeroPadding.pad_zero]
      rcases h with rfl|rfl|rfl|rfl <;> rfl
  · fin_cases j; rfl
theorem old_head (pre out : List Bool) (i : Fin 1336) :
    maskedHeads pre out i=heads pre.length out.length (i.castAdd 2) := by
  refine Fin.addCases (m:=1335) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [maskedHeads,Fin.addCases_left]
    by_cases hs : j=1062
    · subst j; rfl
    by_cases ho : j=1333
    · subst j; rfl
    rw [head_zero pre out j hs ho]
    simp only [heads]
    rw [if_neg (by intro he; have hv:=congrArg Fin.val he; exact hs (Fin.ext hv)),
      if_neg (by intro he; have hv:=congrArg Fin.val he; exact ho (Fin.ext hv))]
  · fin_cases j; rfl

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
