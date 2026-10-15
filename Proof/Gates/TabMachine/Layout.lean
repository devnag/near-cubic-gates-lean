import Proof.Gates.TabMachine.Restrict2

/-! # The cut machine's layout

One stream embedding `Z : Fin 64 ↪ _` and one register embedding `Y : Fin 112 ↪ _`; every component machine
(compiler `S R`, explode `E G`, tuple step `P Q`, stacking `U V`, restriction `A B`) gets its slots by a fixed
injective index map. Shared slots (the compiler's output is explode's input, explode's output is the tuple step's
input, the tuple stream is the stacking machine's input, the restriction's target is the compiler's target, the child
count, the tuple count) are the same index. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine

variable {ns nr : ℕ}

section Layout
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

def ixS : Fin 24 ↪ Fin 64 := Fin.castLEEmb (by norm_num)
def ixE : Fin 8 ↪ Fin 64 := ⟨![2, 24, 25, 26, 27, 28, 29, 30], by decide⟩
def ixP : Fin 4 ↪ Fin 64 := ⟨![30, 31, 32, 33], by decide⟩
def ixU : Fin 14 ↪ Fin 64 := ⟨![31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45], by decide⟩
def ixA : Fin 10 ↪ Fin 64 := ⟨![46, 47, 48, 49, 50, 51, 52, 11, 53, 54], by decide⟩

def ixR : Fin 24 ↪ Fin 112 := Fin.castLEEmb (by norm_num)
def ixG : Fin 11 ↪ Fin 112 := ⟨![24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34], by decide⟩
def ixQ : Fin 17 ↪ Fin 112 := ⟨![35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 34, 46, 47, 48, 49, 50], by decide⟩
def ixV : Fin 25 ↪ Fin 112 :=
  ⟨![51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 47, 72, 73, 74], by decide⟩
def ixB : Fin 12 ↪ Fin 112 := ⟨![75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86], by decide⟩

def zS : Fin 24 ↪ Fin (ns + 1) := (ixS).trans Z
def zE : Fin 8 ↪ Fin (ns + 1) := (ixE).trans Z
def zP : Fin 4 ↪ Fin (ns + 1) := (ixP).trans Z
def zU : Fin 14 ↪ Fin (ns + 1) := (ixU).trans Z
def zA : Fin 10 ↪ Fin (ns + 1) := (ixA).trans Z
def yR : Fin 24 ↪ Fin nr := (ixR).trans Y
def yG : Fin 11 ↪ Fin nr := (ixG).trans Y
def yQ : Fin 17 ↪ Fin nr := (ixQ).trans Y
def yV : Fin 25 ↪ Fin nr := (ixV).trans Y
def yB : Fin 12 ↪ Fin nr := (ixB).trans Y

/-! Shared slots. -/
theorem zE0 : zE Z 0 = zS Z 2 := rfl
theorem zP0 : zP Z 0 = zE Z 7 := rfl
theorem zU0 : zU Z 0 = zP Z 1 := rfl
theorem zU1 : zU Z 1 = zP Z 3 := rfl
theorem zA7 : zA Z 7 = zS Z 11 := rfl
theorem yQ11 : yQ Y 11 = yG Y 10 := rfl
theorem yV21 : yV Y 21 = yQ Y 13 := rfl

/-! Every slot as `Z i` / `Y i` (for distinctness by `decide`). -/
@[simp] theorem zS_apply (k : Fin 24) : zS Z k = Z (ixS k) := rfl
@[simp] theorem zE_apply (k : Fin 8) : zE Z k = Z (ixE k) := rfl
@[simp] theorem zP_apply (k : Fin 4) : zP Z k = Z (ixP k) := rfl
@[simp] theorem zU_apply (k : Fin 14) : zU Z k = Z (ixU k) := rfl
@[simp] theorem zA_apply (k : Fin 10) : zA Z k = Z (ixA k) := rfl
@[simp] theorem yR_apply (k : Fin 24) : yR Y k = Y (ixR k) := rfl
@[simp] theorem yG_apply (k : Fin 11) : yG Y k = Y (ixG k) := rfl
@[simp] theorem yQ_apply (k : Fin 17) : yQ Y k = Y (ixQ k) := rfl
@[simp] theorem yV_apply (k : Fin 25) : yV Y k = Y (ixV k) := rfl
@[simp] theorem yB_apply (k : Fin 12) : yB Y k = Y (ixB k) := rfl

example : zS Z 2 ≠ zU Z 2 := by simp [emb_eq_iff]; decide

end Layout

end NearCubicGates.Close.TabMachine
