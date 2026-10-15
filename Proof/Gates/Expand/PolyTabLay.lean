import Proof.Gates.Expand.PolyTabFit
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

abbrev NSx (te qa : ℕ) : ℕ := 235 + te + qa
abbrev NRk : ℕ := 186

section Lay
variable {te qa : ℕ}

def sI : Fin (NSx te qa + 1) := ⟨0, by unfold NSx; omega⟩
def sZ : Fin 64 ↪ Fin (NSx te qa + 1) :=
  ⟨fun i => ⟨1 + i.val, by unfold NSx; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩
def sS : Fin 40 ↪ Fin (NSx te qa + 1) :=
  ⟨fun i => ⟨65 + i.val, by unfold NSx; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩
def sL : Fin (NSx te qa + 1) := ⟨105, by unfold NSx; omega⟩
def sT : Fin te ↪ Fin (NSx te qa + 1) :=
  ⟨fun i => ⟨106 + i.val, by unfold NSx; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩
def sP : Fin 130 ↪ Fin (NSx te qa + 1) :=
  ⟨fun i => ⟨106 + te + i.val, by unfold NSx; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩
def qv (te j : ℕ) : ℕ := if j = 0 then 106 + te + 128 else 106 + te + 129 + j
def sQ : Fin qa ↪ Fin (NSx te qa + 1) :=
  ⟨fun j => ⟨qv te j.val, by unfold qv NSx; split_ifs <;> omega⟩, fun a b e => Fin.ext (by
    have := congrArg Fin.val e; simp only at this; unfold qv at this; split_ifs at this <;> omega)⟩
def sOUT : Fin (NSx te qa + 1) := ⟨NSx te qa, by unfold NSx; omega⟩

@[simp] theorem sI_val : (sI (te := te) (qa := qa)).val = 0 := rfl
@[simp] theorem sZ_val (i : Fin 64) : (sZ (te := te) (qa := qa) i).val = 1 + i.val := rfl
@[simp] theorem sS_val (i : Fin 40) : (sS (te := te) (qa := qa) i).val = 65 + i.val := rfl
@[simp] theorem sL_val : (sL (te := te) (qa := qa)).val = 105 := rfl
@[simp] theorem sT_val (i : Fin te) : (sT (qa := qa) i).val = 106 + i.val := rfl
@[simp] theorem sP_val (i : Fin 130) : (sP (te := te) (qa := qa) i).val = 106 + te + i.val := rfl
@[simp] theorem sQ_val (j : Fin qa) : (sQ (te := te) j).val = qv te j.val := rfl
@[simp] theorem sOUT_val : (sOUT (te := te) (qa := qa)).val = 235 + te + qa := rfl

theorem sQ_zero (j : Fin qa) (hj : j.val = 0) : sQ (te := te) j = sP 128 := by
  apply Fin.ext; simp [qv, hj]

end Lay

def rY : Fin 112 ↪ Fin NRk :=
  ⟨fun i => ⟨i.val, by unfold NRk; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩
def rX : Fin 64 ↪ Fin NRk :=
  ⟨fun i => ⟨112 + i.val, by unfold NRk; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩
def rB : Fin 10 ↪ Fin NRk :=
  ⟨fun i => ⟨176 + i.val, by unfold NRk; omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩

@[simp] theorem rY_val (i : Fin 112) : (rY i).val = i.val := rfl
@[simp] theorem rX_val (i : Fin 64) : (rX i).val = 112 + i.val := rfl
@[simp] theorem rB_val (i : Fin 10) : (rB i).val = 176 + i.val := rfl

theorem sne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Distinctness of layout slots. -/
macro "polyTabNe" : tactic =>
  `(tactic| (simp only [ne_eq, Fin.ext_iff, sI_val, sZ_val, sS_val, sL_val, sT_val, sP_val, sQ_val, sOUT_val, rY_val,
    rX_val, rB_val, NSx, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or, qv,
    List.nodup_cons, List.nodup_nil, and_true, true_and, not_false_eq_true, Fin.isValue] <;>
    (try simp only [Fin.val_zero, Fin.val_one, Fin.val_two]) <;> (try split_ifs) <;> omega))

end NearCubicGates.Close.Expand.PolyTab

namespace NearCubicGates.Close.Expand.PolyTab
example {te qa : ℕ} : (sZ (te := te) (qa := qa) 3) ≠ sS 4 := by polyTabNe
example {te qa : ℕ} (j : Fin qa) : sQ (te := te) j ≠ sOUT := by have := j.isLt; polyTabNe
example : rX 3 ≠ rY 5 := by polyTabNe
example : [rX 3, rY 5, rB 2].Nodup := by polyTabNe
end NearCubicGates.Close.Expand.PolyTab
