import Proof.Gates.CounterAsm.Copy
import Proof.Gates.CounterMachine.Interval5

set_option autoImplicit false

namespace NearCubicGates.Close.CounterAsm

/-! ## Registers -/

def Q : Fin 20 ↪ Fin 64 := Fin.castLEEmb (by decide)
@[simp] theorem Q_val (i : Fin 20) : (Q i).val = i.val := rfl

def rN : Fin 64 := ⟨20, by decide⟩   -- `n`
def rW : Fin 64 := ⟨21, by decide⟩   -- `W = n + 1`
def rK : Fin 64 := ⟨22, by decide⟩   -- `k`
def aX : Fin 64 := ⟨23, by decide⟩
def aH : Fin 64 := ⟨24, by decide⟩
def aB : Fin 64 := ⟨25, by decide⟩
def aL : Fin 64 := ⟨26, by decide⟩   -- `λ_n`
def aM : Fin 64 := ⟨27, by decide⟩   -- `μ_n`
def aA : Fin 64 := ⟨28, by decide⟩
def aA2 : Fin 64 := ⟨29, by decide⟩
def aT : Fin 64 := ⟨30, by decide⟩
def aC : Fin 64 := ⟨31, by decide⟩
def opZ : Fin 64 := ⟨32, by decide⟩
def rf : Fin 64 := ⟨33, by decide⟩
def rc : Fin 64 := ⟨34, by decide⟩
def rp : Fin 64 := ⟨35, by decide⟩
def rt : Fin 64 := ⟨36, by decide⟩
def scD : Fin 64 := ⟨37, by decide⟩
def kC : Fin 64 := ⟨38, by decide⟩
def opK : Fin 64 := ⟨39, by decide⟩
def opO : Fin 64 := ⟨40, by decide⟩
def scK : Fin 64 := ⟨41, by decide⟩
def scW : Fin 64 := ⟨42, by decide⟩
def opU : Fin 64 := ⟨43, by decide⟩

/-! ## Streams -/

section Streams
variable (tD tK tO : ℕ)

def NS : ℕ := 14 + tD + tK + tO

def OUT : Fin (NS tD tK tO + 1) := ⟨1, by unfold NS; omega⟩
def LD : Fin (NS tD tK tO + 1) := ⟨12, by unfold NS; omega⟩
def LK : Fin (NS tD tK tO + 1) := ⟨13, by unfold NS; omega⟩
def LO : Fin (NS tD tK tO + 1) := ⟨14, by unfold NS; omega⟩

def dmap (j : Fin tD) : Fin (NS tD tK tO + 1) :=
  ⟨if j.val = 0 then 0 else 14 + j.val, by have := j.isLt; unfold NS; split <;> omega⟩
def kmap (j : Fin tK) : Fin (NS tD tK tO + 1) := ⟨14 + tD + j.val, by have := j.isLt; unfold NS; omega⟩
def omap (j : Fin tO) : Fin (NS tD tK tO + 1) := ⟨14 + tD + tK + j.val, by have := j.isLt; unfold NS; omega⟩

@[simp] theorem OUT_val : (OUT tD tK tO).val = 1 := rfl
@[simp] theorem LD_val : (LD tD tK tO).val = 12 := rfl
@[simp] theorem LK_val : (LK tD tK tO).val = 13 := rfl
@[simp] theorem LO_val : (LO tD tK tO).val = 14 := rfl
theorem dmap_val (j : Fin tD) : (dmap tD tK tO j).val = if j.val = 0 then 0 else 14 + j.val := rfl
@[simp] theorem kmap_val (j : Fin tK) : (kmap tD tK tO j).val = 14 + tD + j.val := rfl
@[simp] theorem omap_val (j : Fin tO) : (omap tD tK tO j).val = 14 + tD + tK + j.val := rfl

theorem dmap_inj : Function.Injective (dmap tD tK tO) := by
  intro a b h; have := congrArg Fin.val h; rw [dmap_val, dmap_val] at this
  apply Fin.ext; split_ifs at this <;> omega
theorem kmap_inj : Function.Injective (kmap tD tK tO) := by
  intro a b h; have := congrArg Fin.val h; simp at this; exact Fin.ext this
theorem omap_inj : Function.Injective (omap tD tK tO) := by
  intro a b h; have := congrArg Fin.val h; simp at this; exact Fin.ext this

def pv : Fin 12 → ℕ := ![1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 10, 11]
theorem pv_lt (i : Fin 12) : pv i < 12 := by revert i; decide
theorem pv_inj (i j : Fin 12) (hi : i.val ≠ 4) (hj : j.val ≠ 4) (h : pv i = pv j) : i = j := by
  revert i j; decide

def P (oo : Fin tO) : Fin 12 ↪ Fin (NS tD tK tO + 1) :=
  ⟨fun i => if i.val = 4 then omap tD tK tO oo else ⟨pv i, by have := pv_lt i; unfold NS; omega⟩, by
    intro a b h
    by_cases ha : a.val = 4
    · by_cases hb : b.val = 4
      · exact Fin.ext (by omega)
      · simp only [ha, hb, if_true, if_false] at h
        have := congrArg Fin.val h; simp at this; have := pv_lt b; omega
    · by_cases hb : b.val = 4
      · simp only [ha, hb, if_true, if_false] at h
        have := congrArg Fin.val h; simp at this; have := pv_lt a; omega
      · simp only [ha, hb, if_false] at h
        exact pv_inj a b ha hb (congrArg Fin.val h)⟩

theorem P_val (oo : Fin tO) (i : Fin 12) :
    (P tD tK tO oo i).val = if i.val = 4 then 14 + tD + tK + oo.val else pv i := by
  unfold P; simp only [Function.Embedding.coeFn_mk]; split <;> simp

theorem P_four (oo : Fin tO) : P tD tK tO oo 4 = omap tD tK tO oo := by
  unfold P; simp

theorem P_zero (oo : Fin tO) : P tD tK tO oo 0 = OUT tD tK tO := by
  apply Fin.ext; rw [P_val]; simp [pv]

end Streams

/-- Distinctness of layout entries, by their values. -/
macro "lne" : tactic => `(tactic| (intro e; have := congrArg Fin.val e; simp [dmap_val, P_val, pv] at this; try omega))

end NearCubicGates.Close.CounterAsm
