import Proof.Gates.Cells.Mac
import Mathlib.Data.Nat.Pairing

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": actual natural pairing for auxiliary
proof addresses, implemented by a fixed number of paid arithmetic operations. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Pairing

open NearCubicGates.Close.Cells
variable {V M : ℕ}

private theorem Rne (R : Fin 4 ↪ Fin V) {i j : Fin 4} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

def pairProgram (R : Fin 4 ↪ Fin V) : St V M :=
  .ite (.lt (R 0) (R 1))
    (.seq (.op (.copy (R 2) (R 1)))
      (.seq (.op (.mul (R 1) (R 2) (R 3))) (.op (.add (R 3) (R 0)))))
    (.seq (.op (.copy (R 2) (R 0)))
      (.seq (.op (.mul (R 0) (R 2) (R 3)))
        (.seq (.op (.add (R 3) (R 0))) (.op (.add (R 3) (R 1))))))

theorem pair_program (C : Ctx) (R : Fin 4 ↪ Fin V) (a : DS V M) (x y : ℕ)
    (hx : a.env (R 0) = x) (hy : a.env (R 1) = y) (hW : Nat.pair x y < 2 ^ C.Wd) :
    Ex C (pairProgram R) a ((a.set (R 2) (max x y)).set (R 3) (Nat.pair x y)) 8 := by
  by_cases hxy : x < y
  · have hpair : Nat.pair x y = y * y + x := by simp [Nat.pair, hxy]
    have e1 := Ex.op (OpEx.copy (C := C) (R 2) (R 1) a (Rne R (by decide)))
    rw [hy] at e1
    let b := a.set (R 2) y
    have hb1 : b.env (R 1) = y := by simp [b, DS.set, hy]
    have hb2 : b.env (R 2) = y := by simp [b]
    have e2 := Ex.op (OpEx.mul (C := C) (R 1) (R 2) (R 3) b
      (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (by rw [hb1, hb2]; omega))
    rw [hb1, hb2] at e2
    let d := b.set (R 3) (y * y)
    have hd3 : d.env (R 3) = y * y := by simp [d]
    have hd0 : d.env (R 0) = x := by simp [d, b, DS.set, hx]
    have e3 := Ex.op (OpEx.add (C := C) (R 3) (R 0) d (Rne R (by decide)) (by rw [hd3, hd0, ← hpair]; exact hW))
    rw [hd3, hd0] at e3
    have e : Ex C (pairProgram R) a (d.set (R 3) (y * y + x)) 6 :=
      Ex.iteT (c := Cnd.lt (R 0) (R 1)) (Rne R (by decide))
      (by simp [Cnd.eval, hx, hy, hxy]) (Ex.seq e1 (Ex.seq e2 e3))
    have hf : d.set (R 3) (y * y + x) = (a.set (R 2) (max x y)).set (R 3) (Nat.pair x y) := by
      simp [d, b, DS.set, hpair, max_eq_right hxy.le]
    rw [hf] at e
    exact e.mono (by decide)
  · have hyx : y ≤ x := Nat.le_of_not_gt hxy
    have hpair : Nat.pair x y = x * x + x + y := by simp [Nat.pair, hxy]
    have e1 := Ex.op (OpEx.copy (C := C) (R 2) (R 0) a (Rne R (by decide)))
    rw [hx] at e1
    let b := a.set (R 2) x
    have hb0 : b.env (R 0) = x := by simp [b, DS.set, hx]
    have hb2 : b.env (R 2) = x := by simp [b]
    have e2 := Ex.op (OpEx.mul (C := C) (R 0) (R 2) (R 3) b
      (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (by rw [hb0, hb2]; omega))
    rw [hb0, hb2] at e2
    let d := b.set (R 3) (x * x)
    have hd3 : d.env (R 3) = x * x := by simp [d]
    have hd0 : d.env (R 0) = x := by simp [d, b, DS.set, hx]
    have e3 := Ex.op (OpEx.add (C := C) (R 3) (R 0) d (Rne R (by decide)) (by rw [hd3, hd0]; omega))
    rw [hd3, hd0] at e3
    let f := d.set (R 3) (x * x + x)
    have hf3 : f.env (R 3) = x * x + x := by simp [f]
    have hf1 : f.env (R 1) = y := by simp [f, d, b, DS.set, hy]
    have e4 := Ex.op (OpEx.add (C := C) (R 3) (R 1) f (Rne R (by decide)) (by rw [hf3, hf1, ← hpair]; exact hW))
    rw [hf3, hf1] at e4
    have e : Ex C (pairProgram R) a (f.set (R 3) (x * x + x + y)) 8 :=
      Ex.iteF (c := Cnd.lt (R 0) (R 1)) (Rne R (by decide))
      (by simp [Cnd.eval, hx, hy, hxy]) (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4)))
    have hf : f.set (R 3) (x * x + x + y) = (a.set (R 2) (max x y)).set (R 3) (Nat.pair x y) := by
      simp [f, d, b, DS.set, hpair, max_eq_left hyx]
    rw [hf] at e
    exact e

end NearCubicGates.Adapters.Proximity.Pairing
