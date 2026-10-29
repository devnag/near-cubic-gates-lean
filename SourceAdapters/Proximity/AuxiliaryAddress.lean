import SourceAdapters.Proximity.Pairing

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": charged computation of odd auxiliary
proof addresses. The source row and localIndex literal index remain retained. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Pairing

open NearCubicGates.Close.Cells
variable {V M : ℕ}

private theorem Rne (R : Fin 6 ↪ Fin V) {i j : Fin 6} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

def auxiliaryPairRegs (R : Fin 6 ↪ Fin V) : Fin 4 ↪ Fin V :=
  (⟨![0, 3, 4, 5], by decide⟩ : Fin 4 ↪ Fin 6).trans R

def auxiliaryProgram (R : Fin 6 ↪ Fin V) : St V M :=
  .seq (.op (.copy (R 3) (R 1))) (.seq (.op (.sub (R 3) (R 2)))
    (.seq (pairProgram (auxiliaryPairRegs R)) (.seq (.op (.shl (R 5))) (.op (.inc (R 5))))))

theorem auxiliary_program (C : Ctx) (R : Fin 6 ↪ Fin V) (a : DS V M) (row localIndex q : ℕ)
    (hr : a.env (R 0) = row) (hi : a.env (R 1) = localIndex) (hq : a.env (R 2) = q) (hle : q ≤ localIndex)
    (hW : 2 * Nat.pair row (localIndex - q) + 1 < 2 ^ C.Wd) :
    Ex C (auxiliaryProgram R) a
      (((a.set (R 3) (localIndex - q)).set (R 4) (max row (localIndex - q))).set (R 5)
        (2 * Nat.pair row (localIndex - q) + 1)) 16 := by
  have e1 := Ex.op (OpEx.copy (C := C) (R 3) (R 1) a (Rne R (by decide)))
  rw [hi] at e1
  let b := a.set (R 3) localIndex
  have hb3 : b.env (R 3) = localIndex := by simp [b]
  have hb2 : b.env (R 2) = q := by simp [b, DS.set, hq]
  have e2 := Ex.op (OpEx.sub (C := C) (R 3) (R 2) b (Rne R (by decide)) (by rw [hb3, hb2]; exact hle))
  rw [hb3, hb2] at e2
  let d := b.set (R 3) (localIndex - q)
  have e3 := pair_program C (auxiliaryPairRegs R) d row (localIndex - q)
    (by simp [auxiliaryPairRegs, d, b, DS.set, hr]) (by simp [auxiliaryPairRegs, d]) (by omega)
  let f := (d.set (R 4) (max row (localIndex - q))).set (R 5) (Nat.pair row (localIndex - q))
  change Ex C (pairProgram (auxiliaryPairRegs R)) d f 8 at e3
  have hf5 : f.env (R 5) = Nat.pair row (localIndex - q) := by simp [f]
  have e4 := Ex.op (OpEx.shl (C := C) (R 5) f (by rw [hf5]; omega))
  rw [hf5] at e4
  let g := f.set (R 5) (2 * Nat.pair row (localIndex - q))
  have hg5 : g.env (R 5) = 2 * Nat.pair row (localIndex - q) := by simp [g]
  have e5 := Ex.op (OpEx.inc (C := C) (R 5) g (by rw [hg5]; exact hW))
  rw [hg5] at e5
  have hfinal : g.set (R 5) (2 * Nat.pair row (localIndex - q) + 1) =
      (((a.set (R 3) (localIndex - q)).set (R 4) (max row (localIndex - q))).set (R 5)
        (2 * Nat.pair row (localIndex - q) + 1)) := by simp [g, f, d, b, DS.set]
  rw [hfinal] at e5
  exact Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5)))

end NearCubicGates.Adapters.Proximity.Pairing
