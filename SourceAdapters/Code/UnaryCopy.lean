import SourceAdapters.Code.CellSending

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": retaining the logarithmic allocation prefix through
an actual ordinary decoder preprocessing stage. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.UnaryCopy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

variable {V M : ℕ}

def body (flag : Fin V) : St V M := .seq (.op (.emit true)) (.op (.rdI flag))

def script (zero flag : Fin V) : St V M := .seq (.op (.rdI flag))
  (.seq (.loop (.lt zero flag) (body flag)) (.op (.emit false)))

def state (flag : Fin V) (a : DS V M) (pos bit : ℕ) (out : List Bool) : DS V M :=
  {a.set flag bit with ip := pos, out := out}

private theorem loop_runs (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag)
    (a : DS V M) (hz : a.env zero = 0) :
    ∀ (n : ℕ) (pre tail out : List Bool), C.inp = pre ++ List.replicate n true ++ false :: tail →
      Ex C (.loop (.lt zero flag) (body flag))
        (state flag a (pre.length + 1) (decide (0 < n)).toNat out)
        (state flag a (pre.length + n + 1) 0 (out ++ List.replicate n true)) (5 * n + 2) := by
  intro n
  induction n with
  | zero =>
    intro pre tail out _
    simpa [state] using Ex.loopF (C := C) (c := Cnd.lt zero flag) (s := body flag)
      (a := state flag a (pre.length + 1) 0 out) hzf
      (by simp [Cnd.eval, state, DS.set, hzf, hz])
  | succ n ih =>
    intro pre tail out hin
    let a0 := state flag a (pre.length + 1) 1 out
    have ht : (Cnd.lt zero flag).eval a0 = true := by simp [Cnd.eval, a0, state, DS.set, hzf, hz]
    have e1 := Ex.op (OpEx.emit (C := C) true a0)
    let a1 : DS V M := {a0 with out := out ++ [true]}
    have hin' : C.inp = (pre ++ [true]) ++ List.replicate n true ++ false :: tail := by
      simpa [List.replicate_succ, List.append_assoc] using hin
    have e2 : Ex C (.op (.rdI flag)) a1 (readState flag a1 (decide (0 < n))) 1 := by
      apply read_bit C flag a1 (decide (0 < n))
      · rw [hin']; simp [a1, a0, state]
      · rw [hin', List.append_assoc]
        change ((pre ++ [true]) ++ (List.replicate n true ++ false :: tail)).getD
          (pre.length + 1) false = _
        rw [show pre.length + 1 = (pre ++ [true]).length by simp, List.getD_append_right _ _ _ _ (by omega)]
        cases n <;> simp [List.replicate_succ]
    have hnext : readState flag a1 (decide (0 < n)) =
        state flag a ((pre ++ [true]).length + 1) (decide (0 < n)).toNat (out ++ [true]) := by
      apply state_ext <;> simp [readState, a1, a0, state, DS.set]
    rw [hnext] at e2
    have ei := ih (pre ++ [true]) tail (out ++ [true]) hin'
    have he := Ex.loopT (c := Cnd.lt zero flag) hzf ht (Ex.seq e1 e2) ei
    have hfinal : state flag a ((pre ++ [true]).length + n + 1) 0 ((out ++ [true]) ++ List.replicate n true) =
        state flag a (pre.length + (n + 1) + 1) 0 (out ++ List.replicate (n + 1) true) := by
      congr 1
      · simp; omega
      · simp [List.replicate_succ, List.append_assoc]
    rw [hfinal] at he
    convert he using 1 <;> simp [body, a0]
    omega

theorem runs (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag)
    (a : DS V M) (hz : a.env zero = 0) (n : ℕ) (pre tail : List Bool)
    (hin : C.inp = pre ++ List.replicate n true ++ false :: tail) (hip : a.ip = pre.length) :
    Ex C (script zero flag) a (state flag a (pre.length + n + 1) 0
      (a.out ++ List.replicate n true ++ [false])) (5 * n + 6) := by
  have er : Ex C (.op (.rdI flag)) a (readState flag a (decide (0 < n))) 1 := by
    apply read_bit C flag a (decide (0 < n))
    · rw [hip, hin]; simp
    · rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      cases n <;> simp [List.replicate_succ]
  have heq : readState flag a (decide (0 < n)) = state flag a (pre.length + 1) (decide (0 < n)).toNat a.out := by
    simp [readState, state, hip]
  rw [heq] at er
  have el := loop_runs C zero flag hzf a hz n pre tail a.out hin
  have ee := Ex.op (OpEx.emit (C := C) false
    (state flag a (pre.length + n + 1) 0 (a.out ++ List.replicate n true)))
  exact (Ex.seq er (Ex.seq el ee)).mono (by omega)

end NearCubicGates.Adapters.Code.UnaryCopy
