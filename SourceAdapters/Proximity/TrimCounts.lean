import SourceAdapters.Proximity.TrimSizes
import Proof.Gates.CounterMachine.CellTablesCst2

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid counts for the explicit three-query table.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg

variable {C : Ctx}

def arityReg : Fin VV := 40
def randomReg : Fin VV := 41
def rowsReg : Fin VV := 42
def fieldsReg : Fin VV := 43
def countLoop : Fin VV := 44

def nineProgram : St VV MM :=
  .seq (.op (.copy fieldsReg rowsReg))
    (.seq (.op (.shl fieldsReg))
      (.seq (.op (.shl fieldsReg))
        (.seq (.op (.shl fieldsReg)) (.op (.add fieldsReg rowsReg)))))

theorem nine_program (a : DS VV MM) (r : ℕ) (hr : a.env rowsReg = r)
    (hW : 9 * r < 2 ^ C.Wd) :
    Ex C nineProgram a (a.set fieldsReg (9 * r)) 9 := by
  have e1 := Ex.op (OpEx.copy (C := C) fieldsReg rowsReg a (by decide))
  rw [hr] at e1
  let b := a.set fieldsReg r
  have e2 := Ex.op (OpEx.shl (C := C) fieldsReg b (by simp only [b, DS.set_env_self]; omega))
  simp only [b, DS.set_env_self] at e2
  let c := b.set fieldsReg (2 * r)
  have e3 := Ex.op (OpEx.shl (C := C) fieldsReg c (by simp only [c, DS.set_env_self]; omega))
  simp only [c, DS.set_env_self] at e3
  let d := c.set fieldsReg (2 * (2 * r))
  have e4 := Ex.op (OpEx.shl (C := C) fieldsReg d (by simp only [d, DS.set_env_self]; omega))
  simp only [d, DS.set_env_self] at e4
  let e := d.set fieldsReg (2 * (2 * (2 * r)))
  have er : e.env rowsReg = r := by
    simpa [e, d, c, b, DS.set, fieldsReg, rowsReg] using hr
  have ef : e.env fieldsReg = 2 * (2 * (2 * r)) := by simp [e]
  have e5 := Ex.op (OpEx.add (C := C) fieldsReg rowsReg e (by decide) (by rw [er, ef]; omega))
  rw [er, ef] at e5
  have hx := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5)))
  have hfinal : e.set fieldsReg (2 * (2 * (2 * r)) + r) = a.set fieldsReg (9 * r) := by
    have hnum : 2 * (2 * (2 * r)) + r = 9 * r := by omega
    simp [e, d, c, b, DS.set, hnum]
  rw [hfinal] at hx
  exact hx

def countProgram : St VV MM :=
  .seq (pow2P rowsReg countLoop randomReg) nineProgram

def countTemps : List (Fin VV) := [rowsReg, countLoop, fieldsReg]

theorem count_program (a : DS VV MM) (hc : Cst a) (r : ℕ)
    (hr : a.env randomReg = r) (hR : r < C.Wd) (hW : 9 * 2 ^ r < 2 ^ C.Wd) :
    Hs C countProgram a (5 * r + 16) (fun b =>
      b.env rowsReg = 2 ^ r ∧ b.env fieldsReg = 9 * 2 ^ r ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b countTemps) := by
  refine Hs.mono (Hs.seq (t2 := 9)
    (pow2P_spec C rowsReg countLoop randomReg (by decide) (by decide) (by decide)
      (by decide) a hc r hr hR) (fun b hb => ?_)) (by omega) (fun _ h => h)
  obtain ⟨hrows, hsh, hfr⟩ := hb
  have hx := nine_program b (2 ^ r) hrows hW
  refine ⟨b.set fieldsReg (9 * 2 ^ r), 9, hx, le_rfl, ?_⟩
  have hf : Fr a (b.set fieldsReg (9 * 2 ^ r)) countTemps :=
    Fr.trans (hfr.weaken (by simp [countTemps])) (Fr.set b _ (by simp [countTemps]))
  refine ⟨?_, by simp, by simpa using hsh, Cst.of_fr hc hf (by decide), hf⟩
  rw [DS.set_env_ne _ _ (by decide)]
  exact hrows

end NearCubicGates.Adapters.Proximity.Trim
