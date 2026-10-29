import SourceAdapters.Proximity.TrimRenderFrame

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact paid arithmetic for dense indices and signed literals.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.Trim
open NearCubicGates.Close.Cells
variable {C : Ctx}

def addRank : St VV MM := .seq (.op (.copy codeReg rankReg)) (.op (.add codeReg arityReg))

theorem add_rank (a : DS VV MM) (n r : ℕ) (hn : a.env arityReg = n) (hr : a.env rankReg = r)
    (hW : n + r < 2 ^ C.Wd) : Ex C addRank a (a.set codeReg (n + r)) 3 := by
  have e1 := Ex.op (OpEx.copy (C := C) codeReg rankReg a (by decide))
  rw [hr] at e1
  let b := a.set codeReg r
  have hbn : b.env arityReg = n := by vsimp [b, hn]
  have hbr : b.env codeReg = r := by simp [b]
  have e2 := Ex.op (OpEx.add (C := C) codeReg arityReg b (by decide) (by rw [hbn, hbr]; omega))
  rw [hbn, hbr] at e2
  have he := Ex.seq e1 e2
  simpa [addRank, b, DS.set, Nat.add_comm] using he

def signCode : St VV MM := .seq (.op (.shl codeReg)) (.op (.add codeReg signReg))

theorem sign_code (a : DS VV MM) (v s : ℕ) (hv : a.env codeReg = v) (hs : a.env signReg = s)
    (hW : 2 * v + s < 2 ^ C.Wd) : Ex C signCode a (a.set codeReg (2 * v + s)) 3 := by
  have e1 := Ex.op (OpEx.shl (C := C) codeReg a (by rw [hv]; omega))
  rw [hv] at e1
  let b := a.set codeReg (2 * v)
  have hbs : b.env signReg = s := by vsimp [b, hs]
  have hbv : b.env codeReg = 2 * v := by simp [b]
  have e2 := Ex.op (OpEx.add (C := C) codeReg signReg b (by decide) (by rw [hbs, hbv]; exact hW))
  rw [hbs, hbv] at e2
  have he := Ex.seq e1 e2
  simpa [signCode, b, DS.set] using he

end NearCubicGates.Adapters.Proximity.Trim
