import SourceAdapters.Proximity.TrimHonestRegisters

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid halving/parity preparation for retained proof labels.
-/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicGates.Close.Cells
variable {C : Ctx}

def splitAddress : St VV MM :=
  .seq (.seq (.op (.copy halfReg addressReg)) (.op (.half halfReg)))
    (.seq (.op (.copy evenReg halfReg)) (.op (.shl evenReg)))

theorem split_address (a : DS VV MM) (value : ℕ) (hv : a.env addressReg = value)
    (hW : value < 2 ^ C.Wd) :
    Ex C splitAddress a ((a.set halfReg (value / 2)).set evenReg (2 * (value / 2))) 7 := by
  have e1 := Ex.op (OpEx.copy (C := C) halfReg addressReg a (by decide))
  rw [hv] at e1
  let b := a.set halfReg value
  have e2 := Ex.op (OpEx.half (C := C) halfReg b)
  have h2 : b.env halfReg = value := by simp [b]
  rw [h2] at e2
  let d := a.set halfReg (value / 2)
  have first : Ex C (.seq (.op (.copy halfReg addressReg)) (.op (.half halfReg))) a d 3 := by
    simpa [b, d, DS.set] using Ex.seq e1 e2
  have e3 := Ex.op (OpEx.copy (C := C) evenReg halfReg d (by decide))
  have hd : d.env halfReg = value / 2 := by simp [d]
  rw [hd] at e3
  let e := d.set evenReg (value / 2)
  have he : e.env evenReg = value / 2 := by simp [e]
  have e4 := Ex.op (OpEx.shl (C := C) evenReg e (by rw [he]; omega))
  rw [he] at e4
  simpa [splitAddress, d, e, DS.set] using Ex.seq first (Ex.seq e3 e4)

theorem address_even_iff (value : ℕ) : value = 2 * (value / 2) ↔ value % 2 = 0 := by omega

end NearCubicGates.Adapters.Proximity.TrimHonest
