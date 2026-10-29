import SourceAdapters.Proximity.HeaderRewind
import SourceAdapters.Proximity.SourceResults

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": retain the source arity and restore the exact
source-word input position before any source request is constructed. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceResults (readRegs resultReg powerReg)
open FrameReading

def scratch : List (Fin VV) := [t0, resultReg, powerReg, arityReg, aw0, rewindReg]

def readArity : Script := .seq (readBinary false readRegs)
  (.seq (.op (.copy arityReg resultReg)) rewindField)

theorem read_arity (C : Ctx) (a : State) (hc : Cst a) (n : ℕ) (pre tail : List Bool)
    (hin : C.inp = pre ++ frame n.bits ++ tail) (hip : a.ip = pre.length)
    (hW : n.bits.length + 1 ≤ C.Wd) (hrew : 2 * n.bits.length + 1 < 2 ^ C.Wd) :
    Hs C readArity a (25 * n.bits.length + 33)
      (fun b => b.env arityReg = n ∧ Same a b ∧ Fr a b scratch) := by
  have e1 := read_natural C false readRegs a n pre tail hc.z hin hip hW
  let b := finish false readRegs a (pre.length + 2 * n.bits.length + 1) n (2 ^ n.bits.length)
  have hb : b.env resultReg = n := by simp [b, finish, readRegs, resultReg, powerReg]
  have hbfr : Fr a b [t0, resultReg, powerReg] := by
    intro x hx
    have h0 : x ≠ t0 := fun h => hx (by simp [h])
    have hr : x ≠ resultReg := fun h => hx (by simp [h])
    have hp : x ≠ powerReg := fun h => hx (by simp [h])
    simp [b, finish, position, readRegs, DS.set, h0, hr, hp]
  have hbC := Cst.of_fr hc hbfr (by decide)
  have e2 := Ex.op (OpEx.copy (C := C) arityReg resultReg b (by decide))
  rw [hb] at e2
  let d := b.set arityReg n
  have hdC : Cst d := Cst.of_fr hbC (Fr.set b n (T := [arityReg]) (by simp)) (by decide)
  have e3 := rewind_field C d hdC n pre.length (by simp [d]) rfl hrew
  obtain ⟨f, cost, he3, hcost, hfip, hfo, hfm, hfrc, hfki, hfko, hfkc, hffr⟩ := e3
  refine ⟨f, (10 * n.bits.length + 10) + (1 + cost + 1) + 1,
    Ex.seq e1 (Ex.seq e2 he3), by omega, ?_, ?_, ?_⟩
  · rw [hffr arityReg (by decide)]
    simp [d]
  · exact ⟨hfip.trans hip.symm, hfo, hfm, hfrc, hfki, hfko, hfkc⟩
  · exact (hbfr.weaken (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [scratch])).trans
      ((Fr.set b n (by simp [scratch])).trans (hffr.weaken (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp [scratch])))

end NearCubicGates.Adapters.Proximity.SourceHeader
