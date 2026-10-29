import SourceAdapters.Proximity.SourceResults

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact sequential reading of one raw local literal
from the finite block compiler, retaining all source-row data and channels. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.ReadLiteral

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open SourceRequests (State Script)
open SourceResults (readRegs resultReg powerReg tagReg)
open FrameReading

def scratch : List (Fin VV) := [t0, resultReg, powerReg, tagReg]
def readLiteral : Script := readTaggedNatural true readRegs tagReg

structure Parsed (a b : State) (cursor : ℕ) (positive : Bool) (index : ℕ) : Prop where
  value_eq : b.env resultReg = index
  sign_eq : b.env tagReg = positive.toNat
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out
  ram_eq : b.ram = a.ram
  rc_eq : b.rc = a.rc
  kin_eq : b.kin = a.kin
  kout_eq : b.kout = a.kout
  cursor_eq : b.kc = cursor
  vars : Fr a b scratch

theorem Parsed.constants {a b : State} {cursor index : ℕ} {positive : Bool}
    (h : Parsed a b cursor positive index) (hc : Cst a) : Cst b := Cst.of_fr hc h.vars (by decide)

theorem read_literal (C : Ctx) (a : State) (hc : Cst a) (pre tail : List Bool) (positive : Bool) (index : ℕ)
    (hin : a.kout = pre ++ positive :: (frame index.bits ++ tail)) (hip : a.kc = pre.length)
    (hwidth : index.bits.length + 1 ≤ C.Wd) :
    Hs C readLiteral a (10 * index.bits.length + 12)
      (fun b => Parsed a b (pre.length + 2 * index.bits.length + 2) positive index) := by
  have e := read_tagged_natural C true readRegs tagReg (by decide) a positive index pre tail hc.z hin hip hwidth
  refine ⟨_, _, e, le_rfl, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
  · simp [finish, position, readRegs, resultReg, powerReg]
  · change (((((a.set tagReg positive.toNat).set t0 0).set resultReg index).set
      powerReg (2 ^ index.bits.length))).env tagReg = positive.toNat
    rw [DS.set_env_ne _ _ (by decide : tagReg ≠ powerReg),
      DS.set_env_ne _ _ (by decide : tagReg ≠ resultReg),
      DS.set_env_ne _ _ (by decide : tagReg ≠ t0), DS.set_env_self]
  · intro x hx
    have h0 : x ≠ t0 := fun h => hx (by simp [scratch, h])
    have hr : x ≠ resultReg := fun h => hx (by simp [scratch, h])
    have hp : x ≠ powerReg := fun h => hx (by simp [scratch, h])
    have ht : x ≠ tagReg := fun h => hx (by simp [scratch, h])
    simp [finish, position, readState, readRegs, DS.set, h0, hr, hp, ht]

end NearCubicGates.Adapters.Proximity.ReadLiteral
