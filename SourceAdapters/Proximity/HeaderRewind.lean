import SourceAdapters.Proximity.RequestWriting
import Proof.Gates.Cells.Arith

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": restore the source-input cursor after reading its
arity. The exact frame length is computed by the actual halving counter,
then every backward input move is paid. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CountedParsing
abbrev State := DS VV MM
abbrev Script := St VV MM

def arityReg : Fin VV := 39
def rewindReg : Fin VV := 41

def rewindField : Script := .seq (sizeP arityReg rewindReg)
  (.seq (.op (.shl rewindReg)) (.seq (.op (.inc rewindReg)) (rewindCount vZ v1 rewindReg)))

theorem rewind_field (C : Ctx) (a : State) (hc : Cst a) (n base : ℕ)
    (hn : a.env arityReg = n) (hip : a.ip = base + 2 * n.bits.length + 1)
    (hW : 2 * n.bits.length + 1 < 2 ^ C.Wd) :
    Hs C rewindField a (15 * n.bits.length + 20) (fun b =>
      b.ip = base ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [aw0, rewindReg]) := by
  have hs : Nat.size (a.env arityReg) = n.bits.length := by rw [hn, Nat.size_eq_bits_len]
  have e1 := sizeP_spec (C := C) arityReg rewindReg (by decide) (by decide) (by decide) a hc
    (by rw [hs]; omega)
  rw [hs] at e1
  obtain ⟨b, cost, he1, hcost, hb, hsh, hf⟩ := e1
  have hsame := Same.of_sh hsh
  have hbC : Cst b := Cst.of_fr hc hf (by decide)
  have e2 := Ex.op (OpEx.shl (C := C) rewindReg b (by rw [hb]; omega))
  rw [hb] at e2
  let d := b.set rewindReg (2 * n.bits.length)
  have e3 := Ex.op (OpEx.inc (C := C) rewindReg d (by simpa only [d, DS.set_env_self] using hW))
  let f := d.set rewindReg (2 * n.bits.length + 1)
  change Ex C (.op (.inc rewindReg)) d f 1 at e3
  have e4 := rewind_count C vZ v1 rewindReg (by decide) (by decide) f
    (by simp only [f, d, DS.set_env_ne _ _ (by decide : vZ ≠ rewindReg)]; exact hbC.z)
    (by simp only [f, d, DS.set_env_ne _ _ (by decide : v1 ≠ rewindReg)]; exact hbC.one)
    base (2 * n.bits.length + 1)
  have hstart : rewindState rewindReg f (base + (2 * n.bits.length + 1)) (2 * n.bits.length + 1) = f := by
    apply state_ext
    · simp [rewindState, f, d, DS.set]
    · change base + (2 * n.bits.length + 1) = b.ip
      rw [hsame.ip, hip]
      omega
    all_goals rfl
  rw [hstart] at e4
  refine ⟨_, cost + (1 + (1 + (5 * (2 * n.bits.length + 1) + 2) + 1) + 1) + 1,
    Ex.seq he1 (Ex.seq e2 (Ex.seq e3 e4)), by omega, ?_⟩
  refine ⟨rfl, hsame.out, hsame.ram, hsame.rc, hsame.kin, hsame.kout, hsame.kc, ?_⟩
  intro x hx
  have hxw : x ≠ rewindReg := fun h => hx (by simp [h])
  simp only [rewindState, f, d, DS.set_env_ne _ _ hxw]
  exact hf x hx

end NearCubicGates.Adapters.Proximity.SourceHeader
