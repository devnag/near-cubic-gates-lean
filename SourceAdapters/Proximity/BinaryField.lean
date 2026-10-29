import SourceAdapters.Proximity.BinaryReading
import Proof.PCP.ProjectionDimensionCanonical

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": initialized framed-binary field reader and its exact
source-natural specialization. Both channels use the same paid instructions. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.FrameReading

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CountedParsing (state_ext)
open RadixSemantics (value)
variable {V M : ℕ}

def readBinary (call : Bool) (R : Fin 4 ↪ Fin V) : St V M :=
  .seq (.op (.zero (R 2))) (.seq (.op (.zero (R 3))) (.seq (.op (.inc (R 3)))
    (.seq (.op (readOp call (R 1))) (binaryLoop call R))))

theorem read_binary (C : Ctx) (call : Bool) (R : Fin 4 ↪ Fin V)
    (a : DS V M) (bits pre tail : List Bool) (hz : a.env (R 0) = 0)
    (hin : word C call a = pre ++ frame bits ++ tail) (hip : pos call a = pre.length)
    (hv : value bits < 2 ^ C.Wd) (hp : 2 ^ bits.length < 2 ^ C.Wd) :
    Ex C (readBinary call R) a
      (finish call R a (pre.length + 2 * bits.length + 1) (value bits) (2 ^ bits.length))
      (10 * bits.length + 10) := by
  have hcap : 1 < 2 ^ C.Wd := (Nat.one_le_pow bits.length 2 (by decide)).trans_lt hp
  let a1 := a.set (R 2) 0
  let a2 := a1.set (R 3) 0
  let a3 := a2.set (R 3) 1
  have e1 := Ex.op (OpEx.zero (C := C) (R 2) a)
  have e2 := Ex.op (OpEx.zero (C := C) (R 3) a1)
  have e3 : Ex C (.op (.inc (R 3))) a2 a3 1 := by
    simpa [a3, a2] using Ex.op (OpEx.inc (C := C) (R 3) a2 (by simpa only [a2, DS.set_env_self, Nat.zero_add] using hcap))
  have e4 := read_frame_flag C call (R 1) a3 pre bits tail
    (by simpa [a3, a2, a1] using hin) (by simpa [a3, a2, a1] using hip)
  let b := readState call (R 1) a3 (!bits.isEmpty)
  have eb := binary_loop C call R bits pre tail b 0 1
    (by simpa [b, readState, a3, a2, a1] using hin)
    (by simp [b, readState, a3, a2, a1, hip])
    (by simp [b, readState, a3, a2, a1, DS.set, hz])
    (by simp [b, readState])
    (by simp [b, readState, a3, a2, a1, DS.set])
    (by simp [b, readState, a3, DS.set])
    (by simpa using hv) (by simpa using hp)
  have hfinal : finish call R b (pre.length + 2 * bits.length + 1)
      (0 + 1 * value bits) (1 * 2 ^ bits.length) =
    finish call R a (pre.length + 2 * bits.length + 1) (value bits) (2 ^ bits.length) := by
    cases call <;> apply state_ext
    all_goals simp [finish, b, readState, a3, a2, a1, position, pos, DS.set]
    all_goals
      funext i
      simp only [Function.update_apply]
      split_ifs <;> rfl
  rw [hfinal] at eb
  convert Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 eb))) using 1 <;> first | rfl | omega

/-- The source's zero natural is the empty payload; no extra padded bit is assumed. -/
theorem read_natural (C : Ctx) (call : Bool) (R : Fin 4 ↪ Fin V)
    (a : DS V M) (n : ℕ) (pre tail : List Bool) (hz : a.env (R 0) = 0)
    (hin : word C call a = pre ++ frame n.bits ++ tail) (hip : pos call a = pre.length)
    (hW : n.bits.length + 1 ≤ C.Wd) :
    Ex C (readBinary call R) a
      (finish call R a (pre.length + 2 * n.bits.length + 1) n (2 ^ n.bits.length))
      (10 * n.bits.length + 10) := by
  have hp : 2 ^ n.bits.length < 2 ^ C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
  have hn : n < 2 ^ n.bits.length := by simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n
  have hv : n < 2 ^ C.Wd := hn.trans hp
  simpa only [NearCubicWires.RepairSource.ProjectionNormalization.DimensionProducer.bits_value] using
    read_binary C call R a n.bits pre tail hz hin hip (by simpa only [NearCubicWires.RepairSource.ProjectionNormalization.DimensionProducer.bits_value] using hv) hp

end NearCubicGates.Adapters.Proximity.FrameReading
