import Proof.Gates.CounterMachine.TabCallDesc
import Proof.Gates.Codec.Unframe

/-! # RK, part 3: the prefix machine's input

The entry stream holds `frame (descWord ++ cellInput)` = `marks descWord ++ frame cellInput`; after the descriptor,
**`cpIn_spec`** copies `frame cellInput` to the empty stream `PIN` (the prefix machine's input tape) and puts both
heads back (`PIN` at `0`, the entry head after the descriptor). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Codec

variable {ns nr : ℕ} (cap : ℕ)

/-- Copy the framed rest of `IN` to `PIN`; rewind both. -/
def cpIn (IN PIN : Fin (ns + 1)) (OP OP2 T : Fin nr) : WM ns nr :=
  .seq (.whs IN (copyPairW IN PIN OP)) (.seq (copyR OP OP2 T) (.seq (WM.rewind IN OP)
    (.seq (emitC PIN OP2 false) (WM.rewind PIN OP2))))

theorem cpIn_spec (IN PIN : Fin (ns + 1)) (hIP : IN ≠ PIN) (OP OP2 T : Fin nr) (h12 : OP ≠ OP2) (h1T : OP ≠ T)
    (h2T : OP2 ≠ T) (pre x rest : List Bool) (σ : WState ns nr) (hst : σ.st IN = pre ++ RepairOrdinary.frame x ++ rest)
    (hsh : σ.sh IN = pre.length) (hP : σ.st PIN = []) (hPh : σ.sh PIN = 0) (h0 : σ.val OP = 0)
    (h0' : σ.val OP2 = 0) (hT : σ.val T = 0) (hc : 2 * x.length + 2 ≤ cap) :
    WExec cap (cpIn IN PIN OP OP2 T) σ (σ.sets PIN (RepairOrdinary.frame x)) (100 * x.length + 30) := by
  have e1 := copyFrame_loop cap IN PIN hIP OP rest x pre σ hst hsh (by rw [hP, hPh]; rfl) (by omega)
  set σ1 := (appendO σ PIN OP (marks x)).seth IN (pre.length + 2 * x.length) with hσ1
  have v1 : σ1.val OP = 2 * x.length := by simp [hσ1, appendO, h0, Codec.marks_length]
  have e2 := copyR_spec cap (v := OP) (d := OP2) (t := T) h12 h1T h2T σ1
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm h1T), hT])
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm h12), h0']; omega)
  rw [v1] at e2
  set σ2 := σ1.setv OP2 (σ1.val OP2 + 2 * x.length) with hσ2
  have e3 := wrewind_spec (cap := cap) IN OP (2 * x.length) σ2 (by simp [hσ2, Function.update_of_ne h12, v1])
    (by simp [hσ2, Function.update_of_ne h12, v1]; omega)
  set σ3 := (σ2.setv OP 0).seth IN (σ2.sh IN - 2 * x.length) with hσ3
  have hP3 : σ3.sh PIN = (σ3.st PIN).length := by
    simp [hσ3, hσ2, hσ1, appendO, Function.update_apply, hIP.symm, hP, hPh, Codec.marks_length]
  have v3 : σ3.val OP2 = 2 * x.length := by
    simp [hσ3, hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm h12), Function.update_of_ne h12, h0']
  have e4 := emitC_spec (cap := cap) PIN OP2 false σ3 hP3 (by rw [v3]; omega)
  rw [v3] at e4
  set σ4 := ((σ3.sets PIN (σ3.st PIN ++ [false])).seth PIN (σ3.sh PIN + 1)).setv OP2 (2 * x.length + 1) with hσ4
  have e5 := wrewind_spec (cap := cap) PIN OP2 (2 * x.length + 1) σ4 (by simp [hσ4]) (by simp [hσ4]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
  apply WState.eq
  · funext y
    by_cases hy : y = PIN
    · subst hy; simp [hσ4, hσ3, hσ2, hσ1, appendO, hIP.symm, hPh, hP, Codec.marks_length]
    · by_cases hyI : y = IN
      · subst hyI; simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hIP, hsh]
      · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyI]
  · funext y
    by_cases hy : y = PIN
    · subst hy; simp [hσ4, hσ3, hσ2, hσ1, appendO, hP, frame_eq_marks]
    · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne hy]
  · funext r
    by_cases r1 : r = OP2
    · subst r1; simp [h0']
    · by_cases r2 : r = OP
      · subst r2; simp [hσ4, hσ3, Function.update_of_ne r1, h0]
      · by_cases r3 : r = T
        · subst r3
          simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne r1, Function.update_of_ne r2, hT]
        · simp [hσ4, hσ3, hσ2, hσ1, appendO, Function.update_of_ne r1, Function.update_of_ne r2]
  · simp [hσ4, hσ3, hσ2, hσ1, appendO]

end NearCubicGates.Close.CounterMachine
