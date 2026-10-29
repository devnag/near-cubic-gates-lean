import SourceAdapters.Code.ChunkSending

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": exact parsing of a framed source-call output. The caller
pays for every bit read and emitted, including trailing false bits. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.OutputParsing

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

variable {V M : ℕ}

def readState (flag : Fin V) (a : DS V M) (bit : Bool) : DS V M :=
  {a.set flag bit.toNat with kc := a.kc + 1}

def positioned (flag : Fin V) (a : DS V M) (pos value : ℕ) (out : List Bool) : DS V M :=
  {a.set flag value with kc := pos, out := out}

theorem read_bit (C : Ctx) (flag : Fin V) (a : DS V M) (bit : Bool)
    (hi : a.kc < a.kout.length) (hb : a.kout.getD a.kc false = bit) :
    Ex C (.op (.rdK flag)) a (readState flag a bit) 1 := by
  simpa only [readState, bitOf, hb] using Ex.op (OpEx.rdK (C := C) flag a hi)

def copyBody (zero flag : Fin V) : St V M :=
  .seq (.op (.rdK flag)) (.seq (sendReadBit zero flag false) (.op (.rdK flag)))

def copyFrame (zero flag : Fin V) : St V M :=
  .seq (.op (.rdK flag)) (.loop (.lt zero flag) (copyBody zero flag))

private theorem copy_loop (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag)
    (a : DS V M) (hz : a.env zero = 0) :
    ∀ (bits pre suffix out : List Bool), a.kout = pre ++ frame bits ++ suffix →
      Ex C (.loop (.lt zero flag) (copyBody zero flag))
        (positioned flag a (pre.length + 1) (!bits.isEmpty).toNat out)
        (positioned flag a (pre.length + 2 * bits.length + 1) 0 (out ++ bits)) (8 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix out _
    have he := Ex.loopF (C := C) (c := Cnd.lt zero flag) (s := copyBody zero flag)
      (a := positioned flag a (pre.length + 1) 0 out) hzf
      (by simp [Cnd.eval, positioned, DS.set, hzf, hz])
    simpa using he
  | cons bit bits ih =>
    intro pre suffix out hin
    let a0 := positioned flag a (pre.length + 1) 1 out
    have ht : (Cnd.lt zero flag).eval a0 = true := by simp [Cnd.eval, a0, positioned, DS.set, hzf, hz]
    have e1 : Ex C (.op (.rdK flag)) a0 (readState flag a0 bit) 1 := by
      apply read_bit C flag a0 bit
      · simp [a0, positioned, hin, frame]
      · change a.kout.getD (pre.length + 1) false = bit
        rw [hin]
        rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        simp [frame]
    let a1 := readState flag a0 bit
    have e2 := send_read_bit C zero flag hzf false a1 bit
      (by simp [a1, readState, a0, positioned, DS.set, hzf, hz])
      (by simp [a1, readState]) (by simp)
    let a2 : DS V M := {a1 with out := out ++ [bit]}
    have hin' : a.kout = (pre ++ [true, bit]) ++ frame bits ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hpos : a2.kc = (pre ++ [true, bit]).length := by simp [a2, a1, readState, a0, positioned]
    have e3 : Ex C (.op (.rdK flag)) a2 (readState flag a2 (!bits.isEmpty)) 1 := by
      apply read_bit C flag a2 (!bits.isEmpty)
      · change a2.kc < a.kout.length
        rw [hpos, hin']
        have hf := Parsing.frame_nonempty bits
        simp only [List.length_append]
        omega
      · change a.kout.getD a2.kc false = _
        rw [hpos, hin', List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        simpa using Parsing.frame_first bits suffix
    have ebody := Ex.seq e1 (Ex.seq e2 e3)
    have hnext : readState flag a2 (!bits.isEmpty) =
        positioned flag a ((pre ++ [true, bit]).length + 1) (!bits.isEmpty).toNat (out ++ [bit]) := by
      apply state_ext <;> simp [readState, a2, a1, a0, positioned, DS.set]
    rw [hnext] at ebody
    have ei := ih (pre ++ [true, bit]) suffix (out ++ [bit]) hin'
    have he := Ex.loopT (c := Cnd.lt zero flag) hzf ht ebody ei
    have hfinal : positioned flag a ((pre ++ [true, bit]).length + 2 * bits.length + 1) 0 ((out ++ [bit]) ++ bits) =
        positioned flag a (pre.length + 2 * (bit :: bits).length + 1) 0 (out ++ bit :: bits) := by
      congr 1
      · simp; omega
      · simp [List.append_assoc]
    rw [hfinal] at he
    convert he using 1 <;> simp [copyBody, a0]
    omega

theorem copy_frame (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag)
    (a : DS V M) (hz : a.env zero = 0) (bits pre suffix : List Bool)
    (hin : a.kout = pre ++ frame bits ++ suffix) (hip : a.kc = pre.length) :
    Ex C (copyFrame zero flag) a
      (positioned flag a (pre.length + 2 * bits.length + 1) 0 (a.out ++ bits)) (8 * bits.length + 4) := by
  have er : Ex C (.op (.rdK flag)) a (readState flag a (!bits.isEmpty)) 1 := by
    apply read_bit C flag a (!bits.isEmpty)
    · rw [hip, hin]
      simp only [List.length_append]
      have hf := Parsing.frame_nonempty bits
      omega
    · rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simpa using Parsing.frame_first bits suffix
  have he : readState flag a (!bits.isEmpty) =
      positioned flag a (pre.length + 1) (!bits.isEmpty).toNat a.out := by simp [readState, positioned, hip]
  rw [he] at er
  exact (Ex.seq er (copy_loop C zero flag hzf a hz bits pre suffix a.out hin)).mono (by omega)

end NearCubicGates.Adapters.Code.OutputParsing
