import SourceAdapters.Code.OutputParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": ordinary counting of exact framed source-call outputs.
This computes source block lengths by running the encoder on zero messages. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.OutputCounting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing

variable {V M : ℕ}

def readState (flag : Fin V) (a : DS V M) (bit : Bool) : DS V M :=
  {a.set flag bit.toNat with kc := a.kc + 1}

theorem read_bit (C : Ctx) (flag : Fin V) (a : DS V M) (bit : Bool)
    (hi : a.kc < a.kout.length) (hb : a.kout.getD a.kc false = bit) :
    Ex C (.op (.rdK flag)) a (readState flag a bit) 1 := by
  simpa only [readState, bitOf, hb] using Ex.op (OpEx.rdK (C := C) flag a hi)

theorem read_at_prefix (C : Ctx) (flag : Fin V) (a : DS V M) (pre : List Bool) (b : Bool)
    (tail : List Bool) (hin : a.kout = pre ++ b :: tail) (hip : a.kc = pre.length) :
    Ex C (.op (.rdK flag)) a (readState flag a b) 1 := by
  apply read_bit C flag a b
  · rw [hin, hip]; simp
  · rw [hin, hip]; simp

def countBody (flag count : Fin V) : St V M :=
  .seq (.op (.rdK flag)) (.seq (.op (.inc count)) (.op (.rdK flag)))

def countField (zero flag count : Fin V) : St V M :=
  .seq (.op (.rdK flag)) (.loop (.lt zero flag) (countBody flag count))

def counted (flag count : Fin V) (a : DS V M) (pos bit value : ℕ) : DS V M :=
  {a with kc := pos, env := fun i => if i = flag then bit else if i = count then value else a.env i}

private theorem loop_count (C : Ctx) (zero flag count : Fin V)
    (hzf : zero ≠ flag) (hzc : zero ≠ count) (hfc : flag ≠ count)
    (a : DS V M) (hz : a.env zero = 0) :
    ∀ (bits pre suffix : List Bool) (value : ℕ), a.kout = pre ++ frame bits ++ suffix →
      value + bits.length < 2 ^ C.Wd →
      Ex C (.loop (.lt zero flag) (countBody flag count))
        (counted flag count a (pre.length + 1) (!bits.isEmpty).toNat value)
        (counted flag count a (pre.length + 2 * bits.length + 1) 0 (value + bits.length))
        (7 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix value _ _
    have h := Ex.loopF (C := C) (c := Cnd.lt zero flag) (s := countBody flag count)
      (a := counted flag count a (pre.length + 1) 0 value) hzf
      (by simp [Cnd.eval, counted, hzf, hzc, hz])
    simpa using h
  | cons b bits ih =>
    intro pre suffix value hin hcap
    let a0 := counted flag count a (pre.length + 1) 1 value
    have ht : (Cnd.lt zero flag).eval a0 = true := by
      simp [Cnd.eval, a0, counted, hzf, hzc, hz]
    have hin0 : a.kout = (pre ++ [true]) ++ b :: (frame bits ++ suffix) := by
      simpa [frame, List.append_assoc] using hin
    have e1 := read_at_prefix C flag a0 (pre ++ [true]) b (frame bits ++ suffix) hin0
      (by simp [a0, counted])
    let a1 := readState flag a0 b
    have hc1 : a1.env count = value := by simp [a1, readState, a0, counted, DS.set, Ne.symm hfc]
    have e2 := Ex.op (OpEx.inc (C := C) count a1 (by rw [hc1]; simp only [List.length_cons] at hcap; omega))
    let a2 := a1.set count (value + 1)
    rw [hc1] at e2
    have hin1 : a.kout = (pre ++ [true, b]) ++ frame bits ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hip : a2.kc = (pre ++ [true, b]).length := by
      simp [a2, a1, readState, a0, counted]
    have e3 : Ex C (.op (.rdK flag)) a2 (readState flag a2 (!bits.isEmpty)) 1 := by
      apply read_bit C flag a2 (!bits.isEmpty)
      · change a2.kc < a.kout.length
        rw [hip, hin1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hp := Parsing.frame_nonempty bits
        omega
      · change a.kout.getD a2.kc false = _
        rw [hip, hin1, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        simpa using Parsing.frame_first bits suffix
    have ebody := Ex.seq e1 (Ex.seq e2 e3)
    have hnext : readState flag a2 (!bits.isEmpty) =
        counted flag count a ((pre ++ [true, b]).length + 1) (!bits.isEmpty).toNat (value + 1) := by
      apply state_ext
      · funext i
        by_cases hf : i = flag
        · subst i; simp [readState, counted, DS.set]
        · by_cases hc : i = count
          · subst i; simp [readState, a2, a1, a0, counted, DS.set, Ne.symm hfc]
          · simp [readState, a2, a1, a0, counted, DS.set, hf, hc]
      all_goals simp [readState, a2, a1, a0, counted]
    rw [hnext] at ebody
    have ei := ih (pre ++ [true, b]) suffix (value + 1) hin1 (by simp only [List.length_cons] at hcap; omega)
    have e := Ex.loopT (c := Cnd.lt zero flag) hzf ht ebody ei
    have hfinal : counted flag count a ((pre ++ [true, b]).length + 2 * bits.length + 1) 0
        (value + 1 + bits.length) =
        counted flag count a (pre.length + 2 * (b :: bits).length + 1) 0 (value + (b :: bits).length) := by
      congr 1 <;> simp <;> omega
    rw [hfinal] at e
    convert e using 1 <;> simp [countBody, a0]
    omega

theorem count_field (C : Ctx) (zero flag count : Fin V)
    (hzf : zero ≠ flag) (hzc : zero ≠ count) (hfc : flag ≠ count)
    (a : DS V M) (hz : a.env zero = 0) (bits pre suffix : List Bool)
    (hin : a.kout = pre ++ frame bits ++ suffix) (hip : a.kc = pre.length)
    (hcap : a.env count + bits.length < 2 ^ C.Wd) :
    Ex C (countField zero flag count) a
      (counted flag count a (pre.length + 2 * bits.length + 1) 0 (a.env count + bits.length))
      (7 * bits.length + 4) := by
  have er : Ex C (.op (.rdK flag)) a (readState flag a (!bits.isEmpty)) 1 := by
    apply read_bit C flag a (!bits.isEmpty)
    · rw [hip, hin]
      simp only [List.length_append]
      have hp := Parsing.frame_nonempty bits
      omega
    · rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simpa using Parsing.frame_first bits suffix
  have he : readState flag a (!bits.isEmpty) =
      counted flag count a (pre.length + 1) (!bits.isEmpty).toNat (a.env count) := by
    apply state_ext
    · funext i
      by_cases hf : i = flag
      · subst i; simp [readState, counted, DS.set]
      · by_cases hc : i = count
        · subst i; simp [readState, counted, DS.set, Ne.symm hfc]
        · simp [readState, counted, DS.set, hf, hc]
    all_goals simp [readState, counted, hip]
  rw [he] at er
  exact (Ex.seq er (loop_count C zero flag count hzf hzc hfc a hz bits pre suffix (a.env count) hin hcap)).mono
    (by omega)

end NearCubicGates.Adapters.Code.OutputCounting
