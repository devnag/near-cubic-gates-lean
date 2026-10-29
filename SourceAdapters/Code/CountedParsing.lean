import SourceAdapters.Code.Preparation
import Proof.Gates.Cells.Hs

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid counting and interval parsing for the ordinary code algorithms. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CountedParsing

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells

variable {V M : ℕ}

theorem state_ext {a b : DS V M} (he : a.env = b.env) (hi : a.ip = b.ip)
    (ho : a.out = b.out) (hr : a.ram = b.ram) (hc : a.rc = b.rc)
    (hki : a.kin = b.kin) (hko : a.kout = b.kout) (hkc : a.kc = b.kc) : a = b := by
  cases a; cases b; cases he; cases hi; cases ho; cases hr; cases hc; cases hki; cases hko; cases hkc
  rfl

def readState (flag : Fin V) (a : DS V M) (bit : Bool) : DS V M :=
  {a.set flag bit.toNat with ip := a.ip + 1}

theorem read_bit (C : Ctx) (flag : Fin V) (a : DS V M) (bit : Bool)
    (hi : a.ip < C.inp.length) (hb : C.inp.getD a.ip false = bit) :
    Ex C (.op (.rdI flag)) a (readState flag a bit) 1 := by
  simpa only [readState, bitOf, hb] using Ex.op (OpEx.rdI (C := C) flag a hi)

theorem read_at_prefix (C : Ctx) (flag : Fin V) (a : DS V M) (pre : List Bool) (b : Bool)
    (tail : List Bool) (hin : C.inp = pre ++ b :: tail) (hip : a.ip = pre.length) :
    Ex C (.op (.rdI flag)) a (readState flag a b) 1 := by
  apply read_bit C flag a b
  · rw [hin, hip]; simp
  · rw [hin, hip]; simp

def countBody (flag count : Fin V) : St V M :=
  .seq (.op (.rdI flag)) (.seq (.op (.inc count)) (.op (.rdI flag)))

def countField (zero flag count : Fin V) : St V M :=
  .seq (.op (.rdI flag)) (.loop (.lt zero flag) (countBody flag count))

def counted (flag count : Fin V) (a : DS V M) (pos bit value : ℕ) : DS V M :=
  {a with ip := pos, env := fun i => if i = flag then bit else if i = count then value else a.env i}

private theorem loop_count (C : Ctx) (zero flag count : Fin V)
    (hzf : zero ≠ flag) (hzc : zero ≠ count) (hfc : flag ≠ count)
    (a : DS V M) (hz : a.env zero = 0) :
    ∀ (bits pre suffix : List Bool) (value : ℕ), C.inp = pre ++ frame bits ++ suffix →
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
    have hin0 : C.inp = (pre ++ [true]) ++ b :: (frame bits ++ suffix) := by
      simpa [frame, List.append_assoc] using hin
    have e1 := read_at_prefix C flag a0 (pre ++ [true]) b (frame bits ++ suffix) hin0
      (by simp [a0, counted])
    let a1 := readState flag a0 b
    have hc1 : a1.env count = value := by simp [a1, readState, a0, counted, DS.set, Ne.symm hfc]
    have e2 := Ex.op (OpEx.inc (C := C) count a1 (by rw [hc1]; simp only [List.length_cons] at hcap; omega))
    let a2 := a1.set count (value + 1)
    rw [hc1] at e2
    have hin1 : C.inp = (pre ++ [true, b]) ++ frame bits ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hip : a2.ip = (pre ++ [true, b]).length := by
      simp [a2, a1, readState, a0, counted]
    have e3 : Ex C (.op (.rdI flag)) a2 (readState flag a2 (!bits.isEmpty)) 1 := by
      apply read_bit C flag a2 (!bits.isEmpty)
      · rw [hip, hin1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hp := Parsing.frame_nonempty bits
        omega
      · rw [hip, hin1, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
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
    (hin : C.inp = pre ++ frame bits ++ suffix) (hip : a.ip = pre.length)
    (hcap : a.env count + bits.length < 2 ^ C.Wd) :
    Ex C (countField zero flag count) a
      (counted flag count a (pre.length + 2 * bits.length + 1) 0 (a.env count + bits.length))
      (7 * bits.length + 4) := by
  have er : Ex C (.op (.rdI flag)) a (readState flag a (!bits.isEmpty)) 1 := by
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

def flagged (flag : Fin V) (a : DS V M) (pos bit : ℕ) : DS V M :=
  {a.set flag bit with ip := pos}

def skipUnary (zero flag : Fin V) : St V M :=
  .seq (.op (.rdI flag)) (.loop (.lt zero flag) (.op (.rdI flag)))

private theorem loop_unary (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag)
    (a : DS V M) (hz : a.env zero = 0) :
    ∀ (n : ℕ) (pre tail : List Bool), C.inp = pre ++ List.replicate n true ++ false :: tail →
      Ex C (.loop (.lt zero flag) (.op (.rdI flag)))
        (flagged flag a (pre.length + 1) (decide (0 < n)).toNat)
        (flagged flag a (pre.length + n + 1) 0) (3 * n + 2) := by
  intro n
  induction n with
  | zero =>
    intro pre tail _
    have e := Ex.loopF (C := C) (c := Cnd.lt zero flag) (s := .op (.rdI flag))
      (a := flagged flag a (pre.length + 1) 0) hzf
      (by simp [Cnd.eval, flagged, DS.set, hzf, hz])
    simpa using e
  | succ n ih =>
    intro pre tail hin
    let a0 := flagged flag a (pre.length + 1) 1
    have hin' : C.inp = (pre ++ [true]) ++ List.replicate n true ++ false :: tail := by
      simpa [List.replicate_succ, List.append_assoc] using hin
    have er : Ex C (.op (.rdI flag)) a0 (readState flag a0 (decide (0 < n))) 1 := by
      apply read_bit C flag a0 (decide (0 < n))
      · rw [hin']; simp [a0, flagged]
      · rw [hin', List.append_assoc]
        change ((pre ++ [true]) ++ (List.replicate n true ++ false :: tail)).getD
          (pre.length + 1) false = _
        rw [show pre.length + 1 = (pre ++ [true]).length by simp, List.getD_append_right _ _ _ _ (by omega)]
        cases n <;> simp [List.replicate_succ]
    have hs : readState flag a0 (decide (0 < n)) =
        flagged flag a ((pre ++ [true]).length + 1) (decide (0 < n)).toNat := by
      apply state_ext <;> simp [readState, a0, flagged, DS.set]
    rw [hs] at er
    have ei := ih (pre ++ [true]) tail hin'
    have he := Ex.loopT (c := Cnd.lt zero flag) hzf
      (show (Cnd.lt zero flag).eval a0 = true by simp [Cnd.eval, a0, flagged, DS.set, hzf, hz]) er ei
    convert he using 1 <;> simp [a0]
    · congr 1; omega
    · omega

theorem skip_unary (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag)
    (a : DS V M) (hz : a.env zero = 0) (n : ℕ) (pre tail : List Bool)
    (hin : C.inp = pre ++ List.replicate n true ++ false :: tail) (hip : a.ip = pre.length) :
    Ex C (skipUnary zero flag) a (flagged flag a (pre.length + n + 1) 0) (3 * n + 4) := by
  have er : Ex C (.op (.rdI flag)) a (readState flag a (decide (0 < n))) 1 := by
    apply read_bit C flag a (decide (0 < n))
    · rw [hip, hin]; simp
    · rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      cases n <;> simp [List.replicate_succ]
  have hs : readState flag a (decide (0 < n)) =
      flagged flag a (pre.length + 1) (decide (0 < n)).toNat := by simp [readState, flagged, hip]
  rw [hs] at er
  exact (Ex.seq er (loop_unary C zero flag hzf a hz n pre tail hin)).mono (by omega)

def rewindCount (zero one count : Fin V) : St V M :=
  .loop (.lt zero count) (.seq (.op (.sub count one)) (.op .bkI))

def rewindState (count : Fin V) (a : DS V M) (pos value : ℕ) : DS V M :=
  {a.set count value with ip := pos}

theorem rewind_count (C : Ctx) (zero one count : Fin V)
    (hzc : zero ≠ count) (hoc : one ≠ count) (a : DS V M)
    (hz : a.env zero = 0) (ho : a.env one = 1) (base : ℕ) :
    ∀ n : ℕ, Ex C (rewindCount zero one count)
      (rewindState count a (base + n) n) (rewindState count a base 0) (5 * n + 2) := by
  intro n
  induction n with
  | zero =>
    exact Ex.loopF hzc (by simp [Cnd.eval, rewindState, DS.set, hzc, hz])
  | succ n ih =>
    let b := rewindState count a (base + (n + 1)) (n + 1)
    have hc : b.env count = n + 1 := by simp [b, rewindState, DS.set]
    have h1 : b.env one = 1 := by simp [b, rewindState, DS.set, hoc, ho]
    have es := Ex.op (OpEx.sub (C := C) count one b (Ne.symm hoc) (by rw [h1, hc]; omega))
    rw [hc, h1, Nat.add_sub_cancel] at es
    have eb := Ex.op (OpEx.bkI (C := C) (b.set count n) (by simp [b, rewindState]))
    have hs : {(b.set count n) with ip := (b.set count n).ip - 1} = rewindState count a (base + n) n := by
      apply state_ext <;> simp [b, rewindState, DS.set]
    rw [hs] at eb
    have h := Ex.loopT (c := Cnd.lt zero count) hzc
      (show (Cnd.lt zero count).eval b = true by simp [Cnd.eval, b, rewindState, DS.set, hzc, hz])
      (Ex.seq es eb) ih
    convert h using 1 <;> simp [rewindCount]
    omega

end NearCubicGates.Adapters.Code.CountedParsing
