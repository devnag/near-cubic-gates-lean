import SourceAdapters.Code.CellSending

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": read a counted consecutive message block and
write its actual bits to a source-call input or the final output. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CellSending

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells CountedParsing

variable {V M : ℕ}

def chunkBody (zero one flag count : Fin V) (call framed : Bool) : St V M :=
  .seq (.op (.rdI flag)) (.seq (.op (.rdI flag)) (.seq (sendPayload zero flag call framed)
    (.seq (.op (.sub count one)) (.op (.zero flag)))))

def sendChunk (zero one flag count : Fin V) (call framed : Bool) : St V M :=
  .loop (.lt zero count) (chunkBody zero one flag count call framed)

def chunkResult (flag count : Fin V) (call : Bool) (a : DS V M) (pos : ℕ) (word : List Bool) : DS V M :=
  sent call { (a.set flag 0).set count 0 with ip := pos } word

theorem send_chunk (C : Ctx) (zero one flag count : Fin V)
    (hzf : zero ≠ flag) (hzc : zero ≠ count) (hof : one ≠ flag) (hoc : one ≠ count) (hfc : flag ≠ count)
    (call framed : Bool) : ∀ (bits pre tail suffix : List Bool) (a : DS V M),
      a.env zero = 0 → a.env one = 1 → a.env flag = 0 → a.env count = bits.length →
      C.inp = pre ++ frame (bits ++ tail) ++ suffix → a.ip = pre.length →
      (call = true → a.kin.length + (bits.flatMap (payload framed)).length ≤ C.Lk) →
      Ex C (sendChunk zero one flag count call framed) a
        (chunkResult flag count call a (pre.length + 2 * bits.length) (bits.flatMap (payload framed)))
        ((payloadCost framed + 10) * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre tail suffix a hz _ hf hc _ hip _
    have he : chunkResult flag count call a (pre.length + 2 * ([] : List Bool).length) ([].flatMap (payload framed)) = a := by
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, List.flatMap_nil, chunkResult, sent_nil]
      apply state_ext
      · funext i
        by_cases hif : i = flag
        · subst i; simp [DS.set, hfc, hf]
        · by_cases hic : i = count
          · subst i; simpa [DS.set] using hc.symm
          · simp [DS.set, hif, hic]
      all_goals simp [hip]
    rw [he]
    exact Ex.loopF hzc (by simp [Cnd.eval, hz, hc])
  | cons bit bits ih =>
    intro pre tail suffix a hz ho hf hc hin hip hroom
    have hin0 : C.inp = pre ++ true :: (bit :: (frame (bits ++ tail) ++ suffix)) := by
      simpa [frame, List.append_assoc] using hin
    have e1 := read_at_prefix C flag a pre true _ hin0 hip
    let a1 := readState flag a true
    have hin1 : C.inp = (pre ++ [true]) ++ bit :: (frame (bits ++ tail) ++ suffix) := by
      simpa [frame, List.append_assoc] using hin
    have e2 := read_at_prefix C flag a1 (pre ++ [true]) bit _ hin1
      (by simp [a1, readState, hip])
    let a2 := readState flag a1 bit
    have hz2 : a2.env zero = 0 := by simp [a2, a1, readState, DS.set, hzf, hz]
    have hb2 : a2.env flag = bit.toNat := by simp [a2, readState]
    have e3 := send_payload C zero flag hzf call framed a2 bit hz2 hb2
      (by intro h; have := hroom h; simp only [List.flatMap_cons, List.length_append] at this
          simp only [a2, a1, readState, DS.set_kin]
          omega)
    let a3 := sent call a2 (payload framed bit)
    have hc3 : a3.env count = bits.length + 1 := by
      simpa [a3, a2, a1, readState, DS.set, Ne.symm hfc] using hc
    have ho3 : a3.env one = 1 := by simp [a3, a2, a1, readState, DS.set, hof, ho]
    have e4 := Ex.op (OpEx.sub (C := C) count one a3 (Ne.symm hoc) (by rw [ho3, hc3]; omega))
    rw [hc3, ho3, Nat.add_sub_cancel] at e4
    have e5 := Ex.op (OpEx.zero (C := C) flag (a3.set count bits.length))
    let a4 := (a3.set count bits.length).set flag 0
    have ebody := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5)))
    have hin2 : C.inp = (pre ++ [true, bit]) ++ frame (bits ++ tail) ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hip4 : a4.ip = (pre ++ [true, bit]).length := by simp [a4, a3, a2, a1, readState, hip]
    have ei := ih (pre ++ [true, bit]) tail suffix a4
      (by simp [a4, a3, a2, a1, readState, DS.set, hzf, hzc, hz])
      (by simp [a4, a3, a2, a1, readState, DS.set, hof, hoc, ho])
      (by simp [a4]) (by simp [a4, DS.set, Ne.symm hfc]) hin2 hip4
      (by intro h; subst call; have := hroom rfl
          simpa [a4, a3, a2, a1, readState, List.length_append, List.flatMap_cons, Nat.add_assoc] using this)
    have he := Ex.loopT (c := Cnd.lt zero count) hzc
      (show (Cnd.lt zero count).eval a = true by simp [Cnd.eval, hz, hc]) ebody ei
    have hfinal : chunkResult flag count call a4 ((pre ++ [true, bit]).length + 2 * bits.length)
        (bits.flatMap (payload framed)) =
        chunkResult flag count call a (pre.length + 2 * (bit :: bits).length)
          ((bit :: bits).flatMap (payload framed)) := by
      have hev : ((a4.set flag 0).set count 0).env = ((a.set flag 0).set count 0).env := by
        funext i
        by_cases hif : i = flag
        · subst i; simp [DS.set, hfc, a4]
        · by_cases hic : i = count
          · subst i; simp [DS.set]
          · simp [a4, a3, a2, a1, readState, DS.set, hif, hic]
      apply state_ext
      · simpa only [chunkResult, sent_env] using hev
      all_goals cases call <;> simp [chunkResult, a4, a3, a2, a1, readState, sent, hip, List.append_assoc]
      all_goals omega
    rw [hfinal] at he
    convert he using 1 <;> simp [sendChunk, chunkBody]
    ring

end NearCubicGates.Adapters.Code.CellSending
