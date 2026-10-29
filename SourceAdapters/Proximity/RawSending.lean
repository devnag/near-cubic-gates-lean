import SourceAdapters.Code.ChunkSending

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": paid copying of the actual raw source description
into the next call input. The count is explicit and every payload bit is read. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CountedParsing NearCubicGates.Adapters.Code.CellSending
variable {V M : ℕ}

def rawChunkBody (zero one flag count : Fin V) (call : Bool) : St V M :=
  .seq (.op (.rdI flag)) (.seq (sendReadBit zero flag call)
    (.seq (.op (.sub count one)) (.op (.zero flag))))

def sendRawChunk (zero one flag count : Fin V) (call : Bool) : St V M :=
  .loop (.lt zero count) (rawChunkBody zero one flag count call)

theorem send_raw_chunk (C : Ctx) (zero one flag count : Fin V)
    (hzf : zero ≠ flag) (hzc : zero ≠ count) (hof : one ≠ flag) (hoc : one ≠ count) (hfc : flag ≠ count)
    (call : Bool) : ∀ (bits pre suffix : List Bool) (a : DS V M),
      a.env zero = 0 → a.env one = 1 → a.env flag = 0 → a.env count = bits.length →
      C.inp = pre ++ bits ++ suffix → a.ip = pre.length →
      (call = true → a.kin.length + bits.length ≤ C.Lk) →
      Ex C (sendRawChunk zero one flag count call) a
        (chunkResult flag count call a (pre.length + bits.length) bits) (10 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix a hz _ hf hc _ hip _
    have he : chunkResult flag count call a (pre.length + ([] : List Bool).length) [] = a := by
      simp only [List.length_nil, Nat.add_zero, chunkResult, sent_nil]
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
    intro pre suffix a hz ho hf hc hin hip hroom
    have e1 := read_at_prefix C flag a pre bit (bits ++ suffix) (by simpa using hin) hip
    let a1 := readState flag a bit
    have hz1 : a1.env zero = 0 := by simp [a1, readState, DS.set, hzf, hz]
    have hb1 : a1.env flag = bit.toNat := by simp [a1, readState]
    have e2 := send_read_bit C zero flag hzf call a1 bit hz1 hb1
      (by intro h; have := hroom h; simp only [a1, readState, DS.set_kin]; simp only [List.length_cons] at this; omega)
    let a2 := sent call a1 [bit]
    have hc2 : a2.env count = bits.length + 1 := by
      simpa [a2, a1, readState, DS.set, Ne.symm hfc] using hc
    have ho2 : a2.env one = 1 := by simp [a2, a1, readState, DS.set, hof, ho]
    have e3 := Ex.op (OpEx.sub (C := C) count one a2 (Ne.symm hoc) (by rw [ho2, hc2]; omega))
    rw [hc2, ho2, Nat.add_sub_cancel] at e3
    have e4 := Ex.op (OpEx.zero (C := C) flag (a2.set count bits.length))
    let a3 := (a2.set count bits.length).set flag 0
    have hin' : C.inp = (pre ++ [bit]) ++ bits ++ suffix := by simpa [List.append_assoc] using hin
    have hip' : a3.ip = (pre ++ [bit]).length := by simp [a3, a2, a1, readState, hip]
    have ei := ih (pre ++ [bit]) suffix a3
      (by simp [a3, a2, a1, readState, DS.set, hzf, hzc, hz])
      (by simp [a3, a2, a1, readState, DS.set, hof, hoc, ho])
      (by simp [a3]) (by simp [a3, DS.set, Ne.symm hfc]) hin' hip'
      (by intro h; subst call; have hh := hroom rfl
          simp only [a3, DS.set_kin, a2, sent_kin, a1, readState, List.length_append, List.length_cons, List.length_nil]
          simp only [List.length_cons] at hh
          omega)
    have hfinal : chunkResult flag count call a3 ((pre ++ [bit]).length + bits.length) bits =
        chunkResult flag count call a (pre.length + (bit :: bits).length) (bit :: bits) := by
      have hev : ((a3.set flag 0).set count 0).env = ((a.set flag 0).set count 0).env := by
        funext i
        by_cases hif : i = flag
        · subst i; simp [DS.set, hfc, a3]
        · by_cases hic : i = count
          · subst i; simp [DS.set]
          · simp [a3, a2, a1, readState, DS.set, hif, hic]
      apply state_ext
      · simpa only [chunkResult, sent_env] using hev
      all_goals cases call <;> simp [chunkResult, a3, a2, a1, readState, sent, hip, List.append_assoc]
      all_goals omega
    rw [hfinal] at ei
    have eb := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))
    have he := Ex.loopT (c := Cnd.lt zero count) hzc
      (show (Cnd.lt zero count).eval a = true by simp [Cnd.eval, hz, hc]) eb ei
    convert he using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

end NearCubicGates.Adapters.Proximity
