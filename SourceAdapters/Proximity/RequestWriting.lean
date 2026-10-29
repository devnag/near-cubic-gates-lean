import SourceAdapters.Proximity.RawSending
import SourceAdapters.Proximity.NaturalSending

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": repeatable source-description request writing.
The original input cursor is restored by paid instructions after every copy. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.RequestWriting

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code.CountedParsing NearCubicGates.Adapters.Code.CellSending
variable {V M : ℕ}

private theorem Rne (R : Fin 5 ↪ Fin V) {i j : Fin 5} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

def copySource (R : Fin 5 ↪ Fin V) : St V M :=
  .seq (.op (.copy (R 3) (R 4))) (.seq (.op (.zero (R 2)))
    (.seq (sendRawChunk (R 0) (R 1) (R 2) (R 3) true)
      (.seq (.op (.copy (R 3) (R 4))) (rewindCount (R 0) (R 1) (R 3)))))

theorem copy_source (C : Ctx) (R : Fin 5 ↪ Fin V) (a : DS V M) (bits pre tail : List Bool)
    (hz : a.env (R 0) = 0) (ho : a.env (R 1) = 1) (hl : a.env (R 4) = bits.length)
    (hin : C.inp = pre ++ bits ++ tail) (hip : a.ip = pre.length)
    (hroom : a.kin.length + bits.length ≤ C.Lk) :
    Ex C (copySource R) a (sent true ((a.set (R 2) 0).set (R 3) 0) bits) (15 * bits.length + 11) := by
  have e1 := Ex.op (OpEx.copy (C := C) (R 3) (R 4) a (Rne R (by decide)))
  rw [hl] at e1
  let a1 := a.set (R 3) bits.length
  have e2 := Ex.op (OpEx.zero (C := C) (R 2) a1)
  let a2 := a1.set (R 2) 0
  have e3 := send_raw_chunk C (R 0) (R 1) (R 2) (R 3)
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) true bits pre tail a2
    (by simp [a2, a1, DS.set, hz]) (by simp [a2, a1, DS.set, ho])
    (by simp [a2]) (by simp [a2, a1, DS.set]) hin (by simp [a2, a1, hip]) (by simpa [a2, a1] using hroom)
  let a3 := chunkResult (R 2) (R 3) true a2 (pre.length + bits.length) bits
  have hlen : a3.env (R 4) = bits.length := by simp [a3, chunkResult, a2, a1, DS.set, hl]
  have e4 := Ex.op (OpEx.copy (C := C) (R 3) (R 4) a3 (Rne R (by decide)))
  rw [hlen] at e4
  let a4 := a3.set (R 3) bits.length
  have e5 := rewind_count C (R 0) (R 1) (R 3) (Rne R (by decide)) (Rne R (by decide)) a4
    (by simp [a4, a3, chunkResult, a2, a1, DS.set, hz])
    (by simp [a4, a3, chunkResult, a2, a1, DS.set, ho]) pre.length bits.length
  have hstart : rewindState (R 3) a4 (pre.length + bits.length) bits.length = a4 := by
    apply state_ext <;> simp [rewindState, a4, a3, chunkResult, a2, a1, sent, DS.set]
  rw [hstart] at e5
  have hfinal : rewindState (R 3) a4 pre.length 0 = sent true ((a.set (R 2) 0).set (R 3) 0) bits := by
    apply state_ext
    · funext i
      by_cases h3 : i = R 3
      · subst i; simp [rewindState, sent, DS.set]
      · by_cases h2 : i = R 2
        · subst i; simp [rewindState, a4, a3, chunkResult, a2, a1, sent, DS.set]
        · simp [rewindState, a4, a3, chunkResult, a2, a1, sent, DS.set, h3, h2]
    all_goals simp [rewindState, a4, a3, chunkResult, a2, a1, sent, hip]
  rw [hfinal] at e5
  convert Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 e5))) using 1 <;> first | rfl | omega

def callLiteral (scratch : Fin V) : List Bool → St V M
  | [] => .op (.zero scratch)
  | bit :: bits => .seq (.op (.kem bit)) (callLiteral scratch bits)

theorem call_literal (C : Ctx) (scratch : Fin V) : ∀ (bits : List Bool) (a : DS V M),
    a.kin.length + bits.length ≤ C.Lk →
    Ex C (callLiteral scratch bits) a (sent true (a.set scratch 0) bits) (2 * bits.length + 1) := by
  intro bits
  induction bits with
  | nil => intro a _; simpa [callLiteral] using Ex.op (OpEx.zero (C := C) scratch a)
  | cons bit bits ih =>
    intro a hroom
    have e1 := Ex.op (OpEx.kem (C := C) bit a (by simp only [List.length_cons] at hroom; omega))
    let b := sent true a [bit]
    have e2 := ih b (by
      simp only [b, sent_kin, List.length_append, List.length_cons, List.length_nil]
      simp only [List.length_cons] at hroom
      omega)
    have hs : sent true (b.set scratch 0) bits = sent true (a.set scratch 0) (bit :: bits) := by
      simp [b, sent, DS.set, List.append_assoc]
    rw [hs] at e2
    convert Ex.seq e1 e2 using 1 <;> first | rfl | (simp only [List.length_cons]; omega)

end NearCubicGates.Adapters.Proximity.RequestWriting
