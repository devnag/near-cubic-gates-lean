import SourceAdapters.Code.CellSending

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid repeated-bit emission for zero-message length
queries and unary source decoder requests. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.RepeatedSending

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

variable {V M : ℕ}

def body (one count : Fin V) (call bit : Bool) : St V M :=
  .seq (.op (sendOp call bit)) (.op (.sub count one))

def script (zero one count : Fin V) (call bit : Bool) : St V M :=
  .loop (.lt zero count) (body one count call bit)

theorem runs (C : Ctx) (zero one count : Fin V) (hzc : zero ≠ count) (hoc : one ≠ count)
    (call bit : Bool) : ∀ (n : ℕ) (a : DS V M), a.env zero = 0 → a.env one = 1 → a.env count = n →
      (call = true → a.kin.length + n ≤ C.Lk) →
      Ex C (script zero one count call bit) a
        (sent call (a.set count 0) (List.replicate n bit)) (5 * n + 2) := by
  intro n
  induction n with
  | zero =>
    intro a hz _ hc _
    have he : a.set count 0 = a := by
      apply state_ext <;> try rfl
      funext i
      by_cases hi : i = count
      · subst i; simpa using hc.symm
      · simp [DS.set, hi]
    simpa [he, script] using Ex.loopF (C := C) (c := Cnd.lt zero count) (s := body one count call bit) hzc
      (show (Cnd.lt zero count).eval a = false by simp [Cnd.eval, hz, hc])
  | succ n ih =>
    intro a hz ho hc hroom
    have e1 := send_bit C call bit a (by intro h; have := hroom h; omega)
    let b := sent call a [bit]
    have ec : b.env count = n + 1 := by simp [b, hc]
    have eo : b.env one = 1 := by simp [b, ho]
    have e2 := Ex.op (OpEx.sub (C := C) count one b (Ne.symm hoc) (by rw [eo, ec]; omega))
    rw [ec, eo, Nat.add_sub_cancel] at e2
    have ei := ih (b.set count n) (by simp [DS.set, hzc, b, hz])
      (by simp [DS.set, hoc, b, ho]) (by simp)
      (by intro h; subst call; have := hroom rfl; simp [b]; omega)
    have he := Ex.loopT (c := Cnd.lt zero count) hzc
      (show (Cnd.lt zero count).eval a = true by simp [Cnd.eval, hz, hc]) (Ex.seq e1 e2) ei
    have hf : sent call ((b.set count n).set count 0) (List.replicate n bit) =
        sent call (a.set count 0) (List.replicate (n + 1) bit) := by
      cases call <;> apply state_ext <;> simp [b, sent, DS.set, List.replicate_succ, List.append_assoc]
    rw [hf] at he
    convert he using 1 <;> simp [script, body]
    omega

end NearCubicGates.Adapters.Code.RepeatedSending
