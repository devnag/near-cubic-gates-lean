import SourceAdapters.Code.BlockArithmetic

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid bit and unary-frame emission for source-call inputs
and assembled code outputs. The Cells.Kit emitB/Snk construction is generalized from
its fixed register bank to the code constructor's arbitrary register bank. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CellSending

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells CountedParsing

variable {V M : ℕ}

def sendOp (call bit : Bool) : Op V M := if call then .kem bit else .emit bit

def sent (call : Bool) (a : DS V M) (word : List Bool) : DS V M :=
  if call then {a with kin := a.kin ++ word} else {a with out := a.out ++ word}

@[simp] theorem sent_env (call : Bool) (a : DS V M) (word : List Bool) : (sent call a word).env = a.env := by
  cases call <;> rfl

@[simp] theorem sent_ip (call : Bool) (a : DS V M) (word : List Bool) : (sent call a word).ip = a.ip := by
  cases call <;> rfl

@[simp] theorem sent_kin (a : DS V M) (word : List Bool) : (sent true a word).kin = a.kin ++ word := rfl

@[simp] theorem sent_nil (call : Bool) (a : DS V M) : sent call a [] = a := by cases call <;> simp [sent]

theorem sent_append (call : Bool) (a : DS V M) (x y : List Bool) :
    sent call (sent call a x) y = sent call a (x ++ y) := by cases call <;> simp [sent, List.append_assoc]

theorem sent_set (call : Bool) (a : DS V M) (word : List Bool) (i : Fin V) (n : ℕ) :
    (sent call a word).set i n = sent call (a.set i n) word := by cases call <;> rfl

theorem send_bit (C : Ctx) (call bit : Bool) (a : DS V M)
    (hroom : call = true → a.kin.length < C.Lk) :
    Ex C (.op (sendOp call bit)) a (sent call a [bit]) 1 := by
  cases call
  · exact Ex.op (OpEx.emit bit a)
  · exact Ex.op (OpEx.kem bit a (hroom rfl))

def sendReadBit (zero flag : Fin V) (call : Bool) : St V M :=
  .ite (.eq zero flag) (.op (sendOp call false)) (.op (sendOp call true))

theorem send_read_bit (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag) (call : Bool)
    (a : DS V M) (bit : Bool) (hz : a.env zero = 0) (hb : a.env flag = bit.toNat)
    (hroom : call = true → a.kin.length < C.Lk) :
    Ex C (sendReadBit zero flag call) a (sent call a [bit]) 2 := by
  cases bit
  · exact Ex.iteT hzf (by simp [Cnd.eval, hz, hb]) (send_bit C call false a hroom)
  · exact Ex.iteF hzf (by simp [Cnd.eval, hz, hb]) (send_bit C call true a hroom)

def sendPayload (zero flag : Fin V) (call framed : Bool) : St V M :=
  if framed then .seq (.op (sendOp call true)) (sendReadBit zero flag call)
  else sendReadBit zero flag call

def payload (framed bit : Bool) : List Bool := if framed then [true, bit] else [bit]

def payloadCost (framed : Bool) : ℕ := if framed then 4 else 2

theorem send_payload (C : Ctx) (zero flag : Fin V) (hzf : zero ≠ flag) (call framed : Bool)
    (a : DS V M) (bit : Bool) (hz : a.env zero = 0) (hb : a.env flag = bit.toNat)
    (hroom : call = true → a.kin.length + (payload framed bit).length ≤ C.Lk) :
    Ex C (sendPayload zero flag call framed) a (sent call a (payload framed bit)) (payloadCost framed) := by
  cases framed
  · exact send_read_bit C zero flag hzf call a bit hz hb (by intro h; have := hroom h; simp [payload] at this; omega)
  · have e1 := send_bit C call true a (by intro h; have := hroom h; simp [payload] at this; omega)
    have e2 := send_read_bit C zero flag hzf call (sent call a [true]) bit (by simpa using hz) (by simpa using hb)
      (by intro h; subst call; have := hroom rfl; simp [payload] at this; simp; omega)
    simpa [sendPayload, payloadCost, payload, sent_append] using Ex.seq e1 e2

def unaryBody (one count : Fin V) (call : Bool) : St V M :=
  .seq (.op (sendOp call true)) (.seq (.op (sendOp call true)) (.op (.sub count one)))

def unaryLoop (zero one count : Fin V) (call : Bool) : St V M :=
  .loop (.lt zero count) (unaryBody one count call)

private theorem unary_loop (C : Ctx) (zero one count : Fin V) (hzc : zero ≠ count) (hoc : one ≠ count)
    (call : Bool) : ∀ (n : ℕ) (a : DS V M), a.env zero = 0 → a.env one = 1 → a.env count = n →
      (call = true → a.kin.length + 2 * n ≤ C.Lk) →
      Ex C (unaryLoop zero one count call) a
        (sent call (a.set count 0) (Streaming.marks (List.replicate n true))) (7 * n + 2) := by
  intro n
  induction n with
  | zero =>
    intro a hz _ hc _
    have he : a.set count 0 = a := by
      apply state_ext <;> try rfl
      funext i; by_cases hi : i = count
      · subst i; simpa using hc.symm
      · simp [DS.set, hi]
    simpa [Streaming.marks, he, unaryLoop] using
      Ex.loopF (C := C) (c := Cnd.lt zero count) (s := unaryBody one count call) hzc
        (show (Cnd.lt zero count).eval a = false by simp [Cnd.eval, hz, hc])
  | succ n ih =>
    intro a hz ho hc hroom
    have e1 := send_bit C call true a (by intro h; have := hroom h; omega)
    have e2 := send_bit C call true (sent call a [true])
      (by intro h; subst call; have := hroom rfl; simp; omega)
    let b := sent call (sent call a [true]) [true]
    have ec : b.env count = n + 1 := by simp [b, hc]
    have eo : b.env one = 1 := by simp [b, ho]
    have e3 := Ex.op (OpEx.sub (C := C) count one b (Ne.symm hoc) (by rw [eo, ec]; omega))
    rw [ec, eo, Nat.add_sub_cancel] at e3
    have ei := ih (b.set count n) (by simp [DS.set, hzc, b, hz])
      (by simp [DS.set, hoc, b, ho]) (by simp)
      (by intro h; subst call; have := hroom rfl; simp [b]; omega)
    have he := Ex.loopT (c := Cnd.lt zero count) hzc
      (show (Cnd.lt zero count).eval a = true by simp [Cnd.eval, hz, hc]) (Ex.seq e1 (Ex.seq e2 e3)) ei
    have hf : sent call ((b.set count n).set count 0) (Streaming.marks (List.replicate n true)) =
        sent call (a.set count 0) (Streaming.marks (List.replicate (n + 1) true)) := by
      cases call <;> apply state_ext <;> simp [b, sent, DS.set, Streaming.marks, List.replicate_succ, List.append_assoc]
    rw [hf] at he
    convert he using 1 <;> simp [unaryLoop, unaryBody]
    omega

def sendUnaryFrame (zero one count : Fin V) (call : Bool) : St V M :=
  .seq (unaryLoop zero one count call) (.op (sendOp call false))

theorem send_unary_frame (C : Ctx) (zero one count : Fin V) (hzc : zero ≠ count) (hoc : one ≠ count)
    (call : Bool) (n : ℕ) (a : DS V M) (hz : a.env zero = 0) (ho : a.env one = 1) (hc : a.env count = n)
    (hroom : call = true → a.kin.length + 2 * n + 1 ≤ C.Lk) :
    Ex C (sendUnaryFrame zero one count call) a (sent call (a.set count 0) (frame (List.replicate n true)))
      (7 * n + 4) := by
  have e1 := unary_loop C zero one count hzc hoc call n a hz ho hc (by intro h; have := hroom h; omega)
  have e2 := send_bit C call false (sent call (a.set count 0) (Streaming.marks (List.replicate n true)))
    (by intro h; subst call; have := hroom rfl; simp [Streaming.marks, List.length_flatMap]; simpa [Nat.mul_comm] using this)
  have he := Ex.seq e1 e2
  rw [sent_append, ← NearCubicGates.Close.CounterMachine.CellTablesProg.frame_marks] at he
  simpa [sendUnaryFrame] using he

end NearCubicGates.Adapters.Code.CellSending
