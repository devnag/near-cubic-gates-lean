import SourceAdapters.Code.Algorithms
import Proof.Gates.Cells.Run
import Proof.Foundations.OrdinaryStreaming

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": an ordinary parser for the target's framed message payload. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Parsing

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.PublishedSources.PCPP

abbrev State := DS 2 0
abbrev Script := St 2 0

theorem state_ext {a b : State} (he : a.env = b.env) (hi : a.ip = b.ip)
    (ho : a.out = b.out) (hr : a.ram = b.ram) (hc : a.rc = b.rc)
    (hki : a.kin = b.kin) (hko : a.kout = b.kout) (hkc : a.kc = b.kc) : a = b := by
  cases a
  cases b
  cases he
  cases hi
  cases ho
  cases hr
  cases hc
  cases hki
  cases hko
  cases hkc
  rfl

def positioned (a : State) (ip flag : ℕ) (out : List Bool) : State :=
  { a.set 1 flag with ip := ip, out := out }

theorem positioned_again (a : State) (ip flag : ℕ) (out : List Bool)
    (ip' flag' : ℕ) (out' : List Bool) :
    positioned (positioned a ip flag out) ip' flag' out' = positioned a ip' flag' out' := by
  apply state_ext <;> simp [positioned, DS.set]

def readState (a : State) (bit : Bool) : State := { a.set 1 bit.toNat with ip := a.ip + 1 }

theorem read_bit (C : Ctx) (a : State) (bit : Bool) (hi : a.ip < C.inp.length)
    (hb : C.inp.getD a.ip false = bit) :
    Ex C (.op (.rdI 1)) a (readState a bit) 1 := by
  have h := Ex.op (OpEx.rdI (C := C) (1 : Fin 2) a hi)
  simpa only [readState, bitOf, hb] using h

def emitReadBit : Script := .ite (.eq 0 1) (.op (.emit false)) (.op (.emit true))

theorem emit_read_bit (C : Ctx) (a : State) (bit : Bool)
    (hz : a.env 0 = 0) (hb : a.env 1 = bit.toNat) :
    Ex C emitReadBit a {a with out := a.out ++ [bit]} 2 := by
  cases bit
  · exact Ex.iteT (by norm_num [Cnd.wf]) (by simp [Cnd.eval, hz, hb]) (Ex.op (OpEx.emit false a))
  · exact Ex.iteF (by norm_num [Cnd.wf]) (by simp [Cnd.eval, hz, hb]) (Ex.op (OpEx.emit true a))

def body (copy : Bool) : Script :=
  .seq (.op (.rdI 1))
    (if copy then .seq emitReadBit (.op (.rdI 1)) else .op (.rdI 1))

def readField (copy : Bool) : Script :=
  .seq (.op (.rdI 1)) (.loop (.lt 0 1) (body copy))

def costPerBit (copy : Bool) : ℕ := if copy then 8 else 5

theorem frame_first (bits suffix : List Bool) :
    (frame bits ++ suffix).getD 0 false = !bits.isEmpty := by
  cases bits <;> rfl

theorem frame_nonempty (bits : List Bool) : 0 < (frame bits).length := by
  rw [frame_length]
  omega

theorem read_at_prefix (C : Ctx) (a : State) (pre : List Bool) (b : Bool) (tail : List Bool)
    (hin : C.inp = pre ++ b :: tail) (hip : a.ip = pre.length) :
    Ex C (.op (.rdI 1)) a (readState a b) 1 := by
  apply read_bit C a b
  · rw [hin, hip]
    simp
  · rw [hin, hip]
    simp

private theorem loop_field (C : Ctx) (copy : Bool) (a : State) (hz : a.env 0 = 0) :
    ∀ (bits pre suffix out : List Bool), C.inp = pre ++ frame bits ++ suffix →
      Ex C (.loop (.lt 0 1) (body copy))
        (positioned a (pre.length + 1) (!bits.isEmpty).toNat out)
        (positioned a (pre.length + 2 * bits.length + 1) 0 (out ++ if copy then bits else []))
        (costPerBit copy * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix out _
    have h := Ex.loopF (C := C) (c := Cnd.lt (0 : Fin 2) 1) (s := body copy)
      (a := positioned a (pre.length + 1) 0 out) (by norm_num [Cnd.wf])
      (by simp [Cnd.eval, positioned, DS.set, hz])
    simpa using h
  | cons b bits ih =>
    intro pre suffix out hin
    let a0 := positioned a (pre.length + 1) 1 out
    have ht : (Cnd.lt (0 : Fin 2) 1).eval a0 = true := by
      simp [Cnd.eval, a0, positioned, DS.set, hz]
    have hin0 : C.inp = (pre ++ [true]) ++ b :: (frame bits ++ suffix) := by
      simpa [frame, List.append_assoc] using hin
    have e1 := read_at_prefix C a0 (pre ++ [true]) b (frame bits ++ suffix) hin0 (by simp [a0, positioned])
    let a1 := readState a0 b
    let a2 : State := if copy then {a1 with out := out ++ [b]} else a1
    have e2 : Ex C (if copy then .seq emitReadBit (.op (.rdI 1)) else .op (.rdI 1)) a1
        (readState a2 (!bits.isEmpty)) (if copy then 4 else 1) := by
      have hin1 : C.inp = (pre ++ [true, b]) ++ frame bits ++ suffix := by
        simpa [frame, List.append_assoc] using hin
      have hip : a2.ip = (pre ++ [true, b]).length := by
        cases copy <;> simp [a2, a1, readState, a0, positioned]
      have e3 : Ex C (.op (.rdI 1)) a2 (readState a2 (!bits.isEmpty)) 1 := by
        apply read_bit C a2 (!bits.isEmpty)
        · rw [hip, hin1]
          simp only [List.length_append, List.length_cons, List.length_nil]
          have hp := frame_nonempty bits
          omega
        · rw [hip, hin1]
          rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
          simpa using frame_first bits suffix
      cases copy
      · exact e3
      · have he := emit_read_bit C a1 b
          (by simp [a1, readState, a0, positioned, DS.set, hz])
          (by simp [a1, readState])
        have he' : Ex C emitReadBit a1 a2 2 := by simpa [a2, a1, readState, a0, positioned] using he
        exact Ex.seq he' e3
    have ebody := Ex.seq e1 e2
    have hnext : readState a2 (!bits.isEmpty) =
        positioned a ((pre ++ [true, b]).length + 1) (!bits.isEmpty).toNat
          (out ++ if copy then [b] else []) := by
      apply state_ext <;> cases copy <;> simp [readState, a2, a1, a0, positioned, DS.set]
    rw [hnext] at ebody
    have ei := ih (pre ++ [true, b]) suffix (out ++ if copy then [b] else [])
      (by simpa [frame, List.append_assoc] using hin)
    have e := Ex.loopT (by norm_num [Cnd.wf]) ht ebody ei
    have hfinal : positioned a ((pre ++ [true, b]).length + 2 * bits.length + 1) 0
        ((out ++ if copy then [b] else []) ++ if copy then bits else []) =
        positioned a (pre.length + 2 * (b :: bits).length + 1) 0
          (out ++ if copy then b :: bits else []) := by
      congr 1
      · simp; omega
      · cases copy <;> simp [List.append_assoc]
    rw [hfinal] at e
    convert e using 1 <;> cases copy <;> simp [body, a0, costPerBit] <;> omega

theorem read_field (C : Ctx) (copy : Bool) (a : State) (hz : a.env 0 = 0)
    (bits pre suffix : List Bool) (hin : C.inp = pre ++ frame bits ++ suffix) (hip : a.ip = pre.length) :
    Ex C (readField copy) a
      (positioned a (pre.length + 2 * bits.length + 1) 0 (a.out ++ if copy then bits else []))
      (costPerBit copy * bits.length + 4) := by
  have er : Ex C (.op (.rdI 1)) a (readState a (!bits.isEmpty)) 1 := by
    apply read_bit C a (!bits.isEmpty)
    · rw [hip, hin]
      simp only [List.length_append]
      have hp := frame_nonempty bits
      omega
    · rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simpa using frame_first bits suffix
  have he : readState a (!bits.isEmpty) = positioned a (pre.length + 1) (!bits.isEmpty).toNat a.out := by
    simp [readState, positioned, hip]
  rw [he] at er
  exact (Ex.seq er (loop_field C copy a hz bits pre suffix a.out hin)).mono (by omega)

def pairedWord (p : List Bool × List Bool) : List Bool := frame p.1 ++ frame p.2

def payloadScript : Script := .seq (readField false) (readField true)

def copyCallee : Callee where
  Req := List Bool
  inw := id
  outw := id
  bud word := 4 * word.length + 2
  wf := Streaming.rewoundIdentityCopy.toWordFunction

/-- Only Boolean temporary registers are needed; this program makes no calls. -/
def payloadSize : Sz := ⟨1, 0, 0, 0, 0, 0⟩

def payloadCost (p : List Bool × List Bool) : ℕ := 5 * p.1.length + 8 * p.2.length + 9

theorem payloadScript_runs (p : List Bool × List Bool) :
    ∃ b n, Ex (ctxOf copyCallee payloadSize (pairedWord p)) payloadScript (a0 : State) b n ∧
      b.out = p.2 ∧ n ≤ payloadCost p := by
  let C := ctxOf copyCallee payloadSize (pairedWord p)
  have e1 := read_field C false (a0 : State) rfl p.1 [] (frame p.2)
    (by simp [C, ctxOf, pairedWord]) rfl
  let s1 := positioned (a0 : State) (0 + 2 * p.1.length + 1) 0 ([] ++ if false then p.1 else [])
  have e2 := read_field C true s1 (by simp [s1, positioned, DS.set, a0]) p.2 (frame p.1) []
    (by simp [C, ctxOf, pairedWord]) (by simp [s1, positioned, frame_length])
  refine ⟨_, _, Ex.seq e1 e2, ?_, ?_⟩
  · simp [positioned, s1]
  · simp only [costPerBit, Bool.false_eq_true, if_false, if_true, payloadCost]
    omega

def payloadBudget (p : List Bool × List Bool) : ℕ :=
  langBudget copyCallee payloadSize 2 0 (pairedWord p) (payloadCost p)

/-- An actual ordinary machine for dropping the first framed field and
decoding the second one. This includes input unframing and final head resets. -/
noncomputable def payloadWordFunction :
    WordFunction (List Bool × List Bool) pairedWord Prod.snd payloadBudget :=
  wordFunction_of_lang pairedWord Prod.snd copyCallee payloadSize payloadScript payloadCost
    payloadScript_runs (fun _ => by simp [payloadSize, Sz.W])

theorem payloadBudget_poly : ∃ K e : ℕ, ∀ p : List Bool × List Bool,
    payloadBudget p ≤ K * ((pairedWord p).length + 1) ^ e := by
  refine ⟨100000, 1, fun p => ?_⟩
  have hl := leadOnes_le (pairedWord p)
  have hlen : (pairedWord p).length = 2 * p.1.length + 2 * p.2.length + 2 := by
    simp only [pairedWord, List.length_append, frame_length]
    omega
  dsimp [payloadBudget, langBudget, payloadSize, payloadCost, costA, costB, costC,
    Sz.W, Sz.Lk, Sz.Bk, TSK, copyCallee, Streaming.rewoundIdentityCopy, Streaming.copyProgram]
  norm_num
  omega

/-- Specialization to the exact companion message encoding. -/
noncomputable def messagePayloadWordFunction :
    WordFunction MessageRequest messageWord (fun p => List.ofFn p.2.val)
      (fun p => payloadBudget (p.1.bits, List.ofFn p.2.val)) where
  program := payloadWordFunction.program
  realizes p := payloadWordFunction.realizes (p.1.bits, List.ofFn p.2.val)

theorem messagePayloadBudget_poly : ∃ K e : ℕ, ∀ p : MessageRequest,
    payloadBudget (p.1.bits, List.ofFn p.2.val) ≤ K * ((messageWord p).length + 1) ^ e := by
  obtain ⟨K, e, h⟩ := payloadBudget_poly
  exact ⟨K, e, fun p => h (p.1.bits, List.ofFn p.2.val)⟩

end NearCubicGates.Adapters.Code.Parsing
