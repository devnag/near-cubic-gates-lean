import SourceAdapters.Code.Parsing
import SourceAdapters.Code.Composition
import Proof.Gates.CounterMachine.CellTablesSet

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": prepare an explicitly framed encoder request with a paid
unary bit-length prefix, suitable for the ordinary cell-language compiler. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.Parsing

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.PublishedSources.PCPP

def mapBody (each : Script) : Script := .seq (.op (.rdI 1)) (.seq each (.op (.rdI 1)))
def mapField (each : Script) : Script := .seq (.op (.rdI 1)) (.loop (.lt 0 1) (mapBody each))

private theorem loop_map (C : Ctx) (each : Script) (output : Bool → List Bool) (cost : ℕ)
    (heach : ∀ (a : State) (b : Bool), a.env 0 = 0 → a.env 1 = b.toNat →
      Ex C each a {a with out := a.out ++ output b} cost)
    (a : State) (hz : a.env 0 = 0) :
    ∀ (bits pre suffix out : List Bool), C.inp = pre ++ frame bits ++ suffix →
      Ex C (.loop (.lt 0 1) (mapBody each))
        (positioned a (pre.length + 1) (!bits.isEmpty).toNat out)
        (positioned a (pre.length + 2 * bits.length + 1) 0 (out ++ bits.flatMap output))
        ((cost + 6) * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix out _
    have h := Ex.loopF (C := C) (c := Cnd.lt (0 : Fin 2) 1) (s := mapBody each)
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
    let a2 : State := {a1 with out := out ++ output b}
    have e2 : Ex C each a1 a2 cost := by
      simpa [a2, a1, readState, a0, positioned] using heach a1 b
        (by simp [a1, readState, a0, positioned, DS.set, hz]) (by simp [a1, readState])
    have hin1 : C.inp = (pre ++ [true, b]) ++ frame bits ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hip : a2.ip = (pre ++ [true, b]).length := by
      simp [a2, a1, readState, a0, positioned]
    have e3 : Ex C (.op (.rdI 1)) a2 (readState a2 (!bits.isEmpty)) 1 := by
      apply read_bit C a2 (!bits.isEmpty)
      · rw [hip, hin1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hp := frame_nonempty bits
        omega
      · rw [hip, hin1, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        simpa using frame_first bits suffix
    have ebody := Ex.seq e1 (Ex.seq e2 e3)
    have hnext : readState a2 (!bits.isEmpty) =
        positioned a ((pre ++ [true, b]).length + 1) (!bits.isEmpty).toNat (out ++ output b) := by
      apply state_ext <;> simp [readState, a2, a1, a0, positioned, DS.set]
    rw [hnext] at ebody
    have ei := ih (pre ++ [true, b]) suffix (out ++ output b)
      (by simpa [frame, List.append_assoc] using hin)
    have e := Ex.loopT (by norm_num [Cnd.wf]) ht ebody ei
    have hfinal : positioned a ((pre ++ [true, b]).length + 2 * bits.length + 1) 0
        ((out ++ output b) ++ bits.flatMap output) =
        positioned a (pre.length + 2 * (b :: bits).length + 1) 0 (out ++ (b :: bits).flatMap output) := by
      congr 1
      · simp; omega
      · simp [List.append_assoc]
    rw [hfinal] at e
    convert e using 1 <;> simp [mapBody, a0]
    ring

theorem map_field (C : Ctx) (each : Script) (output : Bool → List Bool) (cost : ℕ)
    (heach : ∀ (a : State) (b : Bool), a.env 0 = 0 → a.env 1 = b.toNat →
      Ex C each a {a with out := a.out ++ output b} cost)
    (a : State) (hz : a.env 0 = 0) (bits pre suffix : List Bool)
    (hin : C.inp = pre ++ frame bits ++ suffix) (hip : a.ip = pre.length) :
    Ex C (mapField each) a
      (positioned a (pre.length + 2 * bits.length + 1) 0 (a.out ++ bits.flatMap output))
      ((cost + 6) * bits.length + 4) := by
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
  exact (Ex.seq er (loop_map C each output cost heach a hz bits pre suffix a.out hin)).mono (by omega)

def emitLiteral : List Bool → Script
  | [] => .op (.zero 0)
  | b :: bs => .seq (.op (.emit b)) (emitLiteral bs)

theorem emit_literal (C : Ctx) (word : List Bool) (a : State) (hz : a.env 0 = 0) :
    Ex C (emitLiteral word) a {a with out := a.out ++ word} (2 * word.length + 1) := by
  induction word generalizing a with
  | nil =>
    have he : a.set 0 0 = a := by
      apply state_ext <;> try rfl
      funext i
      by_cases hi : i = 0
      · subst i; simpa using hz.symm
      · simp [DS.set, Function.update_of_ne hi]
    simpa [emitLiteral, he] using Ex.op (OpEx.zero (C := C) (0 : Fin 2) a)
  | cons b bs ih =>
    have h := Ex.seq (Ex.op (OpEx.emit (C := C) b a)) (ih {a with out := a.out ++ [b]} hz)
    convert h using 1 <;> simp [emitLiteral, List.append_assoc]
    omega

def onesEach : Script := emitLiteral [true, true]
def nestedEach : Script := .seq (emitLiteral [true, true, true]) emitReadBit

theorem ones_each (C : Ctx) (a : State) (b : Bool) (hz : a.env 0 = 0) (_hb : a.env 1 = b.toNat) :
    Ex C onesEach a {a with out := a.out ++ [true, true]} 5 :=
  emit_literal C [true, true] a hz

theorem nested_each (C : Ctx) (a : State) (b : Bool) (hz : a.env 0 = 0) (hb : a.env 1 = b.toNat) :
    Ex C nestedEach a {a with out := a.out ++ [true, true, true, b]} 10 := by
  have h := Ex.seq (emit_literal C [true, true, true] a hz)
    (emit_read_bit C {a with out := a.out ++ [true, true, true]} b hz hb)
  simpa [nestedEach, List.append_assoc] using h

def preparedWord (p : List Bool × List Bool) : List Bool :=
  List.replicate p.1.length true ++ false :: frame p.2

def preparationScript : Script := .seq (mapField onesEach)
  (.seq (emitLiteral [true, false]) (.seq (mapField nestedEach) (emitLiteral [true, false, false])))

def preparationCost (p : List Bool × List Bool) : ℕ := 11 * p.1.length + 16 * p.2.length + 23

private theorem frame_prefix_ones (n : ℕ) (tail : List Bool) :
    frame (List.replicate n true ++ tail) = (List.replicate n [true, true]).flatten ++ frame tail := by
  induction n with
  | zero => rfl
  | succ n ih => simp [frame, ih, List.replicate_succ]

theorem preparedWord_frame (p : List Bool × List Bool) :
    frame (preparedWord p) = p.1.flatMap (fun _ => [true, true]) ++ [true, false] ++
      p.2.flatMap (fun b => [true, true, true, b]) ++ [true, false, false] := by
  have hfirst : ∀ bits : List Bool, bits.flatMap (fun _ => [true, true]) =
      (List.replicate bits.length [true, true]).flatten := by
    intro bits
    induction bits <;> simp_all [List.replicate_succ]
  have hsecond : ∀ bits : List Bool, frame (frame bits) =
      bits.flatMap (fun b => [true, true, true, b]) ++ [true, false, false] := by
    intro bits
    induction bits <;> simp_all [frame]
  rw [preparedWord, frame_prefix_ones, ← hfirst]
  simp only [frame, hsecond]
  simp [List.append_assoc]

theorem preparationScript_runs (p : List Bool × List Bool) :
    ∃ b n, Ex (ctxOf copyCallee payloadSize (pairedWord p)) preparationScript (a0 : State) b n ∧
      b.out = frame (preparedWord p) ∧ n ≤ preparationCost p := by
  let C := ctxOf copyCallee payloadSize (pairedWord p)
  have e1 := map_field C onesEach (fun _ => [true, true]) 5 (ones_each C)
    (a0 : State) rfl p.1 [] (frame p.2) (by simp [C, ctxOf, pairedWord]) rfl
  let s1 := positioned (a0 : State) (0 + 2 * p.1.length + 1) 0
    ([] ++ p.1.flatMap (fun _ => [true, true]))
  have e2 := emit_literal C [true, false] s1 (by simp [s1, positioned, DS.set, a0])
  let s2 : State := {s1 with out := s1.out ++ [true, false]}
  have e3 := map_field C nestedEach (fun b => [true, true, true, b]) 10 (nested_each C)
    s2 (by simp [s2, s1, positioned, DS.set, a0]) p.2 (frame p.1) []
    (by simp [C, ctxOf, pairedWord]) (by simp [s2, s1, positioned, frame_length])
  let s3 := positioned s2 ((frame p.1).length + 2 * p.2.length + 1) 0
    (s2.out ++ p.2.flatMap (fun b => [true, true, true, b]))
  have e4 := emit_literal C [true, false, false] s3
    (by simp [s3, s2, s1, positioned, DS.set, a0])
  refine ⟨_, _, Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4)), ?_, ?_⟩
  · rw [preparedWord_frame]
    simp [s3, s2, s1, positioned]
  · simp only [List.length_cons, List.length_nil, preparationCost]
    omega

def preparationBudget (p : List Bool × List Bool) : ℕ :=
  langBudget copyCallee payloadSize 2 0 (pairedWord p) (preparationCost p)

/-- The output has the extra framing needed for a paid ordinary-program call. -/
noncomputable def preparationWordFunction :
    WordFunction (List Bool × List Bool) pairedWord (fun p => frame (preparedWord p)) preparationBudget :=
  wordFunction_of_lang pairedWord (fun p => frame (preparedWord p)) copyCallee payloadSize
    preparationScript preparationCost preparationScript_runs (fun _ => by simp [payloadSize, Sz.W])

theorem preparationBudget_poly : ∃ K e : ℕ, ∀ p : List Bool × List Bool,
    preparationBudget p ≤ K * ((pairedWord p).length + 1) ^ e := by
  refine ⟨1000000, 1, fun p => ?_⟩
  have hl := leadOnes_le (pairedWord p)
  have hlen : (pairedWord p).length = 2 * p.1.length + 2 * p.2.length + 2 := by
    simp only [pairedWord, List.length_append, frame_length]
    omega
  dsimp [preparationBudget, langBudget, payloadSize, preparationCost, costA, costB, costC,
    Sz.W, Sz.Lk, Sz.Bk, TSK, copyCallee, Streaming.rewoundIdentityCopy, Streaming.copyProgram]
  norm_num
  omega

noncomputable def messagePreparationWordFunction :
    WordFunction MessageRequest messageWord
      (fun p => frame (preparedWord (p.1.bits, List.ofFn p.2.val)))
      (fun p => preparationBudget (p.1.bits, List.ofFn p.2.val)) where
  program := preparationWordFunction.program
  realizes p := preparationWordFunction.realizes (p.1.bits, List.ofFn p.2.val)

theorem messagePreparationBudget_poly : ∃ K e : ℕ, ∀ p : MessageRequest,
    preparationBudget (p.1.bits, List.ofFn p.2.val) ≤ K * ((messageWord p).length + 1) ^ e := by
  obtain ⟨K, e, h⟩ := preparationBudget_poly
  exact ⟨K, e, fun p => h (p.1.bits, List.ofFn p.2.val)⟩

theorem preparedWord_leadOnes (p : List Bool × List Bool) :
    leadOnes (preparedWord p) = p.1.length :=
  NearCubicGates.Close.CounterMachine.CellTablesProg.leadOnes_rep _ _

theorem prepared_message_capacity (p : MessageRequest) :
    p.1 < 2 ^ leadOnes (preparedWord (p.1.bits, List.ofFn p.2.val)) := by
  rw [preparedWord_leadOnes, Nat.size_eq_bits_len]
  exact Nat.lt_size_self _

theorem two_pow_bits_length_le (n : ℕ) : 2 ^ n.bits.length ≤ 2 * (n + 1) := by
  rw [Nat.size_eq_bits_len]
  by_cases hn : n = 0
  · subst n; simp
  · have hs : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have h := Nat.lt_size.mp (show n.size - 1 < n.size by omega)
    have he : n.size = n.size - 1 + 1 := by omega
    rw [he, pow_succ]
    omega

theorem prepared_message_size (p : MessageRequest) :
    2 ^ leadOnes (preparedWord (p.1.bits, List.ofFn p.2.val)) ≤ 2 * (p.1 + 1) := by
  rw [preparedWord_leadOnes]
  exact two_pow_bits_length_le _

end NearCubicGates.Adapters.Code.Parsing
