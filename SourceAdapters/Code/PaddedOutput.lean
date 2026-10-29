import SourceAdapters.Code.OutputParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": bounded source outputs are normalized to exactly the
message length, padding absent bits by false and discarding excess bits. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.PaddedOutput

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing CellSending

abbrev State := DS 12 0
abbrev Script := St 12 0

def resize (bits : List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => bits.headD false :: resize bits.tail n

theorem resize_ofFn (bits : List Bool) (n : ℕ) : resize bits n = List.ofFn (fun i : Fin n => bits.getD i.val false) := by
  induction n generalizing bits with
  | zero => simp [resize]
  | succ n ih =>
    rw [resize, List.ofFn_succ]
    cases bits <;> simp [ih]

def copyStep : Script := .seq (.op (.rdK 1)) (.seq (sendReadBit 0 1 false) (.op (.rdK 1)))

def body : Script := .seq (.ite (.lt 0 1) copyStep (.op (.emit false))) (.op (.sub 9 10))

def script : Script := .seq (.op (.rdK 1)) (.loop (.lt 0 9) body)

def state (a : State) (pos flag count : ℕ) (out : List Bool) : State :=
  {a with kc := pos, out := out, env := fun i => if i = 1 then flag else if i = 9 then count else a.env i}

private theorem loop_runs (C : Ctx) (a : State) (hz : a.env 0 = 0) (ho : a.env 10 = 1) :
    ∀ (n : ℕ) (bits pre suffix out : List Bool), a.kout = pre ++ frame bits ++ suffix →
      Ex C (.loop (.lt 0 9) body)
        (state a (pre.length + 1) (!bits.isEmpty).toNat n out)
        (state a (pre.length + 2 * min n bits.length + 1) (!(bits.drop n).isEmpty).toNat 0 (out ++ resize bits n))
        (12 * n + 2) := by
  intro n
  induction n with
  | zero =>
    intro bits pre suffix out _
    simpa [state, resize] using Ex.loopF (C := C) (c := Cnd.lt (0 : Fin 12) 9) (s := body)
      (a := state a (pre.length + 1) (!bits.isEmpty).toNat 0 out) (by decide : (0 : Fin 12) ≠ 9)
      (by simp [Cnd.eval, state, hz])
  | succ n ih =>
    intro bits pre suffix out hin
    cases bits with
    | nil =>
      let a0 := state a (pre.length + 1) 0 (n + 1) out
      have e1 := Ex.iteF (C := C) (c := Cnd.lt (0 : Fin 12) 1) (s := copyStep)
        (by decide : (0 : Fin 12) ≠ 1) (show (Cnd.lt (0 : Fin 12) 1).eval a0 = false by simp [Cnd.eval, a0, state, hz])
        (Ex.op (OpEx.emit false a0))
      let a1 : State := {a0 with out := out ++ [false]}
      have e2 := Ex.op (OpEx.sub (C := C) (9 : Fin 12) 10 a1 (by decide)
        (by simp [a1, a0, state, ho]))
      have hnext : a1.set 9 (a1.env 9 - a1.env 10) = state a (pre.length + 1) 0 n (out ++ [false]) := by
        apply state_ext
        · funext i
          by_cases h9 : i = 9
          · subst i; simp [a1, a0, state, DS.set, ho]
          · simp [a1, a0, state, DS.set, h9]
        all_goals rfl
      rw [hnext] at e2
      have ei := ih [] pre suffix (out ++ [false]) hin
      have he := Ex.loopT (c := Cnd.lt (0 : Fin 12) 9) (by decide : (0 : Fin 12) ≠ 9)
        (show (Cnd.lt (0 : Fin 12) 9).eval a0 = true by simp [Cnd.eval, a0, state, hz]) (Ex.seq e1 e2) ei
      convert he.mono (m := 12 * (n + 1) + 2) (by omega) using 1 <;>
        simp [body, a0, resize, List.append_assoc]
    | cons bit bits =>
      let a0 := state a (pre.length + 1) 1 (n + 1) out
      have e1 : Ex C (.op (.rdK 1)) a0 (OutputParsing.readState 1 a0 bit) 1 := by
        apply OutputParsing.read_bit C (1 : Fin 12) a0 bit
        · simp [a0, state, hin, frame]
        · change a.kout.getD (pre.length + 1) false = bit
          rw [hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
          simp [frame]
      let a1 := OutputParsing.readState (1 : Fin 12) a0 bit
      have e2 := send_read_bit C (0 : Fin 12) 1 (by decide) false a1 bit
        (by simp [a1, OutputParsing.readState, a0, state, DS.set, hz])
        (by simp [a1, OutputParsing.readState]) (by simp)
      let a2 : State := {a1 with out := out ++ [bit]}
      have hin' : a.kout = (pre ++ [true, bit]) ++ frame bits ++ suffix := by
        simpa [frame, List.append_assoc] using hin
      have hpos : a2.kc = (pre ++ [true, bit]).length := by simp [a2, a1, OutputParsing.readState, a0, state]
      have e3 : Ex C (.op (.rdK 1)) a2 (OutputParsing.readState 1 a2 (!bits.isEmpty)) 1 := by
        apply OutputParsing.read_bit C (1 : Fin 12) a2 (!bits.isEmpty)
        · change a2.kc < a.kout.length
          rw [hpos, hin']
          have hf := Parsing.frame_nonempty bits
          simp only [List.length_append]
          omega
        · change a.kout.getD a2.kc false = _
          rw [hpos, hin', List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
          simpa using Parsing.frame_first bits suffix
      let a3 := OutputParsing.readState (1 : Fin 12) a2 (!bits.isEmpty)
      have ecopy := Ex.iteT (C := C) (c := Cnd.lt (0 : Fin 12) 1) (t := .op (.emit false))
        (by decide : (0 : Fin 12) ≠ 1) (show (Cnd.lt (0 : Fin 12) 1).eval a0 = true by simp [Cnd.eval, a0, state, hz])
        (Ex.seq e1 (Ex.seq e2 e3))
      have e4 := Ex.op (OpEx.sub (C := C) (9 : Fin 12) 10 a3 (by decide)
        (by simp [a3, a2, a1, OutputParsing.readState, a0, state, DS.set, ho]))
      have hnext : a3.set 9 (a3.env 9 - a3.env 10) =
          state a ((pre ++ [true, bit]).length + 1) (!bits.isEmpty).toNat n (out ++ [bit]) := by
        apply state_ext
        · funext i
          by_cases h9 : i = 9
          · subst i; simp [a3, a2, a1, OutputParsing.readState, a0, state, DS.set, ho]
          · by_cases h1 : i = 1
            · subst i; simp [a3, OutputParsing.readState, state, DS.set]
            · simp [a3, a2, a1, OutputParsing.readState, a0, state, DS.set, h9, h1]
        all_goals simp [a3, a2, a1, OutputParsing.readState, a0, state]
      rw [hnext] at e4
      have ei := ih bits (pre ++ [true, bit]) suffix (out ++ [bit]) hin'
      have he := Ex.loopT (c := Cnd.lt (0 : Fin 12) 9) (by decide : (0 : Fin 12) ≠ 9)
        (show (Cnd.lt (0 : Fin 12) 9).eval a0 = true by simp [Cnd.eval, a0, state, hz]) (Ex.seq ecopy e4) ei
      have hfinal : state a ((pre ++ [true, bit]).length + 2 * min n bits.length + 1)
          (!(bits.drop n).isEmpty).toNat 0 ((out ++ [bit]) ++ resize bits n) =
          state a (pre.length + 2 * min (n + 1) (bit :: bits).length + 1)
            (!((bit :: bits).drop (n + 1)).isEmpty).toNat 0 (out ++ resize (bit :: bits) (n + 1)) := by
        congr 1
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · simp [resize, List.append_assoc]
      rw [hfinal] at he
      exact he.mono (by omega)

theorem runs (C : Ctx) (a : State) (hz : a.env 0 = 0) (ho : a.env 10 = 1)
    (n : ℕ) (hn : a.env 9 = n) (bits pre suffix : List Bool)
    (hin : a.kout = pre ++ frame bits ++ suffix) (hip : a.kc = pre.length) :
    Ex C script a
      (state a (pre.length + 2 * min n bits.length + 1) (!(bits.drop n).isEmpty).toNat 0 (a.out ++ resize bits n))
      (12 * n + 4) := by
  have er : Ex C (.op (.rdK 1)) a (OutputParsing.readState 1 a (!bits.isEmpty)) 1 := by
    apply OutputParsing.read_bit C (1 : Fin 12) a (!bits.isEmpty)
    · rw [hip, hin]
      simp only [List.length_append]
      have hf := Parsing.frame_nonempty bits
      omega
    · rw [hip, hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simpa using Parsing.frame_first bits suffix
  have heq : OutputParsing.readState 1 a (!bits.isEmpty) = state a (pre.length + 1) (!bits.isEmpty).toNat n a.out := by
    apply state_ext
    · funext i
      by_cases h1 : i = 1
      · subst i; simp [OutputParsing.readState, state, DS.set]
      · by_cases h9 : i = 9
        · subst i; simp [OutputParsing.readState, state, DS.set, hn]
        · simp [OutputParsing.readState, state, DS.set, h1, h9]
    all_goals simp [OutputParsing.readState, state, hip]
  rw [heq] at er
  exact (Ex.seq er (loop_runs C a hz ho n bits pre suffix a.out hin)).mono (by omega)

end NearCubicGates.Adapters.Code.PaddedOutput
