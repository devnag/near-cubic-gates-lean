import SourceAdapters.Code.CountedParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": actual reading of the target's framed little-endian
`Nat.bits` field. The source decoder's unary tuple is constructed later. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.BinaryParsing

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open CountedParsing

abbrev State := DS 12 0
abbrev Script := St 12 0

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih => rw [Nat.bits_append_bit n b h, value, ih, Nat.bit_val]; omega

def body : Script := .seq (.op (.rdI 1))
  (.seq (.ite (.lt 0 1) (.op (.add 2 3)) (.op (.zero 0)))
    (.seq (.op (.shl 3)) (.op (.rdI 1))))

def script : Script := .seq (.op (.rdI 1)) (.loop (.lt 0 1) body)

def state (a : State) (pos flag acc power : ℕ) : State :=
  {a with ip := pos, env := fun i => if i = 1 then flag else if i = 2 then acc else if i = 3 then power else a.env i}

private theorem loop_runs (C : Ctx) (a : State) (hz : a.env 0 = 0) :
    ∀ (bits pre suffix : List Bool) (acc power : ℕ), C.inp = pre ++ frame bits ++ suffix →
      acc + power * value bits < 2 ^ C.Wd → power * 2 ^ bits.length < 2 ^ C.Wd →
      Ex C (.loop (.lt 0 1) body) (state a (pre.length + 1) (!bits.isEmpty).toNat acc power)
        (state a (pre.length + 2 * bits.length + 1) 0 (acc + power * value bits) (power * 2 ^ bits.length))
        (10 * bits.length + 2) := by
  intro bits
  induction bits with
  | nil =>
    intro pre suffix acc power _ _ _
    simpa [state, value] using Ex.loopF (C := C) (c := Cnd.lt (0 : Fin 12) 1) (s := body)
      (a := state a (pre.length + 1) 0 acc power) (by decide : (0 : Fin 12) ≠ 1)
      (by simp [Cnd.eval, state, hz])
  | cons b bits ih =>
    intro pre suffix acc power hin hv hp
    let a0 := state a (pre.length + 1) 1 acc power
    have ht : (Cnd.lt (0 : Fin 12) 1).eval a0 = true := by simp [Cnd.eval, a0, state, hz]
    have e1 := read_at_prefix C (1 : Fin 12) a0 (pre ++ [true]) b (frame bits ++ suffix)
      (by simpa [frame, List.append_assoc] using hin) (by simp [a0, state])
    let a1 := readState (1 : Fin 12) a0 b
    have hadd : acc + power * b.toNat < 2 ^ C.Wd := by
      dsimp [value] at hv
      nlinarith
    have e2 : Ex C (.ite (.lt 0 1) (.op (.add 2 3)) (.op (.zero 0))) a1
        (a1.set 2 (acc + power * b.toNat)) 2 := by
      cases b with
      | false =>
        have heq : a1.set 0 0 = a1.set 2 (acc + power * false.toNat) := by
          apply state_ext <;> try rfl
          funext i
          by_cases h0 : i = 0
          · subst i; simp [a1, readState, a0, state, DS.set, hz]
          · by_cases h2 : i = 2
            · subst i; simp [a1, readState, a0, state, DS.set]
            · simp [DS.set, h0, h2]
        rw [← heq]
        exact Ex.iteF (by decide : (0 : Fin 12) ≠ 1) (by simp [Cnd.eval, a1, readState, a0, state, DS.set, hz])
          (Ex.op (OpEx.zero 0 a1))
      | true =>
        have he := Ex.op (OpEx.add (C := C) (2 : Fin 12) 3 a1 (by decide)
          (by simpa [a1, readState, a0, state, DS.set] using hadd))
        apply Ex.iteT (c := Cnd.lt (0 : Fin 12) 1) (by decide : (0 : Fin 12) ≠ 1) (by simp [Cnd.eval, a1, readState, a0, state, DS.set, hz])
        simpa [a1, readState, a0, state, DS.set] using he
    let a2 := a1.set 2 (acc + power * b.toNat)
    have hpow : 2 * power < 2 ^ C.Wd := by
      have ht : 1 ≤ 2 ^ bits.length := Nat.one_le_pow _ _ (by omega)
      simp only [List.length_cons, pow_succ] at hp
      nlinarith
    have e3 := Ex.op (OpEx.shl (C := C) (3 : Fin 12) a2
      (by simpa [a2, a1, readState, a0, state, DS.set] using hpow))
    let a3 := a2.set 3 (2 * a2.env 3)
    have hin1 : C.inp = (pre ++ [true, b]) ++ frame bits ++ suffix := by
      simpa [frame, List.append_assoc] using hin
    have hip : a3.ip = (pre ++ [true, b]).length := by simp [a3, a2, a1, readState, a0, state]
    have e4 : Ex C (.op (.rdI 1)) a3 (readState 1 a3 (!bits.isEmpty)) 1 := by
      apply read_bit C (1 : Fin 12) a3 (!bits.isEmpty)
      · rw [hip, hin1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hh := Parsing.frame_nonempty bits
        omega
      · rw [hip, hin1, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
        simpa using Parsing.frame_first bits suffix
    have he := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))
    have hnext : readState 1 a3 (!bits.isEmpty) = state a ((pre ++ [true, b]).length + 1)
        (!bits.isEmpty).toNat (acc + power * b.toNat) (2 * power) := by
      apply state_ext
      · funext i
        by_cases h1 : i = 1
        · subst i; simp [readState, state, DS.set]
        · by_cases h2 : i = 2
          · subst i; simp [a3, a2, a1, readState, a0, state, DS.set]
          · by_cases h3 : i = 3
            · subst i; simp [a3, a2, a1, readState, a0, state, DS.set]
            · simp [a3, a2, a1, readState, a0, state, DS.set, h1, h2, h3]
      all_goals simp [a3, a2, a1, readState, a0, state]
    rw [hnext] at he
    have ev : acc + power * b.toNat + 2 * power * value bits = acc + power * value (b :: bits) := by
      simp only [value]; ring
    have ep : 2 * power * 2 ^ bits.length = power * 2 ^ (b :: bits).length := by
      simp only [List.length_cons, pow_succ]; ring
    have ei := ih (pre ++ [true, b]) suffix (acc + power * b.toNat) (2 * power) hin1
      (by rw [ev]; exact hv) (by rw [ep]; exact hp)
    have h := Ex.loopT (c := Cnd.lt (0 : Fin 12) 1) (by decide : (0 : Fin 12) ≠ 1) ht he ei
    rw [ev, ep] at h
    have hpos : (pre ++ [true, b]).length + 2 * bits.length + 1 = pre.length + 2 * (b :: bits).length + 1 := by simp; omega
    rw [hpos] at h
    exact h.mono (by simp; omega)

theorem runs (C : Ctx) (a : State) (hz : a.env 0 = 0) (bits pre suffix : List Bool)
    (hin : C.inp = pre ++ frame bits ++ suffix) (hip : a.ip = pre.length)
    (hval : a.env 2 + a.env 3 * value bits < 2 ^ C.Wd)
    (hpow : a.env 3 * 2 ^ bits.length < 2 ^ C.Wd) :
    Ex C script a (state a (pre.length + 2 * bits.length + 1) 0
      (a.env 2 + a.env 3 * value bits) (a.env 3 * 2 ^ bits.length)) (10 * bits.length + 4) := by
  have e1 : Ex C (.op (.rdI 1)) a (readState 1 a (!bits.isEmpty)) 1 := by
    apply read_bit C (1 : Fin 12) a (!bits.isEmpty)
    · rw [hin, hip]
      simp only [List.length_append]
      have hh := Parsing.frame_nonempty bits
      omega
    · rw [hin, hip, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
      simpa using Parsing.frame_first bits suffix
  have heq : readState 1 a (!bits.isEmpty) = state a (pre.length + 1) (!bits.isEmpty).toNat (a.env 2) (a.env 3) := by
    apply state_ext
    · funext i
      by_cases h1 : i = 1
      · subst i; simp [readState, state, DS.set]
      · by_cases h2 : i = 2
        · subst i; simp [readState, state, DS.set]
        · by_cases h3 : i = 3
          · subst i; simp [readState, state, DS.set]
          · simp [readState, state, DS.set, h1, h2, h3]
    all_goals simp [readState, state, hip]
  rw [heq] at e1
  exact (Ex.seq e1 (loop_runs C a hz bits pre suffix (a.env 2) (a.env 3) hin hval hpow)).mono (by omega)

end NearCubicGates.Adapters.Code.BinaryParsing
