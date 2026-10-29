import SourceAdapters.Proximity.DecoderBankParse

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": every decoder bank field is produced by an actual
paid ordinary program. Physical frames and padded binary words retain zeros. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecoderBank

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.CheckedPCPP
open PhysicalFields

def bitsRegisters : Fin 8 ↪ Fin 16 := ⟨![8,1,2,3,4,5,6,7], by decide⟩
def arityRegisters : Fin 4 ↪ Fin 16 := ⟨![8,1,2,7], by decide⟩
def guardRegisters : Fin 4 ↪ Fin 16 := ⟨![9,1,2,7], by decide⟩

def binaryLoaded (C : Circuit) : State := (bitsLoaded C).sets 2 (frame (paddedBits C.n))
def unaryLoaded (C : Circuit) : State := (binaryLoaded C).sets 3 (List.replicate C.n true)
def guardCountLoaded (C : Circuit) : State := (unaryLoaded C).setv 9 (C.word.length + 1)
def prepared (C : Circuit) : State := (guardCountLoaded C).sets 1381 (frame (decoderGuard C))

def prepare : Script := .seq loadBits (.seq (writeBits 2 bitsRegisters)
  (.seq (writeRepeatTail 3 arityRegisters [true] [])
    (.seq (.inc 9) (writeRepeatTail 1381 guardRegisters (List.replicate 32 true) [false]))))

def prepareCost (C : Circuit) : ℕ := bitsCost C + 1000 * (C.n + 1) ^ 2 +
  35 * C.n + 438 * (C.word.length + 1) + 36

theorem prepare_run (C : Circuit) : WExec (cap C) prepare (initial C) (prepared C) (prepareCost C) := by
  have hn := arity_bound C
  have hb := NodeEmit.natBitLength_le C.n
  have e2 := write_bits (cap C) (2 : Fin 1382) bitsRegisters (bitsLoaded C)
    (by intro i hi; fin_cases i <;> simp_all [bitsRegisters, bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [bitsRegisters, bitsLoaded, afterArity]; unfold cap; omega)
  have e2' : WExec (cap C) (writeBits 2 bitsRegisters) (bitsLoaded C) (binaryLoaded C)
      (1000 * (C.n + 1) ^ 2) := by simpa [bitsRegisters, bitsLoaded, afterArity, binaryLoaded] using e2
  have e3 := write_repeat_tail (cap C) (3 : Fin 1382) arityRegisters [true] [] (binaryLoaded C)
    (by intro i hi; fin_cases i <;> simp_all [arityRegisters, binaryLoaded, bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [binaryLoaded, bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [binaryLoaded, bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [arityRegisters, binaryLoaded, bitsLoaded, afterArity]; unfold cap; omega)
  have hr : reps C.n [true] = List.replicate C.n true := by
    simpa using reps_ones C.n 1
  have e3' : WExec (cap C) (writeRepeatTail 3 arityRegisters [true] []) (binaryLoaded C) (unaryLoaded C)
      (35 * C.n + 8) := by
    simpa [arityRegisters, binaryLoaded, bitsLoaded, afterArity, unaryLoaded, hr] using e3
  have e4 := WExec.inc (cap := cap C) (9 : Fin 16) (unaryLoaded C)
    (by simp [unaryLoaded, binaryLoaded, bitsLoaded, afterArity, afterLength]; unfold cap; omega)
  have e4' : WExec (cap C) (.inc 9) (unaryLoaded C) (guardCountLoaded C) 3 := by
    simpa [guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded, afterArity, afterLength] using e4
  have e5 := write_repeat_tail (cap C) (1381 : Fin 1382) guardRegisters (List.replicate 32 true) [false]
    (guardCountLoaded C)
    (by intro i hi; fin_cases i <;> simp_all [guardRegisters, guardCountLoaded, unaryLoaded, binaryLoaded,
        bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [guardCountLoaded, unaryLoaded, binaryLoaded, bitsLoaded, afterArity, afterLength, initial, idealStart])
    (by simp [guardRegisters, guardCountLoaded]; unfold cap; omega)
  have e5' : WExec (cap C) (writeRepeatTail 1381 guardRegisters (List.replicate 32 true) [false])
      (guardCountLoaded C) (prepared C) (438 * (C.word.length + 1) + 21) := by
    change WExec (cap C) _ (guardCountLoaded C)
      ((guardCountLoaded C).sets 1381 (reps (C.word.length + 1) (List.replicate 32 true) ++ [false]))
      (438 * (C.word.length + 1) + 13 + 8) at e5
    rw [guard_word] at e5
    exact e5.cast (cap C) rfl (by omega)
  exact (WExec.seq (load_bits C) (WExec.seq e2' (WExec.seq e3' (WExec.seq e4' e5')))).cast
    (cap C) rfl (by unfold prepareCost; omega)

theorem prepare_cost (C : Circuit) : prepareCost C ≤ 30000 * (C.word.length + 1) ^ 2 := by
  have hb := bits_cost C
  have hn := arity_bound C
  have hn' : C.n + 1 ≤ 3 * (C.word.length + 1) := by omega
  have hs := Nat.pow_le_pow_left hn' 2
  unfold prepareCost
  nlinarith

end NearCubicGates.Adapters.Proximity.DecoderBank
