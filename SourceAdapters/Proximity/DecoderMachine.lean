import SourceAdapters.Proximity.DecoderBankDock
import SourceAdapters.Code.Composition

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": an actual ordinary target Circuit.word to native
circuit-descriptor transducer, including paid input-size prefix and bank loading. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.DecoderBank

open NearCubicWires NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open CloseoutWitness

noncomputable def decode : WMX 1381 16 := .seq (.wm prepare) (.mach Oracle.machine decoderSlots)

def decodeCost (C : Circuit) := prepareCost C + 1 + paddedBudget C

theorem decode_run (C : Circuit) : ∃ τ : State,
    WXExec (cap C) decode (initial C) τ (decodeCost C) ∧
      τ.st 1299 = PCPPNative.descriptor C.D := by
  obtain ⟨out, ⟨r, hr, ht, _, _⟩, hd⟩ := padded_ready C
  have hinput : (fun j => (prepared C).st (decoderSlots j)) =
      Oracle.coldInput (decoderGuard C) (decoderBits C) (PhysicalFields.paddedBits C.n) :=
    funext (prepared_tapes C)
  have hr' : run Oracle.machine (paddedBudget C) (fun j => (prepared C).st (decoderSlots j)) = some r := by
    rw [hinput]
    exact hr
  obtain ⟨τ, he, dock⟩ := WXExec.mach_run (cap C) decoderSlots_injective (prepared C) (prepared_heads C) hr'
  refine ⟨τ, WXExec.seq (WXExec.wm (prepare_run C)) he, ?_⟩
  calc
    τ.st 1299 = r.final.tapes Oracle.descriptorSlot := dock.st Oracle.descriptorSlot
    _ = out Oracle.descriptorSlot := congrFun ht Oracle.descriptorSlot
    _ = PCPPNative.descriptor C.D := hd

def decodeCoefficient : ℕ := 100000 + 2 * (40000000000000000000000 * 18 ^ 25)

theorem decode_cost (C : Circuit) :
    2 * decodeCost C + 2 ≤ decodeCoefficient * (C.word.length + 1) ^ 25 := by
  have hp := prepare_cost C
  have hd := padded_budget C
  have he : (C.word.length + 1) ^ 2 ≤ (C.word.length + 1) ^ 25 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1 ≤ (C.word.length + 1) ^ 25 := Nat.one_le_pow _ _ (by omega)
  unfold decodeCost decodeCoefficient
  nlinarith

noncomputable def prefixedNativeWordFunction : WordFunction Circuit inputWord
    (fun C => PCPPNative.descriptor C.D)
    (fun C => decodeCoefficient * (C.word.length + 1) ^ 25) :=
  wordFunction_of_ideal (Request := Circuit) (input := inputWord)
    (output := fun C => PCPPNative.descriptor C.D) decode 1299 (by decide) cap
    (fun _ _ => 0) decodeCost decode_cost (fun C => ⟨rfl, decode_run C⟩)

noncomputable def targetPrefixWordFunction : WordFunction Circuit Circuit.word
    (fun C => frame (inputWord C)) (fun C => 10000 * (C.word.length + 1) ^ 2) where
  program := LengthPrefix.polynomialWordFunction.program
  realizes C := LengthPrefix.polynomialWordFunction.realizes C.word

/-- Full actual target codec. Its polynomial includes physical preparation,
all decoder steps and ordinary head resets, on the original target input. -/
noncomputable def targetNativeWordFunction : WordFunction Circuit Circuit.word
    (fun C => PCPPNative.descriptor C.D)
    (fun C => (20005 + 2 * decodeCoefficient) * (C.word.length + 1) ^ 25) :=
  (Code.composeFramed targetPrefixWordFunction prefixedNativeWordFunction).enlargeBudget
    (fun C => by
      have he : (C.word.length + 1) ^ 2 ≤ (C.word.length + 1) ^ 25 :=
        Nat.pow_le_pow_right (by omega) (by decide)
      have h1 : 1 ≤ (C.word.length + 1) ^ 25 := Nat.one_le_pow _ _ (by omega)
      nlinarith)

end NearCubicGates.Adapters.Proximity.DecoderBank
