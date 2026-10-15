import Proof.Amplification.RecoveryCompactFinish

/-! The34-copy endpoint is exactly the native155 checker input after one
paid finishing transition. The first table is used uniformly in both flat
and nested requests; both valuation copies retain the same original word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankSlots (j : Fin 155) : Fin 493 := j.natAdd 338
theorem bankSlots_injective : Function.Injective bankSlots := by
  intro i j he
  exact Fin.ext (by have h:=congrArg Fin.val he; simp [bankSlots] at h; omega)

theorem prior_blank (bits word innerBits outerBits : List Bool) (n m : Nat)
    (a : Fin 493→List Bool) (ha : ∀ (i : Fin 493),338 ≤ i.val → a i=[]) :
    stage34 bits word innerBits outerBits n m a 404=[] ∧
      stage34 bits word innerBits outerBits n m a 473=[] := by
  simp [stage34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,ha 404 (by decide),ha 473 (by decide)]

theorem bank_inner_tapes (bits word innerBits outerBits : List Bool) (n m : Nat)
    (a : Fin 493→List Bool) (ha : ∀ (i : Fin 493),338 ≤ i.val → a i=[]) (j : Fin 69) :
    finishTapes (stage34 bits word innerBits outerBits n m a) (bankSlots (j.castAdd 86))=
      tapes bits word (buffer innerBits word) (buffer outerBits word) n m (j.castAdd 86) := by
  fin_cases j <;> simp [finishTapes,bankSlots,stage34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,
    tapes,childTapes,baseTapes,lookupTapes,RecoveryColdSAT.tapes,Fin.addCases,CompareMachine.word]
  all_goals exact ha _ (by decide)

theorem bank_outer_tapes (bits word innerBits outerBits : List Bool) (n m : Nat)
    (a : Fin 493→List Bool) (ha : ∀ (i : Fin 493),338 ≤ i.val → a i=[]) (j : Fin 86) :
    finishTapes (stage34 bits word innerBits outerBits n m a) (bankSlots (j.natAdd 69))=
      tapes bits word (buffer innerBits word) (buffer outerBits word) n m (j.natAdd 69) := by
  fin_cases j <;> simp [finishTapes,bankSlots,stage34,stage33,stage32,stage31,stage30,stage29,stage28,stage27,stage26,stage25,stage24,stage23,stage22,stage21,stage20,stage19,stage18,stage17,stage16,stage15,stage14,stage13,stage12,stage11,stage10,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,stage0,put,
    tapes,childTapes,baseTapes,lookupTapes,RecoveryColdSAT.tapes,Fin.addCases,CompareMachine.word]
  all_goals exact ha _ (by decide)

theorem bank_tapes (bits word innerBits outerBits : List Bool) (n m : Nat)
    (a : Fin 493→List Bool) (ha : ∀ (i : Fin 493),338 ≤ i.val → a i=[]) :
    (fun j=>finishTapes (stage34 bits word innerBits outerBits n m a) (bankSlots j))=
      tapes bits word (buffer innerBits word) (buffer outerBits word) n m := by
  funext j
  exact Fin.addCases (m:=69) (n:=86)
    (bank_inner_tapes bits word innerBits outerBits n m a ha)
    (bank_outer_tapes bits word innerBits outerBits n m a ha) j

theorem bank_heads (h : Fin 493→Nat) (hh : ∀ (i : Fin 493),338 ≤ i.val → h i=0) :
    (fun j=>finishHeads h (bankSlots j))=heads := by
  funext j
  fin_cases j <;> simp [finishHeads,finishing,bankSlots,heads]
  all_goals exact hh _ (by decide)

theorem bank_native {s : Nat} (bits word innerBits outerBits : List Bool) (n m : Nat)
    (h : Fin 493→Nat) (a : Fin 493→List Bool) (q : Fin s)
    (hh : ∀ (i : Fin 493),338 ≤ i.val → h i=0)
    (ha : ∀ (i : Fin 493),338 ≤ i.val → a i=[]) :
    ZeroPadding.config (caps bits word)
      ⟨q,(fun j=>finishHeads h (bankSlots j)),
        (fun j=>finishTapes (stage34 bits word innerBits outerBits n m a) (bankSlots j))⟩=
      (state bits word (buffer innerBits word) (buffer outerBits word) n m).cfg q := by
  rw [bank_tapes bits word innerBits outerBits n m a ha,bank_heads h hh]
  exact native_layout bits word (buffer innerBits word) (buffer outerBits word) n m q

end NearCubicWires.RepairOrdinary.RecoveryColdCompact

