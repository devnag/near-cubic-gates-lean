import Proof.Assembly.FramingSpec

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace FramingPortClasses
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
open DatumCopier

/-! ## 1. The three port classes are pairwise distinct.
`target` and `counter` are `natAdd t` of `0` and `1`, so their values are `t`
and `t+1`; every field slot is `castAdd 2` of some `k : Fin t`, so its value is
`k.val < t`. -/

theorem target_ne_counter (t : Nat) : target t ≠ counter t := by
  intro h
  have hv := congrArg Fin.val h
  simp only [target, counter, Fin.val_natAdd] at hv
  omega

theorem slot_ne_target (t : Nat) (k : Fin t) : k.castAdd 2 ≠ target t := by
  intro h
  have hv := congrArg Fin.val h
  have hk := k.isLt
  simp only [target, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem slot_ne_counter (t : Nat) (k : Fin t) : k.castAdd 2 ≠ counter t := by
  intro h
  have hv := congrArg Fin.val h
  have hk := k.isLt
  simp only [counter, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem mem_fieldSlots {t : Nat} {j : Fin (t+2)} (h : j ∈ DatumCopier.fieldSlots t) :
    ∃ k : Fin t, j = k.castAdd 2 := by
  obtain ⟨k, _, hk⟩ := List.mem_map.mp h
  exact ⟨k, hk.symm⟩

/-! ## 2. The entry head vector and bank at each port class. -/

theorem heads_slot (t : Nat) (out : List Bool) (k : Fin t) :
    heads t out (k.castAdd 2) = 0 := by
  simp only [heads, Fin.addCases_left]

theorem heads_target (t : Nat) (out : List Bool) :
    heads t out (target t) = out.length := by
  simp only [heads, target, Fin.addCases_right, Matrix.cons_val_zero]

theorem heads_counter (t : Nat) (out : List Bool) :
    heads t out (counter t) = 0 := by
  simp only [heads, counter, Fin.addCases_right, Matrix.cons_val_one, Matrix.cons_val_zero]

theorem fields_slot {t : Nat} (A : Fin t → List Bool) (k : Fin t) :
    fields A (k.castAdd 2) = A k := by
  simp only [fields, Fin.addCases_left]

theorem bank_slot {t : Nat} (A : Fin t → List Bool) (out : List Bool) (cap : Nat) (k : Fin t) :
    bank A out cap (k.castAdd 2) = frame (A k) := by
  simp only [bank, Fin.addCases_left]

theorem bank_target {t : Nat} (A : Fin t → List Bool) (out : List Bool) (cap : Nat) :
    bank A out cap (target t) = out := by
  simp only [bank, target, Fin.addCases_right, Matrix.cons_val_zero]

theorem bank_counter {t : Nat} (A : Fin t → List Bool) (out : List Bool) (cap : Nat) :
    bank A out cap (counter t) = List.replicate cap false := by
  simp only [bank, counter, Fin.addCases_right, Matrix.cons_val_one, Matrix.cons_val_zero]

/-! ## 3. The emitted stream is exactly the descriptor word.
`DatumCopier.fieldSlots` is a `map`, so `stream` over it is a `flatMap` over `List.finRange t`
after `List.flatMap_map`; `fields` at a field slot is `A` by `addCases_left`. -/

theorem stream_eq_word {t : Nat} (A : Fin t → List Bool) :
    stream (fields A) (DatumCopier.fieldSlots t) = word A := by
  simp only [stream, DatumCopier.fieldSlots, word, List.flatMap_map, fields, Fin.addCases_left]

theorem update_heads {t : Nat} (out w : List Bool) :
    Function.update (heads t out) (target t) (out ++ w).length = heads t (out ++ w) := by
  funext i
  refine Fin.addCases (motive := fun i =>
    Function.update (heads t out) (target t) (out ++ w).length i = heads t (out ++ w) i)
    (fun k => ?_) (fun k => ?_) i
  · rw [Function.update_of_ne (slot_ne_target t k), heads_slot, heads_slot]
  · have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · change Function.update (heads t out) (target t) (out ++ w).length (target t) =
        heads t (out ++ w) (target t)
      rw [Function.update_self, heads_target]
    · change Function.update (heads t out) (target t) (out ++ w).length (counter t) =
        heads t (out ++ w) (counter t)
      rw [Function.update_of_ne (Ne.symm (target_ne_counter t)), heads_counter, heads_counter]

theorem update_bank {t : Nat} (A : Fin t → List Bool) (out w : List Bool) (cap : Nat) :
    Function.update (bank A out cap) (target t) (out ++ w) = bank A (out ++ w) cap := by
  funext i
  refine Fin.addCases (motive := fun i =>
    Function.update (bank A out cap) (target t) (out ++ w) i = bank A (out ++ w) cap i)
    (fun k => ?_) (fun k => ?_) i
  · rw [Function.update_of_ne (slot_ne_target t k), bank_slot, bank_slot]
  · have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · change Function.update (bank A out cap) (target t) (out ++ w) (target t) =
        bank A (out ++ w) cap (target t)
      rw [Function.update_self, bank_target]
    · change Function.update (bank A out cap) (target t) (out ++ w) (counter t) =
        bank A (out ++ w) cap (counter t)
      rw [Function.update_of_ne (Ne.symm (target_ne_counter t)), bank_counter, bank_counter]

/-! ## 5. The unpadded run: one application of the field-list worker. -/

theorem framing_run {t : Nat} (A : Fin t → List Bool) (out : List Bool) (cap : Nat)
    (hcap : ∀ k, 2*(A k).length+1 ≤ cap) :
    Step (machine t) (budget A) (heads t out) (bank A out cap)
      (heads t (out ++ word A)) (bank A (out ++ word A) cap) := by
  obtain ⟨r, hr, hh, ht, _⟩ :=
    list_run (target t) (counter t) (DatumCopier.fieldSlots t) (fields A)
      (target_ne_counter t)
      (fun j hj => by
        obtain ⟨k, rfl⟩ := mem_fieldSlots hj
        exact slot_ne_target t k)
      (fun j hj => by
        obtain ⟨k, rfl⟩ := mem_fieldSlots hj
        exact slot_ne_counter t k)
      out cap (heads t out) (bank A out cap)
      (fun j hj => by
        obtain ⟨k, rfl⟩ := mem_fieldSlots hj
        exact heads_slot t out k)
      (heads_target t out) (heads_counter t out)
      (fun j hj => by
        obtain ⟨k, rfl⟩ := mem_fieldSlots hj
        rw [bank_slot, fields_slot])
      (bank_target A out cap) (bank_counter A out cap)
      (fun j hj => by
        obtain ⟨k, rfl⟩ := mem_fieldSlots hj
        rw [fields_slot]
        exact hcap k)
  have hcfg : RecoveryCalls.restarted (listProgram (target t) (counter t) (DatumCopier.fieldSlots t))
      (heads t out) (bank A out cap)
      = (⟨(machine t).start, heads t out, bank A out cap⟩ :
          Configuration (t+2) (states (DatumCopier.fieldSlots t))) := rfl
  rw [hcfg] at hr
  rw [stream_eq_word] at hh ht
  rw [update_heads] at hh
  rw [update_bank] at ht
  exact Step.of_run hr hh ht

/-! ## 6. Reusable field capacities: the padded bank is the padded unpadded bank.
`reserves F` is `F` on the fields and `0` on the descriptor and the counter, and
`ZeroPadding.pad 0 x = x`, so padding the run by `reserves F` lands exactly on
`paddedBank F`. No capacity is measured and no tape is shortened. -/

theorem padded_eq {t : Nat} (F : Fin t → Nat) (A : Fin t → List Bool)
    (out : List Bool) (cap : Nat) :
    (fun i => ZeroPadding.pad (reserves F i) (bank A out cap i)) = paddedBank F A out cap := by
  funext i
  refine Fin.addCases (motive := fun i =>
    ZeroPadding.pad (reserves F i) (bank A out cap i) = paddedBank F A out cap i)
    (fun k => ?_) (fun k => ?_) i
  · simp only [reserves, bank, paddedBank, Fin.addCases_left]
  · simp only [reserves, bank, paddedBank, Fin.addCases_right, ZeroPadding.pad_zero]

theorem padded_framing_run {t : Nat} (F : Fin t → Nat) (A : Fin t → List Bool)
    (out : List Bool) (cap : Nat) (hcap : ∀ k, 2*(A k).length+1 ≤ cap) :
    Step (machine t) (budget A) (heads t out) (paddedBank F A out cap)
      (heads t (out ++ word A)) (paddedBank F A (out ++ word A) cap) :=
  (((framing_run A out cap hcap).pad (reserves F)).congr_in rfl
      (padded_eq F A out cap)).congr rfl (padded_eq F A (out ++ word A) cap)

/-! ## 7. The consumer's own word is this word.
`Datum.word a d` unfolds to `ReloadStream.stream (ReloadCore.input …) (List.finRange _)`,
which is `(List.finRange _).flatMap (fun j => frame (…)) = word (datumFields a d)`. -/

theorem datum_word_eq (a : WilliamsAlgorithm) (d : P1TopDownPaidReusable.Datum) :
    d.word a = word (datumFields a d) := rfl

/-! ## 8. The assigned law. -/

theorem correct : DatumCopier.Correct := by
  intro a d F out cap hcap
  have h := padded_framing_run F (datumFields a d) out cap hcap
  rw [← datum_word_eq a d] at h
  exact h

end FramingPortClasses
