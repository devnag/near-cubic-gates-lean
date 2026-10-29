import SourceAdapters.Proximity.LiteralSequence
import SourceAdapters.Proximity.SourceCallee
import SourceAdapters.Joins.TrimVerifier

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": exact raw and translated block
data, with a common literal count independent of the source decision table. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.TseitinCNF NearCubicGates.Published.CW19Proximity

def blockLiterals {q : ℕ} (predicate : BitInput q → Bool) : List EncodedLiteral :=
  (predicateBlock predicate).flatten

theorem flatten_three_length (clauses : List (List (Bool × ℕ)))
    (h : ∀ clause ∈ clauses, clause.length = 3) : clauses.flatten.length = 3 * clauses.length := by
  induction clauses with
  | nil => simp
  | cons clause clauses ih =>
    have hc := h clause (by simp)
    have ht := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hc, ht]
    omega

theorem blockLiterals_length {q : ℕ} (predicate : BitInput q → Bool) :
    (blockLiterals predicate).length = 3 * predicateBlockSize q := by
  rw [blockLiterals, flatten_three_length _ (predicateBlock_three predicate), predicateBlock_length]

theorem blockLiterals_index {q : ℕ} (predicate : BitInput q → Bool) (literal : EncodedLiteral)
    (h : literal ∈ blockLiterals predicate) : literal.2 < blockVariableBound q := by
  obtain ⟨clause, hc, hl⟩ := List.mem_flatten.mp h
  exact predicateBlock_indices predicate clause hc literal hl

theorem blockLiterals_raw {q : ℕ} (predicate : BitInput q → Bool) :
    LiteralStep.rawWords (blockLiterals predicate) = blockWord predicate := by
  change (predicateBlock predicate).flatten.flatMap LiteralStep.rawLiteral =
    (predicateBlock predicate).flatMap (fun clause => clause.flatMap LiteralStep.rawLiteral)
  induction predicateBlock predicate with
  | nil => rfl
  | cons clause clauses ih => simp only [List.flatten_cons, List.flatMap_append, List.flatMap_cons, ih]

theorem translated_address_pair {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (index : ℕ) :
    AddressTranslation.translatedAddress (fun j => SourceCallee.addressPair (V.query coins j)) coins.val q index =
      SourceCallee.addressPair (localAddress V coins index) := by
  by_cases h : index < q
  · have hp := SourceCallee.padded_address V coins ⟨index, h⟩
    simp only [AddressTranslation.translatedAddress, h, if_true, localAddress, dif_pos]
    rw [hp]
    have renamed (a : QueryAddress n) :
        ((SourceCallee.addressPair a).1, if (SourceCallee.addressPair a).1 then
          2 * (SourceCallee.addressPair a).2 else (SourceCallee.addressPair a).2) =
        SourceCallee.addressPair (renamedAddress a) := by cases a <;> rfl
    exact renamed _
  · simp [AddressTranslation.translatedAddress, h, localAddress, SourceCallee.addressPair]

theorem translated_literal_word {n q : ℕ} (V : NonadaptiveVerifier n q)
    (coins : Fin (2 ^ V.randomBits)) (literal : EncodedLiteral) :
    LiteralStep.globalWord (fun j => SourceCallee.addressPair (V.query coins j)) coins.val q literal =
      (Joins.trimQueryFields (translatedLiteral V coins literal)).flatMap natWord := by
  unfold LiteralStep.globalWord
  rw [translated_address_pair]
  cases h : localAddress V coins literal.2 <;>
    simp [SourceCallee.addressPair, LiteralFields.literalWord, Joins.trimQueryFields, translatedLiteral, h]

end NearCubicGates.Adapters.Proximity
