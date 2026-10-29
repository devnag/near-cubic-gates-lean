import SourceAdapters.Proximity.HonestPreparedInput
import SourceAdapters.Proximity.TrimSizes
import SourceAdapters.Joins.HonestRestriction

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": every field parsed by the honest initializer is
charged to the exact prepared word, including all binary address digits. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestPrepared

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

def word (source bits : List Bool) (records : List ℕ) : List Bool :=
  natWord source.length ++ source ++ frame bits ++ natWord records.length ++ records.flatMap natWord

def sourcePrefix (source bits : List Bool) (records : List ℕ) : List Bool :=
  natWord (word source bits records).length ++ natWord source.length

theorem word_prepared {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (p : AcceptedSourceInput) :
    word (sourceCircuitWord p.1) (List.ofFn p.2.val) (trimSortedAddresses (clauseTrimRequest V p.1)) =
      preparedHonestInput V p := by
  simp only [word, trimSortedAddresses, Finset.length_sort, preparedHonestInput, trimAddressWord,
    List.append_assoc]

theorem word_bounds (source bits : List Bool) (records : List ℕ) :
    let N := (word source bits records).length
    source.length ≤ N ∧ bits.length ≤ N ∧ records.length ≤ N ∧
    (natWord source.length).length ≤ N ∧ (records.flatMap natWord).length ≤ N ∧
    ∀ x ∈ records, natBitLength x ≤ N := by
  have hc := Trim.fieldWords_count_le records
  dsimp only [word]
  simp only [List.length_append, frame_length]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro x hx
  have h := Trim.field_bitLength_le hx
  omega

end NearCubicGates.Adapters.Proximity.HonestPrepared
