import SourceAdapters.Proximity.SourceCalls
import SourceAdapters.Proximity.AddressLengths

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": ordinary source programs compose through paid raw
output framing. Polynomial output length follows from the actual first run. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins NearCubicGates.Published.CW19Proximity

theorem source_polytime_comp (hX8 : CappedWordRun) {Request : Type}
    (input middle output : Request → List Bool)
    (first : SourcePolyTime input middle) (second : SourcePolyTime middle output) :
    SourcePolyTime input output := by
  obtain ⟨A, d, hlen⟩ := source_output_length input middle first
  obtain ⟨K1, e1, ⟨P⟩⟩ := source_framed_polytime hX8 input middle first
  obtain ⟨K2, e2, ⟨Q⟩⟩ := second
  have hsecond : ∀ r, K2 * ((middle r).length + 1) ^ e2 ≤
      (K2 * (A + 1) ^ e2) * ((input r).length + 1) ^ (d * e2) := by
    intro r
    have hp : 1 ≤ ((input r).length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have hm : (middle r).length + 1 ≤ (A + 1) * ((input r).length + 1) ^ d := by
      have h := hlen r
      nlinarith
    calc
      _ ≤ K2 * ((A + 1) * ((input r).length + 1) ^ d) ^ e2 := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  obtain ⟨K, e, hb⟩ := Code.composeFramed_budget_poly input
    (fun r => K1 * ((input r).length + 1) ^ e1)
    (fun r => K2 * ((middle r).length + 1) ^ e2)
    ⟨K1, e1, fun _ => le_rfl⟩ ⟨K2 * (A + 1) ^ e2, d * e2, hsecond⟩
  exact ⟨K, e, ⟨(Code.composeFramed P Q).enlargeBudget hb⟩⟩

end NearCubicGates.Adapters.Proximity
