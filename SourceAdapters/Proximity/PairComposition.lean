import SourceAdapters.Proximity.OrdinaryCalls
import SourceAdapters.Code.PairTransform
import SourceAdapters.Code.Retained

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": paid ordinary pairing, retention and first-field
application in the source polynomial-time convention. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Published.CW19Proximity

theorem source_retained_polynomial {A : Type} (input output : A → List Bool)
    (h : SourcePolyTime input output) :
    SourcePolyTime input (fun a => frame (input a) ++ frame (output a)) := by
  obtain ⟨K, e, ⟨P⟩⟩ := source_framed_polynomial input output h
  exact ⟨46 * K + 152, e + 1, ⟨(Code.Retained.wordFunction P).enlargeBudget
    (Code.Retained.retainedBudget_poly K e (fun _ => le_rfl))⟩⟩

theorem source_map_first_polynomial {A : Type} (input output : A → List Bool)
    (h : SourcePolyTime input output) :
    SourcePolyTime (fun r : A × List Bool => frame (input r.1) ++ frame r.2)
      (fun r => frame (output r.1) ++ frame r.2) := by
  obtain ⟨K, e, ⟨P⟩⟩ := source_framed_polynomial input output h
  exact ⟨46 * K + 220, e + 1, ⟨(Code.PairTransform.mapFirst P).enlargeBudget
    (Code.PairTransform.mapBudget_poly_of_source K e (fun _ => le_rfl))⟩⟩

theorem source_concatenate_polynomial :
    SourcePolyTime (fun p : List Bool × List Bool => frame p.1 ++ frame p.2) (fun p => p.1 ++ p.2) := by
  refine ⟨100000, 1, ⟨?_⟩⟩
  exact { program := Code.PairTransform.concatenate.program
          realizes := fun p => by
            have h := Code.PairTransform.concatenate.realizes p
            unfold Code.PairTransform.pairWord at h
            simpa only [pow_one] using h }

end NearCubicGates.Adapters.Proximity
