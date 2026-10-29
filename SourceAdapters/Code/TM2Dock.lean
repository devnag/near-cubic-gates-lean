import SourceAdapters.Joins.OrdinaryToTM2
import SourceAdapters.Code.FinitePatch

/-!
`app:sources`, "Uniform three-query PCPP and code interfaces": the two code algorithms on their exact companion encodings.
This dock consumes actual ordinary program witnesses and their input-length
budgets. The ordinary program witnesses are explicit parameters of this theorem.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Published.CW19Code
open NearCubicGates.Adapters.Joins

theorem encoder_tm2_of_ordinary (hX1 : OrdinaryToTM2PolyTime) (E : LinearCodeFamily)
    (budget : MessageRequest → ℕ)
    (hprogram : Nonempty (WordFunction MessageRequest messageWord
      (fun p => List.ofFn (E.enc p.1 p.2.val)) budget))
    (hbudget : ∃ K e : ℕ, ∀ p, budget p ≤ K * ((messageWord p).length + 1) ^ e) :
    Nonempty (Turing.TM2ComputableInPolyTime messageWord (fun word : List Bool => word)
      (fun p => List.ofFn (E.enc p.1 p.2.val))) :=
  hX1 messageWord (fun word : List Bool => word) _ budget hprogram hbudget

theorem decoder_tm2_of_ordinary (hX1 : OrdinaryToTM2PolyTime) (E : LinearCodeFamily)
    (budget : CodewordRequest E → ℕ)
    (hprogram : Nonempty (WordFunction (CodewordRequest E) (codewordWord E)
      (fun p => List.ofFn (E.decoder p.1 p.2.val)) budget))
    (hbudget : ∃ K e : ℕ, ∀ p, budget p ≤ K * ((codewordWord E p).length + 1) ^ e) :
    Nonempty (Turing.TM2ComputableInPolyTime (codewordWord E) (fun word : List Bool => word)
      (fun p => List.ofFn (E.decoder p.1 p.2.val))) :=
  hX1 (codewordWord E) (fun word : List Bool => word) _ budget hprogram hbudget

/-- The full consumer dock. The source mathematics is proved by
`patched_mathematics`; the two actual ordinary algorithms remain hypotheses. -/
theorem efficientLinearCode_of_ordinary (hX1 : OrdinaryToTM2PolyTime)
    (F : BinaryFamily) (onset rate : ℕ) (distance radius : ℝ)
    (D : PromisedDecoder F onset radius) (hlinear : IsLinear F)
    (hd : 0 < distance) (hr : 0 < radius) (hmin : MinimumDistance F onset distance)
    (hrate : ∀ k, onset ≤ k → F.length k ≤ rate * k)
    (encBudget : MessageRequest → ℕ)
    (decBudget : CodewordRequest (patchedFamily F D) → ℕ)
    (henc : Nonempty (WordFunction MessageRequest messageWord
      (fun p => List.ofFn ((patchedFamily F D).enc p.1 p.2.val)) encBudget))
    (hencBudget : ∃ K e : ℕ, ∀ p, encBudget p ≤ K * ((messageWord p).length + 1) ^ e)
    (hdec : Nonempty (WordFunction (CodewordRequest (patchedFamily F D)) (codewordWord (patchedFamily F D))
      (fun p => List.ofFn ((patchedFamily F D).decoder p.1 p.2.val)) decBudget))
    (hdecBudget : ∃ K e : ℕ, ∀ p, decBudget p ≤ K * ((codewordWord (patchedFamily F D) p).length + 1) ^ e) :
    EfficientLinearCodeLiteral := by
  obtain ⟨hr0, hrd, hd1, hlength, hsupport, hdistance, hdecode⟩ :=
    patched_mathematics F onset rate distance radius D hlinear hd hr hmin hrate
  exact ⟨patchedFamily F D, codeDistance onset rate distance, codeRadius onset rate distance radius,
    hr0, hrd, hd1, hlength, hsupport, hdistance, hdecode,
    encoder_tm2_of_ordinary hX1 _ encBudget henc hencBudget,
    decoder_tm2_of_ordinary hX1 _ decBudget hdec hdecBudget⟩

end NearCubicGates.Adapters.Code
