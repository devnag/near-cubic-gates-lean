import SourceAdapters.Proximity.Perfect
import SourceAdapters.Code.Source

/-!
# Input 9 with an efficient linear encoder

The three-query PCPP input needs of the linear code only its encoder (`imp:three-pcpp`, "The published proximity construction and its local gadget": the systematic parity-check
reduction checks `(x, Enc x)` and never decodes). `EfficientLinearEncoder` states that part: a constant-rate linear
code family of positive relative distance with a polynomial-time encoder. It is word for word the definition of the
same name in `NearCubicGates.PublishedSources.PCPP`, where the `threeQueryPCPP` field of `NineInputs` has type
`ThreeQuerySourceGroup = PerfectThreeQueryProximityLiteral ∧ EfficientLinearEncoder`; the adapter below is stated
with the copy here, which is the same definition.

`encoder_of_code` projects the complete code interface `EfficientLinearCodeLiteral` onto it (drop the decoding
radius, the support bound, the decoder and its machine), and `field9Encoder` gives the field from the two published
statements: CW19 Lemma 22 at half soundness (`Proximity.perfect_three_query_proximity`) and CW19 Lemma 26
(`Code.efficientLinearCode_of_lemma26`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Assembly

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP

/-- The encoder part of CW19 Lemma 27's code ("The published proximity construction and its local gadget"; `app:sources`, "Uniform three-query PCPP and code interfaces"): constant rate, relative distance
`distance > 0`, and a polynomial-time TM2 encoder. -/
def EfficientLinearEncoder : Prop :=
  ∃ E : LinearCodeFamily, ∃ distance : ℝ,
    0 < distance ∧ distance < 1 ∧
    (∃ K : ℕ, ∀ n, 2 ≤ n → E.length n ≤ K * (n + 1)) ∧
    (∀ n, 2 ≤ n → ∀ x y : BitInput n, x ≠ y →
      distance ≤ relativeHamming (E.enc n x) (E.enc n y)) ∧
    Nonempty (Turing.TM2ComputableInPolyTime messageWord
      (fun word : List Bool => word)
      (fun p => List.ofFn (E.enc p.1 p.2.val)))

/-- The complete code interface implies the encoder interface (`app:sources`, "Uniform three-query PCPP and code interfaces": the main result uses only the
encoder facts). -/
theorem encoder_of_code (h : EfficientLinearCodeLiteral) : EfficientLinearEncoder := by
  obtain ⟨E, distance, radius, hrad, hrad_lt, hdist_lt, hlen, -, hdistance, -, hencTM, -⟩ := h
  exact ⟨E, distance, hrad.trans hrad_lt, hdist_lt, hlen, hdistance, hencTM⟩

/-- **Input 9 (encoder form)** from the two published statements it rests on: CW19 Lemma 22 at half soundness and
CW19 Lemma 26. -/
theorem field9Encoder (hProx : NearCubicGates.Published.CW19Proximity.Lemma22Half)
    (hCode : NearCubicGates.Published.CW19Code.Lemma26) :
    PerfectThreeQueryProximityLiteral ∧ EfficientLinearEncoder :=
  ⟨NearCubicGates.Adapters.Proximity.perfect_three_query_proximity hProx,
    encoder_of_code (NearCubicGates.Adapters.Code.efficientLinearCode_of_lemma26 hCode)⟩

end NearCubicGates.Adapters.Assembly
