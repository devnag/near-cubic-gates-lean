import SourceAdapters.Amplification.Assembly
import SourceAdapters.Amplification.Reconstruction
import SourceAdapters.Machine.OrdinaryToTM2
import SourceAdapters.Amplification.Construction

/-!
# Input 8 from the STV leaf and the construction condition

`input8_of_obligations` (`Assembly.lean`) takes four hypotheses: the leaf `STV.Theorem29`, A02
(`ReconstructionObligation`), X1 (`OrdinaryToTM2InTime`) and A05 (`ConstructionObligation`). Two are now proved:

* A02: `reconstructionObligation` (`Reconstruction.lean`; `app:sources`, "Full-range amplification interface");
* X1: `NearCubicGates.Adapters.Machine.ordinaryToTM2InTime` (`Machine/OrdinaryToTM2.lean`).

`input8_of_leaf_construction`: the field `CLW20_Lemma3_9_Multitape` from the published leaf and A05 only (an ordinary machine computing the amplifier's truth table in `2^{O(n)}` time for every
time-constructible `S`).

`field8`: A05 is proved (`Construction.lean`, `Enc.constructionObligation`; its dispatcher calls X8's capped time
constructor `Machine.Capped.cappedWordFunction`, the word-level half `CappedWordRun` of X8, proved in
`Machine/CappedWordProof.lean`), so the field follows from the published leaf `STV.Theorem29` alone.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification

open NearCubicGates.Published.STV

/-- **Field 8 from the leaf and A05.** -/
theorem input8_of_leaf_construction (h29 : Theorem29) (hA05 : ConstructionObligation) :
    NearCubicGates.Close.CLW20_Lemma3_9_Multitape :=
  input8_of_obligations h29 reconstructionObligation NearCubicGates.Adapters.Machine.ordinaryToTM2InTime hA05

/-- **Field 8** (`CLW20_Lemma3_9_Multitape`, `imp:ae-amplification`, full-range interface
`app:sources`, "Full-range amplification interface") from the published STV leaf alone. -/
theorem field8 (h29 : Theorem29) : NearCubicGates.Close.CLW20_Lemma3_9_Multitape :=
  input8_of_leaf_construction h29 Enc.constructionObligation

end NearCubicGates.Adapters.Amplification
