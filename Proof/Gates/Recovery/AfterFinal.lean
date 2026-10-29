import Proof.Gates.Recovery.AfterMain
import Proof.Gates.Recovery.AfterHead2
import Proof.Gates.Recovery.AfterMid
import Proof.Gates.Recovery.AfterTail
import Proof.Gates.Recovery.AfterHeadRun

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- **The after-prefix supply, given the first half of the head** (`sec:all-lengths`). -/
theorem afterSupply_of_head
    (hHead : ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (K : Kit s P g) (c : Cfg),
      HeadTwoRuns K c → HeadRuns K c)
    (hT : ENP.TStageRuns) (hC : ∀ s P, Setup.CompU s P) : AfterSupply :=
  afterSupply_of_segs (fun s P g K c => hHead s P g K c (headTwoRuns K c)) (fun _ _ _ K c => midRuns K c)
    (fun _ _ _ K c => tailRuns K c) hT hC

end NearCubicGates.Close.Recovery.After

namespace NearCubicGates.Close.Recovery

/-- **The recovery after the refuter** (`sec:all-lengths`, "For completeness, all canonical choices are recoverable in
E^NP"): the after-prefix SAT-oracle program — stage 1, the canonical→native converter, the A-run (imp:short-pcp's
constructor on `⟨B*_src⟩_ν`), stage 2, stage 3, then Case 1 (i) on `X_z`, the zero slice, Case 1 (iii) on `Ô*` or the
Case 2 hard table — for every source bundle, PCPP and ready parameter choice, from the stage-2 producer and the
composite (for the Case 2 producer). -/
theorem afterSupply_of (hT : ENP.TStageRuns) (hC : ∀ s P, Setup.CompU s P) : AfterSupply :=
  After.afterSupply_of_head (fun _ _ _ K c h2 => After.headRuns_of K c h2) hT hC

end NearCubicGates.Close.Recovery
