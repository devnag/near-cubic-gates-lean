import Proof.CaseAnalysis.RowsSupportSumBody
import Proof.CaseAnalysis.RowsSupportExchange
import Proof.CaseAnalysis.RowsSupportAppendAny
import Proof.CaseAnalysis.WitnessSumWork

/-! The counted term driver keeps its original outer2532 alias. Static
renaming and the unchanged528-tape bank place support at final3061. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
open LocalBitMultitape CloseoutWitness RepairSource.VerifierDecoding
open CloseoutWitness.SupportDock (lift)
open private padded_data from Proof.CaseAnalysis.WitnessSumWork
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def renamed {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  TapeRenaming.machine (Exchange.layout 2532) (SumBody.machine circuit k q)
noncomputable def body {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  AppendBank.machine (e:=528) (renamed circuit k q)
def pads (H : ℕ):Fin 2534→ℕ:=lift (CloseoutWitness.SumWork.pads H) 0

theorem renamed_heads (position : ℕ) (out supports : List Bool) (extra : Fin 1705→ℕ) :
    SumBody.heads position out extra supports ∘ (Exchange.layout 2532).symm=
      lift (CloseoutWitness.SumBody.heads position out extra) supports.length:=by
  exact Exchange.exchange (TermRound.heads position out extra) supports.length 1

theorem renamed_data (P K : ℕ) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (out supports : List Bool) (extra : Fin 1705→List Bool) :
    SumBody.data P K terms ambient out extra supports ∘ (Exchange.layout 2532).symm=
      lift (CloseoutWitness.SumBody.data P K terms ambient out extra) supports:=by
  exact Exchange.exchange (TermRound.data P terms ambient out extra) supports (CompareMachine.word K)

theorem padded_lift (H : ℕ) (values : Fin 2533→List Bool) (supports : List Bool) :
    (fun i=>ZeroPadding.pad (pads H i) (lift values supports i))=
      lift (fun i=>ZeroPadding.pad (CloseoutWitness.SumWork.pads H i) (values i)) supports:=by
  funext i
  refine Fin.addCases (m:=2533) (n:=1) ?_ ?_ i
  · intro j;simp only [pads,lift,Fin.addCases_left]
  · intro j;simp only [pads,lift,Fin.addCases_right,ZeroPadding.pad_zero]

theorem padded_core (P H b core W L K : ℕ) (source out native supports : List Bool)
    (ambient : Fin 94→List Bool) :
    (fun i=>ZeroPadding.pad (pads H i)
      (lift (CloseoutWitness.SumBody.data P K (TermRead.data P b [] source true) ambient out
        (TermEnvironment.tapes H core W L native)) supports i))=
      lift (SumDock.coreData P H b core W L source out native
        (ZeroPadding.pad H (CompareMachine.word K)) true ambient) supports:=by
  rw [padded_lift]
  exact congrArg (fun A=>lift A supports)
    (padded_data H (TermRound.data P (TermRead.data P b [] source true) ambient out
      (TermEnvironment.tapes H core W L native)) (CompareMachine.word K))

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
