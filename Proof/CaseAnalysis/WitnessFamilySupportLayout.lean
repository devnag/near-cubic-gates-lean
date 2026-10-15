import Proof.CaseAnalysis.WitnessFamilyOuterBudget
import Proof.CaseAnalysis.WitnessFamilySupportPrefix
import Proof.CaseAnalysis.WitnessFamilyCacheFields

/-! The pinned support-family continuation enters the original cold source
bank with one final tape. Every original family/cache address keeps its value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def input (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (x raw bits : List Bool):=
  SupportDock.lift (ColdFamily.input source a k D G e E x raw bits) []
def familySlots (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=
  FamilySupportCall.slots (ColdFamily.fields source a k D G e E)
def cache (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (j : Fin 19):=
  (ColdFamily.cache source a k D G e E j).castAdd 1
def guardSlot (a : PointwisePCPPAlgorithm) (k D G e E : ℕ):=
  (ColdFamily.guardSlot source a k D G e E).castAdd 1
def first (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E den : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool):=
  TapeEmbedding.machine 1 (ColdFamily.first source a k CH Cpad cutoff D G copies e E den delta code sym)
def second {s : ℕ} (supplier : Machine 3244 s) (a : PointwisePCPPAlgorithm) (k D G e E K : ℕ):=
  FamilySupportFromPolicy.machine supplier e E K (ColdFamily.lengthSlot source a k D G e)
    (ColdFamily.countSlot source a k D G e) (ColdFamily.rawSlot source a k D G e) (ColdFamily.policy source a k D G e)
def machine {s : ℕ} (supplier : Machine 3244 s) (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies e E K den : ℕ) (delta : ℚ) (code : List Bool) (sym : Bool):=
  CloseoutRowsGateColdPair.machine (first source a k CH Cpad cutoff D G copies e E den delta code sym)
    (second source supplier a k D G e E K) (fun scanned=>scanned (guardSlot source a k D G e E))

theorem family_old (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (i : Fin 3243) :
    familySlots source a k D G e E (i.castAdd 1)=(ColdFamily.familySlots source a k D G e E i).castAdd 1:=
  FamilySupportCall.slots_old _ _
theorem family_support (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) :
    familySlots source a k D G e E 3243=
      (0 : Fin 1).natAdd (ColdFamily.base source a k D G e+FamilyCapacity.Call.extra E+3243):=
  FamilySupportCall.slots_support _

theorem first_run (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies e E den fuel : ℕ)
    (delta : ℚ) (code : List Bool) (sym : Bool) (x raw bits : List Bool)
    (prior : ExecutionReceipt (ColdLegal.tapes source a k D G e) _)
    (hr:run (ColdLegal.machine source a k CH Cpad cutoff D G copies e den delta code sym) fuel
      (ColdLegal.input source a k D G e x raw)=some prior) :
    run (first source a k CH Cpad cutoff D G copies e E den delta code sym) fuel
      (input source a k D G e E x raw bits)=
      some (TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>[]) (ColdFamilyLift.receipt E bits prior)) := by
  have old:=ColdFamilyLift.run_lift E
    (ColdLegal.machine source a k CH Cpad cutoff D G copies e den delta code sym) fuel
    (ColdLegal.input source a k D G e x raw) bits prior hr
  have actual:=TapeEmbedding.run_embed
    (ColdFamily.first source a k CH Cpad cutoff D G copies e E den delta code sym)
    (fun _ : Fin 1=>0) (fun _=>[]) _ _ _ old
  rw [StreamPrepare.embed_initial] at actual
  exact actual

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamilySupport
