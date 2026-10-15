import Proof.CaseAnalysis.WitnessFamilySupportLayout
import Proof.CaseAnalysis.WitnessBoundedFamilyCall

/-! The original bounded header selects one strengthened cold family.
Its two modes share one added support tape and preserve every old address. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def slots (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool):=
  SupportDock.slots (BoundedFamily.slots source a k D G E sym)
def flag (a : PointwisePCPPAlgorithm) (k D G E : ℕ):=(BoundedFamily.flag source a k D G E).castAdd 1
def first (a : PointwisePCPPAlgorithm) (k D G E : ℕ):=TapeEmbedding.machine 1 (BoundedFamily.first source a k D G E)
def branch {s : ℕ} (supplier : Machine 3244 s) (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ) (delta : ℚ) (code : List Bool) (sym : Bool):=
  RecoveryFocus.machine (slots source a k D G E sym)
    (ColdFamilySupport.machine source supplier a k CH Cpad cutoff D G copies (BoundedFamily.exponent sym) E K
      (BoundedFamily.denominator sym symDen thrDen) delta code sym)
def good (a : PointwisePCPPAlgorithm) (k D G E : ℕ)
    (cells : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)→Bool):=
  cells ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 147).castAdd 1)
def mode (a : PointwisePCPPAlgorithm) (k D G E : ℕ)
    (cells : Fin (HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)→Bool):=
  cells ((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)
def machine (suppliers : Bool→Σ s,Machine 3244 s) (a : PointwisePCPPAlgorithm)
    (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ) (delta : ℚ) (code : List Bool):=
  HeaderSwitch.machine (first source a k D G E)
    (branch source (suppliers true).2 a k CH Cpad cutoff D G copies E K symDen thrDen delta code true)
    (branch source (suppliers false).2 a k CH Cpad cutoff D G copies E K symDen thrDen delta code false)
    (good source a k D G E) (mode source a k D G E)
def input (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (x bits : List Bool):=
  SupportDock.lift (BoundedFamily.input source a k D G E x bits) []

theorem slots_injective (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) :
    Function.Injective (slots source a k D G E sym):=
  SupportDock.injective _ (BoundedFamily.slots_injective source a k D G E sym)
theorem flag_slot (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (sym : Bool) :
    slots source a k D G E sym ((ColdFamily.familySlots source a k D G (BoundedFamily.exponent sym) E 724).castAdd 1)=
      flag source a k D G E:=by
  exact (SupportDock.slots_old (BoundedFamily.slots source a k D G E sym)
    (ColdFamily.familySlots source a k D G (BoundedFamily.exponent sym) E 724)).trans
      (congrArg (fun i=>i.castAdd 1) (BoundedFamily.flag_slot source a k D G E sym))

theorem header_run (a : PointwisePCPPAlgorithm) (k D G E : ℕ) (x bits : List Bool) :
    ∃ scratch actual,run (first source a k D G E) (CompetitorWitnessBounded.budget x)
      (input source a k D G E x bits)=some actual ∧
      actual.final.heads=(fun _=>0) ∧
      actual.final.tapes=SupportDock.lift (HeaderDock.input (BoundedFamily.workspace source a k D G E)
        (CompetitorWitnessBounded.output x bits scratch)) []:=by
  obtain ⟨scratch,_bound,prior,run,tapes,heads⟩:=BoundedFamily.header_run source a k D G E x bits
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>[]) prior
  have actual:=TapeEmbedding.run_embed (BoundedFamily.first source a k D G E)
    (fun _ : Fin 1=>0) (fun _=>[]) _ _ prior run
  rw [StreamPrepare.embed_initial] at actual
  refine ⟨scratch,lifted,actual,?_,?_⟩
  · funext i
    simp only [lifted,TapeEmbedding.receipt,TapeEmbedding.config,heads]
    exact Fin.addCases (fun _=>by rw [Fin.addCases_left]) (fun _=>by rw [Fin.addCases_right]) i
  · funext i
    simp only [lifted,TapeEmbedding.receipt,TapeEmbedding.config,tapes,SupportDock.lift]
    rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFamilySupport
