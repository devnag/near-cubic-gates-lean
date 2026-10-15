import Proof.CaseAnalysis.CaseTwoDirectInput

/-! Directly dock the frozen selected Case2 run on five retained physical
words and fresh empty work. Every actual initialization is inside that run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.DirectInput
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

theorem ready_at (k D copies CH Cpad fuel : ℕ) (code hierarchy description address : List Bool) (R B : ℕ)
    (out : Fin (tapes source a k D copies)→List Bool)
    (actual : ClockJoin.ReadyRun (SelectedOutput.machine source a k D copies CH Cpad code) fuel
      (input source a k D copies hierarchy description address R B) out)
    {ambient : ℕ} (slots : Fin (tapes source a k D copies)→Fin ambient) (hinj : Function.Injective slots)
    (H : Fin ambient→ℕ) (bank : Fin ambient→List Bool)
    (hfields : ∀ j,bank (slots (ports source a k D copies j))=words hierarchy description address R B j)
    (hwork : ∀ i,5 ≤ i.val → bank (slots i)=[])
    (hheads : ∀ i,H (slots i)=0) :
    ∃ r,runFrom (RecoveryFocus.machine slots (SelectedOutput.machine source a k D copies CH Cpad code)) fuel
      ⟨(SelectedOutput.machine source a k D copies CH Cpad code).start,H,bank⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=install slots bank out ∧ r.steps ≤ fuel:=by
  have he:=entry_eq source a k D copies hierarchy description address R B (bank∘slots) hfields hwork
  exact actual.focus_at slots hinj H bank (fun i=>congrFun he i) hheads

theorem selected_output_slot (k D copies : ℕ) {ambient : ℕ}
    (slots : Fin (tapes source a k D copies)→Fin ambient) (hinj : Function.Injective slots)
    (bank : Fin ambient→List Bool) (out : Fin (tapes source a k D copies)→List Bool) :
    install slots bank out (slots (outputPort source a k D copies))=out (outputPort source a k D copies):=
  install_slot slots hinj bank out _

theorem retained_input_slot (k D copies : ℕ) {ambient : ℕ}
    (slots : Fin (tapes source a k D copies)→Fin ambient) (hinj : Function.Injective slots)
    (bank : Fin ambient→List Bool) (out : Fin (tapes source a k D copies)→List Bool) (j : Fin 5) :
    install slots bank out (slots (ports source a k D copies j))=out (ports source a k D copies j):=
  install_slot slots hinj bank out _

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.DirectInput
