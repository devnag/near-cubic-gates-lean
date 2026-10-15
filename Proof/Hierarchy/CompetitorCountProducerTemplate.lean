import Proof.Hierarchy.CompetitorCountMask

/-! The exact SUM machine consumes the already-produced native count
sentinel, including its allocated terminal false cell. Padding transport
preserves the actual steps and the rewound scalar output. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountProducer
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templateInput (b w : ℕ) (xs : List ℕ) : Fin 11 → List Bool :=
  Function.update (input b w xs) 8 (UnaryTemplate.tape xs.length)
def templateCaps (n : ℕ) (i : Fin 11) := if i=8 then n+2 else 0

theorem template_run (b w : ℕ) (xs : List ℕ)
    (hw : b≤w) (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r,run machine (budget w xs.length) (templateInput b w xs)=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧ r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps≤budget w xs.length ∧ r.final.heads=finalHeads b xs.length ∧
      r.final.tapes 1=List.replicate b true ∧ r.final.tapes 2=List.replicate w true := by
  obtain ⟨base,hb,b5,b0,bs,bh,b1,b2⟩ := producer_head_run b w xs hw hx hfit
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_config machine (templateCaps xs.length) _ _ base hb
  have hi : ZeroPadding.config (templateCaps xs.length) (initialConfiguration machine (input b w xs))=
      initialConfiguration machine (templateInput b w xs) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,templateCaps,initialConfiguration,templateInput,input,
        ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,hs.trans_le bs,?_,?_,?_⟩
  · rw [hf]
    simpa [ZeroPadding.config,templateCaps] using b5
  · rw [hf]
    simpa [ZeroPadding.config,templateCaps] using b0
  · rw [hf]
    exact bh
  · rw [hf]
    simpa [ZeroPadding.config,templateCaps] using b1
  · rw [hf]
    simpa [ZeroPadding.config,templateCaps] using b2

end NearCubicWires.RepairOrdinary.CompetitorCountProducer
