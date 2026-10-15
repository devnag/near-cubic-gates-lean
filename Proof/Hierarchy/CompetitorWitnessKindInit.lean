import Proof.Amplification.RecoveryRowKind
import Proof.Hierarchy.CompetitorWitnessTriple

/-! A paid cold classifier for the actual witness header: zero, one, two,
and the canonical family alternatives zero/three. Four bounded predecessor
passes distinguish these values for every binary word, including empty. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessKind
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics RecoveryLiteralTag
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (bits : List Bool) (flags : Fin 4 → Bool) (cap : ℕ) : Fin 6 → List Bool :=
  ![frame bits,[flags 0],[flags 1],[flags 2],List.replicate cap false,[flags 3]]
def input (bits : List Bool) (i : Fin 6) : List Bool := if i.val=0 then frame bits else []
def initMachine : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,![none,some false,some false,some false,none,some false],fun _=>.stay⟩ else none

theorem initMachine_ready (bits : List Bool) : ReadyRun initMachine 1 (input bits) (tapes bits (fun _=>false) 0) := by
  let final : Configuration 6 2 := ⟨1,fun _=>0,tapes bits (fun _=>false) 0⟩
  have h : step initMachine (initialConfiguration initMachine (input bits))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],hs⟩

end NearCubicWires.RepairOrdinary.CompetitorWitnessKind
