import Proof.CaseAnalysis.RowsSupportTermLoop
import Proof.CaseAnalysis.WitnessTermLoopMeaning

/-! The one physical loop result is exactly the conjunction of its
original term decisions. Successful exhaustion carries the exact final
mass and both logical retained-record cursors for the sum consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open CloseoutWitness
open CloseoutWitness.TermLoop (iterate_flag range_all mass)
open private result_bits from Proof.CaseAnalysis.WitnessTermLoopMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def passed (C : ℕ) (words : List (List Bool)) (circuitPass : List Bool → Bool) :=
  words.all (fun bits=>TermAll.accepted C bits (circuitPass bits))

theorem successor_flags {s : ℕ} (circuit : Machine 1704 s) (P H C core W L cost : ℕ)
    (words : List (List Bool)) (pre tail out native supports : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool) :
    (RepeatMachine.iterate
      (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
      words.length (0,ambient)).1=passed C words circuitPass := by
  rw [iterate_flag _ (fun j=>TermAll.accepted C (words.getD j []) (circuitPass (words.getD j [])))
    (by intro j bank;rfl)]
  exact range_all words (fun bits=>TermAll.accepted C bits (circuitPass bits))

theorem decision {s : ℕ} (circuit : Machine 1704 s) (P H C T core W L cost : ℕ)
    (words : List (List Bool)) (pre tail out native supports : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord supportWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (final : Configuration 2534 (Fintype.card (RepeatMachine.Control
      (Fintype.card (RecoveryCalls.Control (Term.sizes s))))))
    (hresult : RepeatMachine.Result
      (fun x=>entry circuit P H C core W L words pre tail out native supports nativeWord supportWord x.1 x.2) words.length
      (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
        words.length (0,ambient)) final)
    (hpositive : (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
        words.length (0,ambient)).1=true →
      (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
        words.length (0,ambient)).2.1=words.length ∧
      Store (width T (natBitLength C)) (mass C words words.length) []
        (RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
          words.length (0,ambient)).2.2)
    (hnegative : (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
        words.length (0,ambient)).1=false → final.heads 724=0 ∧ final.tapes 724=[false]) :
    final.heads 724=0 ∧ final.tapes 724=[passed C words circuitPass] ∧
      (passed C words circuitPass=true → ∃ after,
        final=RepeatMachine.cfg 3 (entry circuit P H C core W L words pre tail out native supports nativeWord supportWord words.length after)
          words.length 1 ∧ Store (width T (natBitLength C)) (mass C words words.length) [] after) := by
  let output:=RepeatMachine.iterate
    (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native supports circuitPass nativeWord supportWord))
    words.length (0,ambient)
  have flag : output.1=passed C words circuitPass := successor_flags circuit P H C core W L cost words
    pre tail out native supports circuitPass nativeWord supportWord ambient
  obtain ⟨hh,ht⟩ := result_bits _ words.length output final 724 hresult (by intro x;exact ⟨rfl,rfl⟩) hnegative
  rw [flag] at ht
  refine ⟨hh,ht,?_⟩
  intro hp
  have ho : output.1=true := flag.trans hp
  obtain ⟨index,store⟩ := hpositive ho
  have hr:=hresult
  change RepeatMachine.Result _ words.length output final at hr
  simp only [RepeatMachine.Result,ho,↓reduceIte] at hr
  rw [index] at hr
  exact ⟨output.2.2,hr,store⟩

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.TermLoop
