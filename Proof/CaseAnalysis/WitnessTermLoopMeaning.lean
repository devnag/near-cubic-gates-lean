import Proof.CaseAnalysis.WitnessTermLoopDriver

/-! The one physical loop result is exactly the conjunction of its
original term decisions. Successful exhaustion carries the exact final
mass and both logical retained-record cursors for the sum consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem iterate_flag {α : Type} (next : ℕ → α → Bool×α) (flag : ℕ → Bool)
    (hflag : ∀ j x,(next j x).1=flag j) (n pos : ℕ) (x : α) :
    (RepeatMachine.iterate (CountedReject.advance next) n (pos,x)).1=(List.range' pos n).all flag := by
  induction n generalizing pos x with
  | zero => rfl
  | succ n ih =>
    cases hp : flag pos <;>
      simp only [RepeatMachine.iterate,CountedReject.advance,hflag,hp,Bool.false_eq_true,↓reduceIte,
        List.range'_succ,List.all_cons,Bool.false_and,Bool.true_and,ih]

theorem range_all (words : List (List Bool)) (flag : List Bool → Bool) :
    (List.range' 0 words.length).all (fun j=>flag (words.getD j []))=words.all flag := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_range',Nat.one_mul,Nat.zero_add]
  constructor
  · intro h bits hb
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hb
    subst bits
    simpa only [List.getD_eq_getElem words [] hi] using h i ⟨i,hi,rfl⟩
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := hj
    rw [List.getD_eq_getElem words [] hi]
    exact h _ (List.getElem_mem hi)

def passed (C : ℕ) (words : List (List Bool)) (circuitPass : List Bool → Bool) :=
  words.all (fun bits=>TermRoundAll.accepted C bits (circuitPass bits))

theorem successor_flags {s : ℕ} (circuit : Machine 1703 s) (P H C core W L cost : ℕ)
    (words : List (List Bool)) (pre tail out native : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord : List Bool → List Bool) (ambient : Fin 94 → List Bool) :
    (RepeatMachine.iterate
      (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
      words.length (0,ambient)).1=passed C words circuitPass := by
  rw [iterate_flag _ (fun j=>TermRoundAll.accepted C (words.getD j []) (circuitPass (words.getD j [])))
    (by intro j bank;rfl)]
  exact range_all words (fun bits=>TermRoundAll.accepted C bits (circuitPass bits))

private theorem result_bits {α : Type} {t s : ℕ} (source : α → Configuration t s) (total : ℕ)
    (output : Bool×α) (final : Configuration (t+1) (Fintype.card (RepeatMachine.Control s)))
    (bit : Fin t) (h : RepeatMachine.Result source total output final)
    (htrue : ∀ x,(source x).heads bit=0 ∧ (source x).tapes bit=[true])
    (hfalse : output.1=false → final.heads (bit.castAdd 1)=0 ∧ final.tapes (bit.castAdd 1)=[false]) :
    final.heads (bit.castAdd 1)=0 ∧ final.tapes (bit.castAdd 1)=[output.1] := by
  cases hb : output.1 with
  | false => exact hfalse hb
  | true =>
    simp only [RepeatMachine.Result,hb,↓reduceIte] at h
    rw [h]
    simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using htrue output.2

theorem decision {s : ℕ} (circuit : Machine 1703 s) (P H C T core W L cost : ℕ)
    (words : List (List Bool)) (pre tail out native : List Bool)
    (circuitPass : List Bool → Bool) (nativeWord : List Bool → List Bool) (ambient : Fin 94 → List Bool)
    (final : Configuration 2533 (Fintype.card (RepeatMachine.Control
      (Fintype.card (RecoveryCalls.Control (TermRound.sizes s))))))
    (hresult : RepeatMachine.Result
      (fun x=>entry circuit P H C core W L words pre tail out native nativeWord x.1 x.2) words.length
      (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
        words.length (0,ambient)) final)
    (hpositive : (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
        words.length (0,ambient)).1=true →
      (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
        words.length (0,ambient)).2.1=words.length ∧
      Store (width T (natBitLength C)) (mass C words words.length) []
        (RepeatMachine.iterate
          (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
          words.length (0,ambient)).2.2)
    (hnegative : (RepeatMachine.iterate
        (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
        words.length (0,ambient)).1=false → final.heads 724=0 ∧ final.tapes 724=[false]) :
    final.heads 724=0 ∧ final.tapes 724=[passed C words circuitPass] ∧
      (passed C words circuitPass=true → ∃ after,
        final=RepeatMachine.cfg 3 (entry circuit P H C core W L words pre tail out native nativeWord words.length after)
          words.length 1 ∧ Store (width T (natBitLength C)) (mass C words words.length) [] after) := by
  let output:=RepeatMachine.iterate
    (CountedReject.advance (successor circuit P H C core W L cost words pre tail out native circuitPass nativeWord))
    words.length (0,ambient)
  have flag : output.1=passed C words circuitPass := successor_flags circuit P H C core W L cost words
    pre tail out native circuitPass nativeWord ambient
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
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermLoop
