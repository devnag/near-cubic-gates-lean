import Proof.PCP.ProjectionNormalizationProduct
import Proof.MachineModel.OrdinaryMatrixUnaryDifference

/-! The banked unary subtraction kernel on the actual shorter sentinel
counters. The absent trailing blank is handled by the checked carrier. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Difference
open LocalBitMultitape RepairOrdinary VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input3 (n m : ℕ) : Fin 3 → List Bool := ![CompareMachine.word n,CompareMachine.word m,[]]
def capacities (n m : ℕ) : Fin 3 → ℕ := ![n+2,m+2,0]
def input (n m : ℕ) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input3 n m) (fun _ : Fin 1 => [])
abbrev machine := MatrixUnaryDifference.resetMachine

theorem padded_word (n : ℕ) : ZeroPadding.pad (n+2) (CompareMachine.word n)=UnaryTemplate.tape n := by
  simp [ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem readonly {t s space steps : ℕ} {p : Machine t s} {a b : Configuration t s}
    (h : Prefix p space steps a b) (i : Fin t)
    (hw : ∀ q bits act,p.rule q bits=some act → act.write i=none) : b.tapes i=a.tapes i := by
  induction h with
  | refl => rfl
  | @step n a c b hc hn hs ht ih =>
    rw [ih]
    cases hr : p.rule a.control a.scanned with
    | none => simp [step,hr] at hs
    | some act =>
      have he : c=applyAction a act := by simpa [step,hr] using hs.symm
      rw [he]
      simp [applyAction,hw _ _ _ hr]

theorem raw_run (n m : ℕ) (hm : m ≤ n) :
    ∃ r,run MatrixUnaryDifference.machine (n+3) (input3 n m)=some r ∧
      r.final.tapes 0=CompareMachine.word n ∧ r.final.tapes 1=CompareMachine.word m ∧
      r.final.tapes 2=UnaryTemplate.tape (n-m) ∧ r.steps=n+3 := by
  obtain ⟨base,hb,hbf,hbs⟩ := MatrixUnaryDifference.difference_run n m hm
  have he : ZeroPadding.config (capacities n m) (initialConfiguration MatrixUnaryDifference.machine (input3 n m))=
      initialConfiguration MatrixUnaryDifference.machine (MatrixUnaryDifference.input n m) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;>
        simp [ZeroPadding.config,capacities,initialConfiguration,input3,MatrixUnaryDifference.input,padded_word]
  unfold run at hb
  rw [←he] at hb
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_unpad MatrixUnaryDifference.machine (capacities n m) _ _ base hb
  have hread (i : Fin 3) (hi : i=0 ∨ i=1) : r.final.tapes i=input3 n m i := by
    apply readonly (prefix_of_run MatrixUnaryDifference.machine _ _ r hr).1 i
    intro q bits act ha
    fin_cases q <;> simp only [MatrixUnaryDifference.machine] at ha
    all_goals split_ifs at ha <;> simp_all
    all_goals rw [←ha]
    all_goals rcases hi with rfl|rfl <;> rfl
  refine ⟨r,hr,hread 0 (by simp),hread 1 (by simp),?_,hrs.trans hbs⟩
  have h := congrArg (fun c => c.tapes 2) hrf
  rw [hbf] at h
  simpa [ZeroPadding.config,capacities,MatrixUnaryDifference.output] using h

theorem difference_run (n m : ℕ) (hm : m ≤ n) :
    ∃ r,run machine (2*n+8) (input n m)=some r ∧
      r.final.tapes 0=CompareMachine.word n ∧ r.final.tapes 1=CompareMachine.word m ∧
      r.final.tapes 2=UnaryTemplate.tape (n-m) ∧ (∀ i,r.final.heads i=0) ∧ r.steps=2*n+8 := by
  obtain ⟨base,hb,h0,h1,h2,hbs⟩ := raw_run n m hm
  obtain ⟨r,hr,ht,hh,hs,_⟩ := Rewind.reset_run MatrixUnaryDifference.machine _ _ base hb
  refine ⟨r,?_,(ht 0).trans h0,(ht 1).trans h1,(ht 2).trans h2,hh,?_⟩
  · simpa [hbs,machine,MatrixUnaryDifference.resetMachine,input,Nat.mul_add,Nat.add_assoc] using hr
  · omega

end NearCubicWires.RepairSource.ProjectionNormalization.Difference
