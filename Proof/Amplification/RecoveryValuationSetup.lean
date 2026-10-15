import Proof.Amplification.RecoveryValuationLayout

/-! The first certificate-parser call uses the actual cold-produced tapes.
One physical transition initializes its flags/count sentinel and positions
its three unary heads. The witness copy retains its original frame. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def before (bits word : List Bool) (c s : Nat) (i : Fin 32) : List Bool :=
  Fin.addCases (RecoveryColdPreliminary.output bits word c s) (fun _ : Fin 6=>[]) i
def flags (i : Fin 32) : Prop := i.val=27 ∨ i.val=28 ∨ i.val=30 ∨ i.val=31
def moves (i : Fin 32) : Prop := i.val=14 ∨ i.val=21 ∨ i.val=31
instance (i : Fin 32) : Decidable (flags i) := inferInstanceAs (Decidable (_∨_∨_∨_))
instance (i : Fin 32) : Decidable (moves i) := inferInstanceAs (Decidable (_∨_∨_))
noncomputable def after (bits word : List Bool) (c s : Nat) (i : Fin 32) : List Bool :=
  if flags i then [false] else before bits word c s i
def positioned (i : Fin 32) : Nat := if moves i then 1 else 0

def setupMachine : Machine 32 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    (fun i=>if flags i then some false else none),(fun i=>if moves i then .right else .stay)⟩ else none

theorem setup_step (bits word : List Bool) (c s : Nat) :
    step setupMachine (initialConfiguration setupMachine (before bits word c s))=
      some ⟨1,positioned,after bits word c s⟩ := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem setup_run (bits word : List Bool) (c s : Nat) :
    ∃ r,run setupMachine 1 (before bits word c s)=some r ∧
      r.final.heads=positioned ∧ r.final.tapes=after bits word c s := by
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) (setup_step bits word c s)).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf]⟩

def slots : Fin 10→Fin 32 := ![23,26,14,10,27,28,29,30,31,21]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def parserMachine := RecoveryFocus.machine slots machine

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem parser_input (bits word : List Bool) (c s : Nat) :
    RecoveryFocus.config slots positioned (after bits word c s)
      (⟨machine.start,heads,tapes bits word⟩ : Configuration 10 _)=
      (⟨parserMachine.start,positioned,after bits word c s⟩ : Configuration 32 _) := by
  apply focus_configuration slots slots_injective
  · rfl
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j
    · exact (preliminary_word bits word c s).symm
    · rfl
    · exact (preliminary_width bits word c s).symm
    · exact (preliminary_zero bits word c s).symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (preliminary_cap bits word c s).symm
  · intro i _
    rfl
  · intro i _
    rfl

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
