import Proof.MachineModel.OrdinaryMatrixSignedMaskPass

/-! Two paid transitions initialize the first plane's finite byte-offset
sentinel and flag and position the already produced loop dimensions. -/
namespace NearCubicWires.RepairOrdinary.MatrixSignedBootstrap
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance (i : Fin 409) : Prop := i=401 ∨ i=22 ∨ i=32 ∨ i=256 ∨ i=321 ∨ i=200
instance (i : Fin 409) : Decidable (advance i) := inferInstanceAs (Decidable (i=401 ∨ i=22 ∨ i=32 ∨ i=256 ∨ i=321 ∨ i=200))
def machine : Machine 409 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if q.val=0 then some ⟨1,
      fun i => if i=401 ∨ i=402 then some false else none,
      fun i => if advance i then .right else .stay⟩
    else if q.val=1 then some ⟨2,fun i => if i=401 then some false else none,fun _ => .stay⟩ else none

def middle {s : ℕ} (c : Configuration 409 s) : Configuration 409 3 :=
  ⟨1,fun i => if advance i then c.heads i+1 else c.heads i,
    fun i => if i=401 ∨ i=402 then [false] else c.tapes i⟩
def final {s : ℕ} (c : Configuration 409 s) : Configuration 409 3 :=
  ⟨2,(middle c).heads,fun i => if i=401 then [false,false] else (middle c).tapes i⟩

theorem boot_run {s : ℕ} (c : Configuration 409 s)
    (t401 : c.tapes 401=[]) (t402 : c.tapes 402=[]) (h401 : c.heads 401=0) (h402 : c.heads 402=0) : ∃ actual,
    runFrom machine 2 (Composition.restart c machine.start)=some actual ∧
    actual.final=final c ∧ actual.steps=2 := by
  have first : step machine (Composition.restart c machine.start)=some (middle c) := by
    simp only [step,machine,Composition.restart]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : advance i <;> simp [applyAction,middle,hi,HeadMove.apply]
    · funext i
      by_cases h1 : i=401
      · subst i; simp [applyAction,middle,t401,h401,writeTapeBit]
      by_cases h2 : i=402
      · subst i; simp [applyAction,middle,t402,h402,writeTapeBit]
      · simp [applyAction,middle,h1,h2]
  have second : step machine (middle c)=some (final c) := by
    simp only [step,machine,middle]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,final,middle,HeadMove.apply]
    · funext i
      by_cases hi : i=401
      · subst i; simp [applyAction,final,middle,advance,h401,writeTapeBit]
      · simp [applyAction,final,middle,hi]
  exact ((Timed.single (by rfl) first).trans (Timed.single (by rfl) second)).run (by rfl)

end NearCubicWires.RepairOrdinary.MatrixSignedBootstrap
