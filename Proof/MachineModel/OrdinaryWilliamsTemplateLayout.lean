import Proof.MachineModel.OrdinaryMatrixNaturalHeader

/-! Fixed finite layout for the eight physical template/header calls.
Installation below describes actual focused outputs; the machine has no
instruction that performs a mathematical tape installation. -/
namespace NearCubicWires.RepairOrdinary.WilliamsTemplates
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairRepresentation RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def widthSlots : Fin 5 → Fin 50 := ![4,6,7,8,9]
def deltaSlots : Fin 4 → Fin 50 := ![2,0,10,11]
def gapSlots : Fin 4 → Fin 50 := ![8,3,12,13]
def usedSlots : Fin 12 → Fin 50 := ![0,14,15,16,17,1,18,19,20,21,22,23]
def padSlots : Fin 12 → Fin 50 := ![10,24,25,26,27,1,28,29,30,31,32,33]
def tailSlots : Fin 12 → Fin 50 := ![10,34,35,36,37,8,38,39,40,41,42,43]
def copySlots : Fin 5 → Fin 50 := ![0,44,45,46,47]
def headerSlots : Fin 4 → Fin 50 := ![5,6,48,49]
def sizes : Fin 8 → ℕ := ![8,6,6,21,21,21,8,6]
noncomputable def programs (j : Fin 8) : Machine 50 (sizes j) := by
  refine Fin.cases (RecoveryFocus.machine widthSlots MatrixTemplateCopy.resetMachine) ?_ j
  intro j1
  refine Fin.cases (RecoveryFocus.machine deltaSlots MatrixUnaryDifference.resetMachine) ?_ j1
  intro j2
  refine Fin.cases (RecoveryFocus.machine gapSlots MatrixUnaryDifference.resetMachine) ?_ j2
  intro j3
  refine Fin.cases (RecoveryFocus.machine usedSlots MatrixTemplateProduct.machine) ?_ j3
  intro j4
  refine Fin.cases (RecoveryFocus.machine padSlots MatrixTemplateProduct.machine) ?_ j4
  intro j5
  refine Fin.cases (RecoveryFocus.machine tailSlots MatrixTemplateProduct.machine) ?_ j5
  intro j6
  refine Fin.cases (RecoveryFocus.machine copySlots MatrixTemplateCopy.resetMachine) ?_ j6
  intro last
  have he : last=0 := Subsingleton.elim _ _
  subst last
  exact RecoveryFocus.machine headerSlots MatrixNaturalHeader.resetMachine
def next (j : Fin 8) (_ : Fin (sizes j)) (_ : Fin 50 → Bool) : Option (Fin 8) :=
  if h : j.val+1<8 then some ⟨j.val+1,h⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def boundary (j : Fin 8) (a : Fin 50 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (initialConfiguration (programs j) a)
def input (u c v : ℕ) : Fin 50 → List Bool := fun i =>
  if i=0 then UnaryTemplate.tape u else if i=1 then UnaryTemplate.tape c
  else if i=2 then UnaryTemplate.tape v else if i=3 then UnaryTemplate.tape (natBitLength u)
  else if i=4 then CompareMachine.word (natBitLength v)
  else if i=5 then frame (binary (natBitLength v) v) else []

def Blank (start : ℕ) (a : Fin 50 → List Bool) : Prop := ∀ i, start ≤ i.val → a i=[]
def Old (finish : ℕ) (a b : Fin 50 → List Bool) : Prop := ∀ i, i.val<finish → b i=a i

theorem install_old {t : ℕ} (slot : Fin t → Fin 50) (a out : _ → List Bool) (finish : ℕ)
    (h : ∀ j, (slot j).val<finish → out j=a (slot j)) : Old finish a (install slot a out) := by
  intro i hi
  cases hp : RecoveryFocus.pick slot i with
  | none => simp [install,hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simp only [install,hp]
    have hj := h j (by rw [he]; exact hi)
    exact hj.trans (congrArg a he)

theorem install_blank {t : ℕ} (slot : Fin t → Fin 50) (a out : _ → List Bool) (finish : ℕ)
    (h : ∀ j, (slot j).val<finish) (ha : Blank finish a) : Blank finish (install slot a out) := by
  intro i hi
  rw [install_other slot a out i (by intro j he; have := h j; rw [he] at this; omega)]
  exact ha i hi

theorem Blank.later {a : Fin 50 → List Bool} {n m : ℕ} (h : Blank n a) (hm : n ≤ m) : Blank m a :=
  fun i hi => h i (hm.trans hi)

theorem input_blank (u c v : ℕ) : Blank 6 (input u c v) := by
  intro i hi
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  have h2 : i≠2 := by intro h; subst i; simp at hi
  have h3 : i≠3 := by intro h; subst i; simp at hi
  have h4 : i≠4 := by intro h; subst i; simp at hi
  have h5 : i≠5 := by intro h; subst i; simp at hi
  simp [input,h0,h1,h2,h3,h4,h5]

end NearCubicWires.RepairOrdinary.WilliamsTemplates
