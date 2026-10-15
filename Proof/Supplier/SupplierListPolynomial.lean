import Proof.Supplier.SupplierListCompiler
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Literal window polynomials for the Toeplitz list

Each seed gives one terminal population window and one signed-difference
window per level.  Literal occurrences are tagged by their level, so all
window polynomials live in one common polynomial ring without pretending
that complemented literals are independent source coordinates.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierListPolynomial

open NearCubicWires.SupplierList
open NearCubicWires.SupplierListCompiler
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierToeplitz
open NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWindow

abbrev 𝔽₂ := ZMod 2

inductive ListLiteralVariable (depth population : ℕ) where
  | terminal (coordinate : Fin population)
  | delta (level : Fin depth) (slot : Fin (2 * population))
  deriving DecidableEq

def hashIndexCell
    {rank population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (cell : Finset (BinaryVector rank)) : Finset (Fin population) :=
  Finset.univ.filter fun coordinate =>
    toeplitzHash (label coordinate) seed ∈ cell

@[simp] theorem mem_hashIndexCell
    {rank population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (cell : Finset (BinaryVector rank))
    (coordinate : Fin population) :
    coordinate ∈ hashIndexCell label seed cell ↔
      toeplitzHash (label coordinate) seed ∈ cell := by
  simp [hashIndexCell]

theorem toeplitzCellCount_eq_filter_card
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (cell : Finset (BinaryVector rank)) :
    toeplitzCellCount active label cell seed =
      (active.filter fun coordinate =>
        toeplitzHash (label coordinate) seed ∈ cell).card := by
  unfold toeplitzCellCount
  calc
    (∑ coordinate ∈ active,
        (decide
          (toeplitzHash (label coordinate) seed ∈ cell) : Bool).toNat) =
        ∑ coordinate ∈ active,
          if toeplitzHash (label coordinate) seed ∈ cell
            then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro coordinate _
      by_cases hmember :
          toeplitzHash (label coordinate) seed ∈ cell <;>
        simp [hmember]
    _ = (active.filter fun coordinate =>
        toeplitzHash (label coordinate) seed ∈ cell).card :=
      Finset.sum_boole _ _

def leftLiteralSlot {population : ℕ}
    (coordinate : Fin population) : Fin (2 * population) :=
  ⟨coordinate.val, by omega⟩

def rightLiteralSlot {population : ℕ}
    (coordinate : Fin population) : Fin (2 * population) :=
  ⟨population + coordinate.val, by omega⟩

theorem leftLiteralSlot_injective {population : ℕ} :
    Function.Injective (@leftLiteralSlot population) := by
  intro left right hequal
  apply Fin.ext
  simpa [leftLiteralSlot] using congrArg Fin.val hequal

theorem rightLiteralSlot_injective {population : ℕ} :
    Function.Injective (@rightLiteralSlot population) := by
  intro left right hequal
  apply Fin.ext
  have hvalue := congrArg Fin.val hequal
  simp only [rightLiteralSlot] at hvalue
  omega

theorem left_rightLiteralSlot_ne
    {population : ℕ} (left right : Fin population) :
    leftLiteralSlot left ≠ rightLiteralSlot right := by
  intro hequal
  have hvalue := congrArg Fin.val hequal
  simp only [leftLiteralSlot, rightLiteralSlot] at hvalue
  have hleft := left.isLt
  omega

def terminalLiteralActive
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (depth : ℕ) :
    Finset (Fin population) :=
  active ∩ hashIndexCell label seed (zeroPrefixCell rank depth)

def deltaLiteralActive
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) :
    Finset (Fin (2 * population)) :=
  ((active ∩
      hashIndexCell label seed
        (siblingPrefixCell rank level)).image leftLiteralSlot) ∪
    ((hashIndexCell label seed
      (zeroPrefixCell rank (level + 1)) \ active).image rightLiteralSlot)

theorem terminalLiteralActive_card
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (depth : ℕ) :
    (terminalLiteralActive active label seed depth).card =
      prefixCount active label seed depth := by
  unfold terminalLiteralActive prefixCount
  rw [toeplitzCellCount_eq_filter_card]
  congr 1
  ext coordinate
  simp

theorem deltaLiteralActive_card
    {rank population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) (level : ℕ) :
    ((deltaLiteralActive active label seed level).card : ℤ) =
      (hashIndexCell label seed
          (zeroPrefixCell rank (level + 1))).card +
        prefixDelta active label seed level := by
  let sibling :=
    active ∩ hashIndexCell label seed
      (siblingPrefixCell rank level)
  let child :=
    hashIndexCell label seed
      (zeroPrefixCell rank (level + 1))
  have himageDisjoint :
      Disjoint
        (sibling.image leftLiteralSlot)
        ((child \ active).image rightLiteralSlot) := by
    rw [Finset.disjoint_left]
    intro slot hleft hright
    rcases Finset.mem_image.mp hleft with
      ⟨left, _hleft, rfl⟩
    rcases Finset.mem_image.mp hright with
      ⟨right, _hright, hequal⟩
    exact left_rightLiteralSlot_ne left right hequal.symm
  have hsiblingCard :
      (sibling.image leftLiteralSlot).card = sibling.card :=
    Finset.card_image_of_injective _ leftLiteralSlot_injective
  have hchildCard :
      ((child \ active).image rightLiteralSlot).card =
        (child \ active).card :=
    Finset.card_image_of_injective _ rightLiteralSlot_injective
  have hactiveChildSubset : active ∩ child ⊆ child :=
    Finset.inter_subset_right
  have hchildDifference :
      (child \ active).card =
        child.card - (active ∩ child).card := by
    rw [Finset.card_sdiff]
  have hsiblingCount :
      sibling.card =
        toeplitzCellCount active label
          (siblingPrefixCell rank level) seed := by
    rw [toeplitzCellCount_eq_filter_card]
    congr 1
    ext coordinate
    simp [sibling]
  have hchildCount :
      (active ∩ child).card =
        toeplitzCellCount active label
          (zeroPrefixCell rank (level + 1)) seed := by
    rw [toeplitzCellCount_eq_filter_card]
    congr 1
    ext coordinate
    simp [child]
  have hdelta :
      prefixDelta active label seed level =
        (toeplitzCellCount active label
            (siblingPrefixCell rank level) seed : ℤ) -
          (toeplitzCellCount active label
            (zeroPrefixCell rank (level + 1)) seed : ℤ) := by
    have hadd :=
      toeplitzPrefixCount_add (level := level) active label seed
    unfold prefixDelta prefixCount
    rw [hadd]
    omega
  unfold deltaLiteralActive
  change
    ((sibling.image leftLiteralSlot ∪
        (child \ active).image rightLiteralSlot).card : ℤ) =
      child.card + prefixDelta active label seed level
  rw [Finset.card_union_of_disjoint himageDisjoint,
    hsiblingCard, hchildCard, hchildDifference,
    hsiblingCount, hchildCount, hdelta]
  have hactiveChildCard :
      (active ∩ child).card ≤ child.card :=
    Finset.card_le_card hactiveChildSubset
  omega

def listLiteralAssignment
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank) :
    ListLiteralVariable depth population → 𝔽₂
  | .terminal coordinate =>
      bitAssignment (terminalLiteralActive active label seed depth)
        coordinate
  | .delta level slot =>
      bitAssignment
        (deltaLiteralActive active label seed level.val) slot

noncomputable def terminalWindowPolynomial
    (depth population terminalWindow target : ℕ) :
    MvPolynomial (ListLiteralVariable depth population) 𝔽₂ :=
  MvPolynomial.rename ListLiteralVariable.terminal
    (consecutiveWindowIndicator
      population 0 terminalWindow target)

noncomputable def deltaWindowPolynomial
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    MvPolynomial (ListLiteralVariable depth population) 𝔽₂ :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  MvPolynomial.rename (ListLiteralVariable.delta level)
    (consecutiveWindowIndicator
      (2 * population) (childCard - window level)
      (2 * window level) target)

def desiredDeltaLiteral
    (childCard parent child : ℕ) : ℤ :=
  (childCard : ℤ) + parent - 2 * child

/-- Translate a proposed `(parent, child)` pair to the local literal-window
coordinate.  Pairs outside the printed window have no factor. -/
def deltaTarget?
    (childCard window parent child : ℕ) : Option ℕ :=
  let offset := childCard - window
  let desired := desiredDeltaLiteral childCard parent child
  if _hbounds :
      (offset : ℤ) ≤ desired ∧
        desired ≤ (offset + 2 * window : ℕ) then
    some (Int.toNat (desired - offset))
  else
    none

theorem deltaTarget?_some_spec
    {childCard window parent child target : ℕ}
    (htarget :
      deltaTarget? childCard window parent child = some target) :
    desiredDeltaLiteral childCard parent child =
        (childCard - window : ℕ) + target ∧
      target ≤ 2 * window := by
  change
    (if _h :
        (childCard - window : ℕ) ≤
            desiredDeltaLiteral childCard parent child ∧
          desiredDeltaLiteral childCard parent child ≤
            ((childCard - window + 2 * window : ℕ) : ℤ)
      then
        some (Int.toNat
          (desiredDeltaLiteral childCard parent child -
            (childCard - window : ℕ)))
      else none) = some target at htarget
  by_cases hbounds :
      (childCard - window : ℕ) ≤
          desiredDeltaLiteral childCard parent child ∧
        desiredDeltaLiteral childCard parent child ≤
          ((childCard - window + 2 * window : ℕ) : ℤ)
  · rw [dif_pos hbounds] at htarget
    have htargetValue :
        target =
          Int.toNat
            (desiredDeltaLiteral childCard parent child -
              (childCard - window : ℕ)) := by
      exact Option.some.inj htarget.symm
    have hnonnegative :
        0 ≤ desiredDeltaLiteral childCard parent child -
          (childCard - window : ℕ) := by
      omega
    have htoNat :
        (Int.toNat
          (desiredDeltaLiteral childCard parent child -
            (childCard - window : ℕ)) : ℤ) =
          desiredDeltaLiteral childCard parent child -
            (childCard - window : ℕ) := by
      exact Int.toNat_of_nonneg hnonnegative
    constructor
    · rw [htargetValue]
      omega
    · rw [htargetValue]
      have hupper := hbounds.2
      omega
  · rw [dif_neg hbounds] at htarget
    contradiction

theorem deltaTarget?_exists_of_bounds
    {childCard window parent child : ℕ}
    (hlower :
      (childCard - window : ℕ) ≤
        desiredDeltaLiteral childCard parent child)
    (hupper :
      desiredDeltaLiteral childCard parent child ≤
        (childCard - window : ℕ) + 2 * window) :
    ∃ target,
      deltaTarget? childCard window parent child = some target := by
  have hbounds :
      (childCard - window : ℕ) ≤
          desiredDeltaLiteral childCard parent child ∧
        desiredDeltaLiteral childCard parent child ≤
          ((childCard - window + 2 * window : ℕ) : ℤ) := by
    constructor
    · exact hlower
    · norm_cast at hupper ⊢
  refine ⟨Int.toNat
    (desiredDeltaLiteral childCard parent child -
      (childCard - window : ℕ)), ?_⟩
  unfold deltaTarget?
  dsimp only
  rw [dif_pos hbounds]

noncomputable def deltaFactor
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    MvPolynomial (ListLiteralVariable depth population) 𝔽₂ :=
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  match deltaTarget? childCard (window level)
      parent.val child.val with
  | none => 0
  | some target =>
      deltaWindowPolynomial label seed window level target

theorem aeval_terminalWindowPolynomial
    {rank depth population terminalWindow target : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (hterminal :
      prefixCount active label seed depth ≤ terminalWindow) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (terminalWindowPolynomial depth population
          terminalWindow target) =
      if prefixCount active label seed depth = target then 1 else 0 := by
  rw [terminalWindowPolynomial, MvPolynomial.aeval_rename]
  have hcomposition :
      listLiteralAssignment (depth := depth) active label seed ∘
          (@ListLiteralVariable.terminal depth population) =
        bitAssignment
          (terminalLiteralActive active label seed depth) := by
    rfl
  rw [hcomposition]
  rw [aeval_consecutiveWindowIndicator
    (terminalLiteralActive active label seed depth)
    (Nat.zero_le _)]
  · rw [terminalLiteralActive_card]
    simp
  · rw [terminalLiteralActive_card]
    omega

theorem aeval_deltaWindowPolynomial
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (target : ℕ)
    (hgood :
      |prefixDelta active label seed level.val| ≤ window level) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (deltaWindowPolynomial label seed window level target) =
      if (deltaLiteralActive active label seed level.val).card =
          (hashIndexCell label seed
              (zeroPrefixCell rank (level.val + 1))).card -
            window level + target
        then 1 else 0 := by
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  let literalCard :=
    (deltaLiteralActive active label seed level.val).card
  have hcard :
      (literalCard : ℤ) =
        childCard + prefixDelta active label seed level.val := by
    exact deltaLiteralActive_card active label seed level.val
  have hdeltaBounds :
      -(window level : ℤ) ≤
          prefixDelta active label seed level.val ∧
        prefixDelta active label seed level.val ≤ window level :=
    abs_le.mp hgood
  have hlower : childCard - window level ≤ literalCard := by
    omega
  have hupper :
      literalCard ≤ childCard - window level + 2 * window level := by
    omega
  rw [deltaWindowPolynomial, MvPolynomial.aeval_rename]
  have hcomposition :
      listLiteralAssignment active label seed ∘
          ListLiteralVariable.delta level =
        bitAssignment
          (deltaLiteralActive active label seed level.val) := by
    rfl
  rw [hcomposition]
  exact aeval_consecutiveWindowIndicator
    (deltaLiteralActive active label seed level.val)
    hlower hupper

theorem aeval_deltaFactor_at_actualChild
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (parent child : Fin (population + 1))
    (hchild :
      child.val =
        prefixCount active label seed (level.val + 1))
    (hgood :
      |prefixDelta active label seed level.val| ≤ window level) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (deltaFactor label seed window level parent child) =
      if parent.val =
          prefixCount active label seed level.val
        then 1 else 0 := by
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  let literalCard :=
    (deltaLiteralActive active label seed level.val).card
  let actualParent :=
    prefixCount active label seed level.val
  let actualChild :=
    prefixCount active label seed (level.val + 1)
  have hcard :
      (literalCard : ℤ) =
        childCard + prefixDelta active label seed level.val := by
    exact deltaLiteralActive_card active label seed level.val
  have hrelation :
      (actualParent : ℤ) =
        2 * (actualChild : ℤ) +
          prefixDelta active label seed level.val := by
    exact prefixCount_relation active label seed level.val
  have hdeltaBounds :
      -(window level : ℤ) ≤
          prefixDelta active label seed level.val ∧
        prefixDelta active label seed level.val ≤ window level :=
    abs_le.mp hgood
  have hliteralLower :
      childCard - window level ≤ literalCard := by
    omega
  have hliteralUpper :
      literalCard ≤ childCard - window level + 2 * window level := by
    omega
  have hactualDesired :
      desiredDeltaLiteral childCard actualParent actualChild =
        literalCard := by
    unfold desiredDeltaLiteral
    omega
  have hactualTarget :
      ∃ target,
        deltaTarget? childCard (window level)
          actualParent actualChild = some target := by
    apply deltaTarget?_exists_of_bounds
    · rw [hactualDesired]
      exact_mod_cast hliteralLower
    · rw [hactualDesired]
      exact_mod_cast hliteralUpper
  change
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (match deltaTarget? childCard (window level)
            parent.val child.val with
          | none => 0
          | some target =>
              deltaWindowPolynomial label seed window level target) =
      if parent.val = actualParent then 1 else 0
  cases htarget :
      deltaTarget? childCard (window level)
        parent.val child.val with
  | none =>
      simp only
      have hparentNe : parent.val ≠ actualParent := by
        intro hparent
        rcases hactualTarget with ⟨target, htargetActual⟩
        have hsame :
            deltaTarget? childCard (window level)
                parent.val child.val =
              deltaTarget? childCard (window level)
                actualParent actualChild := by
          rw [hparent, hchild]
        rw [hsame, htargetActual] at htarget
        contradiction
      rw [if_neg hparentNe]
      exact map_zero _
  | some target =>
      simp only
      rw [aeval_deltaWindowPolynomial
        active label seed window level target hgood]
      have htargetSpec :=
        deltaTarget?_some_spec htarget
      have hequivalence :
          literalCard =
              childCard - window level + target ↔
            parent.val = actualParent := by
        constructor
        · intro hliteral
          unfold desiredDeltaLiteral at htargetSpec
          omega
        · intro hparent
          unfold desiredDeltaLiteral at htargetSpec
          omega
      exact if_congr hequivalence rfl rfl

abbrev ListPolynomialVector (depth population : ℕ) :=
  Fin (population + 1) →
    MvPolynomial (ListLiteralVariable depth population) 𝔽₂

noncomputable def terminalPolynomialVector
    (depth population terminalWindow : ℕ) :
    ListPolynomialVector depth population :=
  fun candidate =>
    terminalWindowPolynomial depth population
      terminalWindow candidate.val

noncomputable def combineListLevel
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : ListPolynomialVector depth population) :
    ListPolynomialVector depth population :=
  fun parent =>
    ∑ child : Fin (population + 1),
      childPolynomials child *
        deltaFactor label seed window level parent child

theorem aeval_terminalPolynomialVector
    {rank depth population terminalWindow : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (hterminal :
      prefixCount active label seed depth ≤ terminalWindow)
    (candidate : Fin (population + 1)) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (terminalPolynomialVector depth population
          terminalWindow candidate) =
      if candidate.val =
          prefixCount active label seed depth
        then 1 else 0 := by
  rw [terminalPolynomialVector,
    aeval_terminalWindowPolynomial
      active label seed hterminal]
  exact if_congr eq_comm rfl rfl

theorem aeval_combineListLevel
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : ListPolynomialVector depth population)
    (hchild : ∀ candidate,
      MvPolynomial.aeval
          (listLiteralAssignment active label seed)
          (childPolynomials candidate) =
        if candidate.val =
            prefixCount active label seed (level.val + 1)
          then 1 else 0)
    (hgood :
      |prefixDelta active label seed level.val| ≤ window level)
    (parent : Fin (population + 1)) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (combineListLevel label seed window level
          childPolynomials parent) =
      if parent.val =
          prefixCount active label seed level.val
        then 1 else 0 := by
  have hcountBound :
      prefixCount active label seed (level.val + 1) ≤ population := by
    exact (prefixCount_le_active_card active label seed
      (level.val + 1)).trans
        (by
          simpa only [Fintype.card_fin] using
            Finset.card_le_univ active)
  let actualChild : Fin (population + 1) :=
    ⟨prefixCount active label seed (level.val + 1), by omega⟩
  unfold combineListLevel
  rw [map_sum]
  rw [Fintype.sum_eq_single actualChild]
  · rw [map_mul, hchild actualChild, if_pos rfl, one_mul]
    exact aeval_deltaFactor_at_actualChild
      active label seed window level parent actualChild rfl hgood
  · intro child hchildNe
    have hvalueNe :
        child.val ≠
          prefixCount active label seed (level.val + 1) := by
      intro hvalue
      apply hchildNe
      apply Fin.ext
      exact hvalue
    rw [map_mul, hchild child, if_neg hvalueNe, zero_mul]

/-- Compile levels `level, ..., depth - 1`; at `depth` the terminal window is
used.  The recursion is structural in the number of remaining levels. -/
noncomputable def listPolynomialVectorFrom
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ) :
    ListPolynomialVector depth population :=
  if hlevel : level < depth then
    combineListLevel label seed window ⟨level, hlevel⟩
      (listPolynomialVectorFrom label seed window
        terminalWindow (level + 1))
  else
    terminalPolynomialVector depth population terminalWindow
termination_by depth - level
decreasing_by omega

noncomputable def listPolynomialVector
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ) :
    ListPolynomialVector depth population :=
  listPolynomialVectorFrom label seed window terminalWindow 0

theorem aeval_listPolynomialVectorFrom
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (hlevel : level ≤ depth)
    (hterminal :
      prefixCount active label seed depth ≤ terminalWindow)
    (hgood : ∀ candidate : Fin depth,
      |prefixDelta active label seed candidate.val| ≤
        window candidate)
    (candidate : Fin (population + 1)) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (listPolynomialVectorFrom label seed window
          terminalWindow level candidate) =
      if candidate.val =
          prefixCount active label seed level
        then 1 else 0 := by
  rw [listPolynomialVectorFrom]
  by_cases hnext : level < depth
  · rw [dif_pos hnext]
    apply aeval_combineListLevel active label seed window
      ⟨level, hnext⟩
    · intro childCandidate
      exact aeval_listPolynomialVectorFrom active label seed
        window terminalWindow (level + 1)
        (by omega) hterminal hgood childCandidate
    · exact hgood ⟨level, hnext⟩
  · rw [dif_neg hnext]
    have hequal : level = depth := by omega
    subst level
    exact aeval_terminalPolynomialVector
      active label seed hterminal candidate
termination_by depth - level
decreasing_by omega

theorem aeval_listPolynomialVector
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (hterminal :
      prefixCount active label seed depth ≤ terminalWindow)
    (hgood : ∀ candidate : Fin depth,
      |prefixDelta active label seed candidate.val| ≤
        window candidate)
    (candidate : Fin (population + 1)) :
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (listPolynomialVector label seed window
          terminalWindow candidate) =
      if candidate.val = active.card then 1 else 0 := by
  have hbase :
      prefixCount active label seed 0 = active.card := by
    unfold prefixCount toeplitzCellCount
    have hcell :
        zeroPrefixCell rank 0 =
          (Finset.univ : Finset (BinaryVector rank)) := by
      ext output
      simp
    rw [hcell]
    simp
  unfold listPolynomialVector
  rw [aeval_listPolynomialVectorFrom active label seed
    window terminalWindow 0 (Nat.zero_le depth)
    hterminal hgood candidate]
  rw [hbase]

theorem totalDegree_terminalWindowPolynomial_le
    (depth population terminalWindow target : ℕ) :
    (terminalWindowPolynomial depth population
      terminalWindow target).totalDegree ≤ terminalWindow := by
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (totalDegree_consecutiveWindowIndicator_le
      population 0 terminalWindow target)

theorem totalDegree_deltaWindowPolynomial_le
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth) (target : ℕ) :
    (deltaWindowPolynomial label seed window level target).totalDegree ≤
      2 * window level := by
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (totalDegree_consecutiveWindowIndicator_le
      (2 * population)
      ((hashIndexCell label seed
        (zeroPrefixCell rank (level.val + 1))).card -
          window level)
      (2 * window level) target)

theorem totalDegree_deltaFactor_le
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ)
    (level : Fin depth)
    (parent child : Fin (population + 1)) :
    (deltaFactor label seed window level parent child).totalDegree ≤
      2 * window level := by
  let childCard :=
    (hashIndexCell label seed
      (zeroPrefixCell rank (level.val + 1))).card
  change
    (match deltaTarget? childCard (window level)
        parent.val child.val with
      | none => 0
      | some target =>
          deltaWindowPolynomial label seed window level target).totalDegree ≤
      2 * window level
  cases htarget :
      deltaTarget? childCard (window level)
        parent.val child.val with
  | none =>
      simp
  | some target =>
      exact totalDegree_deltaWindowPolynomial_le
        label seed window level target

theorem totalDegree_terminalPolynomialVector_le
    (depth population terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    (terminalPolynomialVector depth population
      terminalWindow candidate).totalDegree ≤ terminalWindow :=
  totalDegree_terminalWindowPolynomial_le
    depth population terminalWindow candidate.val

theorem totalDegree_combineListLevel_le
    {rank depth population degree : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (level : Fin depth)
    (childPolynomials : ListPolynomialVector depth population)
    (hchild : ∀ candidate,
      (childPolynomials candidate).totalDegree ≤ degree)
    (parent : Fin (population + 1)) :
    (combineListLevel label seed window level
      childPolynomials parent).totalDegree ≤
        degree + 2 * window level := by
  unfold combineListLevel
  apply MvPolynomial.totalDegree_finsetSum_le
  intro child _
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add (hchild child)
      (totalDegree_deltaFactor_le
        label seed window level parent child))

def listDegreeFrom
    {depth : ℕ} (window : Fin depth → ℕ)
    (terminalWindow level : ℕ) : ℕ :=
  if hlevel : level < depth then
    listDegreeFrom window terminalWindow (level + 1) +
      2 * window ⟨level, hlevel⟩
  else
    terminalWindow
termination_by depth - level
decreasing_by omega

def listDegree
    {depth : ℕ} (window : Fin depth → ℕ)
    (terminalWindow : ℕ) : ℕ :=
  listDegreeFrom window terminalWindow 0

theorem totalDegree_listPolynomialVectorFrom_le
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow level : ℕ)
    (candidate : Fin (population + 1)) :
    (listPolynomialVectorFrom label seed window
      terminalWindow level candidate).totalDegree ≤
        listDegreeFrom window terminalWindow level := by
  rw [listPolynomialVectorFrom, listDegreeFrom]
  by_cases hnext : level < depth
  · rw [dif_pos hnext, dif_pos hnext]
    exact totalDegree_combineListLevel_le
      label seed window ⟨level, hnext⟩
      (listPolynomialVectorFrom label seed window
        terminalWindow (level + 1))
      (fun child =>
        totalDegree_listPolynomialVectorFrom_le
          label seed window terminalWindow (level + 1) child)
      candidate
  · rw [dif_neg hnext, dif_neg hnext]
    exact totalDegree_terminalPolynomialVector_le
      depth population terminalWindow candidate
termination_by depth - level
decreasing_by omega

theorem totalDegree_listPolynomialVector_le
    {rank depth population : ℕ}
    (label : Fin population → BinaryVector rank)
    (seed : ToeplitzSeed rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (candidate : Fin (population + 1)) :
    (listPolynomialVector label seed window
      terminalWindow candidate).totalDegree ≤
        listDegree window terminalWindow :=
  totalDegree_listPolynomialVectorFrom_le
    label seed window terminalWindow 0 candidate

noncomputable def polynomialListSucceeds
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (seed : ToeplitzSeed rank) : Bool :=
  decide (∀ candidate : Fin (population + 1),
    MvPolynomial.aeval
        (listLiteralAssignment active label seed)
        (listPolynomialVector label seed window
          terminalWindow candidate) =
      if candidate.val = active.card then 1 else 0)

theorem polynomialListSucceeds_of_not_bad
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (seed : ToeplitzSeed rank)
    (hbad :
      prefixListBad active label window terminalWindow seed = false) :
    polynomialListSucceeds active label window terminalWindow seed = true := by
  have hnotBad :
      ¬(terminalWindow <
            prefixCount active label seed depth ∨
        ∃ level : Fin depth,
          (window level : ℤ) <
            |prefixDelta active label seed level.val|) := by
    unfold prefixListBad at hbad
    exact of_decide_eq_false hbad
  have hterminal :
      prefixCount active label seed depth ≤ terminalWindow :=
    le_of_not_gt fun hterminal =>
      hnotBad (Or.inl hterminal)
  have hgood : ∀ level : Fin depth,
      |prefixDelta active label seed level.val| ≤
        window level := by
    intro level
    exact le_of_not_gt fun hlevel =>
      hnotBad (Or.inr ⟨level, hlevel⟩)
  apply decide_eq_true
  intro candidate
  exact aeval_listPolynomialVector active label seed
    window terminalWindow hterminal hgood candidate

theorem polynomialListFailure_pointwise_le_bad
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (seed : ToeplitzSeed rank) :
    bitAsReal
        (!(polynomialListSucceeds active label
          window terminalWindow seed)) ≤
      bitAsReal
        (prefixListBad active label window terminalWindow seed) := by
  cases hbad :
      prefixListBad active label window terminalWindow seed
  · have hsuccess :=
      polynomialListSucceeds_of_not_bad
        active label window terminalWindow seed hbad
    rw [hsuccess]
    simp [bitAsReal]
  · cases polynomialListSucceeds active label
      window terminalWindow seed <;>
      simp [bitAsReal]

theorem polynomialListFailure_le_bad
    {rank depth population : ℕ}
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (window : Fin depth → ℕ) (terminalWindow : ℕ) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      !(polynomialListSucceeds active label
        window terminalWindow seed)) ≤
      booleanMean
        (prefixListBad active label window terminalWindow) := by
  unfold booleanMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun seed _ =>
      polynomialListFailure_pointwise_le_bad
        active label window terminalWindow seed
  · positivity

noncomputable def listFailureBound
    {depth : ℕ} (activeBound : ℕ)
    (window : Fin depth → ℕ) (terminalWindow : ℕ) : ℝ :=
  ((activeBound : ℝ) / (2 : ℝ) ^ depth) /
      (terminalWindow + 1 : ℕ) +
    ∑ level : Fin depth,
      (((activeBound : ℝ) *
          (1 / (2 : ℝ) ^ level.val)) /
        (window level : ℝ) ^ 2)

theorem polynomialListFailure_bound
    {rank depth population : ℕ} (hdepth : depth ≤ rank)
    (active : Finset (Fin population))
    (label : Fin population → BinaryVector rank)
    (activeBound : ℕ) (window : Fin depth → ℕ)
    (terminalWindow : ℕ)
    (hlabels : ∀ left ∈ active, ∀ right ∈ active,
      left ≠ right → label left ≠ label right)
    (hactive : active.card ≤ activeBound)
    (hwindow : ∀ level, 0 < window level) :
    booleanMean (fun seed : ToeplitzSeed rank =>
      !(polynomialListSucceeds active label
        window terminalWindow seed)) ≤
      listFailureBound activeBound window terminalWindow := by
  exact (polynomialListFailure_le_bad
    active label window terminalWindow).trans
      (prefixListBad_unionBound hdepth active label
        activeBound window terminalWindow
        hlabels hactive hwindow)

abbrev BoundedActiveSet (population activeBound : ℕ) :=
  {active : Finset (Fin population) // active.card ≤ activeBound}

noncomputable def toeplitzBaseListCertificate
    {rank depth population activeBound : ℕ}
    (hdepth : depth ≤ rank)
    (label : Fin population → BinaryVector rank)
    (hlabel : Function.Injective label)
    (window : Fin depth → ℕ) (terminalWindow : ℕ)
    (hwindow : ∀ level, 0 < window level) :
    AmplifiedListCertificate
      (BoundedActiveSet population activeBound)
      (ToeplitzSeed rank) where
  cardPositive := Fintype.card_pos
  succeeds := fun input seed =>
    polynomialListSucceeds input.1 label
      window terminalWindow seed
  failure := listFailureBound activeBound window terminalWindow
  failureNonnegative := by
    unfold listFailureBound
    positivity
  pointwise := by
    intro input
    apply polynomialListFailure_bound hdepth input.1 label
      activeBound window terminalWindow
    · intro left _ right _ hne
      exact hlabel.ne hne
    · exact input.2
    · exact hwindow

end NearCubicWires.SupplierListPolynomial
