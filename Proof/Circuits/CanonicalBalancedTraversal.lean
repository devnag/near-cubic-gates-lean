import Proof.Foundations.CanonicalBinaryProgram

/-!
# Exact interpreter semantics for balanced public sequences

`CanonicalBalanced` is the sole public variable-length sequence ABI.  This
module gives its fixed depth-first controller a compositional interpreter
semantics.  The semantic tree below is a proof view of the canonical code, not
another accepted encoding: executable interfaces still receive only
`encodeBalancedList`.
-/

namespace NearCubicWires.CanonicalBinaryProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.PolynomialClock

/-- Proof-only syntax matching the three constructors of
`encodeBalancedList`. -/
inductive BalancedTraversalTree where
  | empty
  | leaf (atom : ℕ)
  | branch (left right : BalancedTraversalTree)
  deriving DecidableEq, Repr

namespace BalancedTraversalTree

def code : BalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf atom => Nat.pair 1 atom
  | .branch left right =>
      Nat.pair 2 (Nat.pair left.code right.code)

def atoms : BalancedTraversalTree → List ℕ
  | .empty => []
  | .leaf atom => [atom]
  | .branch left right => left.atoms ++ right.atoms

def map (f : ℕ → ℕ) : BalancedTraversalTree → BalancedTraversalTree
  | .empty => .empty
  | .leaf atom => .leaf (f atom)
  | .branch left right => .branch (left.map f) (right.map f)

def height : BalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .branch left right => 1 + max left.height right.height

def leafCount : BalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf _ => 1
  | .branch left right => left.leafCount + right.leafCount

def nodeCount : BalancedTraversalTree → ℕ
  | .empty => 1
  | .leaf _ => 1
  | .branch left right => 1 + left.nodeCount + right.nodeCount

@[simp] theorem atoms_map (tree : BalancedTraversalTree) (f : ℕ → ℕ) :
    (tree.map f).atoms = tree.atoms.map f := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right ihLeft ihRight =>
      simp [map, atoms, ihLeft, ihRight]

@[simp] theorem leafCount_eq_length_atoms (tree : BalancedTraversalTree) :
    tree.leafCount = tree.atoms.length := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right ihLeft ihRight =>
      simp [leafCount, atoms, ihLeft, ihRight]

@[simp] theorem nodeCount_map (tree : BalancedTraversalTree) (f : ℕ → ℕ) :
    (tree.map f).nodeCount = tree.nodeCount := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right ihLeft ihRight =>
      simp [map, nodeCount, ihLeft, ihRight]

end BalancedTraversalTree

/-! ## Total structural view of arbitrary raw codes -/

/-- Proof syntax for the controller's behavior on every natural.  Raw tags
are retained so the final equality guard can detect every normalization. -/
inductive RawBalancedTraversalTree where
  | empty
  | leaf (tag atom : ℕ)
  | branch (tag : ℕ)
      (left right : RawBalancedTraversalTree)
  deriving DecidableEq, Repr

namespace RawBalancedTraversalTree

def rawCode : RawBalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf tag atom => Nat.pair tag atom
  | .branch tag left right =>
      Nat.pair tag (Nat.pair left.rawCode right.rawCode)

def normalized : RawBalancedTraversalTree → BalancedTraversalTree
  | .empty => .empty
  | .leaf _tag atom => .leaf atom
  | .branch _tag left right =>
      .branch left.normalized right.normalized

def atoms (tree : RawBalancedTraversalTree) : List ℕ :=
  tree.normalized.atoms

def nodeCount : RawBalancedTraversalTree → ℕ
  | .empty => 1
  | .leaf _ _ => 1
  | .branch _ left right => 1 + left.nodeCount + right.nodeCount

/-- Exactly the raw shapes selected by the fixed controller. -/
def Valid : RawBalancedTraversalTree → Prop
  | .empty => True
  | .leaf tag atom =>
      Nat.pair tag atom ≠ 0 ∧ (Nat.unpair tag).1 = 0
  | .branch tag left right =>
      (Nat.unpair tag).1 ≠ 0 ∧ left.Valid ∧ right.Valid

end RawBalancedTraversalTree

/-- Total parser for the controller's actual raw-tag classification.  This is
a proof view only; executable code remains the fixed register controller. -/
def rawBalancedTraversalTree (code : ℕ) : RawBalancedTraversalTree :=
  if _hzero : code = 0 then
    .empty
  else
    let outer := Nat.unpair code
    if _hleaf : (Nat.unpair outer.1).1 = 0 then
      .leaf outer.1 outer.2
    else
      let branches := Nat.unpair outer.2
      .branch outer.1
        (rawBalancedTraversalTree branches.1)
        (rawBalancedTraversalTree branches.2)
termination_by code
decreasing_by
  all_goals
    have htagPositive : 0 < outer.1 := by
      by_contra hnotPositive
      have htagZero : outer.1 = 0 := Nat.eq_zero_of_not_pos hnotPositive
      exact _hleaf (by simp [htagZero])
    have hpayloadLt : outer.2 < code := by
      have hsum : outer.1 + outer.2 ≤ code := by
        simpa only [outer] using Nat.unpair_add_le code
      omega
  · exact (Nat.unpair_left_le outer.2).trans_lt hpayloadLt
  · exact (Nat.unpair_right_le outer.2).trans_lt hpayloadLt

theorem rawBalancedTraversalTree_rawCode (code : ℕ) :
    (rawBalancedTraversalTree code).rawCode = code := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      rw [rawBalancedTraversalTree]
      split
      · rename_i hzero
        simp [hzero, RawBalancedTraversalTree.rawCode]
      · rename_i hzero
        dsimp only
        split
        · simpa only [RawBalancedTraversalTree.rawCode] using
            Nat.pair_unpair code
        · rename_i hleaf
          let outer := Nat.unpair code
          let branches := Nat.unpair outer.2
          have htagPositiveRaw : 0 < (Nat.unpair code).1 := by
            by_contra hnotPositive
            have htagZero :
                (Nat.unpair code).1 = 0 :=
              Nat.eq_zero_of_not_pos hnotPositive
            exact hleaf (by simp [htagZero])
          have hpayloadLtRaw : (Nat.unpair code).2 < code := by
            have hsum := Nat.unpair_add_le code
            omega
          have hpayloadLt : outer.2 < code := by
            simpa only [outer] using hpayloadLtRaw
          have hleftLt : branches.1 < code :=
            (Nat.unpair_left_le outer.2).trans_lt hpayloadLt
          have hrightLt : branches.2 < code :=
            (Nat.unpair_right_le outer.2).trans_lt hpayloadLt
          simp only [RawBalancedTraversalTree.rawCode]
          rw [inductionHypothesis branches.1 hleftLt,
            inductionHypothesis branches.2 hrightLt]
          simp [branches, outer]

theorem rawBalancedTraversalTree_valid (code : ℕ) :
    (rawBalancedTraversalTree code).Valid := by
  induction code using Nat.strong_induction_on with
  | h code inductionHypothesis =>
      rw [rawBalancedTraversalTree]
      split
      · simp [RawBalancedTraversalTree.Valid]
      · rename_i hzero
        dsimp only
        split
        · rename_i hleaf
          let outer := Nat.unpair code
          simp only [RawBalancedTraversalTree.Valid]
          exact ⟨by
            rw [Nat.pair_unpair]
            exact hzero, hleaf⟩
        · rename_i hleaf
          let outer := Nat.unpair code
          let branches := Nat.unpair outer.2
          have htagPositiveRaw : 0 < (Nat.unpair code).1 := by
            by_contra hnotPositive
            have htagZero :
                (Nat.unpair code).1 = 0 :=
              Nat.eq_zero_of_not_pos hnotPositive
            exact hleaf (by simp [htagZero])
          have hpayloadLtRaw : (Nat.unpair code).2 < code := by
            have hsum := Nat.unpair_add_le code
            omega
          have hpayloadLt : outer.2 < code := by
            simpa only [outer] using hpayloadLtRaw
          have hleftLt : branches.1 < code :=
            (Nat.unpair_left_le outer.2).trans_lt hpayloadLt
          have hrightLt : branches.2 < code :=
            (Nat.unpair_right_le outer.2).trans_lt hpayloadLt
          exact ⟨hleaf,
            inductionHypothesis branches.1 hleftLt,
            inductionHypothesis branches.2 hrightLt⟩

namespace RawBalancedTraversalTree

/-- Canonical structural trees embed with exact public tags. -/
def ofBalanced : BalancedTraversalTree → RawBalancedTraversalTree
  | .empty => .empty
  | .leaf atom => .leaf 1 atom
  | .branch left right =>
      .branch 2 (ofBalanced left) (ofBalanced right)

@[simp] theorem rawCode_ofBalanced (tree : BalancedTraversalTree) :
    (ofBalanced tree).rawCode = tree.code := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right inductionLeft inductionRight =>
      simp [ofBalanced, rawCode, BalancedTraversalTree.code,
        inductionLeft, inductionRight]

@[simp] theorem normalized_ofBalanced (tree : BalancedTraversalTree) :
    (ofBalanced tree).normalized = tree := by
  induction tree with
  | empty => rfl
  | leaf atom => rfl
  | branch left right inductionLeft inductionRight =>
      simp [ofBalanced, normalized, inductionLeft, inductionRight]

theorem valid_ofBalanced (tree : BalancedTraversalTree) :
    (ofBalanced tree).Valid := by
  induction tree with
  | empty =>
      trivial
  | leaf atom =>
      refine ⟨?_, by norm_num [Nat.unpair]⟩
      have := Nat.left_le_pair 1 atom
      omega
  | branch left right inductionLeft inductionRight =>
      exact ⟨by norm_num [Nat.unpair],
        inductionLeft, inductionRight⟩

end RawBalancedTraversalTree

theorem rawBalancedTraversalTree_of_valid
    (tree : RawBalancedTraversalTree) (hvalid : tree.Valid) :
    rawBalancedTraversalTree tree.rawCode = tree := by
  induction tree with
  | empty =>
      simp [rawBalancedTraversalTree,
        RawBalancedTraversalTree.rawCode]
  | leaf tag atom =>
      rcases hvalid with ⟨hnonzero, htagClass⟩
      simp [rawBalancedTraversalTree,
        RawBalancedTraversalTree.rawCode, hnonzero, htagClass]
  | branch tag left right inductionLeft inductionRight =>
      rcases hvalid with
        ⟨htagClass, hleftValid, hrightValid⟩
      have hnonzero :
          Nat.pair tag (Nat.pair left.rawCode right.rawCode) ≠ 0 := by
        intro hzero
        have htagZero : tag = 0 := by
          have := Nat.left_le_pair tag
            (Nat.pair left.rawCode right.rawCode)
          omega
        exact htagClass (by simp [htagZero])
      simp [rawBalancedTraversalTree,
        RawBalancedTraversalTree.rawCode, hnonzero, htagClass,
        inductionLeft hleftValid, inductionRight hrightValid]

theorem rawBalancedTraversalTree_normalized_code
    (tree : BalancedTraversalTree) :
    (rawBalancedTraversalTree tree.code).normalized = tree := by
  rw [← RawBalancedTraversalTree.rawCode_ofBalanced tree,
    rawBalancedTraversalTree_of_valid
      (RawBalancedTraversalTree.ofBalanced tree)
      (RawBalancedTraversalTree.valid_ofBalanced tree)]
  exact RawBalancedTraversalTree.normalized_ofBalanced tree

/-- The proof tree is an exact structural view of the tag decoder whenever
the caller supplies enough recursion fuel.  This theorem intentionally does
not claim that an arbitrary structural tree has the canonical midpoint shape. -/
theorem decodeBalancedListAux_tree
    (tree : BalancedTraversalTree) (fuel : ℕ)
    (hfuel : tree.height ≤ fuel) :
    decodeBalancedListAux fuel tree.code = some tree.atoms := by
  induction tree generalizing fuel with
  | empty =>
      cases fuel <;>
        simp [BalancedTraversalTree.code, BalancedTraversalTree.atoms,
          decodeBalancedListAux]
  | leaf atom =>
      cases fuel with
      | zero =>
          simp [BalancedTraversalTree.height] at hfuel
      | succ fuel =>
          have hnonzero : Nat.pair 1 atom ≠ 0 := by
            have := Nat.left_le_pair 1 atom
            omega
          simp [BalancedTraversalTree.code, BalancedTraversalTree.atoms,
            decodeBalancedListAux, hnonzero]
  | branch left right ihLeft ihRight =>
      cases fuel with
      | zero =>
          simp [BalancedTraversalTree.height] at hfuel
      | succ fuel =>
          have hleft : left.height ≤ fuel := by
            simp [BalancedTraversalTree.height] at hfuel
            omega
          have hright : right.height ≤ fuel := by
            simp [BalancedTraversalTree.height] at hfuel
            omega
          have hdecodeLeft := ihLeft fuel hleft
          have hdecodeRight := ihRight fuel hright
          have hnonzero :
              Nat.pair 2 (Nat.pair left.code right.code) ≠ 0 := by
            have := Nat.left_le_pair 2
              (Nat.pair left.code right.code)
            omega
          simp [BalancedTraversalTree.code, BalancedTraversalTree.atoms,
            decodeBalancedListAux, hnonzero, hdecodeLeft, hdecodeRight]

/-- Structural height is bounded by the code itself.  This supplies a total
decoder budget without trusting a caller-provided recursion limit. -/
theorem balancedTraversalTree_height_le_code
    (tree : BalancedTraversalTree) :
    tree.height ≤ tree.code + 1 := by
  induction tree with
  | empty =>
      simp [BalancedTraversalTree.height, BalancedTraversalTree.code]
  | leaf atom =>
      simp only [BalancedTraversalTree.height, BalancedTraversalTree.code]
      have := Nat.left_le_pair 1 atom
      omega
  | branch left right ihLeft ihRight =>
      let payload := Nat.pair left.code right.code
      have hpayload : payload + 2 ≤ Nat.pair 2 payload := by
        simpa [payload, Nat.add_comm] using Nat.add_le_pair 2 payload
      have hleftCode : left.code ≤ payload := by
        exact Nat.left_le_pair left.code right.code
      have hrightCode : right.code ≤ payload := by
        exact Nat.right_le_pair left.code right.code
      simp only [BalancedTraversalTree.height, BalancedTraversalTree.code]
      change
        1 + max left.height right.height ≤ Nat.pair 2 payload + 1
      omega

theorem decodeBalancedListCandidate_tree
    (tree : BalancedTraversalTree) :
    decodeBalancedListCandidate tree.code = some tree.atoms := by
  unfold decodeBalancedListCandidate
  exact decodeBalancedListAux_tree tree (tree.code + 1)
    (balancedTraversalTree_height_le_code tree)

theorem decodeBalancedList_tree (tree : BalancedTraversalTree) :
    decodeBalancedList tree.code =
      if encodeBalancedList tree.atoms = tree.code
      then some tree.atoms
      else none := by
  unfold decodeBalancedList
  rw [decodeBalancedListCandidate_tree]
  simp

/-- Canonical midpoint tree used only to reason about the public code. -/
def balancedTraversalTree : List ℕ → BalancedTraversalTree
  | [] => .empty
  | [atom] => .leaf atom
  | first :: second :: rest =>
      let values := first :: second :: rest
      let leftLength := (values.length + 1) / 2
      .branch
        (balancedTraversalTree (values.take leftLength))
        (balancedTraversalTree (values.drop leftLength))
termination_by values => values.length
decreasing_by
  all_goals
    simp_wf
    have : ((rest.length + 2 + 1) / 2) ≤ rest.length + 1 := by omega
    simp
    omega

theorem balancedTraversalTree_code (values : List ℕ) :
    (balancedTraversalTree values).code = encodeBalancedList values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, BalancedTraversalTree.code,
            encodeBalancedList]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, BalancedTraversalTree.code,
                encodeBalancedList]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              simp only [balancedTraversalTree, encodeBalancedList,
                BalancedTraversalTree.code]
              change
                Nat.pair 2
                      (Nat.pair
                        (balancedTraversalTree left).code
                        (balancedTraversalTree right).code) =
                    Nat.pair 2
                      (Nat.pair
                        (encodeBalancedList left)
                        (encodeBalancedList right))
              exact congrArg (Nat.pair 2)
                (congrArg₂ Nat.pair ihLeft ihRight)

theorem balancedTraversalTree_atoms (values : List ℕ) :
    (balancedTraversalTree values).atoms = values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, BalancedTraversalTree.atoms]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, BalancedTraversalTree.atoms]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              simp only [balancedTraversalTree,
                BalancedTraversalTree.atoms]
              change
                (balancedTraversalTree left).atoms ++
                    (balancedTraversalTree right).atoms =
                  values
              rw [ihLeft, ihRight]
              simp [left, right]

theorem balancedTraversalTree_nodeCount (values : List ℕ) :
    (balancedTraversalTree values).nodeCount =
      if values = [] then 1 else 2 * values.length - 1 := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, BalancedTraversalTree.nodeCount]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, BalancedTraversalTree.nodeCount]
              simp at hlength
              omega
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hrightPositive : 0 < right.length := by
                rw [hrightLengthEq]
                omega
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              have hleftNonempty : left ≠ [] :=
                List.ne_nil_of_length_pos (by
                  rw [hleftLengthEq]
                  exact hleftPositive)
              have hrightNonempty : right ≠ [] :=
                List.ne_nil_of_length_pos hrightPositive
              simp only [balancedTraversalTree,
                BalancedTraversalTree.nodeCount]
              rw [ihLeft, ihRight]
              simp only [if_neg hleftNonempty, if_neg hrightNonempty]
              simp only [List.cons_ne_nil, if_false]
              rw [← hlengthValues]
              change
                1 + (2 * left.length - 1) +
                    (2 * right.length - 1) =
                  2 * values.length - 1
              have hparts : left.length + right.length = values.length := by
                rw [hleftLengthEq, hrightLengthEq]
                omega
              omega

theorem balancedTraversalTree_map (values : List ℕ) (f : ℕ → ℕ) :
    balancedTraversalTree (values.map f) =
      (balancedTraversalTree values).map f := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, BalancedTraversalTree.map]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, BalancedTraversalTree.map]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have htwo : 2 ≤ values.length := by simp [values]
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              have hleftMap :
                  (values.map f).take leftLength = left.map f := by
                simp [left]
              have hrightMap :
                  (values.map f).drop leftLength = right.map f := by
                simp [right]
              have hmappedMid :
                  ((f first :: f second :: rest.map f).length + 1) / 2 =
                    leftLength := by
                simp [leftLength, values]
              simp only [List.map, balancedTraversalTree,
                BalancedTraversalTree.map]
              rw [hmappedMid]
              change
                BalancedTraversalTree.branch
                    (balancedTraversalTree
                      ((values.map f).take leftLength))
                    (balancedTraversalTree
                      ((values.map f).drop leftLength)) =
                  BalancedTraversalTree.branch
                    ((balancedTraversalTree left).map f)
                    ((balancedTraversalTree right).map f)
              rw [hleftMap, hrightMap, ihLeft, ihRight]

theorem balancedTraversalTree_map_code (values : List ℕ) (f : ℕ → ℕ) :
    ((balancedTraversalTree values).map f).code =
      encodeBalancedList (values.map f) := by
  rw [← balancedTraversalTree_map values f,
    balancedTraversalTree_code]

/-- The proof-view tree has exactly the height charged by the canonical
balanced-list codec.  Keeping this bridge public lets every balanced
controller share the same logarithmic continuation-depth ledger. -/
theorem balancedTraversalTree_height_eq (values : List ℕ) :
    (balancedTraversalTree values).height = balancedListHeight values := by
  induction hlength : values.length using Nat.strong_induction_on
      generalizing values with
  | h length ih =>
      cases values with
      | nil =>
          simp [balancedTraversalTree, balancedListHeight,
            BalancedTraversalTree.height]
      | cons first rest =>
          cases rest with
          | nil =>
              simp [balancedTraversalTree, balancedListHeight,
                BalancedTraversalTree.height]
          | cons second rest =>
              let values := first :: second :: rest
              let leftLength := (values.length + 1) / 2
              let left := values.take leftLength
              let right := values.drop leftLength
              have hlengthValues : values.length = length := by
                simpa [values] using hlength
              have hleftPositive : 0 < leftLength := by
                dsimp [leftLength, values]
                omega
              have hleftLtValues : leftLength < values.length := by
                dsimp [leftLength, values]
                omega
              have hleftLengthEq : left.length = leftLength := by
                simp [left, hleftLtValues.le]
              have hrightLengthEq :
                  right.length = values.length - leftLength := by
                simp [right]
              have hleftLt : left.length < length := by
                rw [hleftLengthEq, ← hlengthValues]
                exact hleftLtValues
              have hrightLt : right.length < length := by
                rw [hrightLengthEq, ← hlengthValues]
                omega
              have ihLeft := ih left.length hleftLt left rfl
              have ihRight := ih right.length hrightLt right rfl
              simp only [balancedTraversalTree, balancedListHeight,
                BalancedTraversalTree.height]
              change
                1 + max (balancedTraversalTree left).height
                      (balancedTraversalTree right).height =
                  1 + max (balancedListHeight left)
                    (balancedListHeight right)
              rw [ihLeft, ihRight]

/-- Exact finite execution segment.  It exposes the reached state even though
`runNPOracleProgram` intentionally exposes only a final output. -/
def RunsToIn (program : NPOracleProgram) (maximumBits steps : ℕ)
    (start finish : NPOracleState) : Prop :=
  ∀ extra,
    runNPOracleProgram program maximumBits (steps + extra) start =
      runNPOracleProgram program maximumBits extra finish

@[refl] theorem RunsToIn.refl (program : NPOracleProgram)
    (maximumBits : ℕ) (state : NPOracleState) :
    RunsToIn program maximumBits 0 state state := by
  intro extra
  simp

theorem RunsToIn.trans {program : NPOracleProgram} {maximumBits first second : ℕ}
    {start middle finish : NPOracleState}
    (hfirst : RunsToIn program maximumBits first start middle)
    (hsecond : RunsToIn program maximumBits second middle finish) :
    RunsToIn program maximumBits (first + second) start finish := by
  intro extra
  rw [Nat.add_assoc, hfirst, hsecond]

def RunsWithin (program : NPOracleProgram) (maximumBits budget : ℕ)
    (start : NPOracleState) (post : NPOracleState → Prop) : Prop :=
  ∀ extra finalOutput,
    (∀ finish unused, post finish →
      runNPOracleProgram program maximumBits (unused + extra) finish =
        some finalOutput) →
    runNPOracleProgram program maximumBits (budget + extra) start =
      some finalOutput

theorem RunsToIn.toRunsWithin
    {program : NPOracleProgram} {maximumBits steps : ℕ}
    {start finish : NPOracleState}
    (hruns : RunsToIn program maximumBits steps start finish) :
    RunsWithin program maximumBits steps start (· = finish) := by
  intro extra finalOutput hcontinuation
  rw [hruns extra]
  simpa using hcontinuation finish 0 rfl

theorem RunsWithin.mono
    {program : NPOracleProgram} {maximumBits budget : ℕ}
    {start : NPOracleState} {strong weak : NPOracleState → Prop}
    (hruns : RunsWithin program maximumBits budget start strong)
    (hpost : ∀ state, strong state → weak state) :
    RunsWithin program maximumBits budget start weak := by
  intro extra finalOutput hcontinuation
  apply hruns extra finalOutput
  intro finish unused hstrong
  exact hcontinuation finish unused (hpost finish hstrong)

theorem RunsWithin.trans
    {program : NPOracleProgram} {maximumBits firstBudget secondBudget : ℕ}
    {start : NPOracleState} {middlePost finishPost : NPOracleState → Prop}
    (hfirst :
      RunsWithin program maximumBits firstBudget start middlePost)
    (hsecond : ∀ middle, middlePost middle →
      RunsWithin program maximumBits secondBudget middle finishPost) :
    RunsWithin program maximumBits (firstBudget + secondBudget)
      start finishPost := by
  intro extra finalOutput hcontinuation
  rw [Nat.add_assoc]
  apply hfirst (secondBudget + extra) finalOutput
  intro middle firstUnused hmiddle
  have hrun := hsecond middle hmiddle (firstUnused + extra) finalOutput
    (by
      intro finish secondUnused hfinish
      have hcontinue :=
        hcontinuation finish (secondUnused + firstUnused) hfinish
      simpa [Nat.add_assoc] using hcontinue)
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun

/-- The fixed controller occupies its canonical PCs in a larger concrete
program.  Handlers and consumers may follow it, but the controller itself is
never relocated or duplicated. -/
def BalancedTraversalControllerAt (program : NPOracleProgram)
    (leafPc donePc : ℕ) : Prop :=
  ∀ (pc : ℕ) (instruction : NPOracleInstruction),
    (balancedTraversalController leafPc donePc)[pc]? = some instruction →
      program[pc]? = some instruction

@[simp] theorem balancedTraversalControllerAt_self (leafPc donePc : ℕ) :
    BalancedTraversalControllerAt
      (balancedTraversalController leafPc donePc) leafPc donePc := by
  intro pc instruction hlookup
  exact hlookup

def SameRegistersFrom (first : ℕ) (left right : NPOracleState) : Prop :=
  ∀ register, first ≤ register →
    right.registers register = left.registers register

@[refl] theorem SameRegistersFrom.refl (first : ℕ) (state : NPOracleState) :
    SameRegistersFrom first state state := by
  intro register _
  rfl

theorem SameRegistersFrom.trans {base : ℕ}
    {first second third : NPOracleState}
    (hfirst : SameRegistersFrom base first second)
    (hsecond : SameRegistersFrom base second third) :
    SameRegistersFrom base first third := by
  intro register hregister
  rw [hsecond register hregister, hfirst register hregister]

theorem SameRegistersFrom.weaken {low high : ℕ}
    {left right : NPOracleState}
    (hsame : SameRegistersFrom low left right) (hlow : low ≤ high) :
    SameRegistersFrom high left right := by
  intro register hregister
  exact hsame register (hlow.trans hregister)

structure SameTraversalContextFrom (first : ℕ)
    (left right : NPOracleState) : Prop where
  inputLength : right.registers 1 = left.registers 1
  persistent : SameRegistersFrom first left right

@[refl] theorem SameTraversalContextFrom.refl
    (first : ℕ) (state : NPOracleState) :
    SameTraversalContextFrom first state state :=
  ⟨rfl, SameRegistersFrom.refl first state⟩

theorem SameTraversalContextFrom.trans {base : ℕ}
    {first second third : NPOracleState}
    (hfirst : SameTraversalContextFrom base first second)
    (hsecond : SameTraversalContextFrom base second third) :
    SameTraversalContextFrom base first third :=
  ⟨hsecond.inputLength.trans hfirst.inputLength,
    hfirst.persistent.trans hsecond.persistent⟩

theorem SameTraversalContextFrom.weaken {low high : ℕ}
    {left right : NPOracleState}
    (hsame : SameTraversalContextFrom low left right)
    (hlow : low ≤ high) :
    SameTraversalContextFrom high left right :=
  ⟨hsame.inputLength, hsame.persistent.weaken hlow⟩

abbrev SameBalancedPersistent :=
  SameTraversalContextFrom 9

/-- Width certificate for normalizing arbitrary raw syntax.  Visit frames
retain raw right subtrees; combine frames retain the already-normalized left
result, exactly matching the controller's register behavior. -/
def RawBalancedTraversalFits (maximumBits : ℕ) :
    RawBalancedTraversalTree → List BalancedTraversalFrame → Prop
  | tree, frames =>
      natBitLength tree.rawCode ≤ maximumBits ∧
      natBitLength tree.normalized.code ≤ maximumBits ∧
      natBitLength (encodeBalancedTraversalStack frames) ≤ maximumBits ∧
      match tree with
      | .empty => True
      | .leaf _tag atom => natBitLength atom ≤ maximumBits
      | .branch _tag left right =>
          RawBalancedTraversalFits maximumBits left
              (.visitRight right.rawCode :: frames) ∧
            RawBalancedTraversalFits maximumBits right
              (.combineLeft left.normalized.code :: frames)

def rawBalancedTraversalRequiredBits :
    RawBalancedTraversalTree → List BalancedTraversalFrame → ℕ
  | tree, frames =>
      max (natBitLength tree.rawCode)
        (max (natBitLength tree.normalized.code)
          (max (natBitLength (encodeBalancedTraversalStack frames))
            (match tree with
            | .empty => 0
            | .leaf _tag atom => natBitLength atom
            | .branch _tag left right =>
                max
                  (rawBalancedTraversalRequiredBits left
                    (.visitRight right.rawCode :: frames))
                  (rawBalancedTraversalRequiredBits right
                    (.combineLeft left.normalized.code :: frames)))))

theorem rawBalancedTraversalRequiredBits_le_iff
    (maximumBits : ℕ) (tree : RawBalancedTraversalTree)
    (frames : List BalancedTraversalFrame) :
    rawBalancedTraversalRequiredBits tree frames ≤ maximumBits ↔
      RawBalancedTraversalFits maximumBits tree frames := by
  induction tree generalizing frames with
  | empty =>
      simp [rawBalancedTraversalRequiredBits, RawBalancedTraversalFits]
  | leaf tag atom =>
      simp [rawBalancedTraversalRequiredBits, RawBalancedTraversalFits]
  | branch tag left right ihLeft ihRight =>
      simp [rawBalancedTraversalRequiredBits, RawBalancedTraversalFits,
        ihLeft, ihRight]

theorem RawBalancedTraversalFits.stack
    {maximumBits : ℕ} {tree : RawBalancedTraversalTree}
    {frames : List BalancedTraversalFrame}
    (hfit : RawBalancedTraversalFits maximumBits tree frames) :
    natBitLength (encodeBalancedTraversalStack frames) ≤ maximumBits := by
  cases tree <;> simp only [RawBalancedTraversalFits] at hfit
  all_goals exact hfit.2.2.1

theorem RawBalancedTraversalFits.input
    {maximumBits : ℕ} {tree : RawBalancedTraversalTree}
    {frames : List BalancedTraversalFrame}
    (hfit : RawBalancedTraversalFits maximumBits tree frames) :
    natBitLength tree.rawCode ≤ maximumBits := by
  cases tree <;> simp only [RawBalancedTraversalFits] at hfit
  all_goals exact hfit.1

theorem RawBalancedTraversalFits.output
    {maximumBits : ℕ} {tree : RawBalancedTraversalTree}
    {frames : List BalancedTraversalFrame}
    (hfit : RawBalancedTraversalFits maximumBits tree frames) :
    natBitLength tree.normalized.code ≤ maximumBits := by
  cases tree <;> simp only [RawBalancedTraversalFits] at hfit
  all_goals exact hfit.2.1

/-- Recursive width certificate for exactly the values materialized by the
controller.  It is quantitative data, not a semantic assumption: downstream
interfaces discharge it from the balanced-code and logarithmic-stack bounds. -/
def BalancedTraversalFits (maximumBits : ℕ) (f : ℕ → ℕ) :
    BalancedTraversalTree → List BalancedTraversalFrame → Prop
  | tree, frames =>
      natBitLength tree.code ≤ maximumBits ∧
      natBitLength (tree.map f).code ≤ maximumBits ∧
      natBitLength (encodeBalancedTraversalStack frames) ≤ maximumBits ∧
      match tree with
      | .empty => True
      | .leaf atom =>
          natBitLength atom ≤ maximumBits ∧
          natBitLength (f atom) ≤ maximumBits
      | .branch left right =>
          BalancedTraversalFits maximumBits f left
              (.visitRight right.code :: frames) ∧
            BalancedTraversalFits maximumBits f right
              (.combineLeft (left.map f).code :: frames)

/-- Exact computable register-width requirement for a traversal.  This
packages every transient tree, mapped tree, stack, atom, and mapped atom into
one maximum; it is a certificate generator, not an additional semantic
assumption. -/
def balancedTraversalRequiredBits (f : ℕ → ℕ) :
    BalancedTraversalTree → List BalancedTraversalFrame → ℕ
  | tree, frames =>
      max (natBitLength tree.code)
        (max (natBitLength (tree.map f).code)
          (max (natBitLength (encodeBalancedTraversalStack frames))
            (match tree with
            | .empty => 0
            | .leaf atom =>
                max (natBitLength atom) (natBitLength (f atom))
            | .branch left right =>
                max
                  (balancedTraversalRequiredBits f left
                    (.visitRight right.code :: frames))
                  (balancedTraversalRequiredBits f right
                    (.combineLeft (left.map f).code :: frames)))))

theorem balancedTraversalRequiredBits_le_iff
    (maximumBits : ℕ) (f : ℕ → ℕ) (tree : BalancedTraversalTree)
    (frames : List BalancedTraversalFrame) :
    balancedTraversalRequiredBits f tree frames ≤ maximumBits ↔
      BalancedTraversalFits maximumBits f tree frames := by
  induction tree generalizing frames with
  | empty =>
      simp [balancedTraversalRequiredBits, BalancedTraversalFits]
  | leaf atom =>
      simp [balancedTraversalRequiredBits, BalancedTraversalFits]
  | branch left right ihLeft ihRight =>
      simp [balancedTraversalRequiredBits, BalancedTraversalFits,
        ihLeft, ihRight]

theorem balancedTraversalRequiredBits_atom
    {f : ℕ → ℕ} {tree : BalancedTraversalTree}
    {frames : List BalancedTraversalFrame} {atom : ℕ}
    (hmem : atom ∈ tree.atoms) :
    natBitLength atom ≤ balancedTraversalRequiredBits f tree frames := by
  induction tree generalizing frames with
  | empty => simp [BalancedTraversalTree.atoms] at hmem
  | leaf value =>
      simp only [BalancedTraversalTree.atoms, List.mem_singleton] at hmem
      subst atom
      simp [balancedTraversalRequiredBits]
  | branch left right ihLeft ihRight =>
      simp only [BalancedTraversalTree.atoms, List.mem_append] at hmem
      unfold balancedTraversalRequiredBits
      rcases hmem with hleft | hright
      · exact (ihLeft hleft).trans <|
          le_max_of_le_right (le_max_of_le_right
            (le_max_of_le_right (le_max_left _ _)))
      · exact (ihRight hright).trans <|
          le_max_of_le_right (le_max_of_le_right
            (le_max_of_le_right (le_max_right _ _)))

theorem balancedTraversalRequiredBits_mappedAtom
    {f : ℕ → ℕ} {tree : BalancedTraversalTree}
    {frames : List BalancedTraversalFrame} {atom : ℕ}
    (hmem : atom ∈ tree.atoms) :
    natBitLength (f atom) ≤
      balancedTraversalRequiredBits f tree frames := by
  induction tree generalizing frames with
  | empty => simp [BalancedTraversalTree.atoms] at hmem
  | leaf value =>
      simp only [BalancedTraversalTree.atoms, List.mem_singleton] at hmem
      subst atom
      simp [balancedTraversalRequiredBits]
  | branch left right ihLeft ihRight =>
      simp only [BalancedTraversalTree.atoms, List.mem_append] at hmem
      unfold balancedTraversalRequiredBits
      rcases hmem with hleft | hright
      · exact (ihLeft hleft).trans <|
          le_max_of_le_right (le_max_of_le_right
            (le_max_of_le_right (le_max_left _ _)))
      · exact (ihRight hright).trans <|
          le_max_of_le_right (le_max_of_le_right
            (le_max_of_le_right (le_max_right _ _)))

theorem BalancedTraversalFits.stack
    {maximumBits : ℕ} {f : ℕ → ℕ} {tree : BalancedTraversalTree}
    {frames : List BalancedTraversalFrame}
    (hfit : BalancedTraversalFits maximumBits f tree frames) :
    natBitLength (encodeBalancedTraversalStack frames) ≤ maximumBits := by
  cases tree <;> simp only [BalancedTraversalFits] at hfit
  all_goals exact hfit.2.2.1

theorem BalancedTraversalFits.input
    {maximumBits : ℕ} {f : ℕ → ℕ} {tree : BalancedTraversalTree}
    {frames : List BalancedTraversalFrame}
    (hfit : BalancedTraversalFits maximumBits f tree frames) :
    natBitLength tree.code ≤ maximumBits := by
  cases tree <;> simp only [BalancedTraversalFits] at hfit
  all_goals exact hfit.1

theorem BalancedTraversalFits.output
    {maximumBits : ℕ} {f : ℕ → ℕ} {tree : BalancedTraversalTree}
    {frames : List BalancedTraversalFrame}
    (hfit : BalancedTraversalFits maximumBits f tree frames) :
    natBitLength (tree.map f).code ≤ maximumBits := by
  cases tree <;> simp only [BalancedTraversalFits] at hfit
  all_goals exact hfit.2.1

theorem runsTo_branchZero
    {program : NPOracleProgram} {maximumBits pc register zeroTarget
      nonzeroTarget : ℕ} {state : NPOracleState}
    (hlookup : program[pc]? =
      some (.branchZero register zeroTarget nonzeroTarget))
    (hpc : state.pc = pc) :
    RunsToIn program maximumBits 1 state
      (state.jump (if state.registers register = 0 then
        zeroTarget else nonzeroTarget)) := by
  intro extra
  simpa [Nat.add_comm] using
    (run_branchZero_instruction (fuel := extra) hlookup hpc)

theorem runsTo_set
    {program : NPOracleProgram} {maximumBits pc register value next : ℕ}
    {state : NPOracleState}
    (hlookup : program[pc]? = some (.set register value next))
    (hpc : state.pc = pc)
    (hbits : natBitLength value ≤ maximumBits) :
    RunsToIn program maximumBits 1 state
      ((state.write register value).jump next) := by
  intro extra
  simpa [Nat.add_comm] using
    (run_set_instruction (fuel := extra) hlookup hpc hbits)

theorem runsTo_copy
    {program : NPOracleProgram} {maximumBits pc source destination next
      value : ℕ} {state : NPOracleState}
    (hlookup : program[pc]? = some (.copy source destination next))
    (hpc : state.pc = pc)
    (hvalue : state.registers source = value)
    (hbits : natBitLength value ≤ maximumBits) :
    RunsToIn program maximumBits 1 state
      ((state.write destination value).jump next) := by
  intro extra
  simpa [Nat.add_comm] using
    (run_copy_instruction (fuel := extra) hlookup hpc hvalue hbits)

theorem runsTo_pair
    {program : NPOracleProgram} {maximumBits pc left right destination next
      value : ℕ} {state : NPOracleState}
    (hlookup : program[pc]? =
      some (.pair left right destination next))
    (hpc : state.pc = pc)
    (hvalue :
      Nat.pair (state.registers left) (state.registers right) = value)
    (hbits : natBitLength value ≤ maximumBits) :
    RunsToIn program maximumBits 1 state
      ((state.write destination value).jump next) := by
  intro extra
  simpa [Nat.add_comm] using
    (run_pair_instruction (fuel := extra) hlookup hpc hvalue hbits)

theorem runsTo_unpairLeft
    {program : NPOracleProgram} {maximumBits pc source destination next
      value : ℕ} {state : NPOracleState}
    (hlookup : program[pc]? =
      some (.unpairLeft source destination next))
    (hpc : state.pc = pc)
    (hvalue : (Nat.unpair (state.registers source)).1 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    RunsToIn program maximumBits 1 state
      ((state.write destination value).jump next) := by
  intro extra
  simpa [Nat.add_comm] using
    (run_unpairLeft_instruction (fuel := extra)
      hlookup hpc hvalue hbits)

theorem runsTo_unpairRight
    {program : NPOracleProgram} {maximumBits pc source destination next
      value : ℕ} {state : NPOracleState}
    (hlookup : program[pc]? =
      some (.unpairRight source destination next))
    (hpc : state.pc = pc)
    (hvalue : (Nat.unpair (state.registers source)).2 = value)
    (hbits : natBitLength value ≤ maximumBits) :
    RunsToIn program maximumBits 1 state
      ((state.write destination value).jump next) := by
  intro extra
  simpa [Nat.add_comm] using
    (run_unpairRight_instruction (fuel := extra)
      hlookup hpc hvalue hbits)

theorem bitLength_of_le {left right maximumBits : ℕ}
    (hle : left ≤ right) (hbits : natBitLength right ≤ maximumBits) :
    natBitLength left ≤ maximumBits :=
  (natBitLength_mono hle).trans hbits

private theorem controller_lookup
    {program : NPOracleProgram} {leafPc donePc pc : ℕ}
    {instruction : NPOracleInstruction}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hlookup :
      (balancedTraversalController leafPc donePc)[pc]? =
        some instruction) :
    program[pc]? = some instruction :=
  hat pc instruction hlookup

private theorem controller_descend_empty
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = 0)
    (hzero : natBitLength 0 ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 2 state finish ∧
      finish.pc = 15 ∧
      finish.registers 0 = 0 ∧
      finish.registers 2 = state.registers 2 ∧
      SameBalancedPersistent state finish := by
  let afterBranch := state.jump 1
  let finish := (afterBranch.write 0 0).jump 15
  have hlookup0 :
      program[0]? = some (.branchZero 0 1 2) :=
    controller_lookup hat (by rfl)
  have hlookup1 :
      program[1]? = some (.set 0 0 15) :=
    controller_lookup hat (by rfl)
  have hfirst :
      RunsToIn program maximumBits 1 state afterBranch := by
    simpa [afterBranch, hcurrent] using
      runsTo_branchZero hlookup0 hpc
  have hsecond :
      RunsToIn program maximumBits 1 afterBranch finish := by
    exact runsTo_set hlookup1 (by rfl) hzero
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_⟩
  · simpa using hfirst.trans hsecond
  · simp [finish, afterBranch, NPOracleState.write]
  · simp [finish, afterBranch, NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, afterBranch, NPOracleState.write]
    · intro register hregister
      simp [finish, afterBranch, NPOracleState.write]
      omega

private theorem controller_descend_leaf
    {program : NPOracleProgram} {maximumBits leafPc donePc atom : ℕ}
    {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = Nat.pair 1 atom)
    (hcode : natBitLength (Nat.pair 1 atom) ≤ maximumBits)
    (hatom : natBitLength atom ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 6 state finish ∧
      finish.pc = leafPc ∧
      finish.registers 0 = Nat.pair 1 atom ∧
      finish.registers 2 = state.registers 2 ∧
      finish.registers 3 = atom ∧
      SameBalancedPersistent state finish := by
  let state₀ := state.jump 2
  let state₁ := (state₀.write 4 1).jump 3
  let state₂ := (state₁.write 5 0).jump 4
  let state₃ := state₂.jump 5
  let state₄ := (state₃.write 3 atom).jump 6
  let finish := (state₄.write 3 atom).jump leafPc
  have hone :
      natBitLength 1 ≤ maximumBits :=
    bitLength_of_le (Nat.left_le_pair 1 atom) hcode
  have hzero :
      natBitLength 0 ≤ maximumBits :=
    bitLength_of_le (Nat.zero_le 1) hone
  have hlookup0 :
      program[0]? = some (.branchZero 0 1 2) :=
    controller_lookup hat (by rfl)
  have hlookup2 :
      program[2]? = some (.unpairLeft 0 4 3) :=
    controller_lookup hat (by rfl)
  have hlookup3 :
      program[3]? = some (.unpairLeft 4 5 4) :=
    controller_lookup hat (by rfl)
  have hlookup4 :
      program[4]? = some (.branchZero 5 5 7) :=
    controller_lookup hat (by rfl)
  have hlookup5 :
      program[5]? = some (.unpairRight 0 3 6) :=
    controller_lookup hat (by rfl)
  have hlookup6 :
      program[6]? = some (.copy 3 3 leafPc) :=
    controller_lookup hat (by rfl)
  have hnonzero : Nat.pair 1 atom ≠ 0 := by
    have := Nat.left_le_pair 1 atom
    omega
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ := by
    simpa [state₀, hcurrent, hnonzero] using
      runsTo_branchZero hlookup0 hpc
  have step₁ :
      RunsToIn program maximumBits 1 state₀ state₁ := by
    apply runsTo_unpairLeft hlookup2 (by rfl) (value := 1)
    · simp [state₀, hcurrent]
    · exact hone
  have step₂ :
      RunsToIn program maximumBits 1 state₁ state₂ := by
    apply runsTo_unpairLeft hlookup3 (by rfl) (value := 0)
    · change (Nat.unpair 1).1 = 0
      norm_num [Nat.unpair]
    · exact hzero
  have step₃ :
      RunsToIn program maximumBits 1 state₂ state₃ := by
    simpa [state₃, state₂, state₁, state₀, NPOracleState.write] using
      runsTo_branchZero hlookup4 (state := state₂) (by rfl)
  have step₄ :
      RunsToIn program maximumBits 1 state₃ state₄ := by
    apply runsTo_unpairRight hlookup5 (by rfl) (value := atom)
    · simp [state₃, state₂, state₁, state₀, NPOracleState.write,
        hcurrent]
    · exact hatom
  have step₅ :
      RunsToIn program maximumBits 1 state₄ finish := by
    apply runsTo_copy hlookup6 (by rfl) (value := atom)
    · simp [state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write]
    · exact hatom
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using
      (((((step₀.trans step₁).trans step₂).trans step₃).trans step₄).trans
        step₅)
  · simp [finish, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write, hcurrent]
  · simp [finish, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write]
  · simp [finish, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write]
    · intro register hregister
      have hne3 : register ≠ 3 := by omega
      have hne4 : register ≠ 4 := by omega
      have hne5 : register ≠ 5 := by omega
      simp [finish, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, hne3, hne4, hne5]

private theorem controller_descend_rawLeaf
    {program : NPOracleProgram} {maximumBits leafPc donePc tag atom : ℕ}
    {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = Nat.pair tag atom)
    (hnonzero : Nat.pair tag atom ≠ 0)
    (htagClass : (Nat.unpair tag).1 = 0)
    (hcode : natBitLength (Nat.pair tag atom) ≤ maximumBits)
    (hatom : natBitLength atom ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 6 state finish ∧
      finish.pc = leafPc ∧
      finish.registers 0 = Nat.pair tag atom ∧
      finish.registers 2 = state.registers 2 ∧
      finish.registers 3 = atom ∧
      SameBalancedPersistent state finish := by
  let state₀ := state.jump 2
  let state₁ := (state₀.write 4 tag).jump 3
  let state₂ := (state₁.write 5 0).jump 4
  let state₃ := state₂.jump 5
  let state₄ := (state₃.write 3 atom).jump 6
  let finish := (state₄.write 3 atom).jump leafPc
  have htag : natBitLength tag ≤ maximumBits :=
    bitLength_of_le (Nat.left_le_pair tag atom) hcode
  have hclass : natBitLength 0 ≤ maximumBits :=
    bitLength_of_le (Nat.zero_le tag) htag
  have hlookup0 :
      program[0]? = some (.branchZero 0 1 2) :=
    controller_lookup hat (by rfl)
  have hlookup2 :
      program[2]? = some (.unpairLeft 0 4 3) :=
    controller_lookup hat (by rfl)
  have hlookup3 :
      program[3]? = some (.unpairLeft 4 5 4) :=
    controller_lookup hat (by rfl)
  have hlookup4 :
      program[4]? = some (.branchZero 5 5 7) :=
    controller_lookup hat (by rfl)
  have hlookup5 :
      program[5]? = some (.unpairRight 0 3 6) :=
    controller_lookup hat (by rfl)
  have hlookup6 :
      program[6]? = some (.copy 3 3 leafPc) :=
    controller_lookup hat (by rfl)
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ := by
    simpa [state₀, hcurrent, hnonzero] using
      runsTo_branchZero hlookup0 hpc
  have step₁ :
      RunsToIn program maximumBits 1 state₀ state₁ := by
    apply runsTo_unpairLeft hlookup2 (by rfl) (value := tag)
    · simp [state₀, hcurrent]
    · exact htag
  have step₂ :
      RunsToIn program maximumBits 1 state₁ state₂ := by
    apply runsTo_unpairLeft hlookup3 (by rfl) (value := 0)
    · simpa [state₁, state₀, NPOracleState.write] using htagClass
    · exact hclass
  have step₃ :
      RunsToIn program maximumBits 1 state₂ state₃ := by
    simpa [state₃, state₂, state₁, state₀, NPOracleState.write] using
      runsTo_branchZero hlookup4 (state := state₂) (by rfl)
  have step₄ :
      RunsToIn program maximumBits 1 state₃ state₄ := by
    apply runsTo_unpairRight hlookup5 (by rfl) (value := atom)
    · simp [state₃, state₂, state₁, state₀, NPOracleState.write,
        hcurrent]
    · exact hatom
  have step₅ :
      RunsToIn program maximumBits 1 state₄ finish := by
    apply runsTo_copy hlookup6 (by rfl) (value := atom)
    · simp [state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write]
    · exact hatom
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using
      (((((step₀.trans step₁).trans step₂).trans step₃).trans step₄).trans
        step₅)
  · simp [finish, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write, hcurrent]
  · simp [finish, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write]
  · simp [finish, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write]
    · intro register hregister
      have hne3 : register ≠ 3 := by omega
      have hne4 : register ≠ 4 := by omega
      have hne5 : register ≠ 5 := by omega
      simp [finish, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, hne3, hne4, hne5]

private theorem controller_return_leaf
    {program : NPOracleProgram} {maximumBits leafPc donePc mapped : ℕ}
    {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = balancedTraversalLeafReturnPc)
    (hmapped : state.registers 3 = mapped)
    (hcode : natBitLength (Nat.pair 1 mapped) ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 2 state finish ∧
      finish.pc = 15 ∧
      finish.registers 0 = Nat.pair 1 mapped ∧
      finish.registers 2 = state.registers 2 ∧
      SameBalancedPersistent state finish := by
  let state₀ := (state.write 6 1).jump 33
  let finish := (state₀.write 0 (Nat.pair 1 mapped)).jump 15
  have hone :
      natBitLength 1 ≤ maximumBits :=
    bitLength_of_le (Nat.left_le_pair 1 mapped) hcode
  have hlookup32 :
      program[32]? = some (.set 6 1 33) :=
    controller_lookup hat (by rfl)
  have hlookup33 :
      program[33]? = some (.pair 6 3 0 15) :=
    controller_lookup hat (by rfl)
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ :=
    runsTo_set hlookup32 hpc hone
  have step₁ :
      RunsToIn program maximumBits 1 state₀ finish := by
    apply runsTo_pair hlookup33 (by rfl)
        (value := Nat.pair 1 mapped)
    · simp [state₀, NPOracleState.write, hmapped]
    · exact hcode
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_⟩
  · simpa using step₀.trans step₁
  · simp [finish, state₀, NPOracleState.write]
  · simp [finish, state₀, NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₀, NPOracleState.write]
    · intro register hregister
      have hne0 : register ≠ 0 := by omega
      have hne6 : register ≠ 6 := by omega
      simp [finish, state₀, NPOracleState.write, hne0, hne6]

private theorem controller_descend_branch
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    {left right : BalancedTraversalTree}
    {frames : List BalancedTraversalFrame} {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent :
      state.registers 0 =
        BalancedTraversalTree.code (.branch left right))
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hcode :
      natBitLength (BalancedTraversalTree.code (.branch left right)) ≤
        maximumBits)
    (hnewStack :
      natBitLength
          (encodeBalancedTraversalStack
            (.visitRight right.code :: frames)) ≤
        maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 12 state finish ∧
      finish.pc = 0 ∧
      finish.registers 0 = left.code ∧
      finish.registers 2 =
        encodeBalancedTraversalStack
          (.visitRight right.code :: frames) ∧
      SameBalancedPersistent state finish := by
  let payload := Nat.pair left.code right.code
  let stackCode := encodeBalancedTraversalStack frames
  let frameCode := balancedVisitRightFrameCode right.code
  let stackPayload := Nat.pair frameCode stackCode
  let newStack :=
    encodeBalancedTraversalStack (.visitRight right.code :: frames)
  have hbranchCode :
      BalancedTraversalTree.code (.branch left right) =
        Nat.pair 2 payload := rfl
  have hnewStackCode :
      newStack = Nat.pair 1 stackPayload := rfl
  have hnewStack' :
      natBitLength newStack ≤ maximumBits := by
    simpa [newStack] using hnewStack
  have htwo :
      natBitLength 2 ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair 2 payload)
    simpa [hbranchCode] using hcode
  have hone :
      natBitLength 1 ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair 1 stackPayload)
    simpa [hnewStackCode] using hnewStack'
  have hzero :
      natBitLength 0 ≤ maximumBits :=
    bitLength_of_le (Nat.zero_le 1) hone
  have hpayload :
      natBitLength payload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 2 payload)
    simpa [hbranchCode] using hcode
  have hleft :
      natBitLength left.code ≤ maximumBits :=
    bitLength_of_le (Nat.left_le_pair left.code right.code) hpayload
  have hright :
      natBitLength right.code ≤ maximumBits :=
    bitLength_of_le (Nat.right_le_pair left.code right.code) hpayload
  have hframe :
      natBitLength frameCode ≤ maximumBits := by
    apply bitLength_of_le
      ((Nat.left_le_pair frameCode stackCode).trans
        (Nat.right_le_pair 1 stackPayload))
    simpa [hnewStackCode] using hnewStack'
  have hstackPayload :
      natBitLength stackPayload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 1 stackPayload)
    simpa [hnewStackCode] using hnewStack'
  let state₀ := state.jump 2
  let state₁ := (state₀.write 4 2).jump 3
  let state₂ := (state₁.write 5 1).jump 4
  let state₃ := state₂.jump 7
  let state₄ := (state₃.write 4 payload).jump 8
  let state₅ := (state₄.write 0 left.code).jump 9
  let state₆ := (state₅.write 5 right.code).jump 10
  let state₇ := (state₆.write 6 0).jump 11
  let state₈ := (state₇.write 7 frameCode).jump 12
  let state₉ := (state₈.write 8 stackPayload).jump 13
  let state₁₀ := (state₉.write 6 1).jump 14
  let finish := (state₁₀.write 2 newStack).jump 0
  have hlookup0 :
      program[0]? = some (.branchZero 0 1 2) :=
    controller_lookup hat (by rfl)
  have hlookup2 :
      program[2]? = some (.unpairLeft 0 4 3) :=
    controller_lookup hat (by rfl)
  have hlookup3 :
      program[3]? = some (.unpairLeft 4 5 4) :=
    controller_lookup hat (by rfl)
  have hlookup4 :
      program[4]? = some (.branchZero 5 5 7) :=
    controller_lookup hat (by rfl)
  have hlookup7 :
      program[7]? = some (.unpairRight 0 4 8) :=
    controller_lookup hat (by rfl)
  have hlookup8 :
      program[8]? = some (.unpairLeft 4 0 9) :=
    controller_lookup hat (by rfl)
  have hlookup9 :
      program[9]? = some (.unpairRight 4 5 10) :=
    controller_lookup hat (by rfl)
  have hlookup10 :
      program[10]? = some (.set 6 0 11) :=
    controller_lookup hat (by rfl)
  have hlookup11 :
      program[11]? = some (.pair 6 5 7 12) :=
    controller_lookup hat (by rfl)
  have hlookup12 :
      program[12]? = some (.pair 7 2 8 13) :=
    controller_lookup hat (by rfl)
  have hlookup13 :
      program[13]? = some (.set 6 1 14) :=
    controller_lookup hat (by rfl)
  have hlookup14 :
      program[14]? = some (.pair 6 8 2 0) :=
    controller_lookup hat (by rfl)
  have hnonzero :
      BalancedTraversalTree.code (.branch left right) ≠ 0 := by
    rw [hbranchCode]
    have := Nat.left_le_pair 2 payload
    omega
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ := by
    simpa [state₀, hcurrent, hnonzero] using
      runsTo_branchZero hlookup0 hpc
  have step₁ :
      RunsToIn program maximumBits 1 state₀ state₁ := by
    apply runsTo_unpairLeft hlookup2 (by rfl) (value := 2)
    · simp [state₀, hcurrent, hbranchCode]
    · exact htwo
  have step₂ :
      RunsToIn program maximumBits 1 state₁ state₂ := by
    apply runsTo_unpairLeft hlookup3 (by rfl) (value := 1)
    · change (Nat.unpair 2).1 = 1
      norm_num [Nat.unpair]
    · exact hone
  have step₃ :
      RunsToIn program maximumBits 1 state₂ state₃ := by
    simpa [state₃, state₂, state₁, state₀, NPOracleState.write] using
      runsTo_branchZero hlookup4 (state := state₂) (by rfl)
  have step₄ :
      RunsToIn program maximumBits 1 state₃ state₄ := by
    apply runsTo_unpairRight hlookup7 (by rfl) (value := payload)
    · simp [state₃, state₂, state₁, state₀, NPOracleState.write,
        hcurrent, hbranchCode]
    · exact hpayload
  have step₅ :
      RunsToIn program maximumBits 1 state₄ state₅ := by
    apply runsTo_unpairLeft hlookup8 (by rfl) (value := left.code)
    · simp [state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, payload]
    · exact hleft
  have step₆ :
      RunsToIn program maximumBits 1 state₅ state₆ := by
    apply runsTo_unpairRight hlookup9 (by rfl) (value := right.code)
    · simp [state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, payload]
    · exact hright
  have step₇ :
      RunsToIn program maximumBits 1 state₆ state₇ :=
    runsTo_set hlookup10 (by rfl) hzero
  have step₈ :
      RunsToIn program maximumBits 1 state₇ state₈ := by
    apply runsTo_pair hlookup11 (by rfl) (value := frameCode)
    · simp [state₇, state₆, state₅, state₄, state₃, state₂,
        state₁, state₀, NPOracleState.write, frameCode,
        balancedVisitRightFrameCode, encodeBalancedTraversalFrame]
    · exact hframe
  have step₉ :
      RunsToIn program maximumBits 1 state₈ state₉ := by
    apply runsTo_pair hlookup12 (by rfl) (value := stackPayload)
    · simp [state₈, state₇, state₆, state₅, state₄, state₃, state₂,
        state₁, state₀, NPOracleState.write, stackPayload, hstack,
        stackCode]
    · exact hstackPayload
  have step₁₀ :
      RunsToIn program maximumBits 1 state₉ state₁₀ :=
    runsTo_set hlookup13 (by rfl) hone
  have step₁₁ :
      RunsToIn program maximumBits 1 state₁₀ finish := by
    apply runsTo_pair hlookup14 (by rfl) (value := newStack)
    · simp [state₁₀, state₉, state₈, state₇, state₆, state₅, state₄,
        state₃, state₂, state₁, state₀, NPOracleState.write,
        newStack, hnewStackCode]
    · simpa [newStack] using hnewStack
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_⟩
  · simpa using
      (((((((((((step₀.trans step₁).trans step₂).trans step₃).trans
        step₄).trans step₅).trans step₆).trans step₇).trans step₈).trans
        step₉).trans step₁₀).trans step₁₁)
  · simp [finish, state₁₀, state₉, state₈, state₇, state₆, state₅,
      state₄, state₃, state₂, state₁, state₀, NPOracleState.write]
  · simp [finish, newStack, NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₁₀, state₉, state₈, state₇, state₆, state₅,
        state₄, state₃, state₂, state₁, state₀, NPOracleState.write]
    · intro register hregister
      have hne0 : register ≠ 0 := by omega
      have hne2 : register ≠ 2 := by omega
      have hne4 : register ≠ 4 := by omega
      have hne5 : register ≠ 5 := by omega
      have hne6 : register ≠ 6 := by omega
      have hne7 : register ≠ 7 := by omega
      have hne8 : register ≠ 8 := by omega
      simp [finish, state₁₀, state₉, state₈, state₇, state₆, state₅,
        state₄, state₃, state₂, state₁, state₀, NPOracleState.write,
        hne0, hne2, hne4, hne5, hne6, hne7, hne8]

private theorem controller_descend_rawBranch
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    {tag leftCode rightCode : ℕ}
    {frames : List BalancedTraversalFrame} {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent :
      state.registers 0 =
        Nat.pair tag (Nat.pair leftCode rightCode))
    (htagClass : (Nat.unpair tag).1 ≠ 0)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hcode :
      natBitLength (Nat.pair tag (Nat.pair leftCode rightCode)) ≤
        maximumBits)
    (hnewStack :
      natBitLength
          (encodeBalancedTraversalStack
            (.visitRight rightCode :: frames)) ≤
        maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 12 state finish ∧
      finish.pc = 0 ∧
      finish.registers 0 = leftCode ∧
      finish.registers 2 =
        encodeBalancedTraversalStack
          (.visitRight rightCode :: frames) ∧
      SameBalancedPersistent state finish := by
  let payload := Nat.pair leftCode rightCode
  let tagClass := (Nat.unpair tag).1
  let stackCode := encodeBalancedTraversalStack frames
  let frameCode := balancedVisitRightFrameCode rightCode
  let stackPayload := Nat.pair frameCode stackCode
  let newStack :=
    encodeBalancedTraversalStack (.visitRight rightCode :: frames)
  have hrawCode :
      Nat.pair tag (Nat.pair leftCode rightCode) =
        Nat.pair tag payload := rfl
  have hnewStackCode :
      newStack = Nat.pair 1 stackPayload := rfl
  have hnewStack' :
      natBitLength newStack ≤ maximumBits := by
    simpa [newStack] using hnewStack
  have htag :
      natBitLength tag ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair tag payload)
    simpa [hrawCode] using hcode
  have htagClassBits :
      natBitLength tagClass ≤ maximumBits := by
    apply bitLength_of_le (Nat.unpair_left_le tag)
    exact htag
  have hone :
      natBitLength 1 ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair 1 stackPayload)
    simpa [hnewStackCode] using hnewStack'
  have hzero :
      natBitLength 0 ≤ maximumBits :=
    bitLength_of_le (Nat.zero_le 1) hone
  have hpayload :
      natBitLength payload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair tag payload)
    simpa [hrawCode] using hcode
  have hleft :
      natBitLength leftCode ≤ maximumBits :=
    bitLength_of_le (Nat.left_le_pair leftCode rightCode) hpayload
  have hright :
      natBitLength rightCode ≤ maximumBits :=
    bitLength_of_le (Nat.right_le_pair leftCode rightCode) hpayload
  have hframe :
      natBitLength frameCode ≤ maximumBits := by
    apply bitLength_of_le
      ((Nat.left_le_pair frameCode stackCode).trans
        (Nat.right_le_pair 1 stackPayload))
    simpa [hnewStackCode] using hnewStack'
  have hstackPayload :
      natBitLength stackPayload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 1 stackPayload)
    simpa [hnewStackCode] using hnewStack'
  let state₀ := state.jump 2
  let state₁ := (state₀.write 4 tag).jump 3
  let state₂ := (state₁.write 5 tagClass).jump 4
  let state₃ := state₂.jump 7
  let state₄ := (state₃.write 4 payload).jump 8
  let state₅ := (state₄.write 0 leftCode).jump 9
  let state₆ := (state₅.write 5 rightCode).jump 10
  let state₇ := (state₆.write 6 0).jump 11
  let state₈ := (state₇.write 7 frameCode).jump 12
  let state₉ := (state₈.write 8 stackPayload).jump 13
  let state₁₀ := (state₉.write 6 1).jump 14
  let finish := (state₁₀.write 2 newStack).jump 0
  have hlookup0 :
      program[0]? = some (.branchZero 0 1 2) :=
    controller_lookup hat (by rfl)
  have hlookup2 :
      program[2]? = some (.unpairLeft 0 4 3) :=
    controller_lookup hat (by rfl)
  have hlookup3 :
      program[3]? = some (.unpairLeft 4 5 4) :=
    controller_lookup hat (by rfl)
  have hlookup4 :
      program[4]? = some (.branchZero 5 5 7) :=
    controller_lookup hat (by rfl)
  have hlookup7 :
      program[7]? = some (.unpairRight 0 4 8) :=
    controller_lookup hat (by rfl)
  have hlookup8 :
      program[8]? = some (.unpairLeft 4 0 9) :=
    controller_lookup hat (by rfl)
  have hlookup9 :
      program[9]? = some (.unpairRight 4 5 10) :=
    controller_lookup hat (by rfl)
  have hlookup10 :
      program[10]? = some (.set 6 0 11) :=
    controller_lookup hat (by rfl)
  have hlookup11 :
      program[11]? = some (.pair 6 5 7 12) :=
    controller_lookup hat (by rfl)
  have hlookup12 :
      program[12]? = some (.pair 7 2 8 13) :=
    controller_lookup hat (by rfl)
  have hlookup13 :
      program[13]? = some (.set 6 1 14) :=
    controller_lookup hat (by rfl)
  have hlookup14 :
      program[14]? = some (.pair 6 8 2 0) :=
    controller_lookup hat (by rfl)
  have hnonzero :
      Nat.pair tag (Nat.pair leftCode rightCode) ≠ 0 := by
    intro hzeroCode
    have htagZero : tag = 0 := by
      have := Nat.left_le_pair tag (Nat.pair leftCode rightCode)
      omega
    exact htagClass (by simp [htagZero])
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ := by
    simpa [state₀, hcurrent, hnonzero] using
      runsTo_branchZero hlookup0 hpc
  have step₁ :
      RunsToIn program maximumBits 1 state₀ state₁ := by
    apply runsTo_unpairLeft hlookup2 (by rfl) (value := tag)
    · simp [state₀, hcurrent]
    · exact htag
  have step₂ :
      RunsToIn program maximumBits 1 state₁ state₂ := by
    apply runsTo_unpairLeft hlookup3 (by rfl) (value := tagClass)
    · simp [state₁, state₀, NPOracleState.write, tagClass]
    · exact htagClassBits
  have step₃ :
      RunsToIn program maximumBits 1 state₂ state₃ := by
    have hclassNonzero : tagClass ≠ 0 := by
      simpa [tagClass] using htagClass
    simpa [state₃, state₂, state₁, state₀, NPOracleState.write,
      hclassNonzero] using
      runsTo_branchZero hlookup4 (state := state₂) (by rfl)
  have step₄ :
      RunsToIn program maximumBits 1 state₃ state₄ := by
    apply runsTo_unpairRight hlookup7 (by rfl) (value := payload)
    · simp [state₃, state₂, state₁, state₀, NPOracleState.write,
        hcurrent, payload]
    · exact hpayload
  have step₅ :
      RunsToIn program maximumBits 1 state₄ state₅ := by
    apply runsTo_unpairLeft hlookup8 (by rfl) (value := leftCode)
    · simp [state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, payload]
    · exact hleft
  have step₆ :
      RunsToIn program maximumBits 1 state₅ state₆ := by
    apply runsTo_unpairRight hlookup9 (by rfl) (value := rightCode)
    · simp [state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, payload]
    · exact hright
  have step₇ :
      RunsToIn program maximumBits 1 state₆ state₇ :=
    runsTo_set hlookup10 (by rfl) hzero
  have step₈ :
      RunsToIn program maximumBits 1 state₇ state₈ := by
    apply runsTo_pair hlookup11 (by rfl) (value := frameCode)
    · simp [state₇, state₆, state₅, state₄, state₃, state₂,
        state₁, state₀, NPOracleState.write, frameCode,
        balancedVisitRightFrameCode, encodeBalancedTraversalFrame]
    · exact hframe
  have step₉ :
      RunsToIn program maximumBits 1 state₈ state₉ := by
    apply runsTo_pair hlookup12 (by rfl) (value := stackPayload)
    · simp [state₈, state₇, state₆, state₅, state₄, state₃, state₂,
        state₁, state₀, NPOracleState.write, stackPayload, hstack,
        stackCode]
    · exact hstackPayload
  have step₁₀ :
      RunsToIn program maximumBits 1 state₉ state₁₀ :=
    runsTo_set hlookup13 (by rfl) hone
  have step₁₁ :
      RunsToIn program maximumBits 1 state₁₀ finish := by
    apply runsTo_pair hlookup14 (by rfl) (value := newStack)
    · simp [state₁₀, state₉, state₈, state₇, state₆, state₅, state₄,
        state₃, state₂, state₁, state₀, NPOracleState.write,
        newStack, hnewStackCode]
    · simpa [newStack] using hnewStack
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_⟩
  · simpa using
      (((((((((((step₀.trans step₁).trans step₂).trans step₃).trans
        step₄).trans step₅).trans step₆).trans step₇).trans step₈).trans
        step₉).trans step₁₀).trans step₁₁)
  · simp [finish, state₁₀, state₉, state₈, state₇, state₆, state₅,
      state₄, state₃, state₂, state₁, state₀, NPOracleState.write]
  · simp [finish, newStack, NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₁₀, state₉, state₈, state₇, state₆, state₅,
        state₄, state₃, state₂, state₁, state₀, NPOracleState.write]
    · intro register hregister
      have hne0 : register ≠ 0 := by omega
      have hne2 : register ≠ 2 := by omega
      have hne4 : register ≠ 4 := by omega
      have hne5 : register ≠ 5 := by omega
      have hne6 : register ≠ 6 := by omega
      have hne7 : register ≠ 7 := by omega
      have hne8 : register ≠ 8 := by omega
      simp [finish, state₁₀, state₉, state₈, state₇, state₆, state₅,
        state₄, state₃, state₂, state₁, state₀, NPOracleState.write,
        hne0, hne2, hne4, hne5, hne6, hne7, hne8]

private theorem controller_resume_visitRight
    {program : NPOracleProgram} {maximumBits leafPc donePc leftOutput
      rightCode : ℕ}
    {frames : List BalancedTraversalFrame} {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 15)
    (hcurrent : state.registers 0 = leftOutput)
    (hstack :
      state.registers 2 =
        encodeBalancedTraversalStack
          (.visitRight rightCode :: frames))
    (hvisitStack :
      natBitLength
          (encodeBalancedTraversalStack
            (.visitRight rightCode :: frames)) ≤
        maximumBits)
    (hcombineStack :
      natBitLength
          (encodeBalancedTraversalStack
            (.combineLeft leftOutput :: frames)) ≤
        maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 13 state finish ∧
      finish.pc = 0 ∧
      finish.registers 0 = rightCode ∧
      finish.registers 2 =
        encodeBalancedTraversalStack
          (.combineLeft leftOutput :: frames) ∧
      SameBalancedPersistent state finish := by
  let oldStack := encodeBalancedTraversalStack frames
  let visitFrame := balancedVisitRightFrameCode rightCode
  let visitPayload := Nat.pair visitFrame oldStack
  let visitStack :=
    encodeBalancedTraversalStack (.visitRight rightCode :: frames)
  let combineFrame := balancedCombineLeftFrameCode leftOutput
  let combinePayload := Nat.pair combineFrame oldStack
  let combineStack :=
    encodeBalancedTraversalStack (.combineLeft leftOutput :: frames)
  have hvisitCode : visitStack = Nat.pair 1 visitPayload := rfl
  have hcombineCode : combineStack = Nat.pair 1 combinePayload := rfl
  have hvisitBits :
      natBitLength visitStack ≤ maximumBits := by
    simpa [visitStack] using hvisitStack
  have hcombineBits :
      natBitLength combineStack ≤ maximumBits := by
    simpa [combineStack] using hcombineStack
  have hone :
      natBitLength 1 ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair 1 combinePayload)
    simpa [hcombineCode] using hcombineBits
  have hzero :
      natBitLength 0 ≤ maximumBits :=
    bitLength_of_le (Nat.zero_le 1) hone
  have hvisitPayload :
      natBitLength visitPayload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 1 visitPayload)
    simpa [hvisitCode] using hvisitBits
  have hvisitFrame :
      natBitLength visitFrame ≤ maximumBits :=
    bitLength_of_le
      (Nat.left_le_pair visitFrame oldStack) hvisitPayload
  have holdStack :
      natBitLength oldStack ≤ maximumBits :=
    bitLength_of_le
      (Nat.right_le_pair visitFrame oldStack) hvisitPayload
  have hright :
      natBitLength rightCode ≤ maximumBits := by
    apply bitLength_of_le
      (Nat.right_le_pair 0 rightCode)
    simpa [visitFrame, balancedVisitRightFrameCode,
      encodeBalancedTraversalFrame] using hvisitFrame
  have hcombineFrame :
      natBitLength combineFrame ≤ maximumBits := by
    apply bitLength_of_le
      ((Nat.left_le_pair combineFrame oldStack).trans
        (Nat.right_le_pair 1 combinePayload))
    simpa [hcombineCode] using hcombineBits
  have hcombinePayload :
      natBitLength combinePayload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 1 combinePayload)
    simpa [hcombineCode] using hcombineBits
  let state₀ := state.jump 16
  let state₁ := (state₀.write 8 visitPayload).jump 17
  let state₂ := (state₁.write 7 visitFrame).jump 18
  let state₃ := (state₂.write 2 oldStack).jump 19
  let state₄ := (state₃.write 6 0).jump 20
  let state₅ := state₄.jump 21
  let state₆ := (state₅.write 5 rightCode).jump 22
  let state₇ := (state₆.write 6 1).jump 23
  let state₈ := (state₇.write 7 combineFrame).jump 24
  let state₉ := (state₈.write 8 combinePayload).jump 25
  let state₁₀ := (state₉.write 6 1).jump 26
  let state₁₁ := (state₁₀.write 2 combineStack).jump 27
  let finish := (state₁₁.write 0 rightCode).jump 0
  have hlookup15 :
      program[15]? = some (.branchZero 2 donePc 16) :=
    controller_lookup hat (by rfl)
  have hlookup16 :
      program[16]? = some (.unpairRight 2 8 17) :=
    controller_lookup hat (by rfl)
  have hlookup17 :
      program[17]? = some (.unpairLeft 8 7 18) :=
    controller_lookup hat (by rfl)
  have hlookup18 :
      program[18]? = some (.unpairRight 8 2 19) :=
    controller_lookup hat (by rfl)
  have hlookup19 :
      program[19]? = some (.unpairLeft 7 6 20) :=
    controller_lookup hat (by rfl)
  have hlookup20 :
      program[20]? = some (.branchZero 6 21 28) :=
    controller_lookup hat (by rfl)
  have hlookup21 :
      program[21]? = some (.unpairRight 7 5 22) :=
    controller_lookup hat (by rfl)
  have hlookup22 :
      program[22]? = some (.set 6 1 23) :=
    controller_lookup hat (by rfl)
  have hlookup23 :
      program[23]? = some (.pair 6 0 7 24) :=
    controller_lookup hat (by rfl)
  have hlookup24 :
      program[24]? = some (.pair 7 2 8 25) :=
    controller_lookup hat (by rfl)
  have hlookup25 :
      program[25]? = some (.set 6 1 26) :=
    controller_lookup hat (by rfl)
  have hlookup26 :
      program[26]? = some (.pair 6 8 2 27) :=
    controller_lookup hat (by rfl)
  have hlookup27 :
      program[27]? = some (.copy 5 0 0) :=
    controller_lookup hat (by rfl)
  have hnonzero : visitStack ≠ 0 := by
    rw [hvisitCode]
    have := Nat.left_le_pair 1 visitPayload
    omega
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ := by
    simpa [state₀, hstack, visitStack, hnonzero] using
      runsTo_branchZero hlookup15 hpc
  have step₁ :
      RunsToIn program maximumBits 1 state₀ state₁ := by
    apply runsTo_unpairRight hlookup16 (by rfl)
        (value := visitPayload)
    · simp [state₀, hstack, visitStack, hvisitCode]
    · exact hvisitPayload
  have step₂ :
      RunsToIn program maximumBits 1 state₁ state₂ := by
    apply runsTo_unpairLeft hlookup17 (by rfl)
        (value := visitFrame)
    · simp [state₁, state₀, NPOracleState.write, visitPayload]
    · exact hvisitFrame
  have step₃ :
      RunsToIn program maximumBits 1 state₂ state₃ := by
    apply runsTo_unpairRight hlookup18 (by rfl)
        (value := oldStack)
    · simp [state₂, state₁, state₀, NPOracleState.write, visitPayload]
    · exact holdStack
  have step₄ :
      RunsToIn program maximumBits 1 state₃ state₄ := by
    apply runsTo_unpairLeft hlookup19 (by rfl) (value := 0)
    · simp [state₃, state₂, state₁, state₀, NPOracleState.write,
        visitFrame, balancedVisitRightFrameCode,
        encodeBalancedTraversalFrame]
    · exact hzero
  have step₅ :
      RunsToIn program maximumBits 1 state₄ state₅ := by
    simpa [state₅, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write] using
      runsTo_branchZero hlookup20 (state := state₄) (by rfl)
  have step₆ :
      RunsToIn program maximumBits 1 state₅ state₆ := by
    apply runsTo_unpairRight hlookup21 (by rfl)
        (value := rightCode)
    · simp [state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, visitFrame, balancedVisitRightFrameCode,
        encodeBalancedTraversalFrame]
    · exact hright
  have step₇ :
      RunsToIn program maximumBits 1 state₆ state₇ :=
    runsTo_set hlookup22 (by rfl) hone
  have step₈ :
      RunsToIn program maximumBits 1 state₇ state₈ := by
    apply runsTo_pair hlookup23 (by rfl) (value := combineFrame)
    · simp [state₇, state₆, state₅, state₄, state₃, state₂, state₁,
        state₀, NPOracleState.write, hcurrent, combineFrame,
        balancedCombineLeftFrameCode, encodeBalancedTraversalFrame]
    · exact hcombineFrame
  have step₉ :
      RunsToIn program maximumBits 1 state₈ state₉ := by
    apply runsTo_pair hlookup24 (by rfl)
        (value := combinePayload)
    · simp [state₈, state₇, state₆, state₅, state₄, state₃, state₂,
        state₁, state₀, NPOracleState.write, combinePayload]
    · exact hcombinePayload
  have step₁₀ :
      RunsToIn program maximumBits 1 state₉ state₁₀ :=
    runsTo_set hlookup25 (by rfl) hone
  have step₁₁ :
      RunsToIn program maximumBits 1 state₁₀ state₁₁ := by
    apply runsTo_pair hlookup26 (by rfl) (value := combineStack)
    · simp [state₁₀, state₉, state₈, state₇, state₆, state₅, state₄,
        state₃, state₂, state₁, state₀, NPOracleState.write,
        combineStack, hcombineCode]
    · exact hcombineBits
  have step₁₂ :
      RunsToIn program maximumBits 1 state₁₁ finish := by
    apply runsTo_copy hlookup27 (by rfl) (value := rightCode)
    · simp [state₁₁, state₁₀, state₉, state₈, state₇, state₆, state₅,
        state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write]
    · exact hright
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_⟩
  · simpa using
      ((((((((((((step₀.trans step₁).trans step₂).trans step₃).trans
        step₄).trans step₅).trans step₆).trans step₇).trans step₈).trans
        step₉).trans step₁₀).trans step₁₁).trans step₁₂)
  · simp [finish, state₁₁, state₁₀, state₉, state₈, state₇, state₆,
      state₅, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write]
  · simp [finish, state₁₁, combineStack, NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₁₁, state₁₀, state₉, state₈, state₇, state₆,
        state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write]
    · intro register hregister
      have hne0 : register ≠ 0 := by omega
      have hne2 : register ≠ 2 := by omega
      have hne5 : register ≠ 5 := by omega
      have hne6 : register ≠ 6 := by omega
      have hne7 : register ≠ 7 := by omega
      have hne8 : register ≠ 8 := by omega
      simp [finish, state₁₁, state₁₀, state₉, state₈, state₇, state₆,
        state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, hne0, hne2, hne5, hne6, hne7, hne8]

private theorem controller_resume_combine
    {program : NPOracleProgram} {maximumBits leafPc donePc leftOutput
      rightOutput : ℕ}
    {frames : List BalancedTraversalFrame} {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 15)
    (hcurrent : state.registers 0 = rightOutput)
    (hstack :
      state.registers 2 =
        encodeBalancedTraversalStack
          (.combineLeft leftOutput :: frames))
    (hcombineStack :
      natBitLength
          (encodeBalancedTraversalStack
            (.combineLeft leftOutput :: frames)) ≤
        maximumBits)
    (houtput :
      natBitLength (balancedBranchCode leftOutput rightOutput) ≤
        maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 10 state finish ∧
      finish.pc = 15 ∧
      finish.registers 0 =
        balancedBranchCode leftOutput rightOutput ∧
      finish.registers 2 = encodeBalancedTraversalStack frames ∧
      SameBalancedPersistent state finish := by
  let oldStack := encodeBalancedTraversalStack frames
  let frameCode := balancedCombineLeftFrameCode leftOutput
  let stackPayload := Nat.pair frameCode oldStack
  let stackCode :=
    encodeBalancedTraversalStack (.combineLeft leftOutput :: frames)
  let outputPayload := Nat.pair leftOutput rightOutput
  let outputCode := balancedBranchCode leftOutput rightOutput
  have hstackCode : stackCode = Nat.pair 1 stackPayload := rfl
  have houtputCode : outputCode = Nat.pair 2 outputPayload := rfl
  have hstackBits :
      natBitLength stackCode ≤ maximumBits := by
    simpa [stackCode] using hcombineStack
  have houtputBits :
      natBitLength outputCode ≤ maximumBits := by
    simpa [outputCode] using houtput
  have hstackPayload :
      natBitLength stackPayload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 1 stackPayload)
    simpa [hstackCode] using hstackBits
  have hframe :
      natBitLength frameCode ≤ maximumBits :=
    bitLength_of_le
      (Nat.left_le_pair frameCode oldStack) hstackPayload
  have holdStack :
      natBitLength oldStack ≤ maximumBits :=
    bitLength_of_le
      (Nat.right_le_pair frameCode oldStack) hstackPayload
  have hone :
      natBitLength 1 ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair 1 stackPayload)
    simpa [hstackCode] using hstackBits
  have hleft :
      natBitLength leftOutput ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 1 leftOutput)
    simpa [frameCode, balancedCombineLeftFrameCode,
      encodeBalancedTraversalFrame] using hframe
  have houtputPayload :
      natBitLength outputPayload ≤ maximumBits := by
    apply bitLength_of_le (Nat.right_le_pair 2 outputPayload)
    simpa [houtputCode] using houtputBits
  have hright :
      natBitLength rightOutput ≤ maximumBits :=
    bitLength_of_le
      (Nat.right_le_pair leftOutput rightOutput) houtputPayload
  have htwo :
      natBitLength 2 ≤ maximumBits := by
    apply bitLength_of_le (Nat.left_le_pair 2 outputPayload)
    simpa [houtputCode] using houtputBits
  let state₀ := state.jump 16
  let state₁ := (state₀.write 8 stackPayload).jump 17
  let state₂ := (state₁.write 7 frameCode).jump 18
  let state₃ := (state₂.write 2 oldStack).jump 19
  let state₄ := (state₃.write 6 1).jump 20
  let state₅ := state₄.jump 28
  let state₆ := (state₅.write 5 leftOutput).jump 29
  let state₇ := (state₆.write 4 outputPayload).jump 30
  let state₈ := (state₇.write 6 2).jump 31
  let finish := (state₈.write 0 outputCode).jump 15
  have hlookup15 :
      program[15]? = some (.branchZero 2 donePc 16) :=
    controller_lookup hat (by rfl)
  have hlookup16 :
      program[16]? = some (.unpairRight 2 8 17) :=
    controller_lookup hat (by rfl)
  have hlookup17 :
      program[17]? = some (.unpairLeft 8 7 18) :=
    controller_lookup hat (by rfl)
  have hlookup18 :
      program[18]? = some (.unpairRight 8 2 19) :=
    controller_lookup hat (by rfl)
  have hlookup19 :
      program[19]? = some (.unpairLeft 7 6 20) :=
    controller_lookup hat (by rfl)
  have hlookup20 :
      program[20]? = some (.branchZero 6 21 28) :=
    controller_lookup hat (by rfl)
  have hlookup28 :
      program[28]? = some (.unpairRight 7 5 29) :=
    controller_lookup hat (by rfl)
  have hlookup29 :
      program[29]? = some (.pair 5 0 4 30) :=
    controller_lookup hat (by rfl)
  have hlookup30 :
      program[30]? = some (.set 6 2 31) :=
    controller_lookup hat (by rfl)
  have hlookup31 :
      program[31]? = some (.pair 6 4 0 15) :=
    controller_lookup hat (by rfl)
  have hnonzero : stackCode ≠ 0 := by
    rw [hstackCode]
    have := Nat.left_le_pair 1 stackPayload
    omega
  have step₀ :
      RunsToIn program maximumBits 1 state state₀ := by
    simpa [state₀, hstack, stackCode, hnonzero] using
      runsTo_branchZero hlookup15 hpc
  have step₁ :
      RunsToIn program maximumBits 1 state₀ state₁ := by
    apply runsTo_unpairRight hlookup16 (by rfl)
        (value := stackPayload)
    · simp [state₀, hstack, stackCode, hstackCode]
    · exact hstackPayload
  have step₂ :
      RunsToIn program maximumBits 1 state₁ state₂ := by
    apply runsTo_unpairLeft hlookup17 (by rfl) (value := frameCode)
    · simp [state₁, state₀, NPOracleState.write, stackPayload]
    · exact hframe
  have step₃ :
      RunsToIn program maximumBits 1 state₂ state₃ := by
    apply runsTo_unpairRight hlookup18 (by rfl) (value := oldStack)
    · simp [state₂, state₁, state₀, NPOracleState.write,
        stackPayload]
    · exact holdStack
  have step₄ :
      RunsToIn program maximumBits 1 state₃ state₄ := by
    apply runsTo_unpairLeft hlookup19 (by rfl) (value := 1)
    · simp [state₃, state₂, state₁, state₀, NPOracleState.write,
        frameCode, balancedCombineLeftFrameCode,
        encodeBalancedTraversalFrame]
    · exact hone
  have step₅ :
      RunsToIn program maximumBits 1 state₄ state₅ := by
    simpa [state₅, state₄, state₃, state₂, state₁, state₀,
      NPOracleState.write] using
      runsTo_branchZero hlookup20 (state := state₄) (by rfl)
  have step₆ :
      RunsToIn program maximumBits 1 state₅ state₆ := by
    apply runsTo_unpairRight hlookup28 (by rfl)
        (value := leftOutput)
    · simp [state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, frameCode, balancedCombineLeftFrameCode,
        encodeBalancedTraversalFrame]
    · exact hleft
  have step₇ :
      RunsToIn program maximumBits 1 state₆ state₇ := by
    apply runsTo_pair hlookup29 (by rfl) (value := outputPayload)
    · simp [state₆, state₅, state₄, state₃, state₂, state₁, state₀,
        NPOracleState.write, hcurrent, outputPayload]
    · exact houtputPayload
  have step₈ :
      RunsToIn program maximumBits 1 state₇ state₈ :=
    runsTo_set hlookup30 (by rfl) htwo
  have step₉ :
      RunsToIn program maximumBits 1 state₈ finish := by
    apply runsTo_pair hlookup31 (by rfl) (value := outputCode)
    · simp [state₈, state₇, state₆, state₅, state₄, state₃, state₂,
        state₁, state₀, NPOracleState.write, outputCode, houtputCode]
    · exact houtputBits
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_⟩
  · simpa using
      (((((((((step₀.trans step₁).trans step₂).trans step₃).trans
        step₄).trans step₅).trans step₆).trans step₇).trans step₈).trans
        step₉)
  · simp [finish, state₈, outputCode, NPOracleState.write]
  · simp [finish, state₈, state₇, state₆, state₅, state₄, state₃,
      state₂, state₁, state₀, oldStack, NPOracleState.write]
  · refine ⟨?_, ?_⟩
    · simp [finish, state₈, state₇, state₆, state₅, state₄, state₃,
        state₂, state₁, state₀, NPOracleState.write]
    · intro register hregister
      have hne0 : register ≠ 0 := by omega
      have hne2 : register ≠ 2 := by omega
      have hne4 : register ≠ 4 := by omega
      have hne5 : register ≠ 5 := by omega
      have hne6 : register ≠ 6 := by omega
      have hne7 : register ≠ 7 := by omega
      have hne8 : register ≠ 8 := by omega
      simp [finish, state₈, state₇, state₆, state₅, state₄, state₃,
        state₂, state₁, state₀, NPOracleState.write, hne0, hne2,
        hne4, hne5, hne6, hne7, hne8]

def balancedTraversalSteps (leafSteps : ℕ → ℕ) :
    BalancedTraversalTree → ℕ
  | .empty => 2
  | .leaf atom => 6 + leafSteps atom + 2
  | .branch left right =>
      12 + balancedTraversalSteps leafSteps left + 13 +
        balancedTraversalSteps leafSteps right + 10

def balancedTraversalStructuralSteps : BalancedTraversalTree → ℕ
  | .empty => 2
  | .leaf _ => 8
  | .branch left right =>
      35 + balancedTraversalStructuralSteps left +
        balancedTraversalStructuralSteps right

theorem balancedTraversalStructuralSteps_le_nodeCount
    (tree : BalancedTraversalTree) :
    balancedTraversalStructuralSteps tree ≤ 35 * tree.nodeCount := by
  induction tree with
  | empty =>
      norm_num [balancedTraversalStructuralSteps,
        BalancedTraversalTree.nodeCount]
  | leaf atom =>
      norm_num [balancedTraversalStructuralSteps,
        BalancedTraversalTree.nodeCount]
  | branch left right ihLeft ihRight =>
      simp only [balancedTraversalStructuralSteps,
        BalancedTraversalTree.nodeCount]
      omega

theorem balancedTraversalStructuralSteps_le_linear (values : List ℕ) :
    balancedTraversalStructuralSteps (balancedTraversalTree values) ≤
      35 * (2 * values.length + 1) := by
  calc
    balancedTraversalStructuralSteps (balancedTraversalTree values) ≤
        35 * (balancedTraversalTree values).nodeCount :=
      balancedTraversalStructuralSteps_le_nodeCount _
    _ ≤ 35 * (2 * values.length + 1) := by
      apply Nat.mul_le_mul_left
      rw [balancedTraversalTree_nodeCount]
      split
      · omega
      · omega

theorem balancedTraversalSteps_eq_structural
    (tree : BalancedTraversalTree) (leafSteps : ℕ → ℕ) :
    balancedTraversalSteps leafSteps tree =
      balancedTraversalStructuralSteps tree +
        (tree.atoms.map leafSteps).sum := by
  induction tree with
  | empty => rfl
  | leaf atom =>
      simp [balancedTraversalSteps, balancedTraversalStructuralSteps,
        BalancedTraversalTree.atoms]
      omega
  | branch left right ihLeft ihRight =>
      simp only [balancedTraversalSteps, balancedTraversalStructuralSteps,
        BalancedTraversalTree.atoms, List.map_append, List.sum_append]
      rw [ihLeft, ihRight]
      omega

/-! ## Reusable stateful fold traversal -/

def balancedFoldLeafSteps
    (step leafSteps : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | accumulator, atom :: atoms =>
      leafSteps accumulator atom +
        balancedFoldLeafSteps step leafSteps
          (step accumulator atom) atoms

def BalancedFoldFits (maximumBits : ℕ) (step : ℕ → ℕ → ℕ) :
    ℕ → List ℕ → Prop
  | accumulator, [] =>
      natBitLength accumulator ≤ maximumBits
  | accumulator, atom :: atoms =>
      natBitLength accumulator ≤ maximumBits ∧
        natBitLength (step accumulator atom) ≤ maximumBits ∧
          BalancedFoldFits maximumBits step
            (step accumulator atom) atoms

def BalancedFoldLeafFits (maximumBits : ℕ) (step : ℕ → ℕ → ℕ)
    (leafRequiredBits : ℕ → ℕ → ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | accumulator, atom :: atoms =>
      leafRequiredBits accumulator atom ≤ maximumBits ∧
        BalancedFoldLeafFits maximumBits step leafRequiredBits
          (step accumulator atom) atoms

theorem BalancedFoldFits.initial
    {maximumBits accumulator : ℕ} {step : ℕ → ℕ → ℕ}
    {atoms : List ℕ}
    (hfit : BalancedFoldFits maximumBits step accumulator atoms) :
    natBitLength accumulator ≤ maximumBits := by
  cases atoms <;> simp_all [BalancedFoldFits]

theorem BalancedFoldFits.final
    {maximumBits accumulator : ℕ} {step : ℕ → ℕ → ℕ}
    {atoms : List ℕ}
    (hfit : BalancedFoldFits maximumBits step accumulator atoms) :
    natBitLength (atoms.foldl step accumulator) ≤ maximumBits := by
  induction atoms generalizing accumulator with
  | nil => simpa [BalancedFoldFits] using hfit
  | cons atom atoms ih =>
      simp only [BalancedFoldFits] at hfit
      exact ih hfit.2.2

@[simp] theorem balancedFoldLeafSteps_append
    (step leafSteps : ℕ → ℕ → ℕ) (accumulator : ℕ)
    (left right : List ℕ) :
    balancedFoldLeafSteps step leafSteps accumulator (left ++ right) =
      balancedFoldLeafSteps step leafSteps accumulator left +
        balancedFoldLeafSteps step leafSteps
          (left.foldl step accumulator) right := by
  induction left generalizing accumulator with
  | nil => simp [balancedFoldLeafSteps]
  | cons atom atoms ih =>
      simp [balancedFoldLeafSteps, ih, Nat.add_assoc]

theorem balancedFoldFits_append
    (maximumBits : ℕ) (step : ℕ → ℕ → ℕ)
    (accumulator : ℕ) (left right : List ℕ) :
    BalancedFoldFits maximumBits step accumulator (left ++ right) ↔
      BalancedFoldFits maximumBits step accumulator left ∧
        BalancedFoldFits maximumBits step
          (left.foldl step accumulator) right := by
  induction left generalizing accumulator with
  | nil =>
      constructor
      · intro hfit
        exact ⟨hfit.initial, hfit⟩
      · rintro ⟨_, hfit⟩
        exact hfit
  | cons atom atoms ih =>
      simp only [List.cons_append, List.foldl_cons, BalancedFoldFits]
      rw [ih]
      aesop

theorem balancedFoldLeafFits_append
    (maximumBits : ℕ) (step : ℕ → ℕ → ℕ)
    (leafRequiredBits : ℕ → ℕ → ℕ)
    (accumulator : ℕ) (left right : List ℕ) :
    BalancedFoldLeafFits maximumBits step leafRequiredBits accumulator
        (left ++ right) ↔
      BalancedFoldLeafFits maximumBits step leafRequiredBits accumulator left ∧
        BalancedFoldLeafFits maximumBits step leafRequiredBits
          (left.foldl step accumulator) right := by
  induction left generalizing accumulator with
  | nil => simp [BalancedFoldLeafFits]
  | cons atom atoms ih =>
      simp only [List.cons_append, List.foldl_cons, BalancedFoldLeafFits]
      rw [ih]
      aesop

/-! ## One-pass natural summation -/

private theorem run_balancedNatSumLeaf
    {program : NPOracleProgram} {maximumBits leafPc atom : ℕ}
    {entry : NPOracleState}
    (hlookup : program[leafPc]? =
      some (.add 9 3 9 balancedTraversalLeafReturnPc))
    (hpc : entry.pc = leafPc)
    (hatom : entry.registers 3 = atom)
    (hbits : natBitLength (entry.registers 9 + atom) ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits 1 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 = atom ∧
      finish.registers 9 = entry.registers 9 + atom ∧
      SameTraversalContextFrom 10 entry finish := by
  let finish :=
    (entry.write 9 (entry.registers 9 + atom)).jump
      balancedTraversalLeafReturnPc
  have hruns : RunsToIn program maximumBits 1 entry finish := by
    intro extra
    simpa [finish, Nat.add_comm] using
      (run_add_instruction (fuel := extra) hlookup hpc
        (value := entry.registers 9 + atom) (by rw [hatom]) hbits)
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · simp [finish, NPOracleState.write, NPOracleState.jump, hatom]
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · refine ⟨?_, ?_⟩
    · simp [finish, NPOracleState.write, NPOracleState.jump]
    · intro register hregister
      have hne : register ≠ 9 := by omega
      simp [finish, NPOracleState.write, NPOracleState.jump, hne]

theorem run_balancedTraversalNatSum_subtree
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (tree : BalancedTraversalTree) (frames : List BalancedTraversalFrame)
    (state : NPOracleState)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hadd : program[leafPc]? =
      some (.add 9 3 9 balancedTraversalLeafReturnPc))
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = tree.code)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hfit :
      BalancedTraversalFits maximumBits (fun value => value) tree frames)
    (hsumBits :
      natBitLength (state.registers 9 + tree.atoms.sum) ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits
        (balancedTraversalStructuralSteps tree + tree.atoms.length)
        state finish ∧
      finish.pc = 15 ∧
      finish.registers 0 =
        (tree.map fun value => value).code ∧
      finish.registers 2 = encodeBalancedTraversalStack frames ∧
      finish.registers 9 = state.registers 9 + tree.atoms.sum ∧
      SameTraversalContextFrom 10 state finish := by
  induction tree generalizing frames state with
  | empty =>
      rcases hfit with ⟨hinput, _, _, _⟩
      rcases controller_descend_empty hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput) with
        ⟨finish, hruns, hfinishPc, hfinishCurrent, hfinishStack,
          hpersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_,
        hpersistent.weaken (by omega)⟩
      · simpa [balancedTraversalStructuralSteps,
          BalancedTraversalTree.atoms] using hruns
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hstack]
      · rw [hpersistent.persistent 9 (by omega)]
        simp [BalancedTraversalTree.atoms]
  | leaf atom =>
      rcases hfit with
        ⟨hinput, houtput, _, hatom, _hmapped⟩
      rcases controller_descend_leaf hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput)
          hatom with
        ⟨entry, hentryRuns, hentryPc, hentryCurrent, hentryStack,
          hentryAtom, hentryPersistent⟩
      have hentry9 := hentryPersistent.persistent 9 (by omega)
      have hentrySumBits :
          natBitLength (entry.registers 9 + atom) ≤ maximumBits := by
        rw [hentry9]
        simpa [BalancedTraversalTree.atoms] using hsumBits
      rcases run_balancedNatSumLeaf hadd hentryPc hentryAtom
          hentrySumBits with
        ⟨returned, haddRuns, hreturnedPc, _hreturnedCurrent,
          hreturnedStack, hreturnedAtom, hreturned9, haddPersistent⟩
      rcases controller_return_leaf hat hreturnedPc hreturnedAtom
          (by simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code] using houtput) with
        ⟨finish, hreturnRuns, hfinishPc, hfinishCurrent,
          hfinishStack, hreturnPersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_, ?_⟩
      · simpa [balancedTraversalStructuralSteps,
          BalancedTraversalTree.atoms] using
          (hentryRuns.trans haddRuns).trans hreturnRuns
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hreturnedStack, hentryStack, hstack]
      · rw [hreturnPersistent.persistent 9 (by omega), hreturned9,
          hentry9]
        simp [BalancedTraversalTree.atoms]
      · exact (hentryPersistent.weaken (by omega)).trans
          (haddPersistent.trans
            (hreturnPersistent.weaken (by omega)))
  | branch left right ihLeft ihRight =>
      rcases hfit with
        ⟨hinput, houtput, _, hleftFit, hrightFit⟩
      have hvisitStack := hleftFit.stack
      have hcombineStack := hrightFit.stack
      rcases controller_descend_branch hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          hstack
          (by simpa [BalancedTraversalTree.code] using hinput)
          hvisitStack with
        ⟨leftStart, hdescendRuns, hleftStartPc, hleftStartCurrent,
          hleftStartStack, hdescendPersistent⟩
      have hdescend9 :=
        hdescendPersistent.persistent 9 (by omega)
      have hleftSumBits :
          natBitLength
              (leftStart.registers 9 + left.atoms.sum) ≤
            maximumBits := by
        apply (natBitLength_mono ?_).trans
          (by simpa [BalancedTraversalTree.atoms] using hsumBits)
        rw [hdescend9]
        omega
      rcases ihLeft (.visitRight right.code :: frames) leftStart
          hleftStartPc hleftStartCurrent hleftStartStack hleftFit
          hleftSumBits with
        ⟨leftFinish, hleftRuns, hleftFinishPc, hleftFinishCurrent,
          hleftFinishStack, hleft9, hleftPersistent⟩
      rcases controller_resume_visitRight hat hleftFinishPc
          hleftFinishCurrent hleftFinishStack hvisitStack hcombineStack with
        ⟨rightStart, hvisitRuns, hrightStartPc, hrightStartCurrent,
          hrightStartStack, hvisitPersistent⟩
      have hvisit9 := hvisitPersistent.persistent 9 (by omega)
      have hrightSumBits :
          natBitLength
              (rightStart.registers 9 + right.atoms.sum) ≤
            maximumBits := by
        rw [hvisit9, hleft9, hdescend9]
        simpa [BalancedTraversalTree.atoms, List.sum_append,
          Nat.add_assoc] using hsumBits
      rcases ihRight
          (.combineLeft
            (left.map fun value => value).code :: frames)
          rightStart hrightStartPc hrightStartCurrent
          hrightStartStack hrightFit hrightSumBits with
        ⟨rightFinish, hrightRuns, hrightFinishPc,
          hrightFinishCurrent, hrightFinishStack, hright9,
          hrightPersistent⟩
      rcases controller_resume_combine hat hrightFinishPc
          hrightFinishCurrent hrightFinishStack hcombineStack
          (by simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code, balancedBranchCode] using
              houtput) with
        ⟨finish, hcombineRuns, hfinishPc, hfinishCurrent,
          hfinishStack, hcombinePersistent⟩
      have hcombine9 :=
        hcombinePersistent.persistent 9 (by omega)
      have hfinal9 :
          finish.registers 9 =
            state.registers 9 + (left.atoms ++ right.atoms).sum := by
        rw [hcombine9, hright9, hvisit9, hleft9, hdescend9,
          List.sum_append]
        omega
      refine ⟨finish, ?_, hfinishPc, ?_, hfinishStack, ?_, ?_⟩
      · convert
          ((((hdescendRuns.trans hleftRuns).trans hvisitRuns).trans
            hrightRuns).trans hcombineRuns) using 1
        simp [balancedTraversalStructuralSteps,
          BalancedTraversalTree.atoms, List.length_append]
        omega
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code, balancedBranchCode] using
          hfinishCurrent
      · simpa [BalancedTraversalTree.atoms] using hfinal9
      · exact (hdescendPersistent.weaken (by omega)).trans
          (hleftPersistent.trans
            ((hvisitPersistent.weaken (by omega)).trans
              (hrightPersistent.trans
                (hcombinePersistent.weaken (by omega)))))

/-- Exact shape-preserving execution theorem for a subtree.  The handler is
not a runtime callback: `hhandler` is an interpreter theorem about the concrete
instructions already present at `leafPc`. -/
theorem run_balancedTraversal_subtree
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (f leafSteps : ℕ → ℕ) (tree : BalancedTraversalTree)
    (frames : List BalancedTraversalFrame) (state : NPOracleState)
    (nativeInputLength : ℕ)
    (persistentBase : ℕ) (hpersistentBase : 9 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = tree.code)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hfit : BalancedTraversalFits maximumBits f tree frames)
    (hhandler :
      ∀ atom, atom ∈ tree.atoms →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (f atom) ≤ maximumBits →
          entry.registers 1 = nativeInputLength →
          ∃ finish,
            RunsToIn program maximumBits (leafSteps atom) entry finish ∧
            finish.pc = balancedTraversalLeafReturnPc ∧
            finish.registers 0 = entry.registers 0 ∧
            finish.registers 2 = entry.registers 2 ∧
            finish.registers 3 = f atom ∧
            SameTraversalContextFrom persistentBase entry finish) :
    ∃ finish,
      RunsToIn program maximumBits
        (balancedTraversalSteps leafSteps tree) state finish ∧
      finish.pc = 15 ∧
      finish.registers 0 = (tree.map f).code ∧
      finish.registers 2 = encodeBalancedTraversalStack frames ∧
      SameTraversalContextFrom persistentBase state finish := by
  induction tree generalizing frames state with
  | empty =>
      rcases hfit with ⟨hinput, _, _, _⟩
      rcases controller_descend_empty hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput) with
        ⟨finish, hruns, hfinishPc, hfinishCurrent, hfinishStack,
          hpersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, ?_,
        hpersistent.weaken hpersistentBase⟩
      · simpa [balancedTraversalSteps] using hruns
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hstack]
  | leaf atom =>
      rcases hfit with
        ⟨hinput, houtput, _, hatom, hmapped⟩
      rcases controller_descend_leaf hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput)
          hatom with
        ⟨entry, hentryRuns, hentryPc, hentryCurrent, hentryStack,
          hentryAtom, hentryPersistent⟩
      rcases hhandler atom (by
          simp [BalancedTraversalTree.atoms])
          entry hentryPc hentryCurrent hentryAtom hmapped
          (hentryPersistent.inputLength.trans hnativeInputLength) with
        ⟨returned, hhandlerRuns, hreturnedPc, hreturnedCurrent,
          hreturnedStack, hreturnedAtom, hhandlerPersistent⟩
      rcases controller_return_leaf hat hreturnedPc hreturnedAtom
          (by simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code] using houtput) with
        ⟨finish, hreturnRuns, hfinishPc, hfinishCurrent,
          hfinishStack, hreturnPersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_⟩
      · simpa [balancedTraversalSteps] using
          (hentryRuns.trans hhandlerRuns).trans hreturnRuns
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hreturnedStack, hentryStack, hstack]
      · exact (hentryPersistent.weaken hpersistentBase).trans
          (hhandlerPersistent.trans
            (hreturnPersistent.weaken hpersistentBase))
  | branch left right ihLeft ihRight =>
      rcases hfit with
        ⟨hinput, houtput, _, hleftFit, hrightFit⟩
      have hvisitStack := hleftFit.stack
      have hcombineStack := hrightFit.stack
      rcases controller_descend_branch hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          hstack
          (by simpa [BalancedTraversalTree.code] using hinput)
          hvisitStack with
        ⟨leftStart, hdescendRuns, hleftStartPc, hleftStartCurrent,
          hleftStartStack, hdescendPersistent⟩
      have hleftHandler :
          ∀ atom, atom ∈ left.atoms →
            ∀ entry : NPOracleState,
              entry.pc = leafPc →
              entry.registers 0 = Nat.pair 1 atom →
              entry.registers 3 = atom →
              natBitLength (f atom) ≤ maximumBits →
              entry.registers 1 = nativeInputLength →
              ∃ finish,
                RunsToIn program maximumBits (leafSteps atom)
                    entry finish ∧
                finish.pc = balancedTraversalLeafReturnPc ∧
                finish.registers 0 = entry.registers 0 ∧
                finish.registers 2 = entry.registers 2 ∧
                finish.registers 3 = f atom ∧
                SameTraversalContextFrom persistentBase entry finish := by
        intro atom hmem entry hentryPc hentryCurrent hentryAtom
          hmapped hentryInputLength
        apply hhandler atom
        · simp [BalancedTraversalTree.atoms, hmem]
        · exact hentryPc
        · exact hentryCurrent
        · exact hentryAtom
        · exact hmapped
        · exact hentryInputLength
      have hleftInputLength :
          leftStart.registers 1 = nativeInputLength :=
        hdescendPersistent.inputLength.trans hnativeInputLength
      rcases ihLeft (.visitRight right.code :: frames) leftStart
          hleftStartPc hleftStartCurrent hleftStartStack
          hleftInputLength hleftFit hleftHandler with
        ⟨leftFinish, hleftRuns, hleftFinishPc, hleftFinishCurrent,
          hleftFinishStack, hleftPersistent⟩
      rcases controller_resume_visitRight hat hleftFinishPc
          hleftFinishCurrent hleftFinishStack hvisitStack hcombineStack with
        ⟨rightStart, hvisitRuns, hrightStartPc, hrightStartCurrent,
          hrightStartStack, hvisitPersistent⟩
      have hrightHandler :
          ∀ atom, atom ∈ right.atoms →
            ∀ entry : NPOracleState,
              entry.pc = leafPc →
              entry.registers 0 = Nat.pair 1 atom →
              entry.registers 3 = atom →
              natBitLength (f atom) ≤ maximumBits →
              entry.registers 1 = nativeInputLength →
              ∃ finish,
                RunsToIn program maximumBits (leafSteps atom)
                    entry finish ∧
                finish.pc = balancedTraversalLeafReturnPc ∧
                finish.registers 0 = entry.registers 0 ∧
                finish.registers 2 = entry.registers 2 ∧
                finish.registers 3 = f atom ∧
                SameTraversalContextFrom persistentBase entry finish := by
        intro atom hmem entry hentryPc hentryCurrent hentryAtom
          hmapped hentryInputLength
        apply hhandler atom
        · simp [BalancedTraversalTree.atoms, hmem]
        · exact hentryPc
        · exact hentryCurrent
        · exact hentryAtom
        · exact hmapped
        · exact hentryInputLength
      have hrightInputLength :
          rightStart.registers 1 = nativeInputLength :=
        hvisitPersistent.inputLength.trans
          (hleftPersistent.inputLength.trans hleftInputLength)
      rcases ihRight (.combineLeft (left.map f).code :: frames)
          rightStart hrightStartPc hrightStartCurrent
          hrightStartStack hrightInputLength hrightFit hrightHandler with
        ⟨rightFinish, hrightRuns, hrightFinishPc,
          hrightFinishCurrent, hrightFinishStack, hrightPersistent⟩
      rcases controller_resume_combine hat hrightFinishPc
          hrightFinishCurrent hrightFinishStack hcombineStack
          (by simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code, balancedBranchCode] using
              houtput) with
        ⟨finish, hcombineRuns, hfinishPc, hfinishCurrent,
          hfinishStack, hcombinePersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, hfinishStack, ?_⟩
      · simpa [balancedTraversalSteps] using
          ((((hdescendRuns.trans hleftRuns).trans hvisitRuns).trans
            hrightRuns).trans hcombineRuns)
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code, balancedBranchCode] using
          hfinishCurrent
      · exact (hdescendPersistent.weaken hpersistentBase).trans
          (hleftPersistent.trans
            ((hvisitPersistent.weaken hpersistentBase).trans
              (hrightPersistent.trans
                (hcombinePersistent.weaken hpersistentBase))))

def rawBalancedTraversalSteps : RawBalancedTraversalTree → ℕ
  | .empty => 2
  | .leaf _tag _atom => 8
  | .branch _tag left right =>
      12 + rawBalancedTraversalSteps left + 13 +
        rawBalancedTraversalSteps right + 10

theorem run_rawBalancedTraversal_subtree
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (tree : RawBalancedTraversalTree)
    (frames : List BalancedTraversalFrame) (state : NPOracleState)
    (nativeInputLength : ℕ)
    (persistentBase : ℕ) (hpersistentBase : 9 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hleafPc : leafPc = balancedTraversalLeafReturnPc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = tree.rawCode)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hvalid : tree.Valid)
    (hfit : RawBalancedTraversalFits maximumBits tree frames) :
    ∃ finish,
      RunsToIn program maximumBits
        (rawBalancedTraversalSteps tree) state finish ∧
      finish.pc = 15 ∧
      finish.registers 0 = tree.normalized.code ∧
      finish.registers 2 = encodeBalancedTraversalStack frames ∧
      SameTraversalContextFrom persistentBase state finish := by
  induction tree generalizing frames state with
  | empty =>
      rcases hfit with ⟨hinput, _houtput, _hstackBits, _⟩
      rcases controller_descend_empty hat hpc
          (by simpa [RawBalancedTraversalTree.rawCode] using hcurrent)
          (by simpa [RawBalancedTraversalTree.rawCode] using hinput) with
        ⟨finish, hruns, hfinishPc, hfinishCurrent, hfinishStack,
          hpersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, ?_,
        hpersistent.weaken hpersistentBase⟩
      · simpa [rawBalancedTraversalSteps] using hruns
      · simpa [RawBalancedTraversalTree.normalized,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hstack]
  | leaf tag atom =>
      rcases hvalid with ⟨hnonzero, htagClass⟩
      rcases hfit with
        ⟨hinput, houtput, _hstackBits, hatom⟩
      rcases controller_descend_rawLeaf hat hpc
          (by simpa [RawBalancedTraversalTree.rawCode] using hcurrent)
          hnonzero htagClass
          (by simpa [RawBalancedTraversalTree.rawCode] using hinput)
          hatom with
        ⟨entry, hentryRuns, hentryPc, _hentryCurrent, hentryStack,
          hentryAtom, hentryPersistent⟩
      have hentryReturnPc :
          entry.pc = balancedTraversalLeafReturnPc := by
        rw [← hleafPc]
        exact hentryPc
      rcases controller_return_leaf hat hentryReturnPc hentryAtom
          (by simpa [RawBalancedTraversalTree.normalized,
            BalancedTraversalTree.code] using houtput) with
        ⟨finish, hreturnRuns, hfinishPc, hfinishCurrent,
          hfinishStack, hreturnPersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_⟩
      · simpa [rawBalancedTraversalSteps] using
          hentryRuns.trans hreturnRuns
      · simpa [RawBalancedTraversalTree.normalized,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hentryStack, hstack]
      · exact (hentryPersistent.weaken hpersistentBase).trans
          (hreturnPersistent.weaken hpersistentBase)
  | branch tag left right inductionLeft inductionRight =>
      rcases hvalid with
        ⟨htagClass, hleftValid, hrightValid⟩
      rcases hfit with
        ⟨hinput, houtput, _hstackBits, hleftFit, hrightFit⟩
      have hvisitStack := hleftFit.stack
      have hcombineStack := hrightFit.stack
      rcases controller_descend_rawBranch hat hpc
          (by simpa [RawBalancedTraversalTree.rawCode] using hcurrent)
          htagClass hstack
          (by simpa [RawBalancedTraversalTree.rawCode] using hinput)
          hvisitStack with
        ⟨leftStart, hdescendRuns, hleftStartPc, hleftStartCurrent,
          hleftStartStack, hdescendPersistent⟩
      have hleftInputLength :
          leftStart.registers 1 = nativeInputLength :=
        hdescendPersistent.inputLength.trans hnativeInputLength
      rcases inductionLeft
          (.visitRight right.rawCode :: frames) leftStart
          hleftStartPc hleftStartCurrent hleftStartStack
          hleftInputLength hleftValid hleftFit with
        ⟨leftFinish, hleftRuns, hleftFinishPc, hleftFinishCurrent,
          hleftFinishStack, hleftPersistent⟩
      rcases controller_resume_visitRight hat hleftFinishPc
          hleftFinishCurrent hleftFinishStack hvisitStack
          hcombineStack with
        ⟨rightStart, hvisitRuns, hrightStartPc, hrightStartCurrent,
          hrightStartStack, hvisitPersistent⟩
      have hrightInputLength :
          rightStart.registers 1 = nativeInputLength :=
        hvisitPersistent.inputLength.trans
          (hleftPersistent.inputLength.trans hleftInputLength)
      rcases inductionRight
          (.combineLeft left.normalized.code :: frames) rightStart
          hrightStartPc hrightStartCurrent hrightStartStack
          hrightInputLength hrightValid hrightFit with
        ⟨rightFinish, hrightRuns, hrightFinishPc,
          hrightFinishCurrent, hrightFinishStack, hrightPersistent⟩
      rcases controller_resume_combine hat hrightFinishPc
          hrightFinishCurrent hrightFinishStack hcombineStack
          (by simpa [RawBalancedTraversalTree.normalized,
            BalancedTraversalTree.code, balancedBranchCode] using
              houtput) with
        ⟨finish, hcombineRuns, hfinishPc, hfinishCurrent,
          hfinishStack, hcombinePersistent⟩
      refine ⟨finish, ?_, hfinishPc, ?_, hfinishStack, ?_⟩
      · simpa [rawBalancedTraversalSteps] using
          ((((hdescendRuns.trans hleftRuns).trans hvisitRuns).trans
            hrightRuns).trans hcombineRuns)
      · simpa [RawBalancedTraversalTree.normalized,
          BalancedTraversalTree.code, balancedBranchCode] using
          hfinishCurrent
      · exact (hdescendPersistent.weaken hpersistentBase).trans
          (hleftPersistent.trans
            ((hvisitPersistent.weaken hpersistentBase).trans
              (hrightPersistent.trans
                (hcombinePersistent.weaken hpersistentBase))))

/-- Budgeted variant of `run_balancedTraversal_subtree`.  A concrete handler
may halt before its published budget; its unused fuel is threaded through the
single structural continuation rather than discarded or guessed. -/
theorem run_balancedTraversal_subtreeWithin
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (f leafBudget : ℕ → ℕ) (tree : BalancedTraversalTree)
    (frames : List BalancedTraversalFrame) (state : NPOracleState)
    (nativeInputLength : ℕ)
    (persistentBase : ℕ) (hpersistentBase : 9 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = tree.code)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hfit : BalancedTraversalFits maximumBits f tree frames)
    (hhandler :
      ∀ atom, atom ∈ tree.atoms →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (f atom) ≤ maximumBits →
          entry.registers 1 = nativeInputLength →
          RunsWithin program maximumBits (leafBudget atom) entry
            (fun finish =>
              finish.pc = balancedTraversalLeafReturnPc ∧
              finish.registers 0 = entry.registers 0 ∧
              finish.registers 2 = entry.registers 2 ∧
              finish.registers 3 = f atom ∧
              SameTraversalContextFrom persistentBase entry finish)) :
    RunsWithin program maximumBits
      (balancedTraversalSteps leafBudget tree) state
      (fun finish =>
        finish.pc = 15 ∧
        finish.registers 0 = (tree.map f).code ∧
        finish.registers 2 = encodeBalancedTraversalStack frames ∧
        SameTraversalContextFrom persistentBase state finish) := by
  induction tree generalizing frames state with
  | empty =>
      rcases hfit with ⟨hinput, _, _, _⟩
      rcases controller_descend_empty hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput) with
        ⟨finish, hruns, hfinishPc, hfinishCurrent, hfinishStack,
          hpersistent⟩
      apply (hruns.toRunsWithin.mono (weak := fun candidate =>
        candidate.pc = 15 ∧
        candidate.registers 0 =
          (BalancedTraversalTree.empty.map f).code ∧
        candidate.registers 2 =
          encodeBalancedTraversalStack frames ∧
        SameTraversalContextFrom persistentBase state candidate))
      intro candidate heq
      subst candidate
      exact ⟨hfinishPc,
        by simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using hfinishCurrent,
        by rw [hfinishStack, hstack],
        hpersistent.weaken hpersistentBase⟩
  | leaf atom =>
      rcases hfit with
        ⟨hinput, houtput, _, hatom, hmapped⟩
      rcases controller_descend_leaf hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput)
          hatom with
        ⟨entry, hentryRuns, hentryPc, hentryCurrent, hentryStack,
          hentryAtom, hentryPersistent⟩
      have hentryWithin :
          RunsWithin program maximumBits 6 state
            (fun candidate =>
              candidate = entry) :=
        hentryRuns.toRunsWithin
      have hhandlerWithin :=
        hhandler atom (by simp [BalancedTraversalTree.atoms])
          entry hentryPc hentryCurrent hentryAtom hmapped
          (hentryPersistent.inputLength.trans hnativeInputLength)
      have hafterHandler :
          RunsWithin program maximumBits (6 + leafBudget atom) state
            (fun returned =>
              returned.pc = balancedTraversalLeafReturnPc ∧
              returned.registers 0 = entry.registers 0 ∧
              returned.registers 2 = entry.registers 2 ∧
              returned.registers 3 = f atom ∧
              SameTraversalContextFrom persistentBase entry returned) := by
        exact hentryWithin.trans (by
          intro candidate heq
          subst candidate
          exact hhandlerWithin)
      have hcomplete :
          ∀ returned,
            (returned.pc = balancedTraversalLeafReturnPc ∧
              returned.registers 0 = entry.registers 0 ∧
              returned.registers 2 = entry.registers 2 ∧
              returned.registers 3 = f atom ∧
              SameTraversalContextFrom persistentBase entry returned) →
            RunsWithin program maximumBits 2 returned
              (fun finish =>
                finish.pc = 15 ∧
                finish.registers 0 =
                  (BalancedTraversalTree.leaf atom |>.map f).code ∧
                finish.registers 2 =
                  encodeBalancedTraversalStack frames ∧
                SameTraversalContextFrom persistentBase state finish) := by
        intro returned hreturned
        rcases hreturned with
          ⟨hreturnedPc, hreturnedCurrent, hreturnedStack,
            hreturnedAtom, hreturnedPersistent⟩
        rcases controller_return_leaf hat hreturnedPc hreturnedAtom
            (by simpa [BalancedTraversalTree.map,
              BalancedTraversalTree.code] using houtput) with
          ⟨finish, hreturnRuns, hfinishPc, hfinishCurrent,
            hfinishStack, hreturnPersistent⟩
        apply hreturnRuns.toRunsWithin.mono
        intro candidate heq
        subst candidate
        refine ⟨hfinishPc, ?_, ?_, ?_⟩
        · simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code] using hfinishCurrent
        · rw [hfinishStack, hreturnedStack, hentryStack, hstack]
        · exact (hentryPersistent.weaken hpersistentBase).trans
            (hreturnedPersistent.trans
              (hreturnPersistent.weaken hpersistentBase))
      have htotal := hafterHandler.trans hcomplete
      simpa [balancedTraversalSteps, Nat.add_assoc] using htotal
  | branch left right ihLeft ihRight =>
      rcases hfit with
        ⟨hinput, houtput, _, hleftFit, hrightFit⟩
      have hvisitStack := hleftFit.stack
      have hcombineStack := hrightFit.stack
      rcases controller_descend_branch hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          hstack
          (by simpa [BalancedTraversalTree.code] using hinput)
          hvisitStack with
        ⟨leftStart, hdescendRuns, hleftStartPc, hleftStartCurrent,
          hleftStartStack, hdescendPersistent⟩
      have hdescendWithin :
          RunsWithin program maximumBits 12 state (· = leftStart) :=
        hdescendRuns.toRunsWithin
      have hleftHandler :
          ∀ atom, atom ∈ left.atoms →
            ∀ entry : NPOracleState,
              entry.pc = leafPc →
              entry.registers 0 = Nat.pair 1 atom →
              entry.registers 3 = atom →
              natBitLength (f atom) ≤ maximumBits →
              entry.registers 1 = nativeInputLength →
              RunsWithin program maximumBits (leafBudget atom) entry
                (fun finish =>
                  finish.pc = balancedTraversalLeafReturnPc ∧
                  finish.registers 0 = entry.registers 0 ∧
                  finish.registers 2 = entry.registers 2 ∧
                  finish.registers 3 = f atom ∧
                  SameTraversalContextFrom persistentBase entry finish) := by
        intro atom hmem entry hentryPc hentryCurrent hentryAtom
          hmapped hentryInputLength
        apply hhandler atom
        · simp [BalancedTraversalTree.atoms, hmem]
        · exact hentryPc
        · exact hentryCurrent
        · exact hentryAtom
        · exact hmapped
        · exact hentryInputLength
      have hleftInputLength :
          leftStart.registers 1 = nativeInputLength :=
        hdescendPersistent.inputLength.trans hnativeInputLength
      have hleftWithin :=
        ihLeft (.visitRight right.code :: frames) leftStart
          hleftStartPc hleftStartCurrent hleftStartStack
          hleftInputLength hleftFit hleftHandler
      have hthroughLeft :
          RunsWithin program maximumBits
              (12 + balancedTraversalSteps leafBudget left) state
            (fun finish =>
              finish.pc = 15 ∧
              finish.registers 0 = (left.map f).code ∧
              finish.registers 2 =
                encodeBalancedTraversalStack
                  (.visitRight right.code :: frames) ∧
              SameTraversalContextFrom persistentBase state finish) := by
        exact hdescendWithin.trans (by
          intro candidate heq
          subst candidate
          apply hleftWithin.mono
          intro finish hfinish
          exact ⟨hfinish.1, hfinish.2.1, hfinish.2.2.1,
            (hdescendPersistent.weaken hpersistentBase).trans
              hfinish.2.2.2⟩)
      have hvisitContinuation :
          ∀ leftFinish,
            (leftFinish.pc = 15 ∧
              leftFinish.registers 0 = (left.map f).code ∧
              leftFinish.registers 2 =
                encodeBalancedTraversalStack
                  (.visitRight right.code :: frames) ∧
              SameTraversalContextFrom persistentBase state leftFinish) →
            RunsWithin program maximumBits 13 leftFinish
              (fun rightStart =>
                rightStart.pc = 0 ∧
                rightStart.registers 0 = right.code ∧
                rightStart.registers 2 =
                  encodeBalancedTraversalStack
                    (.combineLeft (left.map f).code :: frames) ∧
                SameTraversalContextFrom persistentBase state rightStart) := by
        intro leftFinish hleftFinish
        rcases hleftFinish with
          ⟨hleftPc, hleftCurrent, hleftStack, hleftPersistent⟩
        rcases controller_resume_visitRight hat hleftPc hleftCurrent
            hleftStack hvisitStack hcombineStack with
          ⟨rightStart, hvisitRuns, hrightPc, hrightCurrent,
            hrightStack, hvisitPersistent⟩
        apply hvisitRuns.toRunsWithin.mono
        intro candidate heq
        subst candidate
        exact ⟨hrightPc, hrightCurrent, hrightStack,
          hleftPersistent.trans
            (hvisitPersistent.weaken hpersistentBase)⟩
      have hthroughVisit :=
        hthroughLeft.trans hvisitContinuation
      have hrightHandler :
          ∀ atom, atom ∈ right.atoms →
            ∀ entry : NPOracleState,
              entry.pc = leafPc →
              entry.registers 0 = Nat.pair 1 atom →
              entry.registers 3 = atom →
              natBitLength (f atom) ≤ maximumBits →
              entry.registers 1 = nativeInputLength →
              RunsWithin program maximumBits (leafBudget atom) entry
                (fun finish =>
                  finish.pc = balancedTraversalLeafReturnPc ∧
                  finish.registers 0 = entry.registers 0 ∧
                  finish.registers 2 = entry.registers 2 ∧
                  finish.registers 3 = f atom ∧
                  SameTraversalContextFrom persistentBase entry finish) := by
        intro atom hmem entry hentryPc hentryCurrent hentryAtom
          hmapped hentryInputLength
        apply hhandler atom
        · simp [BalancedTraversalTree.atoms, hmem]
        · exact hentryPc
        · exact hentryCurrent
        · exact hentryAtom
        · exact hmapped
        · exact hentryInputLength
      have hthroughRight :
          RunsWithin program maximumBits
              ((12 + balancedTraversalSteps leafBudget left + 13) +
                balancedTraversalSteps leafBudget right) state
            (fun rightFinish =>
              rightFinish.pc = 15 ∧
              rightFinish.registers 0 = (right.map f).code ∧
              rightFinish.registers 2 =
                encodeBalancedTraversalStack
                  (.combineLeft (left.map f).code :: frames) ∧
              SameTraversalContextFrom persistentBase state rightFinish) := by
        apply RunsWithin.trans hthroughVisit
        intro rightStart hrightStart
        have hrightWithin :=
          ihRight (.combineLeft (left.map f).code :: frames)
            rightStart hrightStart.1 hrightStart.2.1
            hrightStart.2.2.1
            (hrightStart.2.2.2.inputLength.trans hnativeInputLength)
            hrightFit hrightHandler
        apply hrightWithin.mono
        intro rightFinish hrightFinish
        exact ⟨hrightFinish.1, hrightFinish.2.1,
          hrightFinish.2.2.1,
          hrightStart.2.2.2.trans hrightFinish.2.2.2⟩
      have hcombineContinuation :
          ∀ rightFinish,
            (rightFinish.pc = 15 ∧
              rightFinish.registers 0 = (right.map f).code ∧
              rightFinish.registers 2 =
                encodeBalancedTraversalStack
                  (.combineLeft (left.map f).code :: frames) ∧
              SameTraversalContextFrom persistentBase state rightFinish) →
            RunsWithin program maximumBits 10 rightFinish
              (fun finish =>
                finish.pc = 15 ∧
                finish.registers 0 =
                  (BalancedTraversalTree.branch left right |>.map f).code ∧
                finish.registers 2 =
                  encodeBalancedTraversalStack frames ∧
                SameTraversalContextFrom persistentBase state finish) := by
        intro rightFinish hrightFinish
        rcases controller_resume_combine hat hrightFinish.1
            hrightFinish.2.1 hrightFinish.2.2.1 hcombineStack
            (by simpa [BalancedTraversalTree.map,
              BalancedTraversalTree.code, balancedBranchCode] using
                houtput) with
          ⟨finish, hcombineRuns, hfinishPc, hfinishCurrent,
            hfinishStack, hcombinePersistent⟩
        apply hcombineRuns.toRunsWithin.mono
        intro candidate heq
        subst candidate
        refine ⟨hfinishPc, ?_, hfinishStack, ?_⟩
        · simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code, balancedBranchCode] using
            hfinishCurrent
        · exact hrightFinish.2.2.2.trans
            (hcombinePersistent.weaken hpersistentBase)
      have htotal := hthroughRight.trans hcombineContinuation
      simpa [balancedTraversalSteps, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using htotal

theorem run_balancedTraversalFold_subtreeWithin
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (step leafBudget leafRequiredBits : ℕ → ℕ → ℕ)
    (tree : BalancedTraversalTree) (frames : List BalancedTraversalFrame)
    (state : NPOracleState) (nativeInputLength persistentBase : ℕ)
    (hpersistentBase : 10 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = tree.code)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hfit :
      BalancedTraversalFits maximumBits (fun value => value) tree frames)
    (hfoldFit :
      BalancedFoldFits maximumBits step (state.registers 9) tree.atoms)
    (hleafFit :
      BalancedFoldLeafFits maximumBits step leafRequiredBits
        (state.registers 9) tree.atoms)
    (hhandler :
      ∀ atom, atom ∈ tree.atoms →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          entry.registers 1 = nativeInputLength →
          natBitLength (entry.registers 9) ≤ maximumBits →
          natBitLength (step (entry.registers 9) atom) ≤ maximumBits →
          leafRequiredBits (entry.registers 9) atom ≤ maximumBits →
          RunsWithin program maximumBits
            (leafBudget (entry.registers 9) atom) entry
            (fun finish =>
              finish.pc = balancedTraversalLeafReturnPc ∧
                finish.registers 0 = entry.registers 0 ∧
                finish.registers 2 = entry.registers 2 ∧
                finish.registers 3 = atom ∧
                finish.registers 9 =
                  step (entry.registers 9) atom ∧
                SameTraversalContextFrom persistentBase entry finish)) :
    RunsWithin program maximumBits
      (balancedTraversalStructuralSteps tree +
        balancedFoldLeafSteps step leafBudget
          (state.registers 9) tree.atoms)
      state
      (fun finish =>
        finish.pc = 15 ∧
          finish.registers 0 =
            (tree.map fun value => value).code ∧
          finish.registers 2 = encodeBalancedTraversalStack frames ∧
          finish.registers 9 =
            tree.atoms.foldl step (state.registers 9) ∧
          SameTraversalContextFrom persistentBase state finish) := by
  induction tree generalizing frames state with
  | empty =>
      rcases hfit with ⟨hinput, _, _, _⟩
      rcases controller_descend_empty hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput) with
        ⟨finish, hruns, hfinishPc, hfinishCurrent, hfinishStack,
          hpersistent⟩
      apply hruns.toRunsWithin.mono
      intro candidate heq
      subst candidate
      refine ⟨hfinishPc, ?_, ?_, ?_, hpersistent.weaken (by omega)⟩
      · simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using hfinishCurrent
      · rw [hfinishStack, hstack]
      · rw [hpersistent.persistent 9 (by omega)]
        simp [BalancedTraversalTree.atoms]
  | leaf atom =>
      rcases hfit with
        ⟨hinput, houtput, _, hatom, _hmapped⟩
      rcases hfoldFit with ⟨haccumulatorBits, hresultBits, _⟩
      rcases hleafFit with ⟨hleafRequiredBits, _⟩
      rcases controller_descend_leaf hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          (by simpa [BalancedTraversalTree.code] using hinput)
          hatom with
        ⟨entry, hentryRuns, hentryPc, hentryCurrent, hentryStack,
          hentryAtom, hentryPersistent⟩
      have hentry9 := hentryPersistent.persistent 9 (by omega)
      have hentryAccumulatorBits :
          natBitLength (entry.registers 9) ≤ maximumBits := by
        rw [hentry9]
        exact haccumulatorBits
      have hentryResultBits :
          natBitLength (step (entry.registers 9) atom) ≤ maximumBits := by
        rw [hentry9]
        exact hresultBits
      have hentryLeafBits :
          leafRequiredBits (entry.registers 9) atom ≤ maximumBits := by
        rw [hentry9]
        exact hleafRequiredBits
      have hentryWithin :
          RunsWithin program maximumBits 6 state (· = entry) :=
        hentryRuns.toRunsWithin
      have hhandlerWithin :=
        hhandler atom (by simp [BalancedTraversalTree.atoms])
          entry hentryPc hentryCurrent hentryAtom
          (hentryPersistent.inputLength.trans hnativeInputLength)
          hentryAccumulatorBits hentryResultBits hentryLeafBits
      have hafterHandler :
          RunsWithin program maximumBits
              (6 + leafBudget (state.registers 9) atom) state
            (fun returned =>
              returned.pc = balancedTraversalLeafReturnPc ∧
                returned.registers 0 = entry.registers 0 ∧
                returned.registers 2 = entry.registers 2 ∧
                returned.registers 3 = atom ∧
                returned.registers 9 =
                  step (entry.registers 9) atom ∧
                SameTraversalContextFrom persistentBase entry returned) := by
        have hcomposed := hentryWithin.trans (by
          intro candidate heq
          subst candidate
          exact hhandlerWithin)
        simpa [hentry9] using hcomposed
      have hcomplete :
          ∀ returned,
            (returned.pc = balancedTraversalLeafReturnPc ∧
              returned.registers 0 = entry.registers 0 ∧
              returned.registers 2 = entry.registers 2 ∧
              returned.registers 3 = atom ∧
              returned.registers 9 =
                step (entry.registers 9) atom ∧
              SameTraversalContextFrom persistentBase entry returned) →
            RunsWithin program maximumBits 2 returned
              (fun finish =>
                finish.pc = 15 ∧
                  finish.registers 0 =
                    (BalancedTraversalTree.leaf atom |>.map
                      fun value => value).code ∧
                  finish.registers 2 =
                    encodeBalancedTraversalStack frames ∧
                  finish.registers 9 =
                    [atom].foldl step (state.registers 9) ∧
                  SameTraversalContextFrom persistentBase state finish) := by
        intro returned hreturned
        rcases hreturned with
          ⟨hreturnedPc, hreturnedCurrent, hreturnedStack,
            hreturnedAtom, hreturned9, hreturnedPersistent⟩
        rcases controller_return_leaf hat hreturnedPc hreturnedAtom
            (by simpa [BalancedTraversalTree.map,
              BalancedTraversalTree.code] using houtput) with
          ⟨finish, hreturnRuns, hfinishPc, hfinishCurrent,
            hfinishStack, hreturnPersistent⟩
        apply hreturnRuns.toRunsWithin.mono
        intro candidate heq
        subst candidate
        refine ⟨hfinishPc, ?_, ?_, ?_, ?_⟩
        · simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code] using hfinishCurrent
        · rw [hfinishStack, hreturnedStack, hentryStack, hstack]
        · rw [hreturnPersistent.persistent 9 (by omega), hreturned9,
            hentry9]
          simp
        · exact (hentryPersistent.weaken (by omega)).trans
            (hreturnedPersistent.trans
              (hreturnPersistent.weaken (by omega)))
      have htotal := hafterHandler.trans hcomplete
      convert htotal using 1
      · simp [balancedTraversalStructuralSteps,
          BalancedTraversalTree.atoms, balancedFoldLeafSteps]
        omega
      · simp [BalancedTraversalTree.atoms]
  | branch left right ihLeft ihRight =>
      rcases hfit with
        ⟨hinput, houtput, _, hleftFit, hrightFit⟩
      have hfoldSplit :=
        (balancedFoldFits_append maximumBits step (state.registers 9)
          left.atoms right.atoms).mp
          (by simpa [BalancedTraversalTree.atoms] using hfoldFit)
      have hleafSplit :=
        (balancedFoldLeafFits_append maximumBits step leafRequiredBits
          (state.registers 9) left.atoms right.atoms).mp
          (by simpa [BalancedTraversalTree.atoms] using hleafFit)
      have hvisitStack := hleftFit.stack
      have hcombineStack := hrightFit.stack
      rcases controller_descend_branch hat hpc
          (by simpa [BalancedTraversalTree.code] using hcurrent)
          hstack
          (by simpa [BalancedTraversalTree.code] using hinput)
          hvisitStack with
        ⟨leftStart, hdescendRuns, hleftStartPc, hleftStartCurrent,
          hleftStartStack, hdescendPersistent⟩
      have hdescend9 :=
        hdescendPersistent.persistent 9 (by omega)
      have hdescendWithin :
          RunsWithin program maximumBits 12 state (· = leftStart) :=
        hdescendRuns.toRunsWithin
      have hleftHandler :
          ∀ atom, atom ∈ left.atoms →
            ∀ entry : NPOracleState,
              entry.pc = leafPc →
              entry.registers 0 = Nat.pair 1 atom →
              entry.registers 3 = atom →
              entry.registers 1 = nativeInputLength →
              natBitLength (entry.registers 9) ≤ maximumBits →
              natBitLength (step (entry.registers 9) atom) ≤ maximumBits →
              leafRequiredBits (entry.registers 9) atom ≤ maximumBits →
              RunsWithin program maximumBits
                (leafBudget (entry.registers 9) atom) entry
                (fun finish =>
                  finish.pc = balancedTraversalLeafReturnPc ∧
                    finish.registers 0 = entry.registers 0 ∧
                    finish.registers 2 = entry.registers 2 ∧
                    finish.registers 3 = atom ∧
                    finish.registers 9 =
                      step (entry.registers 9) atom ∧
                    SameTraversalContextFrom persistentBase entry finish) := by
        intro atom hmem
        apply hhandler atom
        simp [BalancedTraversalTree.atoms, hmem]
      have hleftFoldFit :
          BalancedFoldFits maximumBits step
            (leftStart.registers 9) left.atoms := by
        rw [hdescend9]
        exact hfoldSplit.1
      have hleftLeafFit :
          BalancedFoldLeafFits maximumBits step leafRequiredBits
            (leftStart.registers 9) left.atoms := by
        rw [hdescend9]
        exact hleafSplit.1
      have hleftWithin :=
        ihLeft (.visitRight right.code :: frames) leftStart
          hleftStartPc hleftStartCurrent hleftStartStack
          (hdescendPersistent.inputLength.trans hnativeInputLength)
          hleftFit hleftFoldFit hleftLeafFit hleftHandler
      have hthroughLeft :
          RunsWithin program maximumBits
              (12 +
                (balancedTraversalStructuralSteps left +
                  balancedFoldLeafSteps step leafBudget
                    (state.registers 9) left.atoms))
              state
            (fun leftFinish =>
              leftFinish.pc = 15 ∧
                leftFinish.registers 0 =
                  (left.map fun value => value).code ∧
                leftFinish.registers 2 =
                  encodeBalancedTraversalStack
                    (.visitRight right.code :: frames) ∧
                leftFinish.registers 9 =
                  left.atoms.foldl step (state.registers 9) ∧
                SameTraversalContextFrom persistentBase state leftFinish) := by
        have hcomposed :
            RunsWithin program maximumBits
                (12 +
                  (balancedTraversalStructuralSteps left +
                    balancedFoldLeafSteps step leafBudget
                      (leftStart.registers 9) left.atoms))
                state
              (fun leftFinish =>
                leftFinish.pc = 15 ∧
                  leftFinish.registers 0 =
                    (left.map fun value => value).code ∧
                  leftFinish.registers 2 =
                    encodeBalancedTraversalStack
                      (.visitRight right.code :: frames) ∧
                  leftFinish.registers 9 =
                    left.atoms.foldl step (leftStart.registers 9) ∧
                  SameTraversalContextFrom persistentBase
                    state leftFinish) :=
          hdescendWithin.trans (by
          intro candidate heq
          subst candidate
          apply hleftWithin.mono
          intro finish hfinish
          refine ⟨hfinish.1, hfinish.2.1, hfinish.2.2.1, ?_, ?_⟩
          · exact hfinish.2.2.2.1
          · exact (hdescendPersistent.weaken (by omega)).trans
              hfinish.2.2.2.2)
        simpa [hdescend9] using hcomposed
      have hvisitContinuation :
          ∀ leftFinish,
            (leftFinish.pc = 15 ∧
              leftFinish.registers 0 =
                (left.map fun value => value).code ∧
              leftFinish.registers 2 =
                encodeBalancedTraversalStack
                  (.visitRight right.code :: frames) ∧
              leftFinish.registers 9 =
                left.atoms.foldl step (state.registers 9) ∧
              SameTraversalContextFrom persistentBase state leftFinish) →
            RunsWithin program maximumBits 13 leftFinish
              (fun rightStart =>
                rightStart.pc = 0 ∧
                  rightStart.registers 0 = right.code ∧
                  rightStart.registers 2 =
                    encodeBalancedTraversalStack
                      (.combineLeft
                        (left.map fun value => value).code :: frames) ∧
                  rightStart.registers 9 =
                    left.atoms.foldl step (state.registers 9) ∧
                  SameTraversalContextFrom persistentBase state rightStart) := by
        intro leftFinish hleftFinish
        rcases hleftFinish with
          ⟨hleftPc, hleftCurrent, hleftStack, hleft9, hleftPersistent⟩
        rcases controller_resume_visitRight hat hleftPc hleftCurrent
            hleftStack hvisitStack hcombineStack with
          ⟨rightStart, hvisitRuns, hrightPc, hrightCurrent,
            hrightStack, hvisitPersistent⟩
        apply hvisitRuns.toRunsWithin.mono
        intro candidate heq
        subst candidate
        refine ⟨hrightPc, hrightCurrent, hrightStack, ?_, ?_⟩
        · rw [hvisitPersistent.persistent 9 (by omega), hleft9]
        · exact hleftPersistent.trans
            (hvisitPersistent.weaken (by omega))
      have hthroughVisit :=
        hthroughLeft.trans hvisitContinuation
      have hrightHandler :
          ∀ atom, atom ∈ right.atoms →
            ∀ entry : NPOracleState,
              entry.pc = leafPc →
              entry.registers 0 = Nat.pair 1 atom →
              entry.registers 3 = atom →
              entry.registers 1 = nativeInputLength →
              natBitLength (entry.registers 9) ≤ maximumBits →
              natBitLength (step (entry.registers 9) atom) ≤ maximumBits →
              leafRequiredBits (entry.registers 9) atom ≤ maximumBits →
              RunsWithin program maximumBits
                (leafBudget (entry.registers 9) atom) entry
                (fun finish =>
                  finish.pc = balancedTraversalLeafReturnPc ∧
                    finish.registers 0 = entry.registers 0 ∧
                    finish.registers 2 = entry.registers 2 ∧
                    finish.registers 3 = atom ∧
                    finish.registers 9 =
                      step (entry.registers 9) atom ∧
                    SameTraversalContextFrom persistentBase entry finish) := by
        intro atom hmem
        apply hhandler atom
        simp [BalancedTraversalTree.atoms, hmem]
      have hthroughRight :
          RunsWithin program maximumBits
              ((12 +
                  (balancedTraversalStructuralSteps left +
                    balancedFoldLeafSteps step leafBudget
                      (state.registers 9) left.atoms) + 13) +
                (balancedTraversalStructuralSteps right +
                  balancedFoldLeafSteps step leafBudget
                    (left.atoms.foldl step (state.registers 9))
                    right.atoms))
              state
            (fun rightFinish =>
              rightFinish.pc = 15 ∧
                rightFinish.registers 0 =
                  (right.map fun value => value).code ∧
                rightFinish.registers 2 =
                  encodeBalancedTraversalStack
                    (.combineLeft
                      (left.map fun value => value).code :: frames) ∧
                rightFinish.registers 9 =
                  (left.atoms ++ right.atoms).foldl step
                    (state.registers 9) ∧
                SameTraversalContextFrom persistentBase state rightFinish) := by
        apply RunsWithin.trans hthroughVisit
        intro rightStart hrightStart
        have hrightFoldFit :
            BalancedFoldFits maximumBits step
              (rightStart.registers 9) right.atoms := by
          rw [hrightStart.2.2.2.1]
          exact hfoldSplit.2
        have hrightLeafFit :
            BalancedFoldLeafFits maximumBits step leafRequiredBits
              (rightStart.registers 9) right.atoms := by
          rw [hrightStart.2.2.2.1]
          exact hleafSplit.2
        have hrightWithin :=
          ihRight
            (.combineLeft
              (left.map fun value => value).code :: frames)
            rightStart hrightStart.1 hrightStart.2.1
            hrightStart.2.2.1
            (hrightStart.2.2.2.2.inputLength.trans hnativeInputLength)
            hrightFit hrightFoldFit hrightLeafFit hrightHandler
        rw [List.foldl_append, ← hrightStart.2.2.2.1]
        apply hrightWithin.mono
        intro rightFinish hrightFinish
        refine ⟨hrightFinish.1, hrightFinish.2.1,
          hrightFinish.2.2.1, ?_, ?_⟩
        · exact hrightFinish.2.2.2.1
        · exact hrightStart.2.2.2.2.trans
            hrightFinish.2.2.2.2
      have hcombineContinuation :
          ∀ rightFinish,
            (rightFinish.pc = 15 ∧
              rightFinish.registers 0 =
                (right.map fun value => value).code ∧
              rightFinish.registers 2 =
                encodeBalancedTraversalStack
                  (.combineLeft
                    (left.map fun value => value).code :: frames) ∧
              rightFinish.registers 9 =
                (left.atoms ++ right.atoms).foldl step
                  (state.registers 9) ∧
              SameTraversalContextFrom persistentBase state rightFinish) →
            RunsWithin program maximumBits 10 rightFinish
              (fun finish =>
                finish.pc = 15 ∧
                  finish.registers 0 =
                    (BalancedTraversalTree.branch left right |>.map
                      fun value => value).code ∧
                  finish.registers 2 =
                    encodeBalancedTraversalStack frames ∧
                  finish.registers 9 =
                    (left.atoms ++ right.atoms).foldl step
                      (state.registers 9) ∧
                  SameTraversalContextFrom persistentBase state finish) := by
        intro rightFinish hrightFinish
        rcases controller_resume_combine hat hrightFinish.1
            hrightFinish.2.1 hrightFinish.2.2.1 hcombineStack
            (by simpa [BalancedTraversalTree.map,
              BalancedTraversalTree.code, balancedBranchCode] using
                houtput) with
          ⟨finish, hcombineRuns, hfinishPc, hfinishCurrent,
            hfinishStack, hcombinePersistent⟩
        apply hcombineRuns.toRunsWithin.mono
        intro candidate heq
        subst candidate
        refine ⟨hfinishPc, ?_, hfinishStack, ?_, ?_⟩
        · simpa [BalancedTraversalTree.map,
            BalancedTraversalTree.code, balancedBranchCode] using
            hfinishCurrent
        · rw [hcombinePersistent.persistent 9 (by omega),
            hrightFinish.2.2.2.1]
        · exact hrightFinish.2.2.2.2.trans
            (hcombinePersistent.weaken (by omega))
      have htotal := hthroughRight.trans hcombineContinuation
      convert htotal using 1
      · simp [balancedTraversalStructuralSteps,
          BalancedTraversalTree.atoms, balancedFoldLeafSteps_append]
        omega
      · simp [BalancedTraversalTree.atoms]

private theorem controller_finish
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    {state : NPOracleState}
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 15)
    (hstack : state.registers 2 = 0) :
    ∃ finish,
      RunsToIn program maximumBits 1 state finish ∧
      finish.pc = donePc ∧
      finish.registers 0 = state.registers 0 ∧
      finish.registers 2 = 0 ∧
      SameBalancedPersistent state finish := by
  let finish := state.jump donePc
  have hlookup15 :
      program[15]? = some (.branchZero 2 donePc 16) :=
    controller_lookup hat (by rfl)
  have hruns :
      RunsToIn program maximumBits 1 state finish := by
    simpa [finish, hstack] using
      runsTo_branchZero hlookup15 hpc
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_⟩
  · rfl
  · simpa [finish] using hstack
  · refine ⟨rfl, ?_⟩
    intro register _
    rfl

theorem run_balancedTraversalFoldWithin
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (step leafBudget leafRequiredBits : ℕ → ℕ → ℕ)
    (values : List ℕ)
    (state : NPOracleState) (nativeInputLength persistentBase : ℕ)
    (hpersistentBase : 10 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = encodeBalancedList values)
    (hstack : state.registers 2 = 0)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hfit :
      BalancedTraversalFits maximumBits (fun value => value)
        (balancedTraversalTree values) [])
    (hfoldFit :
      BalancedFoldFits maximumBits step (state.registers 9) values)
    (hleafFit :
      BalancedFoldLeafFits maximumBits step leafRequiredBits
        (state.registers 9) values)
    (hhandler :
      ∀ atom, atom ∈ values →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          entry.registers 1 = nativeInputLength →
          natBitLength (entry.registers 9) ≤ maximumBits →
          natBitLength (step (entry.registers 9) atom) ≤ maximumBits →
          leafRequiredBits (entry.registers 9) atom ≤ maximumBits →
          RunsWithin program maximumBits
            (leafBudget (entry.registers 9) atom) entry
            (fun finish =>
              finish.pc = balancedTraversalLeafReturnPc ∧
                finish.registers 0 = entry.registers 0 ∧
                finish.registers 2 = entry.registers 2 ∧
                finish.registers 3 = atom ∧
                finish.registers 9 =
                  step (entry.registers 9) atom ∧
                SameTraversalContextFrom persistentBase entry finish)) :
    RunsWithin program maximumBits
      (balancedTraversalStructuralSteps (balancedTraversalTree values) +
        balancedFoldLeafSteps step leafBudget
          (state.registers 9) values + 1)
      state
      (fun finish =>
        finish.pc = donePc ∧
          finish.registers 0 = encodeBalancedList values ∧
          finish.registers 2 = 0 ∧
          finish.registers 9 =
            values.foldl step (state.registers 9) ∧
          SameTraversalContextFrom persistentBase state finish) := by
  have htreeWithin :=
    run_balancedTraversalFold_subtreeWithin step leafBudget leafRequiredBits
      (balancedTraversalTree values) [] state nativeInputLength
      persistentBase hpersistentBase hat hpc
      (by rw [balancedTraversalTree_code]; exact hcurrent)
      (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using hstack)
      hnativeInputLength hfit
      (by simpa [balancedTraversalTree_atoms] using hfoldFit)
      (by simpa [balancedTraversalTree_atoms] using hleafFit)
      (by simpa [balancedTraversalTree_atoms] using hhandler)
  simp only [balancedTraversalTree_atoms] at htreeWithin
  have htotal :
      RunsWithin program maximumBits
        (balancedTraversalStructuralSteps (balancedTraversalTree values) +
          balancedFoldLeafSteps step leafBudget
            (state.registers 9) values + 1)
        state
        (fun finish =>
          finish.pc = donePc ∧
            finish.registers 0 = encodeBalancedList values ∧
            finish.registers 2 = 0 ∧
            finish.registers 9 =
              values.foldl step (state.registers 9) ∧
            SameTraversalContextFrom persistentBase state finish) := by
    apply htreeWithin.trans
    intro atResume hatResume
    rcases controller_finish hat hatResume.1
        (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using
          hatResume.2.2.1) with
      ⟨finish, hfinishRuns, hfinishPc, hfinishCurrent,
        hfinishStack, hfinishPersistent⟩
    apply hfinishRuns.toRunsWithin.mono
    intro candidate heq
    subst candidate
    refine ⟨hfinishPc, ?_, hfinishStack, ?_, ?_⟩
    · rw [hfinishCurrent, hatResume.2.1,
        balancedTraversalTree_map_code]
      simp
    · rw [hfinishPersistent.persistent 9 (by omega),
        hatResume.2.2.2.1]
    · exact hatResume.2.2.2.2.trans
        (hfinishPersistent.weaken (by omega))
  exact htotal

/-- Public one-pass sum corollary.  Numeric zero is a valid result, so callers
must retain their independent syntax/validity flag rather than treating the
sum as a success sentinel. -/
theorem run_balancedTraversalNatSum
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (values : List ℕ) (state : NPOracleState)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hadd : program[leafPc]? =
      some (.add 9 3 9 balancedTraversalLeafReturnPc))
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = encodeBalancedList values)
    (hstack : state.registers 2 = 0)
    (hfit :
      BalancedTraversalFits maximumBits (fun value => value)
        (balancedTraversalTree values) [])
    (hsumBits :
      natBitLength (state.registers 9 + values.sum) ≤ maximumBits) :
    ∃ finish,
      RunsToIn program maximumBits
        (balancedTraversalStructuralSteps (balancedTraversalTree values) +
          values.length + 1) state finish ∧
      finish.pc = donePc ∧
      finish.registers 0 = encodeBalancedList values ∧
      finish.registers 2 = 0 ∧
      finish.registers 9 = state.registers 9 + values.sum ∧
      SameTraversalContextFrom 10 state finish := by
  rcases run_balancedTraversalNatSum_subtree
      (balancedTraversalTree values) [] state hat hadd hpc
      (by rw [balancedTraversalTree_code]; exact hcurrent)
      (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using
        hstack)
      hfit
      (by simpa [balancedTraversalTree_atoms] using hsumBits) with
    ⟨atResume, htreeRuns, hatResumePc, hatResumeCurrent,
      hatResumeStack, hatResume9, htreePersistent⟩
  rcases controller_finish hat hatResumePc
      (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using
        hatResumeStack) with
    ⟨finish, hfinishRuns, hfinishPc, hfinishCurrent,
      hfinishStack, hfinishPersistent⟩
  refine ⟨finish, ?_, hfinishPc, ?_, hfinishStack, ?_, ?_⟩
  · convert htreeRuns.trans hfinishRuns using 1
    simp [balancedTraversalTree_atoms]
  · rw [hfinishCurrent, hatResumeCurrent,
      balancedTraversalTree_map_code]
    simp
  · rw [hfinishPersistent.persistent 9 (by omega), hatResume9,
      balancedTraversalTree_atoms]
  · exact htreePersistent.trans
      (hfinishPersistent.weaken (by omega))

/-- Public canonical-list corollary.  With the empty internal stack, the exact
run reaches `donePc` and returns the unique balanced encoding of `values.map f`.
-/
theorem run_balancedTraversal
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (f leafSteps : ℕ → ℕ) (values : List ℕ) (state : NPOracleState)
    (nativeInputLength : ℕ)
    (persistentBase : ℕ) (hpersistentBase : 9 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = encodeBalancedList values)
    (hstack : state.registers 2 = 0)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hfit :
      BalancedTraversalFits maximumBits f
        (balancedTraversalTree values) [])
    (hhandler :
      ∀ atom, atom ∈ values →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (f atom) ≤ maximumBits →
          entry.registers 1 = nativeInputLength →
          ∃ finish,
            RunsToIn program maximumBits (leafSteps atom) entry finish ∧
            finish.pc = balancedTraversalLeafReturnPc ∧
            finish.registers 0 = entry.registers 0 ∧
            finish.registers 2 = entry.registers 2 ∧
            finish.registers 3 = f atom ∧
            SameTraversalContextFrom persistentBase entry finish) :
    ∃ finish,
      RunsToIn program maximumBits
        (balancedTraversalStructuralSteps (balancedTraversalTree values) +
          (values.map leafSteps).sum + 1) state finish ∧
      finish.pc = donePc ∧
      finish.registers 0 = encodeBalancedList (values.map f) ∧
      finish.registers 2 = 0 ∧
      SameTraversalContextFrom persistentBase state finish := by
  have htreeHandler :
      ∀ atom, atom ∈ (balancedTraversalTree values).atoms →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (f atom) ≤ maximumBits →
          entry.registers 1 = nativeInputLength →
          ∃ finish,
            RunsToIn program maximumBits (leafSteps atom) entry finish ∧
            finish.pc = balancedTraversalLeafReturnPc ∧
            finish.registers 0 = entry.registers 0 ∧
            finish.registers 2 = entry.registers 2 ∧
            finish.registers 3 = f atom ∧
            SameTraversalContextFrom persistentBase entry finish := by
    simpa [balancedTraversalTree_atoms] using hhandler
  rcases run_balancedTraversal_subtree f leafSteps
      (balancedTraversalTree values) [] state nativeInputLength
      persistentBase hpersistentBase
      hat hpc
      (by rw [balancedTraversalTree_code]; exact hcurrent)
      (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using hstack)
      hnativeInputLength hfit htreeHandler with
    ⟨atResume, htreeRuns, hatResumePc, hatResumeCurrent,
      hatResumeStack, htreePersistent⟩
  rcases controller_finish hat hatResumePc
      (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using
        hatResumeStack) with
    ⟨finish, hfinishRuns, hfinishPc, hfinishCurrent,
      hfinishStack, hfinishPersistent⟩
  refine ⟨finish, ?_, hfinishPc, ?_, hfinishStack, ?_⟩
  · have hdecompose :=
      balancedTraversalSteps_eq_structural
        (balancedTraversalTree values) leafSteps
    rw [balancedTraversalTree_atoms] at hdecompose
    rw [← hdecompose]
    exact htreeRuns.trans hfinishRuns
  · rw [hfinishCurrent, hatResumeCurrent,
      balancedTraversalTree_map_code]
  · exact htreePersistent.trans
      (hfinishPersistent.weaken hpersistentBase)

theorem run_balancedTraversalWithin
    {program : NPOracleProgram} {maximumBits leafPc donePc : ℕ}
    (f leafBudget : ℕ → ℕ) (values : List ℕ) (state : NPOracleState)
    (nativeInputLength : ℕ)
    (persistentBase : ℕ) (hpersistentBase : 9 ≤ persistentBase)
    (hat : BalancedTraversalControllerAt program leafPc donePc)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = encodeBalancedList values)
    (hstack : state.registers 2 = 0)
    (hnativeInputLength :
      state.registers 1 = nativeInputLength)
    (hfit :
      BalancedTraversalFits maximumBits f
        (balancedTraversalTree values) [])
    (hhandler :
      ∀ atom, atom ∈ values →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (f atom) ≤ maximumBits →
          entry.registers 1 = nativeInputLength →
          RunsWithin program maximumBits (leafBudget atom) entry
            (fun finish =>
              finish.pc = balancedTraversalLeafReturnPc ∧
              finish.registers 0 = entry.registers 0 ∧
              finish.registers 2 = entry.registers 2 ∧
              finish.registers 3 = f atom ∧
              SameTraversalContextFrom persistentBase entry finish)) :
    RunsWithin program maximumBits
      (balancedTraversalStructuralSteps (balancedTraversalTree values) +
        (values.map leafBudget).sum + 1) state
      (fun finish =>
        finish.pc = donePc ∧
        finish.registers 0 = encodeBalancedList (values.map f) ∧
        finish.registers 2 = 0 ∧
        SameTraversalContextFrom persistentBase state finish) := by
  have htreeHandler :
      ∀ atom, atom ∈ (balancedTraversalTree values).atoms →
        ∀ entry : NPOracleState,
          entry.pc = leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (f atom) ≤ maximumBits →
          entry.registers 1 = nativeInputLength →
          RunsWithin program maximumBits (leafBudget atom) entry
            (fun finish =>
              finish.pc = balancedTraversalLeafReturnPc ∧
              finish.registers 0 = entry.registers 0 ∧
              finish.registers 2 = entry.registers 2 ∧
              finish.registers 3 = f atom ∧
              SameTraversalContextFrom persistentBase entry finish) := by
    simpa [balancedTraversalTree_atoms] using hhandler
  have htreeWithin :=
    run_balancedTraversal_subtreeWithin f leafBudget
      (balancedTraversalTree values) [] state nativeInputLength
      persistentBase hpersistentBase
      hat hpc
      (by rw [balancedTraversalTree_code]; exact hcurrent)
      (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using hstack)
      hnativeInputLength hfit htreeHandler
  have htotal :
      RunsWithin program maximumBits
        (balancedTraversalSteps leafBudget (balancedTraversalTree values) + 1)
        state
        (fun finish =>
          finish.pc = donePc ∧
          finish.registers 0 = encodeBalancedList (values.map f) ∧
          finish.registers 2 = 0 ∧
          SameTraversalContextFrom persistentBase state finish) := by
    apply htreeWithin.trans
    intro atResume hatResume
    rcases controller_finish hat hatResume.1
        (by simpa [encodeBalancedTraversalStack, encodeTaggedList] using
          hatResume.2.2.1) with
      ⟨finish, hfinishRuns, hfinishPc, hfinishCurrent,
        hfinishStack, hfinishPersistent⟩
    apply hfinishRuns.toRunsWithin.mono
    intro candidate heq
    subst candidate
    refine ⟨hfinishPc, ?_, hfinishStack, ?_⟩
    · rw [hfinishCurrent, hatResume.2.1,
        balancedTraversalTree_map_code]
    · exact hatResume.2.2.2.trans
        (hfinishPersistent.weaken hpersistentBase)
  have hdecompose :=
    balancedTraversalSteps_eq_structural
      (balancedTraversalTree values) leafBudget
  rw [balancedTraversalTree_atoms] at hdecompose
  rw [← hdecompose]
  exact htotal

end NearCubicWires.CanonicalBinaryProgram
