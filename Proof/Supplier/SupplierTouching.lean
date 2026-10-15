import Proof.Foundations.SupplierPipeline

/-!
# Touching-set selection

This module proves the exact finite averaging bound behind `TouchingSelect`.
Support occurrences are indexed by a finite type, so duplicate supports remain
distinct charges.  Among the `K`-subsets of `Fin q`, one selection touches at
most the incidence-average: `q * touched ≤ K * totalSupportMass`.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierTouching

def touchIndicator {Coordinate : Type} [DecidableEq Coordinate]
    (selected support : Finset Coordinate) : ℕ :=
  if Disjoint selected support then 0 else 1

def touchingCost {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate) (selected : Finset Coordinate) : ℕ :=
  ∑ gate, touchIndicator selected (support gate)

def supportIncidenceMass {Gate Coordinate : Type} [Fintype Gate]
    (support : Gate → Finset Coordinate) : ℕ :=
  ∑ gate, (support gate).card

theorem touchIndicator_le_membershipSum
    {Coordinate : Type} [DecidableEq Coordinate]
    (selected support : Finset Coordinate) :
    touchIndicator selected support ≤
      ∑ coordinate ∈ support, if coordinate ∈ selected then 1 else 0 := by
  by_cases hdisjoint : Disjoint selected support
  · simp [touchIndicator, hdisjoint]
  · obtain ⟨coordinate, hselected, hsupport⟩ :=
      Finset.not_disjoint_iff.mp hdisjoint
    have hsingle :
        (if coordinate ∈ selected then 1 else 0) ≤
          ∑ candidate ∈ support,
            if candidate ∈ selected then 1 else 0 := by
      exact Finset.single_le_sum
        (s := support)
        (f := fun candidate =>
          (if candidate ∈ selected then 1 else 0 : ℕ))
        (fun candidate _ => Nat.zero_le _) hsupport
    simpa [touchIndicator, hdisjoint, hselected] using hsingle

def touchingSelections (q K : ℕ) : Finset (Finset (Fin q)) :=
  (Finset.univ : Finset (Fin q)).powersetCard K

theorem touchingSelections_nonempty {q K : ℕ} (hK : K ≤ q) :
    (touchingSelections q K).Nonempty := by
  rw [touchingSelections, Finset.powersetCard_nonempty]
  simpa using hK

theorem touchingSelections_card (q K : ℕ) :
    (touchingSelections q K).card = Nat.choose q K := by
  simp [touchingSelections]

theorem touchingSelections_containing_card
    {q K : ℕ} (hKPositive : 0 < K) (coordinate : Fin q) :
    ((touchingSelections q K).filter
      fun selected => coordinate ∈ selected).card =
        Nat.choose (q - 1) (K - 1) := by
  have hfilters :
      (touchingSelections q K).filter
          (fun selected => coordinate ∈ selected) =
        (touchingSelections q K).filter
          (fun selected => ({coordinate} : Finset (Fin q)) ⊆ selected) := by
    ext selected
    simp
  rw [hfilters]
  unfold touchingSelections
  rw [Finset.card_filter_powersetCard_subset
    ({coordinate} : Finset (Fin q)) Finset.univ K]
  · simp
  · simp
  · exact hKPositive

theorem sum_selection_membership
    {q K : ℕ} (hKPositive : 0 < K) (coordinate : Fin q) :
    (∑ selected ∈ touchingSelections q K,
      if coordinate ∈ selected then 1 else 0) =
        Nat.choose (q - 1) (K - 1) := by
  rw [Finset.sum_boole]
  exact touchingSelections_containing_card hKPositive coordinate

theorem totalTouchingCost_le
    {Gate : Type} [Fintype Gate]
    {q K : ℕ} (hKPositive : 0 < K)
    (support : Gate → Finset (Fin q)) :
    ∑ selected ∈ touchingSelections q K,
        touchingCost support selected ≤
      supportIncidenceMass support * Nat.choose (q - 1) (K - 1) := by
  unfold touchingCost supportIncidenceMass
  calc
    (∑ selected ∈ touchingSelections q K,
        ∑ gate, touchIndicator selected (support gate)) ≤
        ∑ selected ∈ touchingSelections q K,
          ∑ gate, ∑ coordinate ∈ support gate,
            if coordinate ∈ selected then 1 else 0 := by
      apply Finset.sum_le_sum
      intro selected _
      exact Finset.sum_le_sum fun gate _ =>
        touchIndicator_le_membershipSum selected (support gate)
    _ = ∑ gate, ∑ coordinate ∈ support gate,
          ∑ selected ∈ touchingSelections q K,
            if coordinate ∈ selected then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro gate _
      rw [Finset.sum_comm]
    _ = ∑ gate, ∑ _coordinate ∈ support gate,
          Nat.choose (q - 1) (K - 1) := by
      apply Finset.sum_congr rfl
      intro gate _
      apply Finset.sum_congr rfl
      intro coordinate _
      exact sum_selection_membership hKPositive coordinate
    _ = (∑ gate, (support gate).card) *
        Nat.choose (q - 1) (K - 1) := by
      calc
        (∑ gate, ∑ _coordinate ∈ support gate,
            Nat.choose (q - 1) (K - 1)) =
            ∑ gate, (support gate).card *
              Nat.choose (q - 1) (K - 1) := by
          apply Finset.sum_congr rfl
          intro gate _
          simp
        _ = (∑ gate, (support gate).card) *
            Nat.choose (q - 1) (K - 1) := by
          rw [Finset.sum_mul]

/-! ## Closed conditional-expectation ledger -/

/-- Exact number of `k`-completions touching one support after `selected`
has already been fixed and `undecided` remains available. -/
def conditionalGateTouchCount {Coordinate : Type}
    [DecidableEq Coordinate]
    (selected undecided support : Finset Coordinate) (k : ℕ) : ℕ :=
  if Disjoint selected support then
    Nat.choose undecided.card k -
      Nat.choose (undecided \ support).card k
  else
    Nat.choose undecided.card k

/-- The closed, polynomial-bit score used by conditional expectation. -/
def conditionalTouchNumerator
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate) (k : ℕ) : ℕ :=
  ∑ gate,
    conditionalGateTouchCount selected undecided (support gate) k

/-- Semantic completion sum, used only to prove the closed score correct. -/
def completionTouchingSum
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate) (k : ℕ) : ℕ :=
  ∑ completion ∈ undecided.powersetCard k,
    touchingCost support (selected ∪ completion)

theorem touchIndicator_union_of_disjoint
    {Coordinate : Type} [DecidableEq Coordinate]
    (selected completion support : Finset Coordinate)
    (hselected : Disjoint selected support) :
    touchIndicator (selected ∪ completion) support =
      touchIndicator completion support := by
  unfold touchIndicator
  have hequivalence :
      Disjoint (selected ∪ completion) support ↔
        Disjoint completion support := by
    rw [Finset.disjoint_union_left]
    simp [hselected]
  simp only [hequivalence]

theorem disjointCompletion_filter
    {Coordinate : Type} [DecidableEq Coordinate]
    (undecided support : Finset Coordinate) (k : ℕ) :
    (undecided.powersetCard k).filter
        (fun completion => Disjoint completion support) =
      (undecided \ support).powersetCard k := by
  ext completion
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsubset, hcard⟩, hdisjoint⟩
    refine ⟨?_, hcard⟩
    intro coordinate hcoordinate
    exact Finset.mem_sdiff.mpr
      ⟨hsubset hcoordinate,
        fun hsupport =>
          Finset.disjoint_left.mp hdisjoint hcoordinate hsupport⟩
  · rintro ⟨hsubset, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · exact fun coordinate hcoordinate =>
        (Finset.mem_sdiff.mp (hsubset hcoordinate)).1
    · exact Finset.disjoint_left.mpr fun coordinate hcompletion hsupport =>
        (Finset.mem_sdiff.mp (hsubset hcompletion)).2 hsupport

theorem sum_touchIndicator
    {Coordinate : Type} [DecidableEq Coordinate]
    (undecided support : Finset Coordinate) (k : ℕ) :
    (∑ completion ∈ undecided.powersetCard k,
        touchIndicator completion support) =
      Nat.choose undecided.card k -
        Nat.choose (undecided \ support).card k := by
  let candidates := undecided.powersetCard k
  have hsum :
      (∑ completion ∈ candidates,
          touchIndicator completion support) =
        ((candidates.filter
          fun completion => ¬Disjoint completion support).card) := by
    calc
      (∑ completion ∈ candidates,
          touchIndicator completion support) =
          ∑ completion ∈ candidates,
            if ¬Disjoint completion support then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro completion _
        unfold touchIndicator
        by_cases hdisjoint : Disjoint completion support <;>
          simp [hdisjoint]
      _ = ((candidates.filter
          fun completion => ¬Disjoint completion support).card) := by
        rw [← Finset.sum_filter]
        simp
  rw [hsum]
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := candidates)
      (fun completion => Disjoint completion support)
  have hdisjointCard :
      (candidates.filter
        fun completion => Disjoint completion support).card =
          Nat.choose (undecided \ support).card k := by
    rw [show
      candidates.filter
          (fun completion => Disjoint completion support) =
        (undecided \ support).powersetCard k by
      exact disjointCompletion_filter undecided support k]
    simp
  have hcandidatesCard :
      candidates.card = Nat.choose undecided.card k := by
    simp [candidates]
  rw [hdisjointCard, hcandidatesCard] at hpartition
  omega

theorem sum_touchIndicator_union
    {Coordinate : Type} [DecidableEq Coordinate]
    (selected undecided support : Finset Coordinate) (k : ℕ) :
    (∑ completion ∈ undecided.powersetCard k,
        touchIndicator (selected ∪ completion) support) =
      conditionalGateTouchCount selected undecided support k := by
  by_cases hselected : Disjoint selected support
  · simp only [conditionalGateTouchCount, if_pos hselected]
    simp_rw [touchIndicator_union_of_disjoint
      selected _ support hselected]
    exact sum_touchIndicator undecided support k
  · simp only [conditionalGateTouchCount, if_neg hselected]
    have htouched : ∀ completion,
        touchIndicator (selected ∪ completion) support = 1 := by
      intro completion
      unfold touchIndicator
      have hnondisjoint :
          ¬Disjoint (selected ∪ completion) support := by
        intro hunion
        exact hselected
          (hunion.mono_left Finset.subset_union_left)
      simp [hnondisjoint]
    simp_rw [htouched]
    simp

/-- The closed binomial score is exactly the sum of touching costs over all
legal completions.  The selector can therefore compute the former while the
proof reasons about the latter. -/
theorem completionTouchingSum_eq_conditionalTouchNumerator
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate) (k : ℕ) :
    completionTouchingSum support selected undecided k =
      conditionalTouchNumerator support selected undecided k := by
  unfold completionTouchingSum conditionalTouchNumerator touchingCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro gate _
  exact sum_touchIndicator_union selected undecided (support gate) k

theorem completionTouchingSum_branch
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate)
    (coordinate : Coordinate) (hcoordinate : coordinate ∈ undecided)
    (k : ℕ) (hk : 0 < k) :
    completionTouchingSum support selected undecided k =
      completionTouchingSum support (insert coordinate selected)
          (undecided.erase coordinate) (k - 1) +
        completionTouchingSum support selected
          (undecided.erase coordinate) k := by
  let rest := undecided.erase coordinate
  have hcoordinateRest : coordinate ∉ rest := by
    simp [rest]
  have hundecided : insert coordinate rest = undecided := by
    simpa [rest] using Finset.insert_erase hcoordinate
  have hkSucc : (k - 1).succ = k := by omega
  have hdecomposition :
      undecided.powersetCard k =
        rest.powersetCard k ∪
          (rest.powersetCard (k - 1)).image
            (insert coordinate) := by
    rw [← hundecided, ← hkSucc]
    exact Finset.powersetCard_succ_insert
      hcoordinateRest (k - 1)
  have hdisjoint :
      Disjoint (rest.powersetCard k)
        ((rest.powersetCard (k - 1)).image
          (insert coordinate)) := by
    rw [Finset.disjoint_left]
    intro completion hwithout hwith
    rcases Finset.mem_image.mp hwith with
      ⟨base, hbase, hbaseEq⟩
    have hsubset :=
      (Finset.mem_powersetCard.mp hwithout).1
    have hmissing : coordinate ∉ completion :=
      fun hmem => hcoordinateRest (hsubset hmem)
    apply hmissing
    rw [← hbaseEq]
    simp
  have hinjective :
      Set.InjOn (insert coordinate)
        (↑(rest.powersetCard (k - 1)) :
          Set (Finset Coordinate)) := by
    intro left hleft right hright hequal
    have hleftSubset :=
      (Finset.mem_powersetCard.mp hleft).1
    have hrightSubset :=
      (Finset.mem_powersetCard.mp hright).1
    have hleftMissing : coordinate ∉ left :=
      fun hmem => hcoordinateRest (hleftSubset hmem)
    have hrightMissing : coordinate ∉ right :=
      fun hmem => hcoordinateRest (hrightSubset hmem)
    have herased :=
      congrArg (fun value : Finset Coordinate =>
        value.erase coordinate) hequal
    simpa [hleftMissing, hrightMissing] using herased
  unfold completionTouchingSum
  rw [hdecomposition, Finset.sum_union hdisjoint]
  rw [Finset.sum_image hinjective]
  have hincluded :
      (∑ completion ∈ rest.powersetCard (k - 1),
          touchingCost support
            (selected ∪ insert coordinate completion)) =
        ∑ completion ∈ rest.powersetCard (k - 1),
          touchingCost support
            (insert coordinate selected ∪ completion) := by
    apply Finset.sum_congr rfl
    intro completion _
    congr 1
    ext value
    simp
  rw [hincluded]
  exact add_comm _ _

theorem conditionalTouchNumerator_branch
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate)
    (coordinate : Coordinate) (hcoordinate : coordinate ∈ undecided)
    (k : ℕ) (hk : 0 < k) :
    conditionalTouchNumerator support selected undecided k =
      conditionalTouchNumerator support (insert coordinate selected)
          (undecided.erase coordinate) (k - 1) +
        conditionalTouchNumerator support selected
          (undecided.erase coordinate) k := by
  rw [← completionTouchingSum_eq_conditionalTouchNumerator,
    ← completionTouchingSum_eq_conditionalTouchNumerator,
    ← completionTouchingSum_eq_conditionalTouchNumerator]
  exact completionTouchingSum_branch support selected undecided
    coordinate hcoordinate k hk

/-! ## Deterministic conditional-expectation selector -/

/-- Greedy TouchingSelect over one fixed coordinate order.  At each step the
two exact conditional numerators are compared after cross-multiplying by
their binomial fiber sizes; no rational arithmetic or candidate enumeration
is used. -/
def touchingSelectAux
    {Gate : Type} [Fintype Gate]
    {q : ℕ} (support : Gate → Finset (Fin q)) :
    Finset (Fin q) → ℕ → List (Fin q) → Finset (Fin q)
  | selected, _k, [] => selected
  | selected, k, coordinate :: rest =>
      if _hk : k = 0 then
        selected
      else
        let restSet := rest.toFinset
        let included :=
          conditionalTouchNumerator support
            (insert coordinate selected) restSet (k - 1)
        let excluded :=
          conditionalTouchNumerator support selected restSet k
        if included * Nat.choose rest.length k ≤
            excluded * Nat.choose rest.length (k - 1) then
          touchingSelectAux support
            (insert coordinate selected) (k - 1) rest
        else
          touchingSelectAux support selected k rest

def touchingSelect
    {Gate : Type} [Fintype Gate]
    {q : ℕ} (support : Gate → Finset (Fin q)) (K : ℕ) :
    Finset (Fin q) :=
  touchingSelectAux support ∅ K (List.finRange q)

theorem conditionalTouchNumerator_zero
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate) :
    conditionalTouchNumerator support selected undecided 0 =
      touchingCost support selected := by
  rw [← completionTouchingSum_eq_conditionalTouchNumerator]
  simp [completionTouchingSum]

private theorem weightedLeftBranch_le
    {parent left right parentCount leftCount rightCount cost : ℕ}
    (hparent : parent = left + right)
    (hcount : parentCount = leftCount + rightCount)
    (hchoice : left * rightCount ≤ right * leftCount)
    (hleftPositive : 0 < leftCount)
    (hcost : leftCount * cost ≤ left) :
    parentCount * cost ≤ parent := by
  have hscaled :
      leftCount * (parentCount * cost) ≤
        leftCount * parent := by
    calc
      leftCount * (parentCount * cost) =
          parentCount * (leftCount * cost) := by ring
      _ ≤ parentCount * left :=
        Nat.mul_le_mul_left parentCount hcost
      _ = leftCount * left + rightCount * left := by
        rw [hcount]
        ring
      _ ≤ leftCount * left + leftCount * right := by
        exact Nat.add_le_add_left
          (by simpa [mul_comm] using hchoice)
          (leftCount * left)
      _ = leftCount * parent := by
        rw [hparent]
        ring
  exact Nat.le_of_mul_le_mul_left hscaled hleftPositive

private theorem weightedRightBranch_le
    {parent left right parentCount leftCount rightCount cost : ℕ}
    (hparent : parent = left + right)
    (hcount : parentCount = leftCount + rightCount)
    (hchoice : right * leftCount ≤ left * rightCount)
    (hrightPositive : 0 < rightCount)
    (hcost : rightCount * cost ≤ right) :
    parentCount * cost ≤ parent := by
  have hscaled :
      rightCount * (parentCount * cost) ≤
        rightCount * parent := by
    calc
      rightCount * (parentCount * cost) =
          parentCount * (rightCount * cost) := by ring
      _ ≤ parentCount * right :=
        Nat.mul_le_mul_left parentCount hcost
      _ = leftCount * right + rightCount * right := by
        rw [hcount]
        ring
      _ ≤ rightCount * left + rightCount * right := by
        exact Nat.add_le_add_right
          (by simpa [mul_comm] using hchoice)
          (rightCount * right)
      _ = rightCount * parent := by
        rw [hparent]
        ring
  exact Nat.le_of_mul_le_mul_left hscaled hrightPositive

theorem touchingSelectAux_spec
    {Gate : Type} [Fintype Gate]
    {q : ℕ} (support : Gate → Finset (Fin q))
    (selected : Finset (Fin q)) (k : ℕ)
    (coordinates : List (Fin q))
    (hnodup : coordinates.Nodup)
    (hdisjoint : Disjoint selected coordinates.toFinset)
    (hk : k ≤ coordinates.length) :
    let result := touchingSelectAux support selected k coordinates
    selected ⊆ result ∧
      result ⊆ selected ∪ coordinates.toFinset ∧
      result.card = selected.card + k ∧
      Nat.choose coordinates.length k *
          touchingCost support result ≤
        conditionalTouchNumerator support
          selected coordinates.toFinset k := by
  induction coordinates generalizing selected k with
  | nil =>
      have hkZero : k = 0 := by simpa using hk
      subst k
      simp only [touchingSelectAux]
      refine ⟨fun _ h => h, ?_, by simp, ?_⟩
      · intro value hvalue
        simpa using hvalue
      · simpa using
          (conditionalTouchNumerator_zero support selected ∅).ge
  | cons coordinate rest ih =>
      have hcoordinateRest : coordinate ∉ rest := by
        exact (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hcoordinateNotSelected : coordinate ∉ selected := by
        intro hselected
        exact Finset.disjoint_left.mp hdisjoint hselected (by simp)
      by_cases hkZero : k = 0
      · subst k
        simp only [touchingSelectAux, ↓reduceDIte]
        refine ⟨fun _ h => h, Finset.subset_union_left, by simp, ?_⟩
        simpa using
          (conditionalTouchNumerator_zero support selected
            (coordinate :: rest).toFinset).ge
      · have hkPositive : 0 < k := Nat.pos_of_ne_zero hkZero
        let restSet := rest.toFinset
        let included :=
          conditionalTouchNumerator support
            (insert coordinate selected) restSet (k - 1)
        let excluded :=
          conditionalTouchNumerator support selected restSet k
        have hparent :
            conditionalTouchNumerator support selected
                (coordinate :: rest).toFinset k =
              included + excluded := by
          have hbranch :=
            conditionalTouchNumerator_branch support selected
              (coordinate :: rest).toFinset coordinate
              (by simp) k hkPositive
          simpa [included, excluded, restSet,
            hcoordinateRest] using hbranch
        have hcount :
            Nat.choose (coordinate :: rest).length k =
              Nat.choose rest.length (k - 1) +
                Nat.choose rest.length k := by
          simpa using Nat.choose_succ_left rest.length k hkPositive
        by_cases hchoice :
            included * Nat.choose rest.length k ≤
              excluded * Nat.choose rest.length (k - 1)
        · have hkSucc : k ≤ rest.length + 1 := by
            simpa only [List.length_cons] using hk
          have hkRest : k - 1 ≤ rest.length := by omega
          have hincludeDisjoint :
              Disjoint (insert coordinate selected) restSet := by
            apply Finset.disjoint_left.mpr
            intro value hvalue hrest
            rw [Finset.mem_insert] at hvalue
            rcases hvalue with rfl | hselected
            · exact hcoordinateRest
                (List.mem_toFinset.mp hrest)
            · apply Finset.disjoint_left.mp hdisjoint hselected
              simp only [List.mem_toFinset, List.mem_cons]
              exact Or.inr (List.mem_toFinset.mp hrest)
          rcases ih (insert coordinate selected) (k - 1)
              hrestNodup hincludeDisjoint hkRest with
            ⟨hselectedSubset, hresultSubset, hcard, hcost⟩
          let result :=
            touchingSelectAux support
              (insert coordinate selected) (k - 1) rest
          have hresultSubset' :
              result ⊆ selected ∪ (coordinate :: rest).toFinset := by
            apply hresultSubset.trans
            intro value hvalue
            simp only [Finset.mem_union, Finset.mem_insert,
              List.toFinset_cons] at hvalue ⊢
            aesop
          have hcard' : result.card = selected.card + k := by
            dsimp only [result] at hcard ⊢
            rw [Finset.card_insert_of_notMem hcoordinateNotSelected] at hcard
            omega
          have hweighted :
              Nat.choose (coordinate :: rest).length k *
                    touchingCost support result ≤
                conditionalTouchNumerator support selected
                  (coordinate :: rest).toFinset k := by
            apply weightedLeftBranch_le hparent hcount hchoice
              (Nat.choose_pos hkRest)
            simpa only [result] using hcost
          have hresultEq :
              touchingSelectAux support selected k
                  (coordinate :: rest) =
                result := by
            simp [touchingSelectAux, hkZero, included, excluded,
              restSet, hchoice, result]
          rw [hresultEq]
          exact
            ⟨(Finset.subset_insert coordinate selected).trans
                hselectedSubset,
              hresultSubset', hcard', hweighted⟩
        · have hkRest : k ≤ rest.length := by
            by_contra hkRest
            have htooLarge : rest.length < k := by omega
            have hzero :
                Nat.choose rest.length k = 0 :=
              Nat.choose_eq_zero_of_lt htooLarge
            apply hchoice
            rw [hzero, mul_zero]
            exact Nat.zero_le _
          have hexcludeDisjoint :
              Disjoint selected restSet := by
            apply Finset.disjoint_left.mpr
            intro value hselected hrest
            apply Finset.disjoint_left.mp hdisjoint hselected
            simp only [List.mem_toFinset, List.mem_cons]
            exact Or.inr (List.mem_toFinset.mp hrest)
          rcases ih selected k hrestNodup hexcludeDisjoint hkRest with
            ⟨hselectedSubset, hresultSubset, hcard, hcost⟩
          let result := touchingSelectAux support selected k rest
          have hresultSubset' :
              result ⊆ selected ∪ (coordinate :: rest).toFinset := by
            apply hresultSubset.trans
            intro value hvalue
            simp only [Finset.mem_union, List.toFinset_cons,
              Finset.mem_insert] at hvalue ⊢
            aesop
          have hreverse :
              excluded * Nat.choose rest.length (k - 1) ≤
                included * Nat.choose rest.length k :=
            Nat.le_of_lt (Nat.lt_of_not_ge hchoice)
          have hweighted :
              Nat.choose (coordinate :: rest).length k *
                    touchingCost support result ≤
                conditionalTouchNumerator support selected
                  (coordinate :: rest).toFinset k := by
            apply weightedRightBranch_le hparent hcount hreverse
              (Nat.choose_pos hkRest)
            simpa only [result] using hcost
          have hresultEq :
              touchingSelectAux support selected k
                  (coordinate :: rest) =
                result := by
            simp [touchingSelectAux, hkZero, included, excluded,
              restSet, hchoice, result]
          rw [hresultEq]
          exact
            ⟨hselectedSubset, hresultSubset', hcard, hweighted⟩

theorem touchingSelect_spec
    {Gate : Type} [Fintype Gate]
    {q K : ℕ} (hK : K ≤ q)
    (support : Gate → Finset (Fin q)) :
    (touchingSelect support K).card = K ∧
      Nat.choose q K *
          touchingCost support (touchingSelect support K) ≤
        conditionalTouchNumerator support
          ∅ (Finset.univ : Finset (Fin q)) K := by
  have hspec :=
    touchingSelectAux_spec support ∅ K (List.finRange q)
      (List.nodup_finRange q) (by simp) (by simpa using hK)
  rcases hspec with ⟨_, _, hcard, hcost⟩
  constructor
  · simpa [touchingSelect] using hcard
  · simpa [touchingSelect] using hcost

theorem initialConditionalTouchNumerator
    {Gate : Type} [Fintype Gate]
    {q K : ℕ} (support : Gate → Finset (Fin q)) :
    conditionalTouchNumerator support
        ∅ (Finset.univ : Finset (Fin q)) K =
      ∑ selected ∈ touchingSelections q K,
        touchingCost support selected := by
  rw [← completionTouchingSum_eq_conditionalTouchNumerator]
  simp [completionTouchingSum, touchingSelections]

theorem choose_incidence_identity
    {q K : ℕ} (hq : 0 < q) (hK : 0 < K) :
    q * Nat.choose (q - 1) (K - 1) =
      K * Nat.choose q K := by
  have hqOne : 1 ≤ q := hq
  have hKOne : 1 ≤ K := hK
  have hidentity := Nat.add_one_mul_choose_eq (q - 1) (K - 1)
  rw [Nat.sub_add_cancel hqOne, Nat.sub_add_cancel hKOne] at hidentity
  simpa [Nat.mul_comm] using hidentity

theorem touchingSelect_cost
    {Gate : Type} [Fintype Gate]
    {q K : ℕ} (hq : 0 < q) (hKPositive : 0 < K) (hK : K ≤ q)
    (support : Gate → Finset (Fin q)) :
    q * touchingCost support (touchingSelect support K) ≤
      K * supportIncidenceMass support := by
  have hspec := (touchingSelect_spec hK support).2
  rw [initialConditionalTouchNumerator] at hspec
  have htotal := totalTouchingCost_le hKPositive support
  have hscaled :
      Nat.choose q K *
          (q * touchingCost support (touchingSelect support K)) ≤
        Nat.choose q K *
          (K * supportIncidenceMass support) := by
    calc
      Nat.choose q K *
            (q * touchingCost support (touchingSelect support K)) =
          q * (Nat.choose q K *
            touchingCost support (touchingSelect support K)) := by
        ring
      _ ≤ q *
          (∑ selected ∈ touchingSelections q K,
            touchingCost support selected) :=
        Nat.mul_le_mul_left q hspec
      _ ≤ q *
          (supportIncidenceMass support *
            Nat.choose (q - 1) (K - 1)) :=
        Nat.mul_le_mul_left q htotal
      _ = Nat.choose q K *
          (K * supportIncidenceMass support) := by
        calc
          q * (supportIncidenceMass support *
              Nat.choose (q - 1) (K - 1)) =
              supportIncidenceMass support *
                (q * Nat.choose (q - 1) (K - 1)) := by
            ring
          _ = supportIncidenceMass support *
              (K * Nat.choose q K) := by
            rw [choose_incidence_identity hq hKPositive]
          _ = Nat.choose q K *
              (K * supportIncidenceMass support) := by
            ring
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.choose_pos hK)

/-- Exact TouchingSelect existence theorem.  The proof averages only over
structural `K`-subsets and is independent of every later input column. -/
theorem exists_touchingSelection
    {Gate : Type} [Fintype Gate]
    {q K : ℕ} (hq : 0 < q) (hKPositive : 0 < K) (hK : K ≤ q)
    (support : Gate → Finset (Fin q)) :
    ∃ selected : Finset (Fin q),
      selected.card = K ∧
        q * touchingCost support selected ≤
          K * supportIncidenceMass support := by
  let candidates := touchingSelections q K
  have hcandidates : candidates.Nonempty :=
    touchingSelections_nonempty hK
  have htotal := totalTouchingCost_le hKPositive support
  have hscaled :
      (∑ selected ∈ candidates,
        q * touchingCost support selected) ≤
        ∑ _selected ∈ candidates,
          K * supportIncidenceMass support := by
    calc
      (∑ selected ∈ candidates,
          q * touchingCost support selected) =
          q * ∑ selected ∈ candidates,
            touchingCost support selected := by
        rw [Finset.mul_sum]
      _ ≤ q *
          (supportIncidenceMass support *
            Nat.choose (q - 1) (K - 1)) := by
        exact Nat.mul_le_mul_left q htotal
      _ = Nat.choose q K *
          (K * supportIncidenceMass support) := by
        calc
          q * (supportIncidenceMass support *
              Nat.choose (q - 1) (K - 1)) =
              supportIncidenceMass support *
                (q * Nat.choose (q - 1) (K - 1)) := by ring
          _ = supportIncidenceMass support *
              (K * Nat.choose q K) := by
            rw [choose_incidence_identity hq hKPositive]
          _ = Nat.choose q K *
              (K * supportIncidenceMass support) := by ring
      _ = ∑ _selected ∈ candidates,
          K * supportIncidenceMass support := by
        simp [candidates, touchingSelections_card]
  obtain ⟨selected, hselected, hcost⟩ :=
    Finset.exists_le_of_sum_le hcandidates hscaled
  refine ⟨selected, ?_, hcost⟩
  exact (Finset.mem_powersetCard.mp hselected).2

end NearCubicWires.SupplierTouching
