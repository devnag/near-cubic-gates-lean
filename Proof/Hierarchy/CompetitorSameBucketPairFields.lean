import Proof.Hierarchy.CompetitorSameBucketPairCompare

/-! Two actual copied present rank records are decoded and compared in one
reusable scalar workspace. The M-bit template is shared physically. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketPairFields
open LocalBitMultitape SignedSortKey RecoveryRootRound RecoveryExecution
open CompetitorSameBucketRankFields (source)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 13 → Fin 31 := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
theorem left_injective : Function.Injective leftSlots := by decide
def leftPick : Fin 31 → Option (Fin 13) := ![some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]
theorem left_pick (i : Fin 31) : RecoveryFocus.pick leftSlots i=leftPick i := by
  classical
  fin_cases i
  · exact RecoveryFocus.pick_slot leftSlots left_injective 0
  · exact RecoveryFocus.pick_slot leftSlots left_injective 1
  · exact RecoveryFocus.pick_slot leftSlots left_injective 2
  · exact RecoveryFocus.pick_slot leftSlots left_injective 3
  · exact RecoveryFocus.pick_slot leftSlots left_injective 4
  · exact RecoveryFocus.pick_slot leftSlots left_injective 5
  · exact RecoveryFocus.pick_slot leftSlots left_injective 6
  · exact RecoveryFocus.pick_slot leftSlots left_injective 7
  · exact RecoveryFocus.pick_slot leftSlots left_injective 8
  · exact RecoveryFocus.pick_slot leftSlots left_injective 9
  · exact RecoveryFocus.pick_slot leftSlots left_injective 10
  · exact RecoveryFocus.pick_slot leftSlots left_injective 11
  · exact RecoveryFocus.pick_slot leftSlots left_injective 12
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide

def rightSlots : Fin 13 → Fin 31 := ![13,14,15,16,17,18,19,7,20,21,22,23,24]
theorem right_injective : Function.Injective rightSlots := by decide
def rightPick : Fin 31 → Option (Fin 13) := ![none,none,none,none,none,none,none,some 7,none,none,none,none,none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 8,some 9,some 10,some 11,some 12,none,none,none,none,none,none]
theorem right_pick (i : Fin 31) : RecoveryFocus.pick rightSlots i=rightPick i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot rightSlots right_injective 7
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot rightSlots right_injective 0
  · exact RecoveryFocus.pick_slot rightSlots right_injective 1
  · exact RecoveryFocus.pick_slot rightSlots right_injective 2
  · exact RecoveryFocus.pick_slot rightSlots right_injective 3
  · exact RecoveryFocus.pick_slot rightSlots right_injective 4
  · exact RecoveryFocus.pick_slot rightSlots right_injective 5
  · exact RecoveryFocus.pick_slot rightSlots right_injective 6
  · exact RecoveryFocus.pick_slot rightSlots right_injective 8
  · exact RecoveryFocus.pick_slot rightSlots right_injective 9
  · exact RecoveryFocus.pick_slot rightSlots right_injective 10
  · exact RecoveryFocus.pick_slot rightSlots right_injective 11
  · exact RecoveryFocus.pick_slot rightSlots right_injective 12
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide

def compareSlots : Fin 10 → Fin 31 := ![25,10,22,4,17,26,27,28,30,29]
theorem compare_injective : Function.Injective compareSlots := by decide
def comparePick : Fin 31 → Option (Fin 10) := ![none,none,none,none,some 3,none,none,none,none,none,some 1,none,none,none,none,none,none,some 4,none,none,none,none,some 2,none,none,some 0,some 5,some 6,some 7,some 9,some 8]
theorem compare_pick (i : Fin 31) : RecoveryFocus.pick compareSlots i=comparePick i := by
  classical
  fin_cases i
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 3
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 1
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 4
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 2
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · unfold RecoveryFocus.pick
    apply dif_neg
    decide
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 0
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 5
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 6
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 7
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 9
  · exact RecoveryFocus.pick_slot compareSlots compare_injective 8

noncomputable def left := RecoveryFocus.machine leftSlots CompetitorSameBucketRankFields.machine
noncomputable def right := RecoveryFocus.machine rightSlots CompetitorSameBucketRankFields.machine
noncomputable def compare := RecoveryFocus.machine compareSlots CompetitorSameBucketPairCompare.machine
noncomputable def tail := Composition.machine right compare
noncomputable def machine := Composition.machine left tail

def data (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb phase : ℕ) : Fin 31 → List Bool := fun i =>
  if i=0 then ZeroPadding.pad cap (source s k sa a ra)
  else if i=1 ∧ 1≤phase then ZeroPadding.pad cap (source s k sa a ra)
  else if i=4 ∧ 1≤phase then ZeroPadding.pad cap (frame (binary (k+s+1) ra))
  else if i=7 then ZeroPadding.pad cap (frame (binary k 0))
  else if i=10 ∧ 1≤phase then ZeroPadding.pad cap (frame (binary k a))
  else if i=13 then ZeroPadding.pad cap (source s k sb b rb)
  else if i=14 ∧ 2≤phase then ZeroPadding.pad cap (source s k sb b rb)
  else if i=17 ∧ 2≤phase then ZeroPadding.pad cap (frame (binary (k+s+1) rb))
  else if i=22 ∧ 2≤phase then ZeroPadding.pad cap (frame (binary k b))
  else if i=25 then ZeroPadding.pad cap (frame (binary k u))
  else if i=26 then ZeroPadding.pad cap [if 3≤phase then decide (u≤a) else false]
  else if i=27 then ZeroPadding.pad cap [if 3≤phase then decide (u≤b) else false]
  else if i=28 then ZeroPadding.pad cap [if 3≤phase then decide (rb≤ra) else false]
  else if i=29 then ZeroPadding.pad cap [if 3≤phase then CompetitorSameBucketPairCompare.fires u a b ra rb else false]
  else List.replicate cap false

theorem left_input (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    ∀ i, data cap s k u sa sb a b ra rb 0 (leftSlots i)=(CompetitorSameBucketRankFields.paddedInput cap s k sa a ra) i := by
  intro i
  fin_cases i <;> simp [leftSlots,data,CompetitorSameBucketRankFields.paddedInput]

theorem left_install (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    install leftSlots (data cap s k u sa sb a b ra rb 0) (CompetitorSameBucketRankFields.paddedOutput cap s k sa a ra)=
      data cap s k u sa sb a b ra rb 1 := by
  funext i
  simp only [install,left_pick]
  fin_cases i <;> simp [leftPick,data,CompetitorSameBucketRankFields.paddedOutput]

theorem right_input (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    ∀ i, data cap s k u sa sb a b ra rb 1 (rightSlots i)=(CompetitorSameBucketRankFields.paddedInput cap s k sb b rb) i := by
  intro i
  fin_cases i <;> simp [rightSlots,data,CompetitorSameBucketRankFields.paddedInput]

theorem right_install (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    install rightSlots (data cap s k u sa sb a b ra rb 1) (CompetitorSameBucketRankFields.paddedOutput cap s k sb b rb)=
      data cap s k u sa sb a b ra rb 2 := by
  funext i
  simp only [install,right_pick]
  fin_cases i <;> simp [rightPick,data,CompetitorSameBucketRankFields.paddedOutput]

theorem compare_input (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    ∀ i, data cap s k u sa sb a b ra rb 2 (compareSlots i)=(CompetitorSameBucketPairCompare.data cap k (k+s+1) u a b ra rb 0) i := by
  intro i
  fin_cases i <;> simp [compareSlots,data,CompetitorSameBucketPairCompare.data]

theorem compare_install (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    install compareSlots (data cap s k u sa sb a b ra rb 2) (CompetitorSameBucketPairCompare.data cap k (k+s+1) u a b ra rb 4)=
      data cap s k u sa sb a b ra rb 3 := by
  funext i
  simp only [install,compare_pick]
  fin_cases i <;> simp [comparePick,data,CompetitorSameBucketPairCompare.data]

def budget (s k : ℕ) := 100*(k+s+1)+24*k+112

theorem present_ready (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ)
    (hc : 30*(k+s+2)≤cap) (hu : u<2^k) (ha : a<2^k) (hb : b<2^k)
    (hra : ra<2^(k+s+1)) (hrb : rb<2^(k+s+1)) :
    ClockJoin.ReadyRun machine (budget s k) (data cap s k u sa sb a b ra rb 0)
      (data cap s k u sa sb a b ra rb 3) := by
  have hleft := CompetitorRationalProducts.bounded_focus leftSlots left_injective _ _ _
    (CompetitorSameBucketRankFields.padded_ready cap s k sa a ra hc)
    (data cap s k u sa sb a b ra rb 0) (left_input cap s k u sa sb a b ra rb)
  rw [left_install] at hleft
  have hright := CompetitorRationalProducts.bounded_focus rightSlots right_injective _ _ _
    (CompetitorSameBucketRankFields.padded_ready cap s k sb b rb hc)
    (data cap s k u sa sb a b ra rb 1) (right_input cap s k u sa sb a b ra rb)
  rw [right_install] at hright
  have hcompare := CompetitorRationalProducts.bounded_focus compareSlots compare_injective _ _ _
    (CompetitorSameBucketPairCompare.pair_ready cap k (k+s+1) u a b ra rb hu ha hb hra hrb (by omega) (by omega))
    (data cap s k u sa sb a b ra rb 2) (compare_input cap s k u sa sb a b ra rb)
  rw [compare_install] at hcompare
  have htail := ClockJoin.join right compare _ _ _ _ _ hright hcompare
  have hall := ClockJoin.join left tail _ _ _ _ _ hleft htail
  have he : CompetitorSameBucketRankFields.budget s k+1+
      (CompetitorSameBucketRankFields.budget s k+1+(8*k+4*(k+s+1)+16))=budget s k := by
    unfold budget CompetitorSameBucketRankFields.budget
    omega
  rw [he] at hall
  exact hall

theorem output_flag (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) :
    readTapeBit (data cap s k u sa sb a b ra rb 3 29) 0=true ↔ a<u ∧ u≤b ∧ ra<rb := by
  change readTapeBit (ZeroPadding.pad cap [CompetitorSameBucketPairCompare.fires u a b ra rb]) 0=true ↔ _
  rw [ZeroPadding.read_pad]
  exact CompetitorSameBucketPairCompare.fires_iff u a b ra rb

end NearCubicWires.RepairOrdinary.CompetitorSameBucketPairFields
