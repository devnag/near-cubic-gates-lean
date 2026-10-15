import Proof.MachineModel.ClosureCompactSize
import Proof.MachineModel.ClosureRadixNative

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactMetadata
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch ExtIncidence
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

def p (b D Q : Nat) := b*(D*Q)+Q
def outer (B n N b : Nat) := CompactSize.value B n N b*256
def F (B n N b D Q : Nat) := RowCommonAllocation.value (N*Q) (p b D Q) (outer B n N b)
noncomputable def capOutput (n p F w N Q : Nat) :=
  Classical.choose (NativeCapacity.capacity_run n p F w N Q)
theorem cap_spec (n p F w N Q : Nat) :
    ClockJoin.ReadyRun NativeCapacity.machine (NativeCapacity.budget n p F w N Q)
      (NativeCapacity.input n p F w N Q) (capOutput n p F w N Q) ∧
    (∀ i, capOutput n p F w N Q (NativeCapacity.old i) = NativeCapacityParameters.output n p F w N Q i) ∧
    capOutput n p F w N Q 50 = List.replicate (CloseoutRowsPreparationBounds.capacity n p F w N Q) true :=
  Classical.choose_spec (NativeCapacity.capacity_run n p F w N Q)
noncomputable def shortOutput (n w Q : Nat) := Classical.choose (NativeShort.short_run n w Q)
theorem short_spec (n w Q : Nat) :
    ClockJoin.ReadyRun NativeShort.machine (NativeShort.budget n w Q)
      (NativeShort.input n w Q) (shortOutput n w Q) ∧
    (∀ i : Fin 13, shortOutput n w Q (i.castAdd 4) = NativeShort.data5 n w Q (i.castAdd 4)) ∧
    shortOutput n w Q 14 = frame (SignedSortKey.binary w 0) := Classical.choose_spec (NativeShort.short_run n w Q)

abbrev Store := Fin 162 → List Bool

def input (B n N b D Q w : Nat) (cache : List Bool) : Store := fun i =>
  if i=0 then List.replicate (B) true else if i=1 then UnaryTemplate.tape (n) else if i=2 then UnaryTemplate.tape (N) else if i=3 then List.replicate (b) true else if i=4 then UnaryTemplate.tape (D) else if i=5 then UnaryTemplate.tape (Q) else if i=6 then List.replicate (w) true else if i=7 then cache else []

theorem input_fresh (B n N b D Q w : Nat) (cache : List Bool) (i : Fin 162) (hi : 8 ≤ i.val) : input B n N b D Q w cache i=[] := by
  simp only [input]
  split_ifs <;> first | rfl | (exfalso; omega)

def slots1 : Fin 18 → Fin 162 := ![0,1,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,3]
theorem slots1_inj : Function.Injective slots1 := by decide
noncomputable def phase1 := RecoveryFocus.machine slots1 CompactSize.machine
noncomputable def data1 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots1 (input B n N b D Q w cache) (CompactSize.output B n N b)
theorem data1_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 18) : data1 B n N b D Q w cache (slots1 j) = (CompactSize.output B n N b) j :=
  install_slot slots1 slots1_inj (input B n N b D Q w cache) _ j
theorem data1_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots1 j ≠ k) : data1 B n N b D Q w cache k = input B n N b D Q w cache k :=
  install_other slots1 (input B n N b D Q w cache) _ k hk
theorem data1_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 22 ≤ k.val) : data1 B n N b D Q w cache k=[] := by
  rw [data1_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots1 j).val < 22 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact input_fresh B n N b D Q w cache k (by omega)
theorem ready1 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase1 (CompactSize.budget B n N b) (input B n N b D Q w cache) (data1 B n N b D Q w cache) := by
  apply (CompactSize.ready B n N b).focus slots1 slots1_inj (input B n N b D Q w cache)
  intro j
  fin_cases j
  · change input B n N b D Q w cache 0 = (CompactSize.input B n N b) 0
    rfl

  · change input B n N b D Q w cache 1 = (CompactSize.input B n N b) 1
    rfl

  · change input B n N b D Q w cache 2 = (CompactSize.input B n N b) 2
    rfl

  · change input B n N b D Q w cache 8 = (CompactSize.input B n N b) 3
    exact input_fresh B n N b D Q w cache 8 (by decide)

  · change input B n N b D Q w cache 9 = (CompactSize.input B n N b) 4
    exact input_fresh B n N b D Q w cache 9 (by decide)

  · change input B n N b D Q w cache 10 = (CompactSize.input B n N b) 5
    exact input_fresh B n N b D Q w cache 10 (by decide)

  · change input B n N b D Q w cache 11 = (CompactSize.input B n N b) 6
    exact input_fresh B n N b D Q w cache 11 (by decide)

  · change input B n N b D Q w cache 12 = (CompactSize.input B n N b) 7
    exact input_fresh B n N b D Q w cache 12 (by decide)

  · change input B n N b D Q w cache 13 = (CompactSize.input B n N b) 8
    exact input_fresh B n N b D Q w cache 13 (by decide)

  · change input B n N b D Q w cache 14 = (CompactSize.input B n N b) 9
    exact input_fresh B n N b D Q w cache 14 (by decide)

  · change input B n N b D Q w cache 15 = (CompactSize.input B n N b) 10
    exact input_fresh B n N b D Q w cache 15 (by decide)

  · change input B n N b D Q w cache 16 = (CompactSize.input B n N b) 11
    exact input_fresh B n N b D Q w cache 16 (by decide)

  · change input B n N b D Q w cache 17 = (CompactSize.input B n N b) 12
    exact input_fresh B n N b D Q w cache 17 (by decide)

  · change input B n N b D Q w cache 18 = (CompactSize.input B n N b) 13
    exact input_fresh B n N b D Q w cache 18 (by decide)

  · change input B n N b D Q w cache 19 = (CompactSize.input B n N b) 14
    exact input_fresh B n N b D Q w cache 19 (by decide)

  · change input B n N b D Q w cache 20 = (CompactSize.input B n N b) 15
    exact input_fresh B n N b D Q w cache 20 (by decide)

  · change input B n N b D Q w cache 21 = (CompactSize.input B n N b) 16
    exact input_fresh B n N b D Q w cache 21 (by decide)

  · change input B n N b D Q w cache 3 = (CompactSize.input B n N b) 17
    rfl

noncomputable def joined1 := phase1
def budget1 (B n N b _D _Q _w : Nat) := CompactSize.budget B n N b
theorem joined1_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined1 (budget1 B n N b D Q w) (input B n N b D Q w cache) (data1 B n N b D Q w cache) := ready1 B n N b D Q w cache
def slots2 : Fin 17 → Fin 162 := ![3,20,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem slots2_inj : Function.Injective slots2 := by decide
noncomputable def phase2 := RecoveryFocus.machine slots2 RowCommonResources.machine
noncomputable def data2 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots2 (data1 B n N b D Q w cache) (RowCommonResources.output b (CompactSize.value B n N b))
theorem data2_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 17) : data2 B n N b D Q w cache (slots2 j) = (RowCommonResources.output b (CompactSize.value B n N b)) j :=
  install_slot slots2 slots2_inj (data1 B n N b D Q w cache) _ j
theorem data2_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots2 j ≠ k) : data2 B n N b D Q w cache k = data1 B n N b D Q w cache k :=
  install_other slots2 (data1 B n N b D Q w cache) _ k hk
theorem data2_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 37 ≤ k.val) : data2 B n N b D Q w cache k=[] := by
  rw [data2_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots2 j).val < 37 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data1_fresh B n N b D Q w cache k (by omega)
theorem ready2 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase2 (RowCommonResources.budget b (CompactSize.value B n N b)) (data1 B n N b D Q w cache) (data2 B n N b D Q w cache) := by
  apply (RowCommonResources.resources_ready b (CompactSize.value B n N b)).focus slots2 slots2_inj (data1 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data1 B n N b D Q w cache 3 = (RowCommonResources.input b (CompactSize.value B n N b)) 0
    rw [show data1 B n N b D Q w cache 3 = (CompactSize.output B n N b) 17 from data1_slot B n N b D Q w cache 17]
    exact CompactSize.radix_word B n N b

  · change data1 B n N b D Q w cache 20 = (RowCommonResources.input b (CompactSize.value B n N b)) 1
    rw [show data1 B n N b D Q w cache 20 = (CompactSize.output B n N b) 15 from data1_slot B n N b D Q w cache 15]
    exact CompactSize.scale_word B n N b

  · change data1 B n N b D Q w cache 22 = (RowCommonResources.input b (CompactSize.value B n N b)) 2
    exact data1_fresh B n N b D Q w cache 22 (by decide)

  · change data1 B n N b D Q w cache 23 = (RowCommonResources.input b (CompactSize.value B n N b)) 3
    exact data1_fresh B n N b D Q w cache 23 (by decide)

  · change data1 B n N b D Q w cache 24 = (RowCommonResources.input b (CompactSize.value B n N b)) 4
    exact data1_fresh B n N b D Q w cache 24 (by decide)

  · change data1 B n N b D Q w cache 25 = (RowCommonResources.input b (CompactSize.value B n N b)) 5
    exact data1_fresh B n N b D Q w cache 25 (by decide)

  · change data1 B n N b D Q w cache 26 = (RowCommonResources.input b (CompactSize.value B n N b)) 6
    exact data1_fresh B n N b D Q w cache 26 (by decide)

  · change data1 B n N b D Q w cache 27 = (RowCommonResources.input b (CompactSize.value B n N b)) 7
    exact data1_fresh B n N b D Q w cache 27 (by decide)

  · change data1 B n N b D Q w cache 28 = (RowCommonResources.input b (CompactSize.value B n N b)) 8
    exact data1_fresh B n N b D Q w cache 28 (by decide)

  · change data1 B n N b D Q w cache 29 = (RowCommonResources.input b (CompactSize.value B n N b)) 9
    exact data1_fresh B n N b D Q w cache 29 (by decide)

  · change data1 B n N b D Q w cache 30 = (RowCommonResources.input b (CompactSize.value B n N b)) 10
    exact data1_fresh B n N b D Q w cache 30 (by decide)

  · change data1 B n N b D Q w cache 31 = (RowCommonResources.input b (CompactSize.value B n N b)) 11
    exact data1_fresh B n N b D Q w cache 31 (by decide)

  · change data1 B n N b D Q w cache 32 = (RowCommonResources.input b (CompactSize.value B n N b)) 12
    exact data1_fresh B n N b D Q w cache 32 (by decide)

  · change data1 B n N b D Q w cache 33 = (RowCommonResources.input b (CompactSize.value B n N b)) 13
    exact data1_fresh B n N b D Q w cache 33 (by decide)

  · change data1 B n N b D Q w cache 34 = (RowCommonResources.input b (CompactSize.value B n N b)) 14
    exact data1_fresh B n N b D Q w cache 34 (by decide)

  · change data1 B n N b D Q w cache 35 = (RowCommonResources.input b (CompactSize.value B n N b)) 15
    exact data1_fresh B n N b D Q w cache 35 (by decide)

  · change data1 B n N b D Q w cache 36 = (RowCommonResources.input b (CompactSize.value B n N b)) 16
    exact data1_fresh B n N b D Q w cache 36 (by decide)

noncomputable def joined2 := Composition.machine joined1 phase2
def budget2 (B n N b D Q w : Nat) := budget1 B n N b D Q w+1+(RowCommonResources.budget b (CompactSize.value B n N b))
theorem joined2_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined2 (budget2 B n N b D Q w) (input B n N b D Q w cache) (data2 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined1_ready B n N b D Q w cache) (ready2 B n N b D Q w cache)
def slots3 : Fin 17 → Fin 162 := ![3,4,5,37,38,39,40,41,42,43,44,45,46,47,48,49,50]
theorem slots3_inj : Function.Injective slots3 := by decide
noncomputable def phase3 := RecoveryFocus.machine slots3 RowCommonTupleDimensions.machine
noncomputable def data3 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots3 (data2 B n N b D Q w cache) (RowCommonTupleDimensions.output b D Q)
theorem data3_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 17) : data3 B n N b D Q w cache (slots3 j) = (RowCommonTupleDimensions.output b D Q) j :=
  install_slot slots3 slots3_inj (data2 B n N b D Q w cache) _ j
theorem data3_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots3 j ≠ k) : data3 B n N b D Q w cache k = data2 B n N b D Q w cache k :=
  install_other slots3 (data2 B n N b D Q w cache) _ k hk
theorem data3_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 51 ≤ k.val) : data3 B n N b D Q w cache k=[] := by
  rw [data3_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots3 j).val < 51 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data2_fresh B n N b D Q w cache k (by omega)
theorem ready3 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase3 (RowCommonTupleDimensions.budget b D Q) (data2 B n N b D Q w cache) (data3 B n N b D Q w cache) := by
  apply (RowCommonTupleDimensions.dimensions_ready b D Q).focus slots3 slots3_inj (data2 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data2 B n N b D Q w cache 3 = (RowCommonTupleDimensions.input b D Q) 0
    rw [show data2 B n N b D Q w cache 3 = (RowCommonResources.output b (CompactSize.value B n N b)) 0 from data2_slot B n N b D Q w cache 0]
    rfl

  · change data2 B n N b D Q w cache 4 = (RowCommonTupleDimensions.input b D Q) 1
    rw [data2_other B n N b D Q w cache 4 (by decide)]
    rw [data1_other B n N b D Q w cache 4 (by decide)]
    rfl

  · change data2 B n N b D Q w cache 5 = (RowCommonTupleDimensions.input b D Q) 2
    rw [data2_other B n N b D Q w cache 5 (by decide)]
    rw [data1_other B n N b D Q w cache 5 (by decide)]
    rfl

  · change data2 B n N b D Q w cache 37 = (RowCommonTupleDimensions.input b D Q) 3
    exact data2_fresh B n N b D Q w cache 37 (by decide)

  · change data2 B n N b D Q w cache 38 = (RowCommonTupleDimensions.input b D Q) 4
    exact data2_fresh B n N b D Q w cache 38 (by decide)

  · change data2 B n N b D Q w cache 39 = (RowCommonTupleDimensions.input b D Q) 5
    exact data2_fresh B n N b D Q w cache 39 (by decide)

  · change data2 B n N b D Q w cache 40 = (RowCommonTupleDimensions.input b D Q) 6
    exact data2_fresh B n N b D Q w cache 40 (by decide)

  · change data2 B n N b D Q w cache 41 = (RowCommonTupleDimensions.input b D Q) 7
    exact data2_fresh B n N b D Q w cache 41 (by decide)

  · change data2 B n N b D Q w cache 42 = (RowCommonTupleDimensions.input b D Q) 8
    exact data2_fresh B n N b D Q w cache 42 (by decide)

  · change data2 B n N b D Q w cache 43 = (RowCommonTupleDimensions.input b D Q) 9
    exact data2_fresh B n N b D Q w cache 43 (by decide)

  · change data2 B n N b D Q w cache 44 = (RowCommonTupleDimensions.input b D Q) 10
    exact data2_fresh B n N b D Q w cache 44 (by decide)

  · change data2 B n N b D Q w cache 45 = (RowCommonTupleDimensions.input b D Q) 11
    exact data2_fresh B n N b D Q w cache 45 (by decide)

  · change data2 B n N b D Q w cache 46 = (RowCommonTupleDimensions.input b D Q) 12
    exact data2_fresh B n N b D Q w cache 46 (by decide)

  · change data2 B n N b D Q w cache 47 = (RowCommonTupleDimensions.input b D Q) 13
    exact data2_fresh B n N b D Q w cache 47 (by decide)

  · change data2 B n N b D Q w cache 48 = (RowCommonTupleDimensions.input b D Q) 14
    exact data2_fresh B n N b D Q w cache 48 (by decide)

  · change data2 B n N b D Q w cache 49 = (RowCommonTupleDimensions.input b D Q) 15
    exact data2_fresh B n N b D Q w cache 49 (by decide)

  · change data2 B n N b D Q w cache 50 = (RowCommonTupleDimensions.input b D Q) 16
    exact data2_fresh B n N b D Q w cache 50 (by decide)

noncomputable def joined3 := Composition.machine joined2 phase3
def budget3 (B n N b D Q w : Nat) := budget2 B n N b D Q w+1+(RowCommonTupleDimensions.budget b D Q)
theorem joined3_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined3 (budget3 B n N b D Q w) (input B n N b D Q w cache) (data3 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined2_ready B n N b D Q w cache) (ready3 B n N b D Q w cache)
def slots4 : Fin 17 → Fin 162 := ![43,5,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65]
theorem slots4_inj : Function.Injective slots4 := by decide
noncomputable def phase4 := RecoveryFocus.machine slots4 NativeFieldWidth.machine
noncomputable def data4 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots4 (data3 B n N b D Q w cache) (NativeFieldWidth.output (b*(D*Q)) Q)
theorem data4_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 17) : data4 B n N b D Q w cache (slots4 j) = (NativeFieldWidth.output (b*(D*Q)) Q) j :=
  install_slot slots4 slots4_inj (data3 B n N b D Q w cache) _ j
theorem data4_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots4 j ≠ k) : data4 B n N b D Q w cache k = data3 B n N b D Q w cache k :=
  install_other slots4 (data3 B n N b D Q w cache) _ k hk
theorem data4_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 66 ≤ k.val) : data4 B n N b D Q w cache k=[] := by
  rw [data4_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots4 j).val < 66 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data3_fresh B n N b D Q w cache k (by omega)
theorem ready4 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase4 (NativeFieldWidth.budget (b*(D*Q)) Q) (data3 B n N b D Q w cache) (data4 B n N b D Q w cache) := by
  apply (NativeFieldWidth.ready (b*(D*Q)) Q).focus slots4 slots4_inj (data3 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data3 B n N b D Q w cache 43 = (NativeFieldWidth.input (b*(D*Q)) Q) 0
    rw [show data3 B n N b D Q w cache 43 = (RowCommonTupleDimensions.output b D Q) 9 from data3_slot B n N b D Q w cache 9]
    rfl

  · change data3 B n N b D Q w cache 5 = (NativeFieldWidth.input (b*(D*Q)) Q) 1
    rw [show data3 B n N b D Q w cache 5 = (RowCommonTupleDimensions.output b D Q) 2 from data3_slot B n N b D Q w cache 2]
    rfl

  · change data3 B n N b D Q w cache 51 = (NativeFieldWidth.input (b*(D*Q)) Q) 2
    exact data3_fresh B n N b D Q w cache 51 (by decide)

  · change data3 B n N b D Q w cache 52 = (NativeFieldWidth.input (b*(D*Q)) Q) 3
    exact data3_fresh B n N b D Q w cache 52 (by decide)

  · change data3 B n N b D Q w cache 53 = (NativeFieldWidth.input (b*(D*Q)) Q) 4
    exact data3_fresh B n N b D Q w cache 53 (by decide)

  · change data3 B n N b D Q w cache 54 = (NativeFieldWidth.input (b*(D*Q)) Q) 5
    exact data3_fresh B n N b D Q w cache 54 (by decide)

  · change data3 B n N b D Q w cache 55 = (NativeFieldWidth.input (b*(D*Q)) Q) 6
    exact data3_fresh B n N b D Q w cache 55 (by decide)

  · change data3 B n N b D Q w cache 56 = (NativeFieldWidth.input (b*(D*Q)) Q) 7
    exact data3_fresh B n N b D Q w cache 56 (by decide)

  · change data3 B n N b D Q w cache 57 = (NativeFieldWidth.input (b*(D*Q)) Q) 8
    exact data3_fresh B n N b D Q w cache 57 (by decide)

  · change data3 B n N b D Q w cache 58 = (NativeFieldWidth.input (b*(D*Q)) Q) 9
    exact data3_fresh B n N b D Q w cache 58 (by decide)

  · change data3 B n N b D Q w cache 59 = (NativeFieldWidth.input (b*(D*Q)) Q) 10
    exact data3_fresh B n N b D Q w cache 59 (by decide)

  · change data3 B n N b D Q w cache 60 = (NativeFieldWidth.input (b*(D*Q)) Q) 11
    exact data3_fresh B n N b D Q w cache 60 (by decide)

  · change data3 B n N b D Q w cache 61 = (NativeFieldWidth.input (b*(D*Q)) Q) 12
    exact data3_fresh B n N b D Q w cache 61 (by decide)

  · change data3 B n N b D Q w cache 62 = (NativeFieldWidth.input (b*(D*Q)) Q) 13
    exact data3_fresh B n N b D Q w cache 62 (by decide)

  · change data3 B n N b D Q w cache 63 = (NativeFieldWidth.input (b*(D*Q)) Q) 14
    exact data3_fresh B n N b D Q w cache 63 (by decide)

  · change data3 B n N b D Q w cache 64 = (NativeFieldWidth.input (b*(D*Q)) Q) 15
    exact data3_fresh B n N b D Q w cache 64 (by decide)

  · change data3 B n N b D Q w cache 65 = (NativeFieldWidth.input (b*(D*Q)) Q) 16
    exact data3_fresh B n N b D Q w cache 65 (by decide)

noncomputable def joined4 := Composition.machine joined3 phase4
def budget4 (B n N b D Q w : Nat) := budget3 B n N b D Q w+1+(NativeFieldWidth.budget (b*(D*Q)) Q)
theorem joined4_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined4 (budget4 B n N b D Q w) (input B n N b D Q w cache) (data4 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined3_ready B n N b D Q w cache) (ready4 B n N b D Q w cache)
def slots5 : Fin 17 → Fin 162 := ![3,2,5,66,67,68,69,70,71,72,73,74,75,76,77,78,79]
theorem slots5_inj : Function.Injective slots5 := by decide
noncomputable def phase5 := RecoveryFocus.machine slots5 RowCommonTupleDimensions.machine
noncomputable def data5 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots5 (data4 B n N b D Q w cache) (RowCommonTupleDimensions.output b N Q)
theorem data5_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 17) : data5 B n N b D Q w cache (slots5 j) = (RowCommonTupleDimensions.output b N Q) j :=
  install_slot slots5 slots5_inj (data4 B n N b D Q w cache) _ j
theorem data5_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots5 j ≠ k) : data5 B n N b D Q w cache k = data4 B n N b D Q w cache k :=
  install_other slots5 (data4 B n N b D Q w cache) _ k hk
theorem data5_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 80 ≤ k.val) : data5 B n N b D Q w cache k=[] := by
  rw [data5_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots5 j).val < 80 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data4_fresh B n N b D Q w cache k (by omega)
theorem ready5 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase5 (RowCommonTupleDimensions.budget b N Q) (data4 B n N b D Q w cache) (data5 B n N b D Q w cache) := by
  apply (RowCommonTupleDimensions.dimensions_ready b N Q).focus slots5 slots5_inj (data4 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data4 B n N b D Q w cache 3 = (RowCommonTupleDimensions.input b N Q) 0
    rw [data4_other B n N b D Q w cache 3 (by decide)]
    rw [show data3 B n N b D Q w cache 3 = (RowCommonTupleDimensions.output b D Q) 0 from data3_slot B n N b D Q w cache 0]
    rfl

  · change data4 B n N b D Q w cache 2 = (RowCommonTupleDimensions.input b N Q) 1
    rw [data4_other B n N b D Q w cache 2 (by decide)]
    rw [data3_other B n N b D Q w cache 2 (by decide)]
    rw [data2_other B n N b D Q w cache 2 (by decide)]
    rw [show data1 B n N b D Q w cache 2 = (CompactSize.output B n N b) 2 from data1_slot B n N b D Q w cache 2]
    exact CompactSize.retained B n N b 2

  · change data4 B n N b D Q w cache 5 = (RowCommonTupleDimensions.input b N Q) 2
    rw [show data4 B n N b D Q w cache 5 = (NativeFieldWidth.output (b*(D*Q)) Q) 1 from data4_slot B n N b D Q w cache 1]
    rfl

  · change data4 B n N b D Q w cache 66 = (RowCommonTupleDimensions.input b N Q) 3
    exact data4_fresh B n N b D Q w cache 66 (by decide)

  · change data4 B n N b D Q w cache 67 = (RowCommonTupleDimensions.input b N Q) 4
    exact data4_fresh B n N b D Q w cache 67 (by decide)

  · change data4 B n N b D Q w cache 68 = (RowCommonTupleDimensions.input b N Q) 5
    exact data4_fresh B n N b D Q w cache 68 (by decide)

  · change data4 B n N b D Q w cache 69 = (RowCommonTupleDimensions.input b N Q) 6
    exact data4_fresh B n N b D Q w cache 69 (by decide)

  · change data4 B n N b D Q w cache 70 = (RowCommonTupleDimensions.input b N Q) 7
    exact data4_fresh B n N b D Q w cache 70 (by decide)

  · change data4 B n N b D Q w cache 71 = (RowCommonTupleDimensions.input b N Q) 8
    exact data4_fresh B n N b D Q w cache 71 (by decide)

  · change data4 B n N b D Q w cache 72 = (RowCommonTupleDimensions.input b N Q) 9
    exact data4_fresh B n N b D Q w cache 72 (by decide)

  · change data4 B n N b D Q w cache 73 = (RowCommonTupleDimensions.input b N Q) 10
    exact data4_fresh B n N b D Q w cache 73 (by decide)

  · change data4 B n N b D Q w cache 74 = (RowCommonTupleDimensions.input b N Q) 11
    exact data4_fresh B n N b D Q w cache 74 (by decide)

  · change data4 B n N b D Q w cache 75 = (RowCommonTupleDimensions.input b N Q) 12
    exact data4_fresh B n N b D Q w cache 75 (by decide)

  · change data4 B n N b D Q w cache 76 = (RowCommonTupleDimensions.input b N Q) 13
    exact data4_fresh B n N b D Q w cache 76 (by decide)

  · change data4 B n N b D Q w cache 77 = (RowCommonTupleDimensions.input b N Q) 14
    exact data4_fresh B n N b D Q w cache 77 (by decide)

  · change data4 B n N b D Q w cache 78 = (RowCommonTupleDimensions.input b N Q) 15
    exact data4_fresh B n N b D Q w cache 78 (by decide)

  · change data4 B n N b D Q w cache 79 = (RowCommonTupleDimensions.input b N Q) 16
    exact data4_fresh B n N b D Q w cache 79 (by decide)

noncomputable def joined5 := Composition.machine joined4 phase5
def budget5 (B n N b D Q w : Nat) := budget4 B n N b D Q w+1+(RowCommonTupleDimensions.budget b N Q)
theorem joined5_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined5 (budget5 B n N b D Q w) (input B n N b D Q w cache) (data5 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined4_ready B n N b D Q w cache) (ready5 B n N b D Q w cache)
def slots6 : Fin 25 → Fin 162 := ![68,53,32,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101]
theorem slots6_inj : Function.Injective slots6 := by decide
noncomputable def phase6 := RecoveryFocus.machine slots6 RowCommonAllocation.machine
noncomputable def data6 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots6 (data5 B n N b D Q w cache) (RowCommonAllocation.output (N*Q) (p b D Q) (outer B n N b))
theorem data6_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 25) : data6 B n N b D Q w cache (slots6 j) = (RowCommonAllocation.output (N*Q) (p b D Q) (outer B n N b)) j :=
  install_slot slots6 slots6_inj (data5 B n N b D Q w cache) _ j
theorem data6_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots6 j ≠ k) : data6 B n N b D Q w cache k = data5 B n N b D Q w cache k :=
  install_other slots6 (data5 B n N b D Q w cache) _ k hk
theorem data6_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 102 ≤ k.val) : data6 B n N b D Q w cache k=[] := by
  rw [data6_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots6 j).val < 102 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data5_fresh B n N b D Q w cache k (by omega)
theorem ready6 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase6 (RowCommonAllocation.budget (N*Q) (p b D Q) (outer B n N b)) (data5 B n N b D Q w cache) (data6 B n N b D Q w cache) := by
  apply (RowCommonAllocation.allocation_ready (N*Q) (p b D Q) (outer B n N b)).focus slots6 slots6_inj (data5 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data5 B n N b D Q w cache 68 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 0
    rw [show data5 B n N b D Q w cache 68 = (RowCommonTupleDimensions.output b N Q) 5 from data5_slot B n N b D Q w cache 5]
    rfl

  · change data5 B n N b D Q w cache 53 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 1
    rw [data5_other B n N b D Q w cache 53 (by decide)]
    rw [show data4 B n N b D Q w cache 53 = (NativeFieldWidth.output (b*(D*Q)) Q) 4 from data4_slot B n N b D Q w cache 4]
    rfl

  · change data5 B n N b D Q w cache 32 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 2
    rw [data5_other B n N b D Q w cache 32 (by decide)]
    rw [data4_other B n N b D Q w cache 32 (by decide)]
    rw [data3_other B n N b D Q w cache 32 (by decide)]
    rw [show data2 B n N b D Q w cache 32 = (RowCommonResources.output b (CompactSize.value B n N b)) 12 from data2_slot B n N b D Q w cache 12]
    rfl

  · change data5 B n N b D Q w cache 80 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 3
    exact data5_fresh B n N b D Q w cache 80 (by decide)

  · change data5 B n N b D Q w cache 81 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 4
    exact data5_fresh B n N b D Q w cache 81 (by decide)

  · change data5 B n N b D Q w cache 82 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 5
    exact data5_fresh B n N b D Q w cache 82 (by decide)

  · change data5 B n N b D Q w cache 83 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 6
    exact data5_fresh B n N b D Q w cache 83 (by decide)

  · change data5 B n N b D Q w cache 84 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 7
    exact data5_fresh B n N b D Q w cache 84 (by decide)

  · change data5 B n N b D Q w cache 85 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 8
    exact data5_fresh B n N b D Q w cache 85 (by decide)

  · change data5 B n N b D Q w cache 86 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 9
    exact data5_fresh B n N b D Q w cache 86 (by decide)

  · change data5 B n N b D Q w cache 87 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 10
    exact data5_fresh B n N b D Q w cache 87 (by decide)

  · change data5 B n N b D Q w cache 88 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 11
    exact data5_fresh B n N b D Q w cache 88 (by decide)

  · change data5 B n N b D Q w cache 89 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 12
    exact data5_fresh B n N b D Q w cache 89 (by decide)

  · change data5 B n N b D Q w cache 90 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 13
    exact data5_fresh B n N b D Q w cache 90 (by decide)

  · change data5 B n N b D Q w cache 91 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 14
    exact data5_fresh B n N b D Q w cache 91 (by decide)

  · change data5 B n N b D Q w cache 92 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 15
    exact data5_fresh B n N b D Q w cache 92 (by decide)

  · change data5 B n N b D Q w cache 93 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 16
    exact data5_fresh B n N b D Q w cache 93 (by decide)

  · change data5 B n N b D Q w cache 94 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 17
    exact data5_fresh B n N b D Q w cache 94 (by decide)

  · change data5 B n N b D Q w cache 95 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 18
    exact data5_fresh B n N b D Q w cache 95 (by decide)

  · change data5 B n N b D Q w cache 96 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 19
    exact data5_fresh B n N b D Q w cache 96 (by decide)

  · change data5 B n N b D Q w cache 97 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 20
    exact data5_fresh B n N b D Q w cache 97 (by decide)

  · change data5 B n N b D Q w cache 98 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 21
    exact data5_fresh B n N b D Q w cache 98 (by decide)

  · change data5 B n N b D Q w cache 99 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 22
    exact data5_fresh B n N b D Q w cache 99 (by decide)

  · change data5 B n N b D Q w cache 100 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 23
    exact data5_fresh B n N b D Q w cache 100 (by decide)

  · change data5 B n N b D Q w cache 101 = (RowCommonAllocation.input (N*Q) (p b D Q) (outer B n N b)) 24
    exact data5_fresh B n N b D Q w cache 101 (by decide)

noncomputable def joined6 := Composition.machine joined5 phase6
def budget6 (B n N b D Q w : Nat) := budget5 B n N b D Q w+1+(RowCommonAllocation.budget (N*Q) (p b D Q) (outer B n N b))
theorem joined6_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined6 (budget6 B n N b D Q w) (input B n N b D Q w cache) (data6 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined5_ready B n N b D Q w cache) (ready6 B n N b D Q w cache)
def slots7 : Fin 52 → Fin 162 := ![1,53,100,6,2,5,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147]
theorem slots7_inj : Function.Injective slots7 := by decide
noncomputable def phase7 := RecoveryFocus.machine slots7 NativeCapacity.machine
noncomputable def data7 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots7 (data6 B n N b D Q w cache) (capOutput n (p b D Q) (F B n N b D Q) w N Q)
theorem data7_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 52) : data7 B n N b D Q w cache (slots7 j) = (capOutput n (p b D Q) (F B n N b D Q) w N Q) j :=
  install_slot slots7 slots7_inj (data6 B n N b D Q w cache) _ j
theorem data7_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots7 j ≠ k) : data7 B n N b D Q w cache k = data6 B n N b D Q w cache k :=
  install_other slots7 (data6 B n N b D Q w cache) _ k hk
theorem data7_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 148 ≤ k.val) : data7 B n N b D Q w cache k=[] := by
  rw [data7_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots7 j).val < 148 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data6_fresh B n N b D Q w cache k (by omega)
theorem ready7 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase7 (NativeCapacity.budget n (p b D Q) (F B n N b D Q) w N Q) (data6 B n N b D Q w cache) (data7 B n N b D Q w cache) := by
  apply (cap_spec n (p b D Q) (F B n N b D Q) w N Q |>.1).focus slots7 slots7_inj (data6 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data6 B n N b D Q w cache 1 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 0
    rw [data6_other B n N b D Q w cache 1 (by decide)]
    rw [data5_other B n N b D Q w cache 1 (by decide)]
    rw [data4_other B n N b D Q w cache 1 (by decide)]
    rw [data3_other B n N b D Q w cache 1 (by decide)]
    rw [data2_other B n N b D Q w cache 1 (by decide)]
    rw [show data1 B n N b D Q w cache 1 = (CompactSize.output B n N b) 1 from data1_slot B n N b D Q w cache 1]
    exact CompactSize.retained B n N b 1

  · change data6 B n N b D Q w cache 53 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 1
    rw [show data6 B n N b D Q w cache 53 = (RowCommonAllocation.output (N*Q) (p b D Q) (outer B n N b)) 1 from data6_slot B n N b D Q w cache 1]
    rfl

  · change data6 B n N b D Q w cache 100 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 2
    rw [show data6 B n N b D Q w cache 100 = (RowCommonAllocation.output (N*Q) (p b D Q) (outer B n N b)) 23 from data6_slot B n N b D Q w cache 23]
    rfl

  · change data6 B n N b D Q w cache 6 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 3
    rw [data6_other B n N b D Q w cache 6 (by decide)]
    rw [data5_other B n N b D Q w cache 6 (by decide)]
    rw [data4_other B n N b D Q w cache 6 (by decide)]
    rw [data3_other B n N b D Q w cache 6 (by decide)]
    rw [data2_other B n N b D Q w cache 6 (by decide)]
    rw [data1_other B n N b D Q w cache 6 (by decide)]
    rfl

  · change data6 B n N b D Q w cache 2 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 4
    rw [data6_other B n N b D Q w cache 2 (by decide)]
    rw [show data5 B n N b D Q w cache 2 = (RowCommonTupleDimensions.output b N Q) 1 from data5_slot B n N b D Q w cache 1]
    rfl

  · change data6 B n N b D Q w cache 5 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 5
    rw [data6_other B n N b D Q w cache 5 (by decide)]
    rw [show data5 B n N b D Q w cache 5 = (RowCommonTupleDimensions.output b N Q) 2 from data5_slot B n N b D Q w cache 2]
    rfl

  · change data6 B n N b D Q w cache 102 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 6
    exact data6_fresh B n N b D Q w cache 102 (by decide)

  · change data6 B n N b D Q w cache 103 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 7
    exact data6_fresh B n N b D Q w cache 103 (by decide)

  · change data6 B n N b D Q w cache 104 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 8
    exact data6_fresh B n N b D Q w cache 104 (by decide)

  · change data6 B n N b D Q w cache 105 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 9
    exact data6_fresh B n N b D Q w cache 105 (by decide)

  · change data6 B n N b D Q w cache 106 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 10
    exact data6_fresh B n N b D Q w cache 106 (by decide)

  · change data6 B n N b D Q w cache 107 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 11
    exact data6_fresh B n N b D Q w cache 107 (by decide)

  · change data6 B n N b D Q w cache 108 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 12
    exact data6_fresh B n N b D Q w cache 108 (by decide)

  · change data6 B n N b D Q w cache 109 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 13
    exact data6_fresh B n N b D Q w cache 109 (by decide)

  · change data6 B n N b D Q w cache 110 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 14
    exact data6_fresh B n N b D Q w cache 110 (by decide)

  · change data6 B n N b D Q w cache 111 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 15
    exact data6_fresh B n N b D Q w cache 111 (by decide)

  · change data6 B n N b D Q w cache 112 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 16
    exact data6_fresh B n N b D Q w cache 112 (by decide)

  · change data6 B n N b D Q w cache 113 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 17
    exact data6_fresh B n N b D Q w cache 113 (by decide)

  · change data6 B n N b D Q w cache 114 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 18
    exact data6_fresh B n N b D Q w cache 114 (by decide)

  · change data6 B n N b D Q w cache 115 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 19
    exact data6_fresh B n N b D Q w cache 115 (by decide)

  · change data6 B n N b D Q w cache 116 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 20
    exact data6_fresh B n N b D Q w cache 116 (by decide)

  · change data6 B n N b D Q w cache 117 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 21
    exact data6_fresh B n N b D Q w cache 117 (by decide)

  · change data6 B n N b D Q w cache 118 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 22
    exact data6_fresh B n N b D Q w cache 118 (by decide)

  · change data6 B n N b D Q w cache 119 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 23
    exact data6_fresh B n N b D Q w cache 119 (by decide)

  · change data6 B n N b D Q w cache 120 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 24
    exact data6_fresh B n N b D Q w cache 120 (by decide)

  · change data6 B n N b D Q w cache 121 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 25
    exact data6_fresh B n N b D Q w cache 121 (by decide)

  · change data6 B n N b D Q w cache 122 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 26
    exact data6_fresh B n N b D Q w cache 122 (by decide)

  · change data6 B n N b D Q w cache 123 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 27
    exact data6_fresh B n N b D Q w cache 123 (by decide)

  · change data6 B n N b D Q w cache 124 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 28
    exact data6_fresh B n N b D Q w cache 124 (by decide)

  · change data6 B n N b D Q w cache 125 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 29
    exact data6_fresh B n N b D Q w cache 125 (by decide)

  · change data6 B n N b D Q w cache 126 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 30
    exact data6_fresh B n N b D Q w cache 126 (by decide)

  · change data6 B n N b D Q w cache 127 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 31
    exact data6_fresh B n N b D Q w cache 127 (by decide)

  · change data6 B n N b D Q w cache 128 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 32
    exact data6_fresh B n N b D Q w cache 128 (by decide)

  · change data6 B n N b D Q w cache 129 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 33
    exact data6_fresh B n N b D Q w cache 129 (by decide)

  · change data6 B n N b D Q w cache 130 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 34
    exact data6_fresh B n N b D Q w cache 130 (by decide)

  · change data6 B n N b D Q w cache 131 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 35
    exact data6_fresh B n N b D Q w cache 131 (by decide)

  · change data6 B n N b D Q w cache 132 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 36
    exact data6_fresh B n N b D Q w cache 132 (by decide)

  · change data6 B n N b D Q w cache 133 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 37
    exact data6_fresh B n N b D Q w cache 133 (by decide)

  · change data6 B n N b D Q w cache 134 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 38
    exact data6_fresh B n N b D Q w cache 134 (by decide)

  · change data6 B n N b D Q w cache 135 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 39
    exact data6_fresh B n N b D Q w cache 135 (by decide)

  · change data6 B n N b D Q w cache 136 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 40
    exact data6_fresh B n N b D Q w cache 136 (by decide)

  · change data6 B n N b D Q w cache 137 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 41
    exact data6_fresh B n N b D Q w cache 137 (by decide)

  · change data6 B n N b D Q w cache 138 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 42
    exact data6_fresh B n N b D Q w cache 138 (by decide)

  · change data6 B n N b D Q w cache 139 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 43
    exact data6_fresh B n N b D Q w cache 139 (by decide)

  · change data6 B n N b D Q w cache 140 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 44
    exact data6_fresh B n N b D Q w cache 140 (by decide)

  · change data6 B n N b D Q w cache 141 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 45
    exact data6_fresh B n N b D Q w cache 141 (by decide)

  · change data6 B n N b D Q w cache 142 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 46
    exact data6_fresh B n N b D Q w cache 142 (by decide)

  · change data6 B n N b D Q w cache 143 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 47
    exact data6_fresh B n N b D Q w cache 143 (by decide)

  · change data6 B n N b D Q w cache 144 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 48
    exact data6_fresh B n N b D Q w cache 144 (by decide)

  · change data6 B n N b D Q w cache 145 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 49
    exact data6_fresh B n N b D Q w cache 145 (by decide)

  · change data6 B n N b D Q w cache 146 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 50
    exact data6_fresh B n N b D Q w cache 146 (by decide)

  · change data6 B n N b D Q w cache 147 = (NativeCapacity.input n (p b D Q) (F B n N b D Q) w N Q) 51
    exact data6_fresh B n N b D Q w cache 147 (by decide)

noncomputable def joined7 := Composition.machine joined6 phase7
def budget7 (B n N b D Q w : Nat) := budget6 B n N b D Q w+1+(NativeCapacity.budget n (p b D Q) (F B n N b D Q) w N Q)
theorem joined7_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined7 (budget7 B n N b D Q w) (input B n N b D Q w cache) (data7 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined6_ready B n N b D Q w cache) (ready7 B n N b D Q w cache)
def slots8 : Fin 17 → Fin 162 := ![1,6,5,148,149,150,151,152,153,154,155,156,157,158,159,160,161]
theorem slots8_inj : Function.Injective slots8 := by decide
noncomputable def phase8 := RecoveryFocus.machine slots8 NativeShort.machine
noncomputable def data8 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots8 (data7 B n N b D Q w cache) (shortOutput n w Q)
theorem data8_slot (B n N b D Q w : Nat) (cache : List Bool) (j : Fin 17) : data8 B n N b D Q w cache (slots8 j) = (shortOutput n w Q) j :=
  install_slot slots8 slots8_inj (data7 B n N b D Q w cache) _ j
theorem data8_other (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : ∀ j, slots8 j ≠ k) : data8 B n N b D Q w cache k = data7 B n N b D Q w cache k :=
  install_other slots8 (data7 B n N b D Q w cache) _ k hk
theorem data8_fresh (B n N b D Q w : Nat) (cache : List Bool) (k : Fin 162) (hk : 162 ≤ k.val) : data8 B n N b D Q w cache k=[] := by
  rw [data8_other B n N b D Q w cache k (by
    have hs : ∀ j, (slots8 j).val < 162 := by decide
    intro j he; have := hs j; have := congrArg Fin.val he; omega)]
  exact data7_fresh B n N b D Q w cache k (by omega)
theorem ready8 (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun phase8 (NativeShort.budget n w Q) (data7 B n N b D Q w cache) (data8 B n N b D Q w cache) := by
  apply (short_spec n w Q |>.1).focus slots8 slots8_inj (data7 B n N b D Q w cache)
  intro j
  fin_cases j
  · change data7 B n N b D Q w cache 1 = (NativeShort.input n w Q) 0
    rw [show data7 B n N b D Q w cache 1 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 0 from data7_slot B n N b D Q w cache 0]
    exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.1 0

  · change data7 B n N b D Q w cache 6 = (NativeShort.input n w Q) 1
    rw [show data7 B n N b D Q w cache 6 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 3 from data7_slot B n N b D Q w cache 3]
    exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.1 3

  · change data7 B n N b D Q w cache 5 = (NativeShort.input n w Q) 2
    rw [show data7 B n N b D Q w cache 5 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 5 from data7_slot B n N b D Q w cache 5]
    exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.1 5

  · change data7 B n N b D Q w cache 148 = (NativeShort.input n w Q) 3
    exact data7_fresh B n N b D Q w cache 148 (by decide)

  · change data7 B n N b D Q w cache 149 = (NativeShort.input n w Q) 4
    exact data7_fresh B n N b D Q w cache 149 (by decide)

  · change data7 B n N b D Q w cache 150 = (NativeShort.input n w Q) 5
    exact data7_fresh B n N b D Q w cache 150 (by decide)

  · change data7 B n N b D Q w cache 151 = (NativeShort.input n w Q) 6
    exact data7_fresh B n N b D Q w cache 151 (by decide)

  · change data7 B n N b D Q w cache 152 = (NativeShort.input n w Q) 7
    exact data7_fresh B n N b D Q w cache 152 (by decide)

  · change data7 B n N b D Q w cache 153 = (NativeShort.input n w Q) 8
    exact data7_fresh B n N b D Q w cache 153 (by decide)

  · change data7 B n N b D Q w cache 154 = (NativeShort.input n w Q) 9
    exact data7_fresh B n N b D Q w cache 154 (by decide)

  · change data7 B n N b D Q w cache 155 = (NativeShort.input n w Q) 10
    exact data7_fresh B n N b D Q w cache 155 (by decide)

  · change data7 B n N b D Q w cache 156 = (NativeShort.input n w Q) 11
    exact data7_fresh B n N b D Q w cache 156 (by decide)

  · change data7 B n N b D Q w cache 157 = (NativeShort.input n w Q) 12
    exact data7_fresh B n N b D Q w cache 157 (by decide)

  · change data7 B n N b D Q w cache 158 = (NativeShort.input n w Q) 13
    exact data7_fresh B n N b D Q w cache 158 (by decide)

  · change data7 B n N b D Q w cache 159 = (NativeShort.input n w Q) 14
    exact data7_fresh B n N b D Q w cache 159 (by decide)

  · change data7 B n N b D Q w cache 160 = (NativeShort.input n w Q) 15
    exact data7_fresh B n N b D Q w cache 160 (by decide)

  · change data7 B n N b D Q w cache 161 = (NativeShort.input n w Q) 16
    exact data7_fresh B n N b D Q w cache 161 (by decide)

noncomputable def joined8 := Composition.machine joined7 phase8
def budget8 (B n N b D Q w : Nat) := budget7 B n N b D Q w+1+(NativeShort.budget n w Q)
theorem joined8_ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun joined8 (budget8 B n N b D Q w) (input B n N b D Q w cache) (data8 B n N b D Q w cache) :=
  ClockJoin.join _ _ _ _ _ _ _ (joined7_ready B n N b D Q w cache) (ready8 B n N b D Q w cache)
noncomputable def machine := joined8
noncomputable def output := data8
def budget := budget8
def fields : Fin 15 → Fin 162 := ![7,3,28,1,32,57,100,148,2,159,152,156,6,53,154]
theorem fields_injective : Function.Injective fields := by decide
def words (B n N b D Q w : Nat) (cache : List Bool) : Fin 15 → List Bool := ![cache,List.replicate (b) true,List.replicate ((b+1)*32) true,UnaryTemplate.tape (n),List.replicate (outer B n N b) true,CompareMachine.word (p b D Q+1),List.replicate (F B n N b D Q) true,CompareMachine.word (n+1),UnaryTemplate.tape (N),frame (SignedSortKey.binary w 0),CompareMachine.word w,CompareMachine.word 1,List.replicate (w) true,List.replicate (p b D Q) true,CompareMachine.word Q]
theorem ready (B n N b D Q w : Nat) (cache : List Bool) : ClockJoin.ReadyRun machine (budget B n N b D Q w) (input B n N b D Q w cache) (output B n N b D Q w cache) := joined8_ready B n N b D Q w cache
theorem output_fields (B n N b D Q w : Nat) (cache : List Bool) : ∀ j, output B n N b D Q w cache (fields j) = words B n N b D Q w cache j := by
  intro j
  fin_cases j
  · change data8 B n N b D Q w cache 7 = cache
    rw [data8_other B n N b D Q w cache 7 (by decide)]
    rw [data7_other B n N b D Q w cache 7 (by decide)]
    rw [data6_other B n N b D Q w cache 7 (by decide)]
    rw [data5_other B n N b D Q w cache 7 (by decide)]
    rw [data4_other B n N b D Q w cache 7 (by decide)]
    rw [data3_other B n N b D Q w cache 7 (by decide)]
    rw [data2_other B n N b D Q w cache 7 (by decide)]
    rw [data1_other B n N b D Q w cache 7 (by decide)]
    rfl

  · change data8 B n N b D Q w cache 3 = List.replicate (b) true
    rw [data8_other B n N b D Q w cache 3 (by decide)]
    rw [data7_other B n N b D Q w cache 3 (by decide)]
    rw [data6_other B n N b D Q w cache 3 (by decide)]
    rw [show data5 B n N b D Q w cache 3 = (RowCommonTupleDimensions.output b N Q) 0 from data5_slot B n N b D Q w cache 0]
    rfl

  · change data8 B n N b D Q w cache 28 = List.replicate ((b+1)*32) true
    rw [data8_other B n N b D Q w cache 28 (by decide)]
    rw [data7_other B n N b D Q w cache 28 (by decide)]
    rw [data6_other B n N b D Q w cache 28 (by decide)]
    rw [data5_other B n N b D Q w cache 28 (by decide)]
    rw [data4_other B n N b D Q w cache 28 (by decide)]
    rw [data3_other B n N b D Q w cache 28 (by decide)]
    rw [show data2 B n N b D Q w cache 28 = (RowCommonResources.output b (CompactSize.value B n N b)) 8 from data2_slot B n N b D Q w cache 8]
    rfl

  · change data8 B n N b D Q w cache 1 = UnaryTemplate.tape (n)
    rw [show data8 B n N b D Q w cache 1 = (shortOutput n w Q) 0 from data8_slot B n N b D Q w cache 0]
    exact (short_spec n w Q).2.1 0

  · change data8 B n N b D Q w cache 32 = List.replicate (outer B n N b) true
    rw [data8_other B n N b D Q w cache 32 (by decide)]
    rw [data7_other B n N b D Q w cache 32 (by decide)]
    rw [show data6 B n N b D Q w cache 32 = (RowCommonAllocation.output (N*Q) (p b D Q) (outer B n N b)) 2 from data6_slot B n N b D Q w cache 2]
    rfl

  · change data8 B n N b D Q w cache 57 = CompareMachine.word (p b D Q+1)
    rw [data8_other B n N b D Q w cache 57 (by decide)]
    rw [data7_other B n N b D Q w cache 57 (by decide)]
    rw [data6_other B n N b D Q w cache 57 (by decide)]
    rw [data5_other B n N b D Q w cache 57 (by decide)]
    rw [show data4 B n N b D Q w cache 57 = (NativeFieldWidth.output (b*(D*Q)) Q) 8 from data4_slot B n N b D Q w cache 8]
    rfl

  · change data8 B n N b D Q w cache 100 = List.replicate (F B n N b D Q) true
    rw [data8_other B n N b D Q w cache 100 (by decide)]
    rw [show data7 B n N b D Q w cache 100 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 2 from data7_slot B n N b D Q w cache 2]
    exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.1 2

  · change data8 B n N b D Q w cache 148 = CompareMachine.word (n+1)
    rw [show data8 B n N b D Q w cache 148 = (shortOutput n w Q) 3 from data8_slot B n N b D Q w cache 3]
    exact (short_spec n w Q).2.1 3

  · change data8 B n N b D Q w cache 2 = UnaryTemplate.tape (N)
    rw [data8_other B n N b D Q w cache 2 (by decide)]
    rw [show data7 B n N b D Q w cache 2 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 4 from data7_slot B n N b D Q w cache 4]
    exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.1 4

  · change data8 B n N b D Q w cache 159 = frame (SignedSortKey.binary w 0)
    rw [show data8 B n N b D Q w cache 159 = (shortOutput n w Q) 14 from data8_slot B n N b D Q w cache 14]
    exact (short_spec n w Q).2.2

  · change data8 B n N b D Q w cache 152 = CompareMachine.word w
    rw [show data8 B n N b D Q w cache 152 = (shortOutput n w Q) 7 from data8_slot B n N b D Q w cache 7]
    exact (short_spec n w Q).2.1 7

  · change data8 B n N b D Q w cache 156 = CompareMachine.word 1
    rw [show data8 B n N b D Q w cache 156 = (shortOutput n w Q) 11 from data8_slot B n N b D Q w cache 11]
    exact (short_spec n w Q).2.1 11

  · change data8 B n N b D Q w cache 6 = List.replicate (w) true
    rw [show data8 B n N b D Q w cache 6 = (shortOutput n w Q) 1 from data8_slot B n N b D Q w cache 1]
    exact (short_spec n w Q).2.1 1

  · change data8 B n N b D Q w cache 53 = List.replicate (p b D Q) true
    rw [data8_other B n N b D Q w cache 53 (by decide)]
    rw [show data7 B n N b D Q w cache 53 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 1 from data7_slot B n N b D Q w cache 1]
    exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.1 1

  · change data8 B n N b D Q w cache 154 = CompareMachine.word Q
    rw [show data8 B n N b D Q w cache 154 = (shortOutput n w Q) 9 from data8_slot B n N b D Q w cache 9]
    exact (short_spec n w Q).2.1 9

theorem output_capacity (B n N b D Q w : Nat) (cache : List Bool) : output B n N b D Q w cache 146 =
    List.replicate (CloseoutRowsPreparationBounds.capacity n (p b D Q) (F B n N b D Q) w N Q) true := by
  change data8 B n N b D Q w cache 146 = _
  rw [data8_other B n N b D Q w cache 146 (by decide)]
  rw [show data7 B n N b D Q w cache 146 = (capOutput n (p b D Q) (F B n N b D Q) w N Q) 50 from data7_slot B n N b D Q w cache 50]
  exact (cap_spec n (p b D Q) (F B n N b D Q) w N Q).2.2
end NearCubicWires.P1Closure.CompactMetadata
