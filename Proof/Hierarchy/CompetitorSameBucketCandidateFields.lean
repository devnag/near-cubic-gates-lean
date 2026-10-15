import Proof.Hierarchy.CompetitorSameBucketCandidateLoad

/-! Exact local classifier entry after the executed scalar clear/load.
Only retained scalar fields are preconditions; decoded IDs/ranks and the
new right record are outputs of the preceding physical machines. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape SignedSortKey MatrixScoreBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fixedSlots : Fin 7 → Fin 41 := ![0,7,25,31,32,33,34]
def fixed (cap k u p : ℕ) (coefficient : ℤ) (left out : List Bool) : Fin 7 → List Bool :=
  ![ZeroPadding.pad cap left,ZeroPadding.pad cap (frame (binary k 0)),ZeroPadding.pad cap (frame (binary k u)),
    ZeroPadding.pad cap (frame (signMagnitude p coefficient)),ZeroPadding.pad cap (frame (List.replicate (p+1) false)),
    ZeroPadding.pad cap (frame (binary k 0)),out]
def Fields (cap k u p : ℕ) (coefficient : ℤ) (left out : List Bool) (ambient : Fin 41 → List Bool) :=
  ∀ i,ambient (fixedSlots i)=fixed cap k u p coefficient left out i

def initialWork (cap k u : ℕ) (left right : List Bool) : Fin 31 → List Bool := fun i =>
  if i=0 then ZeroPadding.pad cap left else if i=7 then ZeroPadding.pad cap (frame (binary k 0))
  else if i=13 then ZeroPadding.pad cap right else if i=25 then ZeroPadding.pad cap (frame (binary k u))
  else List.replicate cap false
noncomputable def part (cap k u p : ℕ) (coefficient : ℤ) (left right out : List Bool) :=
  CompetitorSameBucketPairEmit.cfg CompetitorSameBucketPairEmit.machine.start (initialWork cap k u left right) cap p k coefficient out

theorem loaded_input (cap k u p : ℕ) (coefficient : ℤ) (left right out : List Bool) (ambient : Fin 41 → List Bool)
    (hfields : Fields cap k u p coefficient left out ambient) :
    ∀ i : Fin 36,loaded cap right ambient (i.castAdd 5)=(part cap k u p coefficient left right out).tapes i := by
  intro i
  fin_cases i
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 0=ZeroPadding.pad cap left
    rw [Function.update_of_ne (by decide : (0 : Fin 41)≠13)]
    exact (clean_other cap ambient 0 (by decide)).trans (hfields 0)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 1=List.replicate cap false
    rw [Function.update_of_ne (by decide : (1 : Fin 41)≠13)]
    exact clean_work cap ambient 0
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 2=List.replicate cap false
    rw [Function.update_of_ne (by decide : (2 : Fin 41)≠13)]
    exact clean_work cap ambient 1
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 3=List.replicate cap false
    rw [Function.update_of_ne (by decide : (3 : Fin 41)≠13)]
    exact clean_work cap ambient 2
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 4=List.replicate cap false
    rw [Function.update_of_ne (by decide : (4 : Fin 41)≠13)]
    exact clean_work cap ambient 3
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 5=List.replicate cap false
    rw [Function.update_of_ne (by decide : (5 : Fin 41)≠13)]
    exact clean_work cap ambient 4
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 6=List.replicate cap false
    rw [Function.update_of_ne (by decide : (6 : Fin 41)≠13)]
    exact clean_work cap ambient 5
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 7=ZeroPadding.pad cap (frame (binary k 0))
    rw [Function.update_of_ne (by decide : (7 : Fin 41)≠13)]
    exact (clean_other cap ambient 7 (by decide)).trans (hfields 1)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 8=List.replicate cap false
    rw [Function.update_of_ne (by decide : (8 : Fin 41)≠13)]
    exact clean_work cap ambient 6
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 9=List.replicate cap false
    rw [Function.update_of_ne (by decide : (9 : Fin 41)≠13)]
    exact clean_work cap ambient 7
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 10=List.replicate cap false
    rw [Function.update_of_ne (by decide : (10 : Fin 41)≠13)]
    exact clean_work cap ambient 8
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 11=List.replicate cap false
    rw [Function.update_of_ne (by decide : (11 : Fin 41)≠13)]
    exact clean_work cap ambient 9
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 12=List.replicate cap false
    rw [Function.update_of_ne (by decide : (12 : Fin 41)≠13)]
    exact clean_work cap ambient 10
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 13=ZeroPadding.pad cap right
    exact Function.update_self ..
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 14=List.replicate cap false
    rw [Function.update_of_ne (by decide : (14 : Fin 41)≠13)]
    exact clean_work cap ambient 12
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 15=List.replicate cap false
    rw [Function.update_of_ne (by decide : (15 : Fin 41)≠13)]
    exact clean_work cap ambient 13
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 16=List.replicate cap false
    rw [Function.update_of_ne (by decide : (16 : Fin 41)≠13)]
    exact clean_work cap ambient 14
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 17=List.replicate cap false
    rw [Function.update_of_ne (by decide : (17 : Fin 41)≠13)]
    exact clean_work cap ambient 15
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 18=List.replicate cap false
    rw [Function.update_of_ne (by decide : (18 : Fin 41)≠13)]
    exact clean_work cap ambient 16
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 19=List.replicate cap false
    rw [Function.update_of_ne (by decide : (19 : Fin 41)≠13)]
    exact clean_work cap ambient 17
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 20=List.replicate cap false
    rw [Function.update_of_ne (by decide : (20 : Fin 41)≠13)]
    exact clean_work cap ambient 18
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 21=List.replicate cap false
    rw [Function.update_of_ne (by decide : (21 : Fin 41)≠13)]
    exact clean_work cap ambient 19
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 22=List.replicate cap false
    rw [Function.update_of_ne (by decide : (22 : Fin 41)≠13)]
    exact clean_work cap ambient 20
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 23=List.replicate cap false
    rw [Function.update_of_ne (by decide : (23 : Fin 41)≠13)]
    exact clean_work cap ambient 21
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 24=List.replicate cap false
    rw [Function.update_of_ne (by decide : (24 : Fin 41)≠13)]
    exact clean_work cap ambient 22
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 25=ZeroPadding.pad cap (frame (binary k u))
    rw [Function.update_of_ne (by decide : (25 : Fin 41)≠13)]
    exact (clean_other cap ambient 25 (by decide)).trans (hfields 2)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 26=List.replicate cap false
    rw [Function.update_of_ne (by decide : (26 : Fin 41)≠13)]
    exact clean_work cap ambient 23
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 27=List.replicate cap false
    rw [Function.update_of_ne (by decide : (27 : Fin 41)≠13)]
    exact clean_work cap ambient 24
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 28=List.replicate cap false
    rw [Function.update_of_ne (by decide : (28 : Fin 41)≠13)]
    exact clean_work cap ambient 25
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 29=List.replicate cap false
    rw [Function.update_of_ne (by decide : (29 : Fin 41)≠13)]
    exact clean_work cap ambient 26
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 30=List.replicate cap false
    rw [Function.update_of_ne (by decide : (30 : Fin 41)≠13)]
    exact clean_work cap ambient 27
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 31=ZeroPadding.pad cap (frame (signMagnitude p coefficient))
    rw [Function.update_of_ne (by decide : (31 : Fin 41)≠13)]
    exact (clean_other cap ambient 31 (by decide)).trans (hfields 3)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 32=ZeroPadding.pad cap (frame (List.replicate (p+1) false))
    rw [Function.update_of_ne (by decide : (32 : Fin 41)≠13)]
    exact (clean_other cap ambient 32 (by decide)).trans (hfields 4)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 33=ZeroPadding.pad cap (frame (binary k 0))
    rw [Function.update_of_ne (by decide : (33 : Fin 41)≠13)]
    exact (clean_other cap ambient 33 (by decide)).trans (hfields 5)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 34=out
    rw [Function.update_of_ne (by decide : (34 : Fin 41)≠13)]
    exact (clean_other cap ambient 34 (by decide)).trans (hfields 6)
  · change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) 35=List.replicate cap false
    rw [Function.update_of_ne (by decide : (35 : Fin 41)≠13)]
    exact clean_work cap ambient 28

theorem Fields.loaded {cap k u p : ℕ} {coefficient : ℤ} {left out : List Bool} {ambient : Fin 41 → List Bool}
    (h : Fields cap k u p coefficient left out ambient) (right : List Bool) :
    Fields cap k u p coefficient left out (loaded cap right ambient) := by
  intro i
  have hn : fixedSlots i≠13 := by fin_cases i <;> decide
  change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap right) (fixedSlots i)=fixed cap k u p coefficient left out i
  rw [Function.update_of_ne hn]
  exact (clean_other cap ambient (fixedSlots i) (by fin_cases i <;> decide)).trans (h i)

theorem pad_false (cap : ℕ) (hc : 1≤cap) : ZeroPadding.pad cap [false]=List.replicate cap false := by
  change ZeroPadding.pad cap (List.replicate 1 false)=_
  rw [Rewind.Workspace.pad_zeros,max_eq_left hc]

theorem initial_present (cap s k u : ℕ) (sa sb : ℤ) (a b ra rb : ℕ) (hc : 1≤cap) :
    initialWork cap k u (CompetitorSameBucketRankFields.source s k sa a ra)
      (CompetitorSameBucketRankFields.source s k sb b rb)=CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 0 := by
  funext i
  fin_cases i <;> simp [initialWork,CompetitorSameBucketPairFields.data,pad_false cap hc]

theorem part_support (cap k u p : ℕ) (coefficient : ℤ) (left right out : List Bool)
    (hl : left.length≤cap) (hr : right.length≤cap) (hk : 2*k+1≤cap) (hp : 2*(p+1)+1≤cap)
    (i : Fin 36) (hi : i≠34) : ((part cap k u p coefficient left right out).tapes i).length≤cap := by
  fin_cases i <;> simp_all [part,CompetitorSameBucketPairEmit.cfg,CompetitorSameBucketPairEmit.extras,
    initialWork,Fin.addCases,ZeroPadding.pad_length]

theorem present_support (cap s k u p : ℕ) (sa sb coefficient : ℤ) (a b ra rb : ℕ) (out : List Bool)
    (hc : 30*(k+s+2)≤cap) (hp : 2*(p+1)+1≤cap) (i : Fin 36) (hi : i≠34) :
    ((CompetitorSameBucketPairEmit.cfg CompetitorSameBucketPairEmit.machine.start
      (CompetitorSameBucketPairFields.data cap s k u sa sb a b ra rb 3) cap p k coefficient out).tapes i).length≤cap := by
  fin_cases i <;> simp_all [CompetitorSameBucketPairEmit.cfg,CompetitorSameBucketPairEmit.extras,
    CompetitorSameBucketPairFields.data,CompetitorSameBucketRankFields.source,KeyLoop.word_length,Fin.addCases,ZeroPadding.pad_length] <;> omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
