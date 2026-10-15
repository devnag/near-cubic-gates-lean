import Proof.Gates.Solve.Sdiv
import Proof.Gates.WordPrograms.Arr
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.WordPrograms.ToReg

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)

abbrev NS : ℕ := 31
abbrev NR : ℕ := 64
abbrev MS := WState NS NR
abbrev Str := Fin (NS + 1)
abbrev Reg := Fin NR

/-! ## Streams -/
abbrev sIN : Str := 0
abbrev sOUT : Str := 1
abbrev sRAW : Str := 2
abbrev sRUL : Str := 3
abbrev sPT : Str := 4
abbrev sSG : Str := 5
abbrev sMAT : Str := 6
abbrev sNEW : Str := 7
/-- The record work word (`getAt`, `recLoop`). -/
abbrev wK : Str := 8
/-- The zero word (width only). -/
abbrev wZ : Str := 9

/-- The words. -/
def wset : List Str := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-! ## Registers -/
abbrev rF : Reg := 0
abbrev rR : Reg := 1
abbrev rS : Reg := 2
abbrev rT : Reg := 3
abbrev rG : Reg := 4
abbrev rK : Reg := 5
abbrev rT2 : Reg := 6
abbrev rCA : Reg := 7
abbrev rCW : Reg := 8
abbrev rK2 : Reg := 9
abbrev rCS : Reg := 10
/-- `addR` scratch. -/
abbrev rTa : Reg := 11

/-- The scratch registers (`0` between operations). -/
def zset : List Reg := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-! ## The abstract state -/

/-- Words hold `v`, scratch registers are `0`, the rest is as in `σ0`. -/
def At (σ0 σ : MS) (W : ℕ) (v : Str → ℕ) : Prop :=
  (∀ X ∈ wset, NumOn σ X (W + 1) (v X)) ∧ (∀ r ∈ zset, σ.val r = 0) ∧ SameExcept σ0 σ wset zset

section At
variable {σ0 σ τ : MS} {W : ℕ} {v : Str → ℕ}

theorem At.num (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) : NumOn σ X (W + 1) (v X) := h.1 X hX
theorem At.zero (h : At σ0 σ W v) {r : Reg} (hr : r ∈ zset) : σ.val r = 0 := h.2.1 r hr
theorem At.st (h : At σ0 σ W v) {X : Str} (hX : X ∉ wset) : σ.st X = σ0.st X := (h.2.2.1 X hX).1
theorem At.sh (h : At σ0 σ W v) {X : Str} (hX : X ∉ wset) : σ.sh X = σ0.sh X := (h.2.2.1 X hX).2
theorem At.val (h : At σ0 σ W v) {r : Reg} (hr : r ∉ zset) : σ.val r = σ0.val r := h.2.2.2.1 r hr

/-- A word overwritten by a number. -/
theorem At.sets (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) (a : ℕ) :
    At σ0 (σ.sets X (frame (binary (W + 1) a))) W (Function.update v X a) := by
  refine ⟨fun Y hY => ?_, fun r hr => by simpa using h.zero hr, ?_⟩
  · by_cases hYX : Y = X
    · subst hYX; simpa using BinW.numOn_sets_self σ Y (W + 1) a (h.num hY).2
    · rw [Function.update_of_ne hYX]; exact BinW.numOn_sets_ne (h.num hY) hYX _
  · exact SameExcept.trans h.2.2 (sameExcept_sets σ hX _)

/-- A word known to hold a number. -/
theorem At.setval (h : At σ0 σ W v) {X : Str} {a : ℕ} (hn : NumOn σ X (W + 1) a) :
    At σ0 σ W (Function.update v X a) := by
  refine ⟨fun Y hY => ?_, h.2.1, h.2.2⟩
  by_cases hYX : Y = X
  · subst hYX; simpa using hn
  · rw [Function.update_of_ne hYX]; exact h.num hY

/-- A frame: only words and scratch registers changed, the words hold numbers, the scratch registers are `0`. -/
theorem At.frame (h : At σ0 σ W v) {S : List Str} {Rg : List Reg} (hfr : SameExcept σ τ S Rg)
    (hS : ∀ Y ∈ S, Y ∈ wset) (hRg : ∀ r ∈ Rg, r ∈ zset) (hz : ∀ r ∈ Rg, τ.val r = 0)
    (hw : ∀ Y ∈ S, ∃ a, NumOn τ Y (W + 1) a) : ∃ v', At σ0 τ W v' ∧ ∀ Y, Y ∉ S → v' Y = v Y := by
  classical
  refine ⟨fun Y => if hY : Y ∈ S then Classical.choose (hw Y hY) else v Y, ⟨fun Y hY => ?_, fun r hr => ?_, ?_⟩,
    fun Y hY => by simp [hY]⟩
  · by_cases hYS : Y ∈ S
    · simp only [hYS, dif_pos]; exact Classical.choose_spec (hw Y hYS)
    · simp only [hYS, dif_neg, not_false_eq_true]; exact hfr.numOn hYS (h.num hY)
  · by_cases hrR : r ∈ Rg
    · exact hz r hrR
    · rw [hfr.val hrR]; exact h.zero hr
  · exact SameExcept.trans h.2.2 (hfr.weaken hS hRg)

/-- The same register update on both sides. -/
theorem At.setv (h : At σ0 σ W v) {r : Reg} (hr : r ∉ zset) (x : ℕ) : At (σ0.setv r x) (σ.setv r x) W v := by
  refine ⟨fun Y hY => BinW.numOn_setv (h.num hY) _ _, fun q hq => ?_, ⟨fun Y hY => ?_, fun q hq => ?_, ?_⟩⟩
  · have : q ≠ r := fun e => hr (e ▸ hq)
    simpa [Function.update_of_ne this] using h.zero hq
  · simpa using h.2.2.1 Y hY
  · by_cases hqr : q = r
    · subst hqr; simp
    · simp [Function.update_of_ne hqr, h.val hq]
  · simpa using h.2.2.2.2

/-- The same stream update on both sides. -/
theorem At.setsO (h : At σ0 σ W v) {X : Str} (hX : X ∉ wset) (l : List Bool) : At (σ0.sets X l) (σ.sets X l) W v := by
  refine ⟨fun Y hY => ?_, fun q hq => by simpa using h.zero hq, ⟨fun Y hY => ?_, fun q hq => ?_, ?_⟩⟩
  · have : Y ≠ X := fun e => hX (e ▸ hY)
    exact BinW.numOn_sets_ne (h.num hY) this _
  · by_cases hYX : Y = X
    · subst hYX; simp [h.sh hX]
    · simp [Function.update_of_ne hYX, h.st hY, h.sh hY]
  · simpa using h.val hq
  · simpa using h.2.2.2.2

/-- The same head update on both sides. -/
theorem At.sethO (h : At σ0 σ W v) {X : Str} (hX : X ∉ wset) (p : ℕ) : At (σ0.seth X p) (σ.seth X p) W v := by
  refine ⟨fun Y hY => ?_, fun q hq => by simpa using h.zero hq, ⟨fun Y hY => ?_, fun q hq => ?_, ?_⟩⟩
  · have : Y ≠ X := fun e => hX (e ▸ hY)
    exact ⟨by simpa using (h.num hY).1, by simp [Function.update_of_ne this, (h.num hY).2]⟩
  · by_cases hYX : Y = X
    · subst hYX; simp [h.st hX]
    · simp [Function.update_of_ne hYX, h.st hY, h.sh hY]
  · simpa using h.val hq
  · simpa using h.2.2.2.2

theorem At.num_lt (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) : (σ.st X).length = 2 * (W + 1) + 1 := by
  rw [(h.num hX).1, frame_length, binary_length]

end At

/-! ## Operations as transformations of `(σ0, v)` -/

section Ops
variable (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ}

theorem wset_ne {X Y : Str} (hX : X ∈ wset) (hY : Y ∉ wset) : X ≠ Y := fun e => hY (e ▸ hX)

/-- `X := y`. -/
theorem opCopy (h : At σ0 σ W v) {X Y : Str} (hX : X ∈ wset) (hY : Y ∈ wset) (hXY : X ≠ Y)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (BinW.copy X Y rF rR) σ (41 * (W + 1) + 3) (fun τ => At σ0 τ W (Function.update v X (v Y))) :=
  Runs.of (BinW.copy_spec cap (W + 1) hXY (by decide) σ (v X) (v Y) (h.num hX) (h.num hY) (h.zero (by decide))
    (h.zero (by decide)) hcap) (h.sets hX _)

/-- `X := 0`. -/
theorem opZero (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) (hXZ : X ≠ wZ) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (BinW.zero X wZ rF rR) σ (41 * (W + 1) + 3) (fun τ => At σ0 τ W (Function.update v X 0)) :=
  Runs.of (BinW.zero_spec cap (W + 1) hXZ (by decide) σ (v X) (v wZ) (h.num hX) (h.num (by decide))
    (h.zero (by decide)) (h.zero (by decide)) hcap) (h.sets hX _)

/-- `X := 2x`. -/
theorem opShl (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) (hXZ : X ≠ wZ) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (BinW.shl X wZ rF rR) σ (41 * (W + 1) + 8) (fun τ => At σ0 τ W (Function.update v X (2 * v X))) :=
  Runs.of (BinW.shl_spec cap (W + 1) hXZ (by decide) σ (v X) (v wZ) (h.num hX) (h.num (by decide))
    (h.zero (by decide)) (h.zero (by decide)) hcap) (h.sets hX _)

/-- `X := x + 1`. -/
theorem opInc (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) (hXZ : X ≠ wZ) (hx : v X + 1 < 2 ^ (W + 1))
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (BinW.inc X wZ rF rR) σ (41 * (W + 1) + 7) (fun τ => At σ0 τ W (Function.update v X (v X + 1))) :=
  Runs.of (BinW.inc_spec cap (W + 1) hXZ (by decide) σ (v X) (v wZ) (h.num hX) (h.num (by decide))
    (h.zero (by decide)) (h.zero (by decide)) hx hcap) (h.sets hX _)

/-- `Q := a / b`, `M := a % b`, `E := 0`. -/
theorem opDivmod (h : At σ0 σ W v) {A B Q M E : Str} (hA : A ∈ wset) (hB : B ∈ wset) (hQ : Q ∈ wset) (hM : M ∈ wset)
    (hE : E ∈ wset) (hd : [A, B, Q, M, E].Nodup) (ha : v A < 2 ^ (W + 1)) (hb : 0 < v B)
    (h2b : 2 * v B ≤ 2 ^ (W + 1)) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (BinW.divmod A B Q M E rF rR rK rT2) σ (BinW.divCost (W + 1))
      (fun τ => At σ0 τ W (Function.update (Function.update (Function.update v Q (v A / v B)) M (v A % v B)) E 0)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨hAB, hAQ, hAM, hAE⟩, ⟨hBQ, hBM, hBE⟩, ⟨hQM, hQE⟩, hME⟩ := hd
  refine Runs.of (BinW.divmod_spec cap (W + 1) hAQ hAM hAE hBQ hBM hBE hQM hQE hME (by decide) (by decide) (by decide)
    (by decide) σ (v A) (v B) (v Q) (v M) (v E) (h.num hA) (h.num hB) (h.num hQ) (h.num hM) (h.num hE)
    (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) ha hb h2b hcap) ?_
  exact ((h.sets hQ _).sets hM _).sets hE _

/-- A signed word. -/
theorem At.snum (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) {z : ℤ} (hv : v X = encS z) (hz : z.natAbs < 2 ^ W) :
    SNumOn σ X W z := ⟨by rw [← hv]; exact h.num hX, hz⟩

/-- `X := x − y` (scratch `M N`). -/
theorem opSsub (h : At σ0 σ W v) {X Y M N : Str} (hX : X ∈ wset) (hY : Y ∈ wset) (hM : M ∈ wset) (hN : N ∈ wset)
    (hd : [X, Y, M, N].Nodup) {x y : ℤ} (hvx : v X = encS x) (hvy : v Y = encS y) (hx : x.natAbs < 2 ^ W)
    (hy : y.natAbs < 2 ^ W) (hxy : (x - y).natAbs < 2 ^ W) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (ssub X Y M N rS rT rF rR) σ (420 * W + 610)
      (fun τ => ∃ v', At σ0 τ W v' ∧ v' X = encS (x - y) ∧ ∀ Z, Z ∉ [X, M, N] → v' Z = v Z) := by
  refine (ssub_spec cap W hd (by decide) σ x y (v M) (v N) (h.snum hX hvx hx) (h.snum hY hvy hy) (h.num hM) (h.num hN)
    (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) hxy hcap).post ?_
  rintro τ ⟨hXτ, ⟨a, ha⟩, ⟨b, hb⟩, hfr⟩
  obtain ⟨v', hv', hv'e⟩ := h.frame (S := [X, M, N]) (Rg := []) hfr (by simp [hX, hM, hN]) (by simp) (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro Y (rfl | rfl | rfl)
        · exact ⟨_, hXτ.1⟩
        · exact ⟨_, ha⟩
        · exact ⟨_, hb⟩)
  exact ⟨Function.update v' X (encS (x - y)), hv'.setval hXτ.1, by simp,
    fun Z hZ => by
      have hZX : Z ≠ X := fun e => hZ (by simp [e])
      rw [Function.update_of_ne hZX, hv'e Z hZ]⟩

/-- `X := x·y` (scratch `M N C D`). -/
theorem opSmul (h : At σ0 σ W v) {X Y M N C D : Str} (hX : X ∈ wset) (hY : Y ∈ wset) (hM : M ∈ wset) (hN : N ∈ wset)
    (hC : C ∈ wset) (hD : D ∈ wset) (hd : [X, Y, M, N, C, D].Nodup) {x y : ℤ} (hvx : v X = encS x)
    (hvy : v Y = encS y) (hx : x.natAbs < 2 ^ W) (hy : y.natAbs < 2 ^ W) (hxy : (x * y).natAbs < 2 ^ W)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (smul X Y M N C D rS rT rF rR rG) σ (smulCost W)
      (fun τ => ∃ v', At σ0 τ W v' ∧ v' X = encS (x * y) ∧ ∀ Z, Z ∉ [X, M, N, C, D] → v' Z = v Z) := by
  refine (smul_spec cap W hd (by decide) σ x y (v M) (v N) (v C) (v D) (h.snum hX hvx hx) (h.snum hY hvy hy)
    (h.num hM) (h.num hN) (h.num hC) (h.num hD) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide))
    (h.zero (by decide)) (h.zero (by decide)) hxy hcap).post ?_
  rintro τ ⟨hXτ, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd'⟩, hfr⟩
  obtain ⟨v', hv', hv'e⟩ := h.frame (S := [X, M, N, C, D]) (Rg := []) hfr (by simp [hX, hM, hN, hC, hD]) (by simp)
    (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro Y (rfl | rfl | rfl | rfl | rfl)
        · exact ⟨_, hXτ.1⟩
        · exact ⟨_, ha⟩
        · exact ⟨_, hb⟩
        · exact ⟨_, hc⟩
        · exact ⟨_, hd'⟩)
  exact ⟨Function.update v' X (encS (x * y)), hv'.setval hXτ.1, by simp,
    fun Z hZ => by
      have hZX : Z ≠ X := fun e => hZ (by simp [e])
      rw [Function.update_of_ne hZX, hv'e Z hZ]⟩

/-- `X := x.tdiv y` (scratch `M N Q Rm E`). -/
theorem opSdiv (h : At σ0 σ W v) {X Y M N Q Rm E : Str} (hX : X ∈ wset) (hY : Y ∈ wset) (hM : M ∈ wset)
    (hN : N ∈ wset) (hQ : Q ∈ wset) (hRm : Rm ∈ wset) (hE : E ∈ wset) (hd : [X, Y, M, N, Q, Rm, E].Nodup) {x y : ℤ}
    (hvx : v X = encS x) (hvy : v Y = encS y) (hx : x.natAbs < 2 ^ W) (hy : y.natAbs < 2 ^ W) (hy0 : y ≠ 0)
    (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (sdiv X Y M N Q Rm E rS rT rF rR rK rT2) σ (sdivCost W)
      (fun τ => ∃ v', At σ0 τ W v' ∧ v' X = encS (x.tdiv y) ∧ ∀ Z, Z ∉ [X, M, N, Q, Rm, E] → v' Z = v Z) := by
  refine (sdiv_spec cap W hd (by decide) σ x y (v M) (v N) (v Q) (v Rm) (v E) (h.snum hX hvx hx) (h.snum hY hvy hy)
    (h.num hM) (h.num hN) (h.num hQ) (h.num hRm) (h.num hE) (h.zero (by decide)) (h.zero (by decide))
    (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) (h.zero (by decide)) hy0 hcap).post ?_
  rintro τ ⟨hXτ, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd'⟩, ⟨e, he⟩, hfr⟩
  obtain ⟨v', hv', hv'e⟩ := h.frame (S := [X, M, N, Q, Rm, E]) (Rg := []) hfr (by simp [hX, hM, hN, hQ, hRm, hE])
    (by simp) (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro Y (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact ⟨_, hXτ.1⟩
        · exact ⟨_, ha⟩
        · exact ⟨_, hb⟩
        · exact ⟨_, hc⟩
        · exact ⟨_, hd'⟩
        · exact ⟨_, he⟩)
  exact ⟨Function.update v' X (encS (x.tdiv y)), hv'.setval hXτ.1, by simp,
    fun Z hZ => by
      have hZX : Z ≠ X := fun e => hZ (by simp [e])
      rw [Function.update_of_ne hZX, hv'e Z hZ]⟩

/-- `NZ := [x ≠ 0]` into a flag register outside the scratch set (`0` before). -/
theorem opNz (h : At σ0 σ W v) {X : Str} (hX : X ∈ wset) (hXZ : X ≠ wZ) {NZ : Reg} (hNZ : NZ ∉ zset)
    (h0 : σ0.val NZ = 0) (hx : v X < 2 ^ (W + 1)) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (nzP X wZ NZ rF rR) σ (41 * (W + 1) + 12)
      (fun τ => At (σ0.setv NZ (decide (v X ≠ 0)).toNat) τ W v) := by
  have hd : [NZ, rF, rR].Nodup := by
    have h1 : NZ ≠ rF := fun e => hNZ (e ▸ by decide)
    have h2 : NZ ≠ rR := fun e => hNZ (e ▸ by decide)
    simp [h1, h2]
  exact Runs.of (nzP_spec cap (W + 1) hXZ hd σ (v X) (v wZ) (h.num hX) (h.num (by decide)) (by rw [h.val hNZ, h0])
    (h.zero (by decide)) (h.zero (by decide)) hx hcap) (h.setv hNZ _)

/-- `wK := xs[n]` from the record stream on `A`, `n` in the index register `IX`. -/
theorem opGetAt (h : At σ0 σ W v) {A : Str} (hA : A ∉ wset) {IX : Reg} (hIX : IX ∉ zset) (xs : List ℕ) (junk : List Bool)
    (hAst : σ0.st A = recStream (xs.map (binary (W + 1))) ++ junk) (hAsh : σ0.sh A = 0) (hn : σ0.val IX < xs.length)
    (hcap : (xs.length + 1) * (2 * (W + 1) + 1) + 2 * σ0.val IX ≤ cap) :
    Runs cap (getAt A wK rCA rCW IX rK2) σ ((σ0.val IX + 1) * (40 * (W + 1) + 40) +
      10 * (σ0.val IX + 1) * (2 * (W + 1) + 1) + 10) (fun τ => At σ0 τ W (Function.update v wK xs[σ0.val IX])) := by
  have hAW : A ≠ wK := fun e => hA (e ▸ by decide)
  have hd : [rCA, rCW, IX, rK2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      first | decide | exact fun e => hIX (e ▸ by decide) | exact fun e => hIX (e.symm ▸ by decide)
  exact Runs.of (getAt_spec cap hAW hd (W + 1) (by omega) xs (σ0.val IX) hn σ junk (by rw [h.st hA, hAst])
    (by rw [h.sh hA, hAsh]) (h.zero (by decide)) (h.num (by decide)).2 (by rw [h.num_lt (by decide)])
    (h.zero (by decide)) (h.val hIX) (h.zero (by decide)) hcap) (h.sets (by decide) _)

/-- Append the word `X` as a record to the output stream `O` (counter `CO`). -/
theorem opAppend (h : At σ0 σ W v) {X O : Str} (hX : X ∈ wset) (hO : O ∉ wset) {CO : Reg} (hCO : CO ∉ zset)
    {out L0 : List Bool} (hout : OutOn σ0 O CO out L0) (hcap : out.length + 2 * (W + 1) + 2 ≤ cap) :
    Runs cap (appendRecX X O rCS CO) σ (40 * (W + 1) + 11) (fun τ => At
      (((σ0.sets O (overlay (out ++ frame (binary (W + 1) (v X))) L0)).seth O
        (out ++ frame (binary (W + 1) (v X))).length).setv CO (out ++ frame (binary (W + 1) (v X))).length) τ W v) := by
  have hXO : X ≠ O := wset_ne hX hO
  have hC : rCS ≠ CO := fun e => hCO (e ▸ by decide)
  have hO' : OutOn σ O CO out L0 := ⟨by rw [h.st hO, hout.1], by rw [h.sh hO, hout.2.1], by rw [h.val hCO, hout.2.2]⟩
  have e := appendRec_spec cap hXO hC σ (binary (W + 1) (v X)) [] out L0 (by rw [(h.num hX).1, BinW.frame_frameP])
    (h.num hX).2 (h.zero (by decide)) hO' (by rw [binary_length]; omega)
  rw [binary_length] at e
  exact Runs.of (WXExec.wm e) (((h.setsO hO _).sethO hO _).setv hCO _)

end Ops

/-! ## Register operations outside the scratch set -/

section Regs
variable (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ}

theorem opIncR (h : At σ0 σ W v) {r : Reg} (hr : r ∉ zset) (hc : σ0.val r < cap) :
    Runs cap (WMX.inc r) σ 3 (fun τ => At (σ0.setv r (σ0.val r + 1)) τ W v) := by
  have e := WXExec.inc cap r σ (by rw [h.val hr]; exact hc)
  rw [h.val hr] at e
  exact Runs.of e (h.setv hr _)

theorem opDecR (h : At σ0 σ W v) {r : Reg} (hr : r ∉ zset) (hc : σ0.val r ≤ cap) :
    Runs cap (WMX.dec r) σ 1 (fun τ => At (σ0.setv r (σ0.val r - 1)) τ W v) := by
  have e := WXExec.dec cap r σ (by rw [h.val hr]; exact hc)
  rw [h.val hr] at e
  exact Runs.of e (h.setv hr _)

/-- `B := B + A`. -/
theorem opAddR (h : At σ0 σ W v) {A B : Reg} (hA : A ∉ zset) (hB : B ∉ zset) (hAB : A ≠ B)
    (hc : σ0.val B + σ0.val A ≤ cap) :
    Runs cap (addR A B rTa) σ (18 * σ0.val A + 3) (fun τ => At (σ0.setv B (σ0.val B + σ0.val A)) τ W v) := by
  have hAT : A ≠ rTa := fun e => hA (e ▸ by decide)
  have hBT : B ≠ rTa := fun e => hB (e ▸ by decide)
  have e := addR_spec cap hAB hAT hBT σ (h.zero (by decide)) (by rw [h.val hA, h.val hB]; exact hc)
  rw [h.val hA, h.val hB] at e
  exact Runs.of e (h.setv hB _)

/-- `r := 0`. -/
theorem opClearR (h : At σ0 σ W v) {r : Reg} (hr : r ∉ zset) (hc : σ0.val r ≤ cap) :
    Runs cap (.wm (WM.clear r)) σ (3 * σ0.val r + 1) (fun τ => At (σ0.setv r 0) τ W v) := by
  have e := wclear_spec (cap := cap) r (σ0.val r) σ (h.val hr) (by rw [h.val hr]; exact hc)
  exact Runs.of (WXExec.wm e) (h.setv hr _)

end Regs

/-- Re-anchor: any state is its own reference. -/
theorem At.self {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) : At σ σ W v :=
  ⟨h.1, h.2.1, SameExcept.refl σ wset zset⟩

/-- A change outside the words and the scratch registers. -/
theorem At.out {σ0 σ τ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {S : List Str} {Rg : List Reg}
    (hfr : SameExcept σ τ S Rg) (hS : ∀ X ∈ S, X ∉ wset) (hRg : ∀ r ∈ Rg, r ∉ zset) : At τ τ W v := by
  refine ⟨fun X hX => hfr.numOn (fun m => hS X m hX) (h.num hX), fun r hr => ?_, SameExcept.refl τ wset zset⟩
  rw [hfr.val (fun m => hRg r m hr)]; exact h.zero hr

/-- The reference state of `τ`: `σ0` on the words and the scratch registers, `τ` elsewhere. -/
def mergeRef (σ0 τ : MS) : MS :=
  ⟨fun i => if i ∈ wset then σ0.sh i else τ.sh i, fun i => if i ∈ wset then σ0.st i else τ.st i,
    fun r => if r ∈ zset then σ0.val r else τ.val r, τ.cell⟩

/-- A change outside the words and the scratch registers, with a new reference. -/
theorem At.merge {σ0 σ τ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {S : List Str} {Rg : List Reg}
    (hfr : SameExcept σ τ S Rg) (hS : ∀ X ∈ S, X ∉ wset) (hRg : ∀ r ∈ Rg, r ∉ zset) :
    At (mergeRef σ0 τ) τ W v ∧ SameExcept σ0 (mergeRef σ0 τ) S Rg ∧
      (∀ X, X ∉ wset → (mergeRef σ0 τ).st X = τ.st X ∧ (mergeRef σ0 τ).sh X = τ.sh X) ∧
      (∀ r, r ∉ zset → (mergeRef σ0 τ).val r = τ.val r) := by
  have hout := h.out hfr hS hRg
  refine ⟨⟨hout.1, hout.2.1, ⟨fun X hX => ?_, fun r hr => ?_, rfl⟩⟩, ⟨fun X hX => ?_, fun r hr => ?_, ?_⟩,
    fun X hX => ?_, fun r hr => ?_⟩
  · simp [mergeRef, hX]
  · simp [mergeRef, hr]
  · by_cases hw : X ∈ wset
    · simp [mergeRef, hw]
    · simp only [mergeRef, hw, if_false]
      rw [hfr.st hX, hfr.sh hX]; exact ⟨h.st hw, h.sh hw⟩
  · by_cases hz : r ∈ zset
    · simp [mergeRef, hz]
    · simp only [mergeRef, hz, if_false]
      rw [hfr.val hr]; exact h.val hz
  · simp only [mergeRef]; rw [hfr.cell]; exact h.2.2.2.2
  · simp [mergeRef, hX]
  · simp [mergeRef, hr]

/-- Close an output stream outside the words. -/
theorem opCloseOut (cap : ℕ) {σ0 σ : MS} {W : ℕ} {v : Str → ℕ} (h : At σ0 σ W v) {O : Str} (hO : O ∉ wset)
    {CO : Reg} (hCO : CO ∉ zset) {out L0 : List Bool} (hout : OutOn σ0 O CO out L0) (hc : out.length ≤ cap) :
    Runs cap (closeOutX O CO) σ (5 * out.length + 3)
      (fun τ => At (((σ0.sets O (overlay (out ++ [false]) L0)).seth O 0).setv CO 0) τ W v) := by
  have hO' : OutOn σ O CO out L0 := ⟨by rw [h.st hO, hout.1], by rw [h.sh hO, hout.2.1], by rw [h.val hCO, hout.2.2]⟩
  exact Runs.of (WXExec.wm (closeOut_spec cap σ out L0 hO' hc)) (((h.setsO hO _).sethO hO _).setv hCO _)

end NearCubicGates.Close.Solve
