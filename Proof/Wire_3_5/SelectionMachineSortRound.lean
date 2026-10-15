import Proof.Wire_3_5.SelectionMachineSortMath

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-! ## The programs -/

/-- Write bit `b` on `B` and advance, counting in `CB`. -/
def emitB (B : Fin (ns + 1)) (CB : Fin nr) (b : Bool) : WM ns nr := .seq (.wr B b) (WM.fwdC B CB)

/-- Skip the rest of a record's frame (the head just after the leading bit), and its terminator. -/
def skipRest (A : Fin (ns + 1)) (CA : Fin nr) : WM ns nr :=
  .seq (.whs A (.seq (WM.fwdC A CA) (WM.fwdC A CA))) (WM.fwdC A CA)

/-- Copy one framed bit (marker, bit) from `A` to `B`. -/
def copyPair (A B : Fin (ns + 1)) (CA CB : Fin nr) : WM ns nr :=
  .seq (emitB B CB true) (.seq (WM.fwdC A CA) (.seq (.ifs A (emitB B CB true) (emitB B CB false)) (WM.fwdC A CA)))

/-- Copy the rest of a record's frame to `B`, then close the rotated record with the leading bit `t`. -/
def copyRest (A B : Fin (ns + 1)) (CA CB : Fin nr) (t : Bool) : WM ns nr :=
  .seq (.whs A (copyPair A B CA CB))
    (.seq (emitB B CB true) (.seq (emitB B CB t) (.seq (emitB B CB false) (WM.fwdC A CA))))

/-- One record in the phase for the leading bit `t`: copy it rotated if its leading bit is `t`, else skip it. -/
def recStep (A B : Fin (ns + 1)) (CA CB : Fin nr) (t : Bool) : WM ns nr :=
  .seq (WM.fwdC A CA)
    (.ifs A (.seq (WM.fwdC A CA) (if t then copyRest A B CA CB true else skipRest A CA))
      (.seq (WM.fwdC A CA) (if t then skipRest A CA else copyRest A B CA CB false)))

/-- One phase: every record of the stream. -/
def phase (A B : Fin (ns + 1)) (CA CB : Fin nr) (t : Bool) : WM ns nr := .whs A (recStep A B CA CB t)

/-- **One radix round** from `A` to `B`. -/
def round (A B : Fin (ns + 1)) (CA CB : Fin nr) : WM ns nr :=
  .seq (phase A B CA CB false) (.seq (WM.rewind A CA) (.seq (phase A B CA CB true)
    (.seq (.wr B false) (.seq (WM.rewind A CA) (WM.rewind B CB)))))

/-! ## Reading a stream -/

theorem rd_app0 (pre rest : List Bool) : readTapeBit (pre ++ rest) pre.length = readTapeBit rest 0 := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]

theorem rd_cons0 (x : Bool) (l : List Bool) : readTapeBit (x :: l) 0 = x := rfl

theorem rd_cons1 (x y : Bool) (l : List Bool) : readTapeBit (x :: y :: l) 1 = y := rfl

/-! ## The round's states -/

section States
variable (cap : ℕ) (σ0 : WState ns nr) (A B : Fin (ns + 1)) (CA CB : Fin nr) (L : List Bool)

/-- The state of a round: `A` at `pA` (counted in `CA`), `B` holding `out` over `L` (its head counted in `CB`). -/
def rst (pA : ℕ) (out : List Bool) : WState ns nr :=
  ⟨Function.update (Function.update σ0.sh A pA) B out.length, Function.update σ0.st B (overlay out L),
    Function.update (Function.update σ0.val CA pA) CB out.length, σ0.cell⟩

variable {A B CA CB}
variable (hAB : A ≠ B) (hC : CA ≠ CB)
include hAB hC

theorem rst_bitA (pA : ℕ) (out : List Bool) : wbit (rst σ0 A B CA CB L pA out) A = readTapeBit (σ0.st A) pA := by
  simp [wbit, rst, hAB]

theorem fwdA_rst (pA : ℕ) (out : List Bool) (hp : pA < cap) :
    WExec cap (WM.fwdC A CA) (rst σ0 A B CA CB L pA out) (rst σ0 A B CA CB L (pA + 1) out) 5 := by
  have h := wfwdC_spec cap A CA (rst σ0 A B CA CB L pA out) (by simp [rst, hC]; exact hp)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [rst, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · funext j; simp only [rst, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

theorem emitB_rst (pA : ℕ) (out : List Bool) (b : Bool) (hq : out.length < cap) :
    WExec cap (emitB B CB b) (rst σ0 A B CA CB L pA out) (rst σ0 A B CA CB L pA (out ++ [b])) 7 := by
  have h1 := WExec.wr (cap := cap) B b (rst σ0 A B CA CB L pA out)
  have e1 : (rst σ0 A B CA CB L pA out).sets B (writeTapeBit ((rst σ0 A B CA CB L pA out).st B)
      ((rst σ0 A B CA CB L pA out).sh B) b) =
      ⟨(rst σ0 A B CA CB L pA out).sh, Function.update σ0.st B (overlay (out ++ [b]) L),
        (rst σ0 A B CA CB L pA out).val, σ0.cell⟩ := by
    apply WState.eq
    · rfl
    · funext j; simp only [rst, WState.sets_st, Function.update_apply]
      split_ifs with h
      · subst h; simp [overlay_write]
      · rfl
    · rfl
    · rfl
  rw [e1] at h1
  have h2 := wfwdC_spec cap B CB (⟨(rst σ0 A B CA CB L pA out).sh, Function.update σ0.st B (overlay (out ++ [b]) L),
    (rst σ0 A B CA CB L pA out).val, σ0.cell⟩ : WState ns nr) (by simp [rst]; exact hq)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  apply WState.eq
  · funext j; simp only [rst, WState.setv_sh, WState.seth_sh, Function.update_apply, List.length_append,
      List.length_singleton]
    split_ifs <;> simp_all
  · rfl
  · funext j; simp only [rst, WState.setv_val, WState.seth_val, Function.update_apply, List.length_append,
      List.length_singleton]
    split_ifs <;> simp_all
  · rfl

theorem copyPair_rst (pA : ℕ) (out : List Bool) (b : Bool) (hb : readTapeBit (σ0.st A) (pA + 1) = b)
    (hp : pA + 2 ≤ cap) (hq : out.length + 2 ≤ cap) :
    WExec cap (copyPair A B CA CB) (rst σ0 A B CA CB L pA out) (rst σ0 A B CA CB L (pA + 2) (out ++ [true, b])) 28 := by
  have e1 := emitB_rst cap σ0 L hAB hC pA out true (by omega)
  have f1 := fwdA_rst cap σ0 L hAB hC pA (out ++ [true]) (by omega)
  have f2 := fwdA_rst cap σ0 L hAB hC (pA + 1) (out ++ [true, b]) (by omega)
  have hbit : wbit (rst σ0 A B CA CB L (pA + 1) (out ++ [true])) A = b := by
    rw [rst_bitA σ0 L hAB hC]; exact hb
  have hmid : WExec cap (.ifs A (emitB B CB true) (emitB B CB false)) (rst σ0 A B CA CB L (pA + 1) (out ++ [true]))
      (rst σ0 A B CA CB L (pA + 1) (out ++ [true, b])) 8 := by
    have e2 := emitB_rst cap σ0 L hAB hC (pA + 1) (out ++ [true]) b (by simp; omega)
    rw [List.append_assoc] at e2
    cases b
    · exact WExec.ifsF hbit e2
    · exact WExec.ifsT hbit e2
  exact WExec.seq e1 (WExec.seq f1 (WExec.seq hmid f2))

theorem copyLoop_rst : ∀ (bits pre out post : List Bool), σ0.st A = pre ++ frameP bits ++ false :: post →
    pre.length + 2 * bits.length < cap → out.length + 2 * bits.length ≤ cap →
    WExec cap (.whs A (copyPair A B CA CB)) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + 2 * bits.length) (out ++ frameP bits)) (30 * bits.length + 1)
  | [], pre, out, post, hA, _, _ => by
    have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = false := by
      rw [rst_bitA σ0 L hAB hC, hA, frameP_nil, List.append_nil, rd_app0, rd_cons0]
    simpa using WExec.whsF (cap := cap) (P := copyPair A B CA CB) hbit
  | b :: bits, pre, out, post, hA, hp, hq => by
    have hA' : σ0.st A = (pre ++ [true, b]) ++ frameP bits ++ false :: post := by
      rw [hA, frameP_cons]; simp
    have hA2 : σ0.st A = pre ++ (true :: b :: (frameP bits ++ false :: post)) := by
      rw [hA, frameP_cons]; simp
    have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = true := by
      rw [rst_bitA σ0 L hAB hC, hA2, rd_app0, rd_cons0]
    have hb : readTapeBit (σ0.st A) (pre.length + 1) = b := by
      rw [hA2]
      have := rd_app0 (pre ++ [true]) (b :: (frameP bits ++ false :: post))
      simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at this
      rw [this, rd_cons0]
    have h1 := copyPair_rst cap σ0 L hAB hC pre.length out b hb (by simp at hp; omega) (by simp at hq; omega)
    have h2 := copyLoop_rst bits (pre ++ [true, b]) (out ++ [true, b]) post hA' (by simp at hp ⊢; omega)
      (by simp at hq ⊢; omega)
    have hl : (pre ++ [true, b]).length = pre.length + 2 := by simp
    rw [hl] at h2
    refine WExec.cast cap (WExec.whsT hbit h1 h2) ?_ (by simp; omega)
    congr 1
    · simp; omega
    · simp [frameP_cons]

theorem skipLoop_rst : ∀ (bits pre out post : List Bool), σ0.st A = pre ++ frameP bits ++ false :: post →
    pre.length + 2 * bits.length < cap →
    WExec cap (.whs A (.seq (WM.fwdC A CA) (WM.fwdC A CA))) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + 2 * bits.length) out) (13 * bits.length + 1)
  | [], pre, out, post, hA, _ => by
    have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = false := by
      rw [rst_bitA σ0 L hAB hC, hA, frameP_nil, List.append_nil, rd_app0, rd_cons0]
    simpa using WExec.whsF (cap := cap) (P := (.seq (WM.fwdC A CA) (WM.fwdC A CA) : WM ns nr)) hbit
  | b :: bits, pre, out, post, hA, hp => by
    have hA' : σ0.st A = (pre ++ [true, b]) ++ frameP bits ++ false :: post := by
      rw [hA, frameP_cons]; simp
    have hA2 : σ0.st A = pre ++ (true :: b :: (frameP bits ++ false :: post)) := by
      rw [hA, frameP_cons]; simp
    have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = true := by
      rw [rst_bitA σ0 L hAB hC, hA2, rd_app0, rd_cons0]
    have f1 := fwdA_rst cap σ0 L hAB hC pre.length out (by simp at hp; omega)
    have f2 := fwdA_rst cap σ0 L hAB hC (pre.length + 1) out (by simp at hp; omega)
    have h2 := skipLoop_rst bits (pre ++ [true, b]) out post hA' (by simp at hp ⊢; omega)
    have hl : (pre ++ [true, b]).length = pre.length + 1 + 1 := by simp
    rw [hl] at h2
    refine WExec.cast cap (WExec.whsT hbit (WExec.seq f1 f2) h2) ?_ (by simp; omega)
    congr 1
    simp; omega

end States

/-! ## Records -/

theorem frameP_append (xs ys : List Bool) : frameP (xs ++ ys) = frameP xs ++ frameP ys := by
  unfold frameP; rw [List.flatMap_append]

theorem recordBits_eq (r : StablePartition.Record) :
    StablePartition.recordBits r = true :: r.1 :: (frameP r.2 ++ [false]) := by
  unfold StablePartition.recordBits; rw [frame_eq_frameP]

/-- A rotated record's bits: the rest of the frame, then the old leading bit. -/
theorem recordBits_rotate (r : StablePartition.Record) :
    StablePartition.recordBits (RecordRotate.rotate r) = frameP r.2 ++ [true, r.1, false] := by
  rcases r with ⟨tag, bits⟩
  cases bits with
  | nil => rfl
  | cons b tail =>
    show StablePartition.recordBits (b, tail ++ [tag]) = _
    rw [recordBits_eq]
    simp [frameP]

theorem recordsBits_cons (r : StablePartition.Record) (rs : List StablePartition.Record) :
    StablePartition.recordsBits (r :: rs) = StablePartition.recordBits r ++ StablePartition.recordsBits rs := rfl

theorem recordsBits_append (xs ys : List StablePartition.Record) :
    StablePartition.recordsBits (xs ++ ys) = StablePartition.recordsBits xs ++ StablePartition.recordsBits ys := by
  unfold StablePartition.recordsBits; rw [List.flatMap_append]

theorem recordBits_length (r : StablePartition.Record) :
    (StablePartition.recordBits r).length = 2 * r.2.length + 3 := by
  rw [recordBits_eq]; simp

section Steps
variable (cap : ℕ) (σ0 : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (L : List Bool)
variable (hAB : A ≠ B) (hC : CA ≠ CB)
include hAB hC

theorem skipRest_rst (bits pre out post : List Bool) (hA : σ0.st A = pre ++ frameP bits ++ false :: post)
    (hp : pre.length + 2 * bits.length < cap) :
    WExec cap (skipRest A CA) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + 2 * bits.length + 1) out) (13 * bits.length + 7) := by
  have h1 := skipLoop_rst cap σ0 L hAB hC bits pre out post hA hp
  have h2 := fwdA_rst cap σ0 L hAB hC (pre.length + 2 * bits.length) out hp
  exact WExec.cast cap (WExec.seq h1 h2) rfl (by omega)

theorem copyRest_rst (t : Bool) (bits pre out post : List Bool) (hA : σ0.st A = pre ++ frameP bits ++ false :: post)
    (hp : pre.length + 2 * bits.length < cap) (hq : out.length + 2 * bits.length + 3 ≤ cap) :
    WExec cap (copyRest A B CA CB t) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + 2 * bits.length + 1) (out ++ (frameP bits ++ [true, t, false])))
      (30 * bits.length + 31) := by
  have h1 := copyLoop_rst cap σ0 L hAB hC bits pre out post hA hp (by omega)
  set p := pre.length + 2 * bits.length
  set o := out ++ frameP bits with ho
  have hol : o.length = out.length + 2 * bits.length := by simp [ho]
  have e1 := emitB_rst cap σ0 L hAB hC p o true (by omega)
  have e2 := emitB_rst cap σ0 L hAB hC p (o ++ [true]) t (by simp; omega)
  have e3 := emitB_rst cap σ0 L hAB hC p (o ++ [true] ++ [t]) false (by simp; omega)
  have f := fwdA_rst cap σ0 L hAB hC p (o ++ [true] ++ [t] ++ [false]) hp
  refine WExec.cast cap (WExec.seq h1 (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 f)))) ?_ (by omega)
  congr 1
  simp [ho]

/-- **One record**: from its first cell, `A` passes the record, and `B` gets it rotated iff its leading bit is `t`. -/
theorem recStep_rst (t : Bool) (r : StablePartition.Record) (pre out post : List Bool)
    (hA : σ0.st A = pre ++ StablePartition.recordBits r ++ post)
    (hp : pre.length + (StablePartition.recordBits r).length ≤ cap)
    (hq : r.1 = t → out.length + (StablePartition.recordBits r).length ≤ cap) :
    WExec cap (recStep A B CA CB t) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + (StablePartition.recordBits r).length)
        (out ++ if r.1 = t then StablePartition.recordBits (RecordRotate.rotate r) else []))
      (30 * r.2.length + 44) := by
  rw [recordBits_length] at hp hq
  have hA2 : σ0.st A = (pre ++ [true, r.1]) ++ frameP r.2 ++ false :: post := by
    rw [hA, recordBits_eq]; simp
  have hA3 : σ0.st A = pre ++ (true :: r.1 :: (frameP r.2 ++ false :: post)) := by
    rw [hA, recordBits_eq]; simp
  have hl : (pre ++ [true, r.1]).length = pre.length + 1 + 1 := by simp
  have f1 := fwdA_rst cap σ0 L hAB hC pre.length out (by omega)
  have f2 := fwdA_rst cap σ0 L hAB hC (pre.length + 1) out (by omega)
  have htag : wbit (rst σ0 A B CA CB L (pre.length + 1) out) A = r.1 := by
    rw [rst_bitA σ0 L hAB hC, hA3]
    have := rd_app0 (pre ++ [true]) (r.1 :: (frameP r.2 ++ false :: post))
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at this
    rw [this, rd_cons0]
  have hskip := skipRest_rst cap σ0 L hAB hC r.2 (pre ++ [true, r.1]) out post hA2 (by rw [hl]; omega)
  have hlen : pre.length + 1 + 1 + 2 * r.2.length + 1 = pre.length + (StablePartition.recordBits r).length := by
    rw [recordBits_length]; omega
  have hcopy : r.1 = t → WExec cap (copyRest A B CA CB r.1) (rst σ0 A B CA CB L (pre.length + 1 + 1) out)
      (rst σ0 A B CA CB L (pre.length + (StablePartition.recordBits r).length)
        (out ++ StablePartition.recordBits (RecordRotate.rotate r))) (30 * r.2.length + 31) := by
    intro hrt
    have h := copyRest_rst cap σ0 L hAB hC r.1 r.2 (pre ++ [true, r.1]) out post hA2 (by rw [hl]; omega)
      (by have := hq hrt; omega)
    rw [hl, hlen, ← recordBits_rotate] at h
    exact h
  rw [hl, hlen] at hskip
  unfold recStep
  cases ht : t <;> cases hr : r.1
  · -- t = false, leading bit false: copy
    have hc := hcopy (by rw [hr, ht])
    rw [hr] at htag hc
    simp only [if_true, Bool.false_eq_true, if_false]
    exact WExec.cast cap (WExec.seq f1 (WExec.ifsF htag (WExec.seq f2 hc))) rfl (by omega)
  · -- t = false, leading bit true: skip
    rw [hr] at htag
    simp only [Bool.true_eq_false, if_false, List.append_nil, Bool.false_eq_true]
    exact WExec.cast cap (WExec.seq f1 (WExec.ifsT htag (WExec.seq f2 hskip))) rfl (by omega)
  · -- t = true, leading bit false: skip
    rw [hr] at htag
    simp only [Bool.false_eq_true, if_false, List.append_nil, if_true]
    exact WExec.cast cap (WExec.seq f1 (WExec.ifsF htag (WExec.seq f2 hskip))) rfl (by omega)
  · -- t = true, leading bit true: copy
    have hc := hcopy (by rw [hr, ht])
    rw [hr] at htag hc
    simp only [if_true]
    exact WExec.cast cap (WExec.seq f1 (WExec.ifsT htag (WExec.seq f2 hc))) rfl (by omega)

end Steps

/-- The cost of one phase over `rest`. -/
def phaseCost (rest : List StablePartition.Record) : ℕ := (rest.map fun r => 30 * r.2.length + 46).sum + 1

section Phase
variable (cap : ℕ) (σ0 : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (L : List Bool)
variable (hAB : A ≠ B) (hC : CA ≠ CB)
include hAB hC

/-- **One phase**: `A` passes every record, and `B` gets, rotated, those whose leading bit is `t`. -/
theorem phase_rst (t : Bool) : ∀ (rest : List StablePartition.Record) (pre post out : List Bool),
    σ0.st A = pre ++ StablePartition.recordsBits rest ++ false :: post →
    pre.length + (StablePartition.recordsBits rest).length < cap →
    out.length + (StablePartition.recordsBits ((StablePartition.selected t rest).map RecordRotate.rotate)).length
      < cap →
    WExec cap (phase A B CA CB t) (rst σ0 A B CA CB L pre.length out)
      (rst σ0 A B CA CB L (pre.length + (StablePartition.recordsBits rest).length)
        (out ++ StablePartition.recordsBits ((StablePartition.selected t rest).map RecordRotate.rotate)))
      (phaseCost rest)
  | [], pre, post, out, hA, _, _ => by
    have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = false := by
      rw [rst_bitA σ0 L hAB hC, hA]
      simp [StablePartition.recordsBits, rd_app0, rd_cons0]
    have h := WExec.whsF (cap := cap) (P := recStep A B CA CB t) hbit
    refine WExec.cast cap h ?_ (by simp [phaseCost])
    simp [StablePartition.recordsBits, StablePartition.selected]
  | r :: rest, pre, post, out, hA, hp, hq => by
    have hA1 : σ0.st A = pre ++ StablePartition.recordBits r ++ (StablePartition.recordsBits rest ++ false :: post) := by
      rw [hA, recordsBits_cons]; simp
    have hA2 : σ0.st A = (pre ++ StablePartition.recordBits r) ++ StablePartition.recordsBits rest ++ false :: post := by
      rw [hA, recordsBits_cons]; simp
    have hbit : wbit (rst σ0 A B CA CB L pre.length out) A = true := by
      rw [rst_bitA σ0 L hAB hC, hA1, List.append_assoc, rd_app0, recordBits_eq]
      rfl
    rw [recordsBits_cons, List.length_append] at hp
    have hsel : StablePartition.selected t (r :: rest) =
        if r.1 = t then r :: StablePartition.selected t rest else StablePartition.selected t rest := by
      unfold StablePartition.selected
      rw [List.filter_cons]
      by_cases h : r.1 = t <;> simp [h]
    have hq1 : r.1 = t → out.length + (StablePartition.recordBits r).length ≤ cap := by
      intro h
      rw [hsel, if_pos h, List.map_cons, recordsBits_cons, List.length_append, RecordRotate.rotate_record_length]
        at hq
      omega
    have h1 := recStep_rst cap σ0 L hAB hC t r pre out _ hA1 (by omega) hq1
    set out' := out ++ if r.1 = t then StablePartition.recordBits (RecordRotate.rotate r) else [] with hout'
    have hq2 : out'.length + (StablePartition.recordsBits ((StablePartition.selected t rest).map
        RecordRotate.rotate)).length < cap := by
      rw [hsel] at hq
      by_cases h : r.1 = t
      · rw [if_pos h, List.map_cons, recordsBits_cons, List.length_append] at hq
        simp only [hout', if_pos h, List.length_append]
        omega
      · rw [if_neg h] at hq
        simp only [hout', if_neg h, List.append_nil]
        exact hq
    have h2 := phase_rst t rest (pre ++ StablePartition.recordBits r) post out' hA2 (by simp; omega) hq2
    rw [List.length_append] at h2
    refine WExec.cast cap (WExec.whsT hbit h1 h2) ?_ ?_
    · congr 1
      · rw [recordsBits_cons, List.length_append]; omega
      · simp only [hout', List.append_assoc]
        congr 1
        rw [hsel]
        by_cases h : r.1 = t
        · simp [h, recordsBits_cons]
        · simp [h]
    · simp [phaseCost]; omega

end Phase

theorem rb_rotate_length (xs : List StablePartition.Record) :
    (StablePartition.recordsBits (xs.map RecordRotate.rotate)).length = (StablePartition.recordsBits xs).length := by
  have h := RecordRotate.rotate_stream_length xs
  simp only [StablePartition.stream, List.length_append] at h
  omega

theorem rb_selected_length (rs : List StablePartition.Record) :
    (StablePartition.recordsBits ((StablePartition.selected false rs).map RecordRotate.rotate)).length +
      (StablePartition.recordsBits ((StablePartition.selected true rs).map RecordRotate.rotate)).length =
      (StablePartition.recordsBits rs).length := by
  have h := PartitionPass.selected_streams_length rs
  simp only [StablePartition.stream, List.length_append, List.length_singleton] at h
  rw [rb_rotate_length, rb_rotate_length]
  omega

theorem rb_round (rs : List StablePartition.Record) :
    StablePartition.recordsBits (RadixRound.records rs) =
      StablePartition.recordsBits ((StablePartition.selected false rs).map RecordRotate.rotate) ++
        StablePartition.recordsBits ((StablePartition.selected true rs).map RecordRotate.rotate) := by
  rw [RadixRound.records, PartitionPass.ordered, List.map_append, recordsBits_append]

/-- The cost of one round. -/
def roundCost (rs : List StablePartition.Record) : ℕ :=
  2 * phaseCost rs + 15 * (StablePartition.recordsBits rs).length + 10

/-- **One radix round** from `A` to `B`: `B` ends holding the stream of `RadixRound.records rs`; everything else,
the heads and the counters come back. -/
theorem round_spec (cap : ℕ) {A B : Fin (ns + 1)} {CA CB : Fin nr} (hAB : A ≠ B) (hC : CA ≠ CB)
    (rs : List StablePartition.Record) (σ0 : WState ns nr) (hA : σ0.st A = StablePartition.stream rs)
    (hAh : σ0.sh A = 0) (hBl : (σ0.st B).length = (StablePartition.stream rs).length) (hBh : σ0.sh B = 0)
    (hCA : σ0.val CA = 0) (hCB : σ0.val CB = 0) (hcap : (StablePartition.stream rs).length + 2 ≤ cap) :
    WExec cap (round A B CA CB) σ0 (σ0.sets B (StablePartition.stream (RadixRound.records rs))) (roundCost rs) := by
  set L := σ0.st B with hL
  set N := (StablePartition.recordsBits rs).length with hN
  set O1 := StablePartition.recordsBits ((StablePartition.selected false rs).map RecordRotate.rotate) with hO1
  set O2 := StablePartition.recordsBits ((StablePartition.selected true rs).map RecordRotate.rotate) with hO2
  have hsum : O1.length + O2.length = N := rb_selected_length rs
  have hstream : (StablePartition.stream rs).length = N + 1 := by simp [StablePartition.stream, hN]
  have hA' : σ0.st A = [] ++ StablePartition.recordsBits rs ++ false :: [] := by
    rw [hA]; rfl
  have e0 : rst σ0 A B CA CB L 0 [] = σ0 := by
    apply WState.eq
    · funext j; simp only [rst, Function.update_apply, List.length_nil]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · funext j; simp only [rst, Function.update_apply]
      split_ifs with h1
      · subst h1; simp [overlay, hL]
      · rfl
    · funext j; simp only [rst, Function.update_apply, List.length_nil]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl
  -- phase false
  have b1 : ([] : List Bool).length +
      (StablePartition.recordsBits ((StablePartition.selected false rs).map RecordRotate.rotate)).length < cap := by
    rw [← hO1]; simp; omega
  have p1 := phase_rst cap σ0 L hAB hC false rs [] [] [] hA' (by simp; omega) b1
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at p1
  rw [e0] at p1
  -- rewind A
  have r1 := wrewind_spec cap A CA N (rst σ0 A B CA CB L N O1) (by simp [rst, hC]) (by simp [rst, hC]; omega)
  have e1 : ((rst σ0 A B CA CB L N O1).setv CA 0).seth A ((rst σ0 A B CA CB L N O1).sh A - N) =
      rst σ0 A B CA CB L 0 O1 := by
    apply WState.eq
    · funext j; simp only [rst, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl
    · funext j; simp only [rst, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl
  rw [e1] at r1
  -- phase true
  have b2 : O1.length +
      (StablePartition.recordsBits ((StablePartition.selected true rs).map RecordRotate.rotate)).length < cap := by
    rw [← hO2]; omega
  have p2 := phase_rst cap σ0 L hAB hC true rs [] [] O1 hA' (by simp; omega) b2
  have e00 : ([] : List Bool).length = 0 := rfl
  rw [e00, Nat.zero_add, ← hN, ← hO2] at p2
  -- the final false of B
  have w := WExec.wr (cap := cap) B false (rst σ0 A B CA CB L N (O1 ++ O2))
  set τ := (rst σ0 A B CA CB L N (O1 ++ O2)).sets B (writeTapeBit ((rst σ0 A B CA CB L N (O1 ++ O2)).st B)
    ((rst σ0 A B CA CB L N (O1 ++ O2)).sh B) false) with hτ
  have hτA : τ.sh A = N := by simp [hτ, rst, hAB]
  have hτCA : τ.val CA = N := by simp [hτ, rst, hC]
  have r2 := wrewind_spec cap A CA N τ hτCA (by omega)
  set τ2 := (τ.setv CA 0).seth A (τ.sh A - N) with hτ2
  have hτ2CB : τ2.val CB = O1.length + O2.length := by simp [hτ2, hτ, rst, Ne.symm hC]
  have r3 := wrewind_spec cap B CB (O1.length + O2.length) τ2 hτ2CB (by omega)
  refine WExec.cast cap (WExec.seq p1 (WExec.seq r1 (WExec.seq p2 (WExec.seq w (WExec.seq r2 r3))))) ?_ ?_
  · have hst : StablePartition.stream (RadixRound.records rs) = O1 ++ O2 ++ [false] := by
      rw [StablePartition.stream, rb_round]
    have hlenL : L.length = (O1 ++ O2 ++ [false]).length := by
      rw [hL, hBl, hstream]; simp; omega
    apply WState.eq
    · funext j; simp only [hτ2, hτ, rst, WState.seth_sh, WState.setv_sh, WState.sets_sh, Function.update_apply]
      split_ifs with h1 h2 h3 <;> subst_vars <;> simp_all
    · funext j; simp only [hτ2, hτ, rst, WState.seth_st, WState.setv_st, WState.sets_st, Function.update_apply]
      split_ifs with h1
      · subst h1
        rw [hst]
        rw [overlay_write]
        simp [overlay, hlenL]
      · rfl
    · funext j; simp only [hτ2, hτ, rst, WState.seth_val, WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl
  · simp only [roundCost]
    rw [← hN]
    omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Sort
