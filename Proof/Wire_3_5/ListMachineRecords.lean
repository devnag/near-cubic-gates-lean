import Proof.Wire_3_5.ListMachineEncoding
import Proof.Wire_3_5.BlockCopy
import Proof.Wire_3_5.BlockWhile

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Rec
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## The open copy: the pairs of a framed word, without its terminator -/

namespace CopyOpen

def action (state : Fin 3) (sourceMove : HeadMove) (output : Option Bool) (outMove : HeadMove) : Action 2 3 :=
  ⟨state, fun i => if i.val = 1 then output else none, fun i => if i.val = 1 then outMove else sourceMove⟩

/-- Tape 0 holds a framed word at its cursor; tape 1 receives its pairs at its cursor. At the terminator it halts
without writing, the source head on the terminator. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then
      (if scanned 0 then some (action 1 .right (some true) .right) else some (action 2 .stay none .stay))
    else if state.val = 1 then some (action 0 .right (some (scanned 0)) .right)
    else none

def config (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    Configuration 2 3 := ⟨state, ![sourceHead, output.length], ![source, overlay output backing]⟩

@[simp] theorem config_cells (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    (config state source sourceHead output backing).tapeCells = source.length + max output.length backing.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

theorem marker_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = true) :
    step machine (config 0 source h output backing) = some (config 1 source (h + 1) (output ++ [true]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem bit_step (source : List Bool) (h : ℕ) (output backing : List Bool) (b : Bool) (hr : readTapeBit source h = b) :
    step machine (config 1 source h output backing) = some (config 0 source (h + 1) (output ++ [b]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem finish_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = false) :
    step machine (config 0 source h output backing) = some (config 2 source h output backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem copy_prefix (pre w tail output backing : List Bool) :
    Prefix machine ((pre ++ frame w ++ tail).length + (output.length + 2 * w.length) + backing.length)
      (2 * w.length + 1)
      (config 0 (pre ++ frame w ++ tail) pre.length output backing)
      (config 2 (pre ++ frame w ++ tail) (pre.length + 2 * w.length) (output ++ Streaming.marks w) backing) := by
  induction w generalizing pre output with
  | nil =>
    have hread := Streaming.read_append pre tail false
    have hp := finish_step (pre ++ frame [] ++ tail) pre.length output backing
      (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) rfl hp ?_
    simpa [Streaming.marks] using Prefix.refl (p := machine)
      (config 2 (pre ++ frame [] ++ tail) pre.length output backing) (by simp; omega)
  | cons a w ih =>
    let src := pre ++ frame (a :: w) ++ tail
    let space := src.length + (output.length + 2 * (a :: w).length) + backing.length
    have ht : Prefix machine space (2 * w.length + 1)
        (config 0 src (pre.length + 2) (output ++ [true, a]) backing)
        (config 2 src (pre.length + 2 * (a :: w).length) (output ++ Streaming.marks (a :: w)) backing) := by
      have hi := ih (pre ++ [true, a]) (output ++ [true, a])
      convert hi using 1 <;> simp [src, space, frame, Streaming.marks, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    have hread : readTapeBit src pre.length = true := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append pre (a :: frame w ++ tail) true
    have hbit : readTapeBit src (pre.length + 1) = a := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) a
    have hp := Prefix.step (by simp [space]; omega :
        (config 1 src (pre.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
      rfl (bit_step src (pre.length + 1) (output ++ [true]) backing a hbit)
      (by simpa [List.append_assoc, Nat.add_assoc] using ht)
    have hstart := Prefix.step (by simp [space]; omega :
        (config 0 src pre.length output backing).tapeCells ≤ space)
      rfl (marker_step src pre.length output backing hread) hp
    convert hstart using 1 <;> (simp [src, frame, List.append_assoc]; try omega)

/-- **The open copy**: from the source cursor at `frame w`, the pairs of `w` are written at the output cursor; the
source head stops on the terminator. -/
theorem run (pre w tail output backing : List Bool) :
    Step machine (2 * w.length + 1) ![pre.length, output.length] ![pre ++ frame w ++ tail, overlay output backing]
      ![pre.length + 2 * w.length, (output ++ Streaming.marks w).length] ![pre ++ frame w ++ tail, overlay (output ++ Streaming.marks w) backing] := by
  obtain ⟨r, hr, hf, _, _⟩ := (copy_prefix pre w tail output backing).run rfl (by simp [frame_length]; omega)
  refine Step.of_run hr ?_ ?_
  · rw [hf]; rfl
  · rw [hf]; rfl

end CopyOpen

/-! ## The full copy that steps past the terminator -/

namespace CopyPast

def action (state : Fin 3) (output : Option Bool) : Action 2 3 :=
  ⟨state, fun i => if i.val = 1 then output else none, fun _ => .right⟩

/-- Tape 0 holds a framed word at its cursor; tape 1 receives the framed word at its cursor. Both heads end one cell
past the terminator. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state scanned => if state.val = 0 then
      (if scanned 0 then some (action 1 (some true)) else some (action 2 (some false)))
    else if state.val = 1 then some (action 0 (some (scanned 0)))
    else none

def config (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    Configuration 2 3 := ⟨state, ![sourceHead, output.length], ![source, overlay output backing]⟩

@[simp] theorem config_cells (state : Fin 3) (source : List Bool) (sourceHead : ℕ) (output backing : List Bool) :
    (config state source sourceHead output backing).tapeCells = source.length + max output.length backing.length := by
  simp [config, Configuration.tapeCells, Fin.sum_univ_succ]

theorem marker_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = true) :
    step machine (config 0 source h output backing) = some (config 1 source (h + 1) (output ++ [true]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem bit_step (source : List Bool) (h : ℕ) (output backing : List Bool) (b : Bool) (hr : readTapeBit source h = b) :
    step machine (config 1 source h output backing) = some (config 0 source (h + 1) (output ++ [b]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem finish_step (source : List Bool) (h : ℕ) (output backing : List Bool) (hr : readTapeBit source h = false) :
    step machine (config 0 source h output backing) = some (config 2 source (h + 1) (output ++ [false]) backing) := by
  simp [step, machine, config, Configuration.scanned, hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, overlay_write]

theorem copy_prefix (pre w tail output backing : List Bool) :
    Prefix machine ((pre ++ frame w ++ tail).length + (output.length + 2 * w.length + 1) + backing.length)
      (2 * w.length + 1)
      (config 0 (pre ++ frame w ++ tail) pre.length output backing)
      (config 2 (pre ++ frame w ++ tail) (pre.length + 2 * w.length + 1) (output ++ frame w) backing) := by
  induction w generalizing pre output with
  | nil =>
    have hread := Streaming.read_append pre tail false
    have hp := finish_step (pre ++ frame [] ++ tail) pre.length output backing
      (by simpa [frame, List.append_assoc] using hread)
    refine Prefix.step (by simp; omega) rfl hp ?_
    simpa [frame] using Prefix.refl (p := machine)
      (config 2 (pre ++ frame [] ++ tail) (pre.length + 1) (output ++ [false]) backing) (by simp; omega)
  | cons a w ih =>
    let src := pre ++ frame (a :: w) ++ tail
    let space := src.length + (output.length + 2 * (a :: w).length + 1) + backing.length
    have ht : Prefix machine space (2 * w.length + 1)
        (config 0 src (pre.length + 2) (output ++ [true, a]) backing)
        (config 2 src (pre.length + 2 * (a :: w).length + 1) (output ++ frame (a :: w)) backing) := by
      have hi := ih (pre ++ [true, a]) (output ++ [true, a])
      convert hi using 1 <;> simp [src, space, frame, List.append_assoc, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    have hread : readTapeBit src pre.length = true := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append pre (a :: frame w ++ tail) true
    have hbit : readTapeBit src (pre.length + 1) = a := by
      simpa [src, frame, List.append_assoc] using Streaming.read_append (pre ++ [true]) (frame w ++ tail) a
    have hp := Prefix.step (by simp [space]; omega :
        (config 1 src (pre.length + 1) (output ++ [true]) backing).tapeCells ≤ space)
      rfl (bit_step src (pre.length + 1) (output ++ [true]) backing a hbit)
      (by simpa [List.append_assoc, Nat.add_assoc] using ht)
    have hstart := Prefix.step (by simp [space]; omega :
        (config 0 src pre.length output backing).tapeCells ≤ space)
      rfl (marker_step src pre.length output backing hread) hp
    convert hstart using 1 <;> simp [src, frame, List.append_assoc, Nat.add_assoc, Nat.mul_add]

/-- **The full copy**: `frame w` from the source cursor onto the output cursor; both heads pass the terminator. -/
theorem run (pre w tail output backing : List Bool) :
    Step machine (2 * w.length + 1) ![pre.length, output.length] ![pre ++ frame w ++ tail, overlay output backing]
      ![pre.length + 2 * w.length + 1, (output ++ frame w).length] ![pre ++ frame w ++ tail, overlay (output ++ frame w) backing] := by
  obtain ⟨r, hr, hf, _, _⟩ := (copy_prefix pre w tail output backing).run rfl (by simp [frame_length]; omega)
  refine Step.of_run hr ?_ ?_
  · rw [hf]; rfl
  · rw [hf]; rfl

end CopyPast

/-! ## The record marker: write `true`, step both heads -/

namespace Mark

def machine (b : Bool) : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then
      some ⟨1, fun i => if i.val = 1 then some b else none, fun _ => .right⟩ else none

theorem run (b : Bool) (source : List Bool) (h : ℕ) (output backing : List Bool) :
    Step (machine b) 1 ![h, output.length] ![source, overlay output backing]
      ![h + 1, (output ++ [b]).length] ![source, overlay (output ++ [b]) backing] := by
  have hs : step (machine b) ⟨(machine b).start, ![h, output.length], ![source, overlay output backing]⟩ =
      some ⟨1, ![h + 1, (output ++ [b]).length], ![source, overlay (output ++ [b]) backing]⟩ := by
    simp [step, machine]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction, overlay_write]
  obtain ⟨r, hr, hf, _⟩ := (RecoveryExecution.Timed.single (p := machine b) rfl hs).run rfl
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

end Mark

/-! ## Docking helpers -/

theorem dockRun {t u s n : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (RecoveryRootRound.install slots A tout) := by
  have hf := h.focus slots hi H A
  have e1 : dockH slots H hin = H := by
    funext i
    cases hp : RecoveryFocus.pick slots i with
    | none => simp [dockH, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [dockH, hp]
      rw [← he]
      exact (hH j).symm
  rwa [e1, RecoveryRootRound.install_existing slots A tin hA] at hf

/-- The masked (head-rewinding) form of a step whose selected heads start at `0`: the log tape is the last. -/
theorem maskRun {t s n cap : ℕ} {p : Machine t s} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (sel : Fin t → Bool) (hstart : ∀ i, sel i = true → hin i = 0) (hcap : n ≤ cap) :
    Step (MaskedReset.machine p sel) (2 * n + 2) (Fin.addCases hin (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => List.replicate cap false))
      (Fin.addCases (fun i => if sel i then 0 else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate cap false)) :=
  h.mask sel hstart hcap

/-! ## CopyO as a step -/

theorem copyO_step (pre w tail output backing : List Bool) :
    Step Block.CopyO.machine (2 * w.length + 1) ![pre.length, output.length] ![pre ++ frame w ++ tail, overlay output backing]
      ![pre.length + 2 * w.length, (output ++ frame w).length] ![pre ++ frame w ++ tail, overlay (output ++ frame w) backing] := by
  obtain ⟨r, hr, hf⟩ := Block.CopyO.copy_run pre w tail output backing
  refine Step.of_run hr ?_ ?_
  · rw [hf]; funext i; fin_cases i <;> simp [Block.CopyO.config, frame_length]
  · rw [hf]; rfl

/-! ## The inner pass of the product: one monomial `a` against every monomial of `q` -/

namespace ProdInner

/-- Tapes: 0 the records of `q`, 1 the scratch holding `frame (monoBits a)`, 2 the output, 3 the scratch's log. -/
def slMark : Fin 2 → Fin 4 := ![0, 2]
def slOpen : Fin 3 → Fin 4 := ![1, 2, 3]
def selS : Fin 2 → Bool := ![true, false]

noncomputable def st1 : Machine 4 2 := RecoveryFocus.machine slMark (Mark.machine true)
noncomputable def st2 : Machine 4 (3 + 2) := RecoveryFocus.machine slOpen (MaskedReset.machine CopyOpen.machine selS)
noncomputable def st3 : Machine 4 3 := RecoveryFocus.machine slMark CopyPast.machine
/-- **The inner body**: mark the output record, write `a`'s pairs, copy `b`'s framed word. -/
noncomputable def body : Machine 4 (2 + (3 + 2) + 3) := Composition.machine (Composition.machine st1 st2) st3

theorem slMark_inj : Function.Injective slMark := by decide
theorem slOpen_inj : Function.Injective slOpen := by decide

theorem dockH_mark (H : Fin 4 → ℕ) (v : Fin 2 → ℕ) : dockH slMark H v = ![v 0, H 1, v 1, H 3] := by
  funext i; fin_cases i
  · exact dockH_slot slMark slMark_inj H v 0
  · exact dockH_other slMark H v 1 (by decide)
  · exact dockH_slot slMark slMark_inj H v 1
  · exact dockH_other slMark H v 3 (by decide)

theorem install_mark (A : Fin 4 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slMark A v = ![v 0, A 1, v 1, A 3] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slMark slMark_inj A v 0
  · exact RecoveryRootRound.install_other slMark A v 1 (by decide)
  · exact RecoveryRootRound.install_slot slMark slMark_inj A v 1
  · exact RecoveryRootRound.install_other slMark A v 3 (by decide)

theorem dockH_open (H : Fin 4 → ℕ) (v : Fin 3 → ℕ) : dockH slOpen H v = ![H 0, v 0, v 1, v 2] := by
  funext i; fin_cases i
  · exact dockH_other slOpen H v 0 (by decide)
  · exact dockH_slot slOpen slOpen_inj H v 0
  · exact dockH_slot slOpen slOpen_inj H v 1
  · exact dockH_slot slOpen slOpen_inj H v 2

theorem install_open (A : Fin 4 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install slOpen A v = ![A 0, v 0, v 1, v 2] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slOpen A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slOpen slOpen_inj A v 0
  · exact RecoveryRootRound.install_slot slOpen slOpen_inj A v 1
  · exact RecoveryRootRound.install_slot slOpen slOpen_inj A v 2

/-- The cost of one inner pass. -/
def bodyCost (ma mb : List Bool) : ℕ := 1 + 1 + (2 * (2 * ma.length + 1) + 2) + 1 + (2 * mb.length + 1)

/-- **One inner pass**: from the record `b` of `q` (cursor on its marker), with the scratch holding `a`, the output
receives the product record `true :: frame (monoBits a ++ monoBits b)`; the cursor passes `b`. -/
theorem body_step (preB mb tailB ma junk out backing : List Bool) (cap : ℕ) (hcap : 2 * ma.length + 1 ≤ cap) :
    Step body (bodyCost ma mb)
      ![preB.length, 0, out.length, 0]
      ![preB ++ [true] ++ frame mb ++ tailB, frame ma ++ junk, overlay out backing, List.replicate cap false]
      ![preB.length + 1 + 2 * mb.length + 1, 0, (out ++ (true :: frame (ma ++ mb))).length, 0]
      ![preB ++ [true] ++ frame mb ++ tailB, frame ma ++ junk, overlay (out ++ (true :: frame (ma ++ mb))) backing,
        List.replicate cap false] := by
  set Bw := preB ++ [true] ++ frame mb ++ tailB with hBw
  -- stage 1: the marker
  have h1 := dockRun (Mark.run true Bw preB.length out backing) slMark slMark_inj
    ![preB.length, 0, out.length, 0] ![Bw, frame ma ++ junk, overlay out backing, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_mark, install_mark] at h1
  -- stage 2: the open copy of `a`, the scratch head rewound
  have hc := CopyOpen.run [] ma junk (out ++ [true]) backing
  have hm := maskRun hc selS (by intro i hi; fin_cases i <;> simp_all [selS]) (by omega : 2 * ma.length + 1 ≤ cap)
  have h2 := dockRun hm slOpen slOpen_inj
    ![preB.length + 1, 0, (out ++ [true]).length, 0]
    ![Bw, frame ma ++ junk, overlay (out ++ [true]) backing, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_open, install_open] at h2
  -- stage 3: the framed copy of `b`
  have hBsplit : Bw = (preB ++ [true]) ++ frame mb ++ tailB := by simp [hBw, List.append_assoc]
  have h3 := dockRun (CopyPast.run (preB ++ [true]) mb tailB (out ++ [true] ++ Streaming.marks ma) backing) slMark slMark_inj
    ![preB.length + 1, 0, (out ++ [true] ++ Streaming.marks ma).length, 0]
    ![Bw, frame ma ++ junk, overlay (out ++ [true] ++ Streaming.marks ma) backing, List.replicate cap false]
    (by intro j; fin_cases j <;> first | rfl | simp [slMark]) (by intro j; fin_cases j <;> rfl)
  rw [dockH_mark, install_mark] at h3
  have h12 := Step.seq h1 (h2.congr_in (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))
  have h123 := Step.seq h12 (h3.congr_in (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))
  refine (h123.congr ?_ ?_).enlarge (le_of_eq ?_)
  · funext i; fin_cases i <;> first | rfl | simp [Streaming.frame_append, frame_length]
  · funext i; fin_cases i <;> first | rfl | simp [hBsplit, Streaming.frame_append, List.append_assoc]
  · simp [bodyCost]

end ProdInner

/-! ## Record streams -/

theorem flatMap_take_succ {α β : Type} (f : α → List β) (l : List α) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).flatMap f = (l.take j).flatMap f ++ f l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.flatMap_append]
  simp

theorem polyWord_split (q : List (List ℕ)) (j : ℕ) (hj : j < q.length) :
    polyWord q = ((q.take j).flatMap recW ++ [true]) ++ frame (monoBits q[j]) ++
      ((q.drop (j + 1)).flatMap recW ++ [false]) := by
  unfold polyWord
  conv_lhs => rw [← List.take_append_drop j q]
  rw [List.flatMap_append, List.drop_eq_getElem_cons hj, List.flatMap_cons]
  simp [recW, List.append_assoc]

/-- A polynomial's records inside a tape, split at record `j`: before it, its marker, its framed word, the rest. -/
theorem stream_split (pre tail : List Bool) (q : List (List ℕ)) (j : ℕ) (hj : j < q.length) :
    pre ++ (polyWord q ++ tail) = (pre ++ (q.take j).flatMap recW ++ [true]) ++ frame (monoBits q[j]) ++
      ((q.drop (j + 1)).flatMap recW ++ [false] ++ tail) := by
  rw [polyWord_split q j hj]; simp [List.append_assoc]

theorem stream_read_marker (pre tail : List Bool) (q : List (List ℕ)) (j : ℕ) (hj : j < q.length) :
    readTapeBit (pre ++ (polyWord q ++ tail)) (pre ++ (q.take j).flatMap recW).length = true := by
  have e : pre ++ (polyWord q ++ tail) = (pre ++ (q.take j).flatMap recW) ++
      true :: (frame (monoBits q[j]) ++ ((q.drop (j + 1)).flatMap recW ++ [false] ++ tail)) := by
    rw [stream_split pre tail q j hj]; simp [List.append_assoc]
  rw [e]; exact Streaming.read_append _ _ _

theorem stream_read_end (pre tail : List Bool) (q : List (List ℕ)) :
    readTapeBit (pre ++ (polyWord q ++ tail)) (pre ++ (q.take q.length).flatMap recW).length = false := by
  rw [List.take_length]
  have e : pre ++ (polyWord q ++ tail) = (pre ++ q.flatMap recW) ++ false :: tail := by simp [polyWord]
  rw [e]; exact Streaming.read_append _ _ _

theorem polyWord_read_marker (q : List (List ℕ)) (tail : List Bool) (j : ℕ) (hj : j < q.length) :
    readTapeBit (polyWord q ++ tail) ((q.take j).flatMap recW).length = true := by
  have h := stream_read_marker [] tail q j hj
  simp only [List.nil_append] at h
  exact h

theorem polyWord_read_end (q : List (List ℕ)) (tail : List Bool) :
    readTapeBit (polyWord q ++ tail) ((q.take q.length).flatMap recW).length = false := by
  have h := stream_read_end [] tail q
  simp only [List.nil_append] at h
  exact h

/-- The cost of the inner pass of a monomial with bits `ma` over the records of `q`. -/
def innerCost (q : List (List ℕ)) (ma : List Bool) : ℕ :=
  ((List.range q.length).map fun i => ProdInner.bodyCost ma (monoBits (q.getD i [])) + 2).sum + 1

namespace ProdInner

/-- The inner loop over the monomials of `q`, the scratch holding `a`. -/
noncomputable def loop (q : List (List ℕ)) (a : List ℕ) (tailB junk out backing : List Bool) (cap : ℕ)
    (hcap : 2 * (monoBits a).length + 1 ≤ cap) : Block.WhileBody 4 (2 + (3 + 2) + 3) where
  body := body
  tape := 0
  bound := q.length
  H := fun j => ![((q.take j).flatMap recW).length, 0,
    (out ++ (q.take j).flatMap fun b => recW (a ++ b)).length, 0]
  A := fun j => ![polyWord q ++ tailB, frame (monoBits a) ++ junk,
    overlay (out ++ (q.take j).flatMap fun b => recW (a ++ b)) backing, List.replicate cap false]
  cost := fun j => bodyCost (monoBits a) (monoBits (q.getD j []))
  step := by
    intro j hj
    have h := body_step ((q.take j).flatMap recW) (monoBits q[j])
      ((q.drop (j + 1)).flatMap recW ++ [false] ++ tailB)
      (monoBits a) junk (out ++ (q.take j).flatMap fun b => recW (a ++ b)) backing cap hcap
    have hs : polyWord q ++ tailB = (q.take j).flatMap recW ++ [true] ++ frame (monoBits q[j]) ++
        ((q.drop (j + 1)).flatMap recW ++ [false] ++ tailB) := by
      rw [polyWord_split q j hj]; simp [List.append_assoc]
    rw [← hs] at h
    have hg : q.getD j [] = q[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg]
    refine h.congr ?_ ?_
    · funext i; fin_cases i
      · show _ = ((q.take (j + 1)).flatMap recW).length
        rw [flatMap_take_succ _ _ _ hj]; simp; omega
      · rfl
      · show _ = (out ++ (q.take (j + 1)).flatMap fun b => recW (a ++ b)).length
        rw [flatMap_take_succ _ _ _ hj]; simp [recW, monoBits_append, frame_length]
      · rfl
    · funext i; fin_cases i
      · rfl
      · rfl
      · show _ = overlay (out ++ (q.take (j + 1)).flatMap fun b => recW (a ++ b)) backing
        rw [flatMap_take_succ _ _ _ hj]; simp [recW, monoBits_append, List.append_assoc]
      · rfl
  cont := fun j hj => polyWord_read_marker q tailB j hj
  halt := polyWord_read_end q tailB

/-- **The inner pass**: every product record `a·b`, `b` in `q`, appended to the output; `q`'s cursor ends on its
terminator, the scratch cursor at `0`. -/
theorem loop_run (q : List (List ℕ)) (a : List ℕ) (tailB junk out backing : List Bool) (cap : ℕ)
    (hcap : 2 * (monoBits a).length + 1 ≤ cap) :
    Step (StreamController.machine body 0) (innerCost q (monoBits a))
      ![0, 0, out.length, 0] ![polyWord q ++ tailB, frame (monoBits a) ++ junk, overlay out backing, List.replicate cap false]
      ![(q.flatMap recW).length, 0, (out ++ q.flatMap fun b => recW (a ++ b)).length, 0]
      ![polyWord q ++ tailB, frame (monoBits a) ++ junk, overlay (out ++ q.flatMap fun b => recW (a ++ b)) backing,
        List.replicate cap false] := by
  have h := (loop q a tailB junk out backing cap hcap).run
  have hc : (loop q a tailB junk out backing cap hcap).rest 0 = innerCost q (monoBits a) := by
    simp [Block.WhileBody.rest, loop, innerCost]
  rw [hc] at h
  simp only [loop, List.take_zero, List.flatMap_nil, List.append_nil, List.length_nil, List.take_length] at h
  exact h

end ProdInner

/-! ## One step right -/

namespace Skip

def machine : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .right⟩ else none

theorem run (tape : List Bool) (h : ℕ) : Step machine 1 ![h] ![tape] ![h + 1] ![tape] := by
  have hs : step machine ⟨machine.start, ![h], ![tape]⟩ = some ⟨1, ![h + 1], ![tape]⟩ := by
    simp [step, machine]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, _⟩ := (RecoveryExecution.Timed.single (p := machine) rfl hs).run rfl
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

end Skip

/-! ## The product `p·q`, unreduced: for each monomial `a` of `p`, the records `a·b`, `b` in `q` -/

/-- The product records of one monomial `a` against `q`. -/
def prodRecs (q : List (List ℕ)) (a : List ℕ) : List Bool := q.flatMap fun b => recW (a ++ b)

/-- The scratch tape after the copies of the monomials of `l`. -/
def scrAfter (S0 : List Bool) (l : List (List ℕ)) : List Bool :=
  l.foldl (fun s a => overlay (frame (monoBits a)) s) S0

theorem scrAfter_take_succ (S0 : List Bool) (p : List (List ℕ)) (j : ℕ) (hj : j < p.length) :
    scrAfter S0 (p.take (j + 1)) = overlay (frame (monoBits p[j])) (scrAfter S0 (p.take j)) := by
  unfold scrAfter
  simp only [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The printed product is the unreduced product's word (`ListMachine.pmul p q` is this list). -/
theorem polyWord_prod (p q : List (List ℕ)) :
    polyWord (p.flatMap fun a => q.map fun b => a ++ b) = p.flatMap (prodRecs q) ++ [false] := by
  unfold polyWord
  congr 1
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [List.flatMap_cons, List.flatMap_append, ih, List.flatMap_cons]
    congr 1
    clear ih
    unfold prodRecs
    induction q with
    | nil => rfl
    | cons b q ihq => simp [ihq]

/-- The cost of one outer pass: the marker, the copy of `a` (bits `ma`) with the rewind, the inner pass with the
rewind. -/
def passCost (ma : List Bool) (inner : ℕ) : ℕ := 1 + 1 + (2 * (2 * ma.length + 1) + 2) + 1 + (2 * inner + 2)

/-- The cost of the outer loop over `p`. -/
def outerCost (p q : List (List ℕ)) : ℕ :=
  ((List.range p.length).map fun i =>
    passCost (monoBits (p.getD i [])) (innerCost q (monoBits (p.getD i []))) + 2).sum + 1

/-- The cost of the product machine. -/
def pmulCost (p q : List (List ℕ)) : ℕ := outerCost p q + 1 + 1

namespace ProdOuter

/-- Tapes: 0 the records of `p`, 1 the records of `q`, 2 the scratch, 3 the output, 4 the scratch's log, 5 the log of
`q`'s tape. -/
def slSkip : Fin 1 → Fin 6 := ![0]
def slCopy : Fin 3 → Fin 6 := ![0, 2, 4]
def slIn : Fin 5 → Fin 6 := ![1, 2, 3, 4, 5]
def slEnd : Fin 2 → Fin 6 := ![0, 3]
def selOut : Fin 2 → Bool := ![false, true]
def selB : Fin 4 → Bool := ![true, false, false, false]

noncomputable def inner : Machine 4 (2 + (3 + 2) + 3 + 2) := StreamController.machine ProdInner.body 0
noncomputable def o1 : Machine 6 2 := RecoveryFocus.machine slSkip Skip.machine
noncomputable def o2 : Machine 6 (3 + 2) := RecoveryFocus.machine slCopy (MaskedReset.machine CopyPast.machine selOut)
noncomputable def o3 : Machine 6 (2 + (3 + 2) + 3 + 2 + 2) := RecoveryFocus.machine slIn (MaskedReset.machine inner selB)
/-- **The outer body**: pass `a`'s marker, copy `a` onto the scratch (rewound), run the inner pass (`q` rewound). -/
noncomputable def body : Machine 6 (2 + (3 + 2) + (2 + (3 + 2) + 3 + 2 + 2)) :=
  Composition.machine (Composition.machine o1 o2) o3

theorem slSkip_inj : Function.Injective slSkip := by decide
theorem slCopy_inj : Function.Injective slCopy := by decide
theorem slIn_inj : Function.Injective slIn := by decide
theorem slEnd_inj : Function.Injective slEnd := by decide

theorem dockH_skip (H : Fin 6 → ℕ) (v : Fin 1 → ℕ) : dockH slSkip H v = ![v 0, H 1, H 2, H 3, H 4, H 5] := by
  funext i; fin_cases i
  · exact dockH_slot slSkip slSkip_inj H v 0
  · exact dockH_other slSkip H v 1 (by decide)
  · exact dockH_other slSkip H v 2 (by decide)
  · exact dockH_other slSkip H v 3 (by decide)
  · exact dockH_other slSkip H v 4 (by decide)
  · exact dockH_other slSkip H v 5 (by decide)

theorem install_skip (A : Fin 6 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slSkip A v = ![v 0, A 1, A 2, A 3, A 4, A 5] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slSkip slSkip_inj A v 0
  · exact RecoveryRootRound.install_other slSkip A v 1 (by decide)
  · exact RecoveryRootRound.install_other slSkip A v 2 (by decide)
  · exact RecoveryRootRound.install_other slSkip A v 3 (by decide)
  · exact RecoveryRootRound.install_other slSkip A v 4 (by decide)
  · exact RecoveryRootRound.install_other slSkip A v 5 (by decide)

theorem dockH_copy (H : Fin 6 → ℕ) (v : Fin 3 → ℕ) : dockH slCopy H v = ![v 0, H 1, v 1, H 3, v 2, H 5] := by
  funext i; fin_cases i
  · exact dockH_slot slCopy slCopy_inj H v 0
  · exact dockH_other slCopy H v 1 (by decide)
  · exact dockH_slot slCopy slCopy_inj H v 1
  · exact dockH_other slCopy H v 3 (by decide)
  · exact dockH_slot slCopy slCopy_inj H v 2
  · exact dockH_other slCopy H v 5 (by decide)

theorem install_copy (A : Fin 6 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install slCopy A v = ![v 0, A 1, v 1, A 3, v 2, A 5] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slCopy slCopy_inj A v 0
  · exact RecoveryRootRound.install_other slCopy A v 1 (by decide)
  · exact RecoveryRootRound.install_slot slCopy slCopy_inj A v 1
  · exact RecoveryRootRound.install_other slCopy A v 3 (by decide)
  · exact RecoveryRootRound.install_slot slCopy slCopy_inj A v 2
  · exact RecoveryRootRound.install_other slCopy A v 5 (by decide)

theorem dockH_in (H : Fin 6 → ℕ) (v : Fin 5 → ℕ) : dockH slIn H v = ![H 0, v 0, v 1, v 2, v 3, v 4] := by
  funext i; fin_cases i
  · exact dockH_other slIn H v 0 (by decide)
  · exact dockH_slot slIn slIn_inj H v 0
  · exact dockH_slot slIn slIn_inj H v 1
  · exact dockH_slot slIn slIn_inj H v 2
  · exact dockH_slot slIn slIn_inj H v 3
  · exact dockH_slot slIn slIn_inj H v 4

theorem install_in (A : Fin 6 → List Bool) (v : Fin 5 → List Bool) :
    RecoveryRootRound.install slIn A v = ![A 0, v 0, v 1, v 2, v 3, v 4] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slIn A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slIn slIn_inj A v 0
  · exact RecoveryRootRound.install_slot slIn slIn_inj A v 1
  · exact RecoveryRootRound.install_slot slIn slIn_inj A v 2
  · exact RecoveryRootRound.install_slot slIn slIn_inj A v 3
  · exact RecoveryRootRound.install_slot slIn slIn_inj A v 4

theorem dockH_end (H : Fin 6 → ℕ) (v : Fin 2 → ℕ) : dockH slEnd H v = ![v 0, H 1, H 2, v 1, H 4, H 5] := by
  funext i; fin_cases i
  · exact dockH_slot slEnd slEnd_inj H v 0
  · exact dockH_other slEnd H v 1 (by decide)
  · exact dockH_other slEnd H v 2 (by decide)
  · exact dockH_slot slEnd slEnd_inj H v 1
  · exact dockH_other slEnd H v 4 (by decide)
  · exact dockH_other slEnd H v 5 (by decide)

theorem install_end (A : Fin 6 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slEnd A v = ![v 0, A 1, A 2, v 1, A 4, A 5] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_slot slEnd slEnd_inj A v 0
  · exact RecoveryRootRound.install_other slEnd A v 1 (by decide)
  · exact RecoveryRootRound.install_other slEnd A v 2 (by decide)
  · exact RecoveryRootRound.install_slot slEnd slEnd_inj A v 1
  · exact RecoveryRootRound.install_other slEnd A v 4 (by decide)
  · exact RecoveryRootRound.install_other slEnd A v 5 (by decide)

/-- **One outer pass**: from the record `a` of `p` (cursor on its marker), the scratch receives `a`, and the output
receives every product record `a·b`, `b` in `q`; the cursor of `p` passes `a`, the others return to `0`. -/
theorem body_step (preA tailA : List Bool) (a : List ℕ) (q : List (List ℕ)) (tailB S out backing : List Bool)
    (capS capB : ℕ) (hS : 2 * (monoBits a).length + 1 ≤ capS) (hB : innerCost q (monoBits a) ≤ capB) :
    Step body (passCost (monoBits a) (innerCost q (monoBits a)))
      ![preA.length, 0, 0, out.length, 0, 0]
      ![preA ++ [true] ++ frame (monoBits a) ++ tailA, polyWord q ++ tailB, S, overlay out backing,
        List.replicate capS false, List.replicate capB false]
      ![(preA ++ [true]).length + 2 * (monoBits a).length + 1, 0, 0, (out ++ prodRecs q a).length, 0, 0]
      ![preA ++ [true] ++ frame (monoBits a) ++ tailA, polyWord q ++ tailB, overlay (frame (monoBits a)) S,
        overlay (out ++ prodRecs q a) backing, List.replicate capS false, List.replicate capB false] := by
  -- stage 1: pass the marker
  have h1 := dockRun (Skip.run (preA ++ [true] ++ frame (monoBits a) ++ tailA) preA.length) slSkip slSkip_inj
    ![preA.length, 0, 0, out.length, 0, 0]
    ![preA ++ [true] ++ frame (monoBits a) ++ tailA, polyWord q ++ tailB, S, overlay out backing,
      List.replicate capS false, List.replicate capB false]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_skip, install_skip] at h1
  -- stage 2: copy `a` onto the scratch, its head rewound
  have hc := CopyPast.run (preA ++ [true]) (monoBits a) tailA [] S
  have hm := maskRun hc selOut (by intro i hi; fin_cases i <;> simp_all [selOut]) (by omega : 2 * (monoBits a).length + 1 ≤ capS)
  have h2 := dockRun hm slCopy slCopy_inj
    ![(preA ++ [true]).length, 0, 0, out.length, 0, 0]
    ![preA ++ [true] ++ frame (monoBits a) ++ tailA, polyWord q ++ tailB, S, overlay out backing,
      List.replicate capS false, List.replicate capB false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_copy, install_copy] at h2
  -- stage 3: the inner pass, `q`'s head rewound
  have hl := ProdInner.loop_run q a tailB (S.drop (frame (monoBits a)).length) out backing capS hS
  have hm3 := maskRun hl selB (by intro i hi; fin_cases i <;> simp_all [selB]) hB
  have h3 := dockRun hm3 slIn slIn_inj
    ![(preA ++ [true]).length + 2 * (monoBits a).length + 1, 0, 0, out.length, 0, 0]
    ![preA ++ [true] ++ frame (monoBits a) ++ tailA, polyWord q ++ tailB,
      frame (monoBits a) ++ S.drop (frame (monoBits a)).length, overlay out backing,
      List.replicate capS false, List.replicate capB false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [dockH_in, install_in] at h3
  have h12 := Step.seq h1 (h2.congr_in (by funext i; fin_cases i <;> first | rfl | simp)
    (by funext i; fin_cases i <;> rfl))
  have h123 := Step.seq h12 (h3.congr_in (by funext i; fin_cases i <;> rfl) (by funext i; fin_cases i <;> rfl))
  refine (h123.congr ?_ ?_).enlarge (le_of_eq ?_)
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · simp [passCost]

/-- The outer loop over the monomials of `p`. -/
noncomputable def loop (p q : List (List ℕ)) (preA tailA tailB S0 out backing : List Bool) (capS capB : ℕ)
    (hS : ∀ a ∈ p, 2 * (monoBits a).length + 1 ≤ capS) (hB : ∀ a ∈ p, innerCost q (monoBits a) ≤ capB) :
    Block.WhileBody 6 (2 + (3 + 2) + (2 + (3 + 2) + 3 + 2 + 2)) where
  body := body
  tape := 0
  bound := p.length
  H := fun j => ![(preA ++ (p.take j).flatMap recW).length, 0, 0, (out ++ (p.take j).flatMap (prodRecs q)).length, 0, 0]
  A := fun j => ![preA ++ (polyWord p ++ tailA), polyWord q ++ tailB, scrAfter S0 (p.take j),
    overlay (out ++ (p.take j).flatMap (prodRecs q)) backing, List.replicate capS false, List.replicate capB false]
  cost := fun j => passCost (monoBits (p.getD j [])) (innerCost q (monoBits (p.getD j [])))
  step := by
    intro j hj
    have hmem : p[j] ∈ p := List.getElem_mem hj
    have h := body_step (preA ++ (p.take j).flatMap recW) ((p.drop (j + 1)).flatMap recW ++ [false] ++ tailA) p[j] q
      tailB (scrAfter S0 (p.take j)) (out ++ (p.take j).flatMap (prodRecs q)) backing capS capB (hS _ hmem) (hB _ hmem)
    rw [← stream_split preA tailA p j hj] at h
    have hg : p.getD j [] = p[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg]
    refine h.congr ?_ ?_
    · funext i; fin_cases i
      · show (preA ++ (p.take j).flatMap recW ++ [true]).length + 2 * (monoBits p[j]).length + 1 =
          (preA ++ (p.take (j + 1)).flatMap recW).length
        rw [flatMap_take_succ _ _ _ hj]
        simp only [List.length_append, List.length_singleton, recW_length]
        omega
      · rfl
      · rfl
      · show (out ++ (p.take j).flatMap (prodRecs q) ++ prodRecs q p[j]).length =
          (out ++ (p.take (j + 1)).flatMap (prodRecs q)).length
        rw [flatMap_take_succ _ _ _ hj, List.append_assoc]
      · rfl
      · rfl
    · funext i; fin_cases i
      · rfl
      · rfl
      · show overlay (frame (monoBits p[j])) (scrAfter S0 (p.take j)) = scrAfter S0 (p.take (j + 1))
        rw [scrAfter_take_succ S0 p j hj]
      · show overlay (out ++ (p.take j).flatMap (prodRecs q) ++ prodRecs q p[j]) backing =
          overlay (out ++ (p.take (j + 1)).flatMap (prodRecs q)) backing
        rw [flatMap_take_succ _ _ _ hj, List.append_assoc]
      · rfl
      · rfl
  cont := fun j hj => stream_read_marker preA tailA p j hj
  halt := stream_read_end preA tailA p

/-- **The outer loop**: all product records, `p`'s cursor on its terminator. -/
theorem loop_run (p q : List (List ℕ)) (preA tailA tailB S0 out backing : List Bool) (capS capB : ℕ)
    (hS : ∀ a ∈ p, 2 * (monoBits a).length + 1 ≤ capS) (hB : ∀ a ∈ p, innerCost q (monoBits a) ≤ capB) :
    Step (StreamController.machine body 0) (outerCost p q)
      ![preA.length, 0, 0, out.length, 0, 0]
      ![preA ++ (polyWord p ++ tailA), polyWord q ++ tailB, S0, overlay out backing,
        List.replicate capS false, List.replicate capB false]
      ![(preA ++ p.flatMap recW).length, 0, 0, (out ++ p.flatMap (prodRecs q)).length, 0, 0]
      ![preA ++ (polyWord p ++ tailA), polyWord q ++ tailB, scrAfter S0 p, overlay (out ++ p.flatMap (prodRecs q)) backing,
        List.replicate capS false, List.replicate capB false] := by
  have h := (loop p q preA tailA tailB S0 out backing capS capB hS hB).run
  have hc : (loop p q preA tailA tailB S0 out backing capS capB hS hB).rest 0 = outerCost p q := by
    simp [Block.WhileBody.rest, loop, outerCost]
  rw [hc] at h
  simp only [loop, List.take_zero, List.flatMap_nil, List.append_nil, List.take_length] at h
  exact h

end ProdOuter

/-- **The product machine** (unreduced): the outer loop, then the output's terminator; `p`'s cursor passes its own. -/
noncomputable def pmulM := Composition.machine (StreamController.machine ProdOuter.body 0)
  (RecoveryFocus.machine ProdOuter.slEnd (Mark.machine false))

/-- **The product**: from `p`'s records at its cursor and `q`'s at the start of its tape, the machine appends the word
of the unreduced product `p·q = [a ++ b | a ∈ p, b ∈ q]` (`ListMachine.pmul p q`) at the output cursor; `p`'s cursor
passes `p`, `q`'s and the scratch's return to `0`, the logs are unchanged. -/
theorem pmul_run (p q : List (List ℕ)) (preA tailA tailB S0 out backing : List Bool) (capS capB : ℕ)
    (hS : ∀ a ∈ p, 2 * (monoBits a).length + 1 ≤ capS) (hB : ∀ a ∈ p, innerCost q (monoBits a) ≤ capB) :
    Step pmulM (pmulCost p q)
      ![preA.length, 0, 0, out.length, 0, 0]
      ![preA ++ (polyWord p ++ tailA), polyWord q ++ tailB, S0, overlay out backing,
        List.replicate capS false, List.replicate capB false]
      ![(preA ++ polyWord p).length, 0, 0, (out ++ polyWord (p.flatMap fun a => q.map fun b => a ++ b)).length, 0, 0]
      ![preA ++ (polyWord p ++ tailA), polyWord q ++ tailB, scrAfter S0 p,
        overlay (out ++ polyWord (p.flatMap fun a => q.map fun b => a ++ b)) backing,
        List.replicate capS false, List.replicate capB false] := by
  have h1 := ProdOuter.loop_run p q preA tailA tailB S0 out backing capS capB hS hB
  have h2 := dockRun (Mark.run false (preA ++ (polyWord p ++ tailA)) (preA ++ p.flatMap recW).length
      (out ++ p.flatMap (prodRecs q)) backing) ProdOuter.slEnd ProdOuter.slEnd_inj
    ![(preA ++ p.flatMap recW).length, 0, 0, (out ++ p.flatMap (prodRecs q)).length, 0, 0]
    ![preA ++ (polyWord p ++ tailA), polyWord q ++ tailB, scrAfter S0 p, overlay (out ++ p.flatMap (prodRecs q)) backing,
      List.replicate capS false, List.replicate capB false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [ProdOuter.dockH_end, ProdOuter.install_end] at h2
  refine (Step.seq h1 h2).congr ?_ ?_
  · funext i; fin_cases i
    · show (preA ++ p.flatMap recW).length + 1 = (preA ++ polyWord p).length
      simp only [polyWord, List.length_append, List.length_singleton]
      omega
    · rfl
    · rfl
    · show (out ++ p.flatMap (prodRecs q) ++ [false]).length = (out ++ polyWord _).length
      rw [polyWord_prod, List.append_assoc]
    · rfl
    · rfl
  · funext i; fin_cases i
    · rfl
    · rfl
    · rfl
    · show overlay (out ++ p.flatMap (prodRecs q) ++ [false]) backing = overlay (out ++ polyWord _) backing
      rw [polyWord_prod, List.append_assoc]
    · rfl
    · rfl

end NearCubicWires.WireExponent3_5.ListMachine.Rec
