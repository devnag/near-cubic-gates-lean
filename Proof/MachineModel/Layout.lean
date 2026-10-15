import Proof.MachineModel.Runs
import Proof.MachineModel.Semantics
import Proof.Circuits.DecompositionSourceRecords

/-! P25: the fixed finite layout of the ordered decomposition-source batch.

Tapes: the whole single-request source bank of `DecompositionSource.Counted`
(unchanged, reused as-is) followed by twelve named ports. The layout, the slot
maps and the machine below depend only on `a`; nothing depends on `q`, on the
occurrence list, or on any source output. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)

abbrev SB := Counted.tapes a
abbrev T := SB a + 12

def bk (i : Fin (SB a)) : Fin (T a) := i.castAdd 12
def ex (i : Fin 12) : Fin (T a) := i.natAdd (SB a)

@[simp] theorem bk_val (i : Fin (SB a)) : (bk a i).val = i.val := rfl
@[simp] theorem ex_val (i : Fin 12) : (ex a i).val = SB a + i.val := rfl

theorem bk_injective : Function.Injective (bk a) := by
  intro i j h; exact Fin.ext (by simpa using congrArg (fun k : Fin (T a) => k.val) h)
theorem ex_injective : Function.Injective (ex a) := by
  intro i j h
  have hv := congrArg (fun k : Fin (T a) => k.val) h
  simp only [ex_val] at hv
  exact Fin.ext (by omega)
theorem bk_ne_ex (i : Fin (SB a)) (j : Fin 12) : bk a i ≠ ex a j := by
  intro h
  have hv := congrArg (fun k : Fin (T a) => k.val) h
  simp only [bk_val, ex_val] at hv
  have := i.isLt
  omega

/-! ## Named ports -/

def str := ex a 0   -- circuit stream
def cnt := ex a 1   -- occurrence counts, `counts.flatMap natWord`
def bod := ex a 2   -- child body, `GS.flatMap exactWord`
def tot := ex a 3   -- unary total, `false :: 1^m`, head at its end
def cch := ex a 4   -- native child cache
def una := ex a 5   -- `replicate B true`, head 0
def scr := ex a 6   -- incidence row scratch
def fcp := ex a 7   -- framed-copy marker counter
def drv := ex a 8   -- erase driver, `replicate C true`
def wsp := ex a 9   -- erase workspace
def dom := ex a 10  -- retained domain template `UnaryTemplate.tape q`, head 1
def hdr := ex a 11  -- header staging

/-! ## Bank ports, and the value arithmetic that separates them -/

def bin := bk a (Counted.localTape a 0)          -- framed native request word
def bsrc := bk a (Counted.sourceTape a)          -- source output `exactListWord children`
def bfld := bk a (Counted.localTape a 14)        -- reusable field/record backing
def bcnt := bk a (Counted.fresh a 9)             -- child-count template

theorem out_val : (Counted.sourceTape a).val = 16 + (Call.sourceProgram a).outputTape.val := by
  have hf := (Call.sourceProgram a).outputFresh
  simp only [Counted.sourceTape, Counted.old, Call.outputTape, Call.slots, hf, if_false,
    Fin.val_castAdd, Fin.val_natAdd]
theorem local_val (i : Fin 16) : (Counted.localTape a i).val = i.val := rfl
theorem fresh_val (i : Fin 11) : (Counted.fresh a i).val = Call.tapes a + i.val := rfl
theorem out_lt : (Call.sourceProgram a).outputTape.val < (Call.sourceProgram a).tapeCount :=
  (Call.sourceProgram a).outputTape.isLt

/-! ## Docking with an already matching ambient -/

theorem dockH_existing {t u : ℕ} (slots : Fin t → Fin u) (ambient : Fin u → ℕ) (local' : Fin t → ℕ)
    (h : ∀ j, ambient (slots j) = local' j) : dockH slots ambient local' = ambient := by
  classical
  funext i
  unfold dockH
  cases hp : RecoveryFocus.pick slots i with
  | none => rfl
  | some j =>
    have hs := RecoveryFocus.slot_of_pick slots hp
    rw [← hs, h j]

/-- One docked stage at an ambient that already carries its input. -/
theorem Step.dock {t u s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout)
    (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have hfoc := h.focus slots hi H A
  rw [dockH_existing slots H hin hH, install_existing slots A tin hA] at hfoc
  exact hfoc

/-! ## Padding helpers used by the bank stages -/

theorem pad_replicate_false (cap k : ℕ) (h : k ≤ cap) :
    ZeroPadding.pad cap (List.replicate k false) = List.replicate cap false := by
  rw [Rewind.Workspace.pad_zeros]
  congr 1
  omega

theorem pad_template (cap k : ℕ) (h : k+2 ≤ cap) :
    ZeroPadding.pad cap (RepairSource.VerifierDecoding.CompareMachine.word k) =
      ZeroPadding.pad cap (UnaryTemplate.tape k) := by
  have hw : (RepairSource.VerifierDecoding.CompareMachine.word k).length = k+1 := by
    simp [RepairSource.VerifierDecoding.CompareMachine.word]
  have ht : UnaryTemplate.tape k = RepairSource.VerifierDecoding.CompareMachine.word k ++ [false] := by
    simp [UnaryTemplate.tape, RepairSource.VerifierDecoding.CompareMachine.word]
  rw [ht]
  simp only [ZeroPadding.pad, hw, List.length_append, List.length_singleton, List.append_assoc]
  congr 1
  have : cap - (k+1) = 1 + (cap - (k+1+1)) := by omega
  rw [this, List.replicate_add]
  rfl

theorem pad_exact (cap : ℕ) (w : List Bool) :
    ZeroPadding.pad cap w = w ++ List.replicate (cap - w.length) false := rfl

end NearCubicWires.ExtDecompositionBatch
