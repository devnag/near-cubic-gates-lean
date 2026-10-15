import Proof.SourceAssembly.SLoadRequestFrames
import Proof.Assembly.AppendOutputFrame
import Proof.Amplification.RecoveryPCPFormulaResumeForward

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.SuffixFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- A `Step` receipt is deterministic: the machine, fuel and entry
configuration already fix the exit heads and the exit bank. This is what lets
`Ready`'s `ambientA`, which is bound OUTSIDE its `∀ B`, be chosen from one
compatible mask bank. -/
theorem step_det {t s : Nat} {p : Machine t s} {n : Nat} {hin : Fin t → Nat}
    {tin : Fin t → List Bool} {h1 h2 : Fin t → Nat} {t1 t2 : Fin t → List Bool}
    (x : Step p n hin tin h1 t1) (y : Step p n hin tin h2 t2) : h1 = h2 ∧ t1 = t2 := by
  obtain ⟨r1, hr1, hh1, ht1, _⟩ := x
  obtain ⟨r2, hr2, hh2, ht2, _⟩ := y
  have hrr : r1 = r2 := Option.some.inj (hr1.symm.trans hr2)
  subst hrr
  exact ⟨hh1.symm.trans hh2, ht1.symm.trans ht2⟩

/-- The framing pass of `SLoadRequestFrames`, on its own nine local tapes:
mask output, unary mask driver, framing scratch, the four retained request
fields, the growing packet-input scratch and the shared reset log. -/
def raw : Machine 9 25 := RequestFrames.machine 0 1 2 3 4 5 6 7 8

theorem ports_injective :
    Function.Injective (RequestFrames.ports (0 : Fin 9) 1 2 3 4 5 6 7 8) := by
  have h : ∀ x y : Fin 9, RequestFrames.ports (0 : Fin 9) 1 2 3 4 5 6 7 8 x
      = RequestFrames.ports (0 : Fin 9) 1 2 3 4 5 6 7 8 y → x = y := by decide
  exact fun x y hxy => h x y hxy

/-- One frame-append stage never moves the shared output cursor left. -/
theorem stage_forward (s : Fin 9) (h7 : s ≠ 7) (h8 : s ≠ 8) :
    RepairSource.ProjectionNormalization.CursorRestore.NoLeft
      (Frames.stage s (7 : Fin 9) 8) 7 := by
  have hinj := SLoad.triple_injective s (7 : Fin 9) 8 h7 h8 (by decide)
  exact RepairSource.ProjectionNormalization.CursorRestore.focus_forward
    (Frames.ports s (7 : Fin 9) 8) hinj CompetitorFrameAppend.machine 1
    RepairSource.RecoveryPCPFormulaResumeForward.field_append

/-- The whole framing pass is append-only on its packet-input scratch tape:
the mask framer never touches it, and each of the five frame appenders only
streams it rightwards. -/
theorem raw_forward :
    RepairSource.ProjectionNormalization.CursorRestore.NoLeft raw 7 := by
  have hmask : RepairSource.ProjectionNormalization.CursorRestore.NoLeft
      (MaskFrame.machine (0 : Fin 9) 1 2 8) 7 :=
    EquationRowCuts.unselected_forward (![(0 : Fin 9), 1, 2, 8]) AppendFrameKernel.machine 7
      (by decide)
  have h3 := stage_forward 3 (by decide) (by decide)
  have h4 := stage_forward 4 (by decide) (by decide)
  have h2 := stage_forward 2 (by decide) (by decide)
  have h5 := stage_forward 5 (by decide) (by decide)
  have h6 := stage_forward 6 (by decide) (by decide)
  have hframes : RepairSource.ProjectionNormalization.CursorRestore.NoLeft
      (Frames.machine (3 : Fin 9) 4 2 5 6 7 8) 7 :=
    RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _ h3
      (RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _ h4
        (RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _ h2
          (RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _ h5 h6)))
  exact RepairSource.ProjectionNormalization.CursorRestore.composition_forward _ _ _ hmask hframes

/-- The framed suffix program: the framing pass, its paid output measurement
and its paid output framer, all with numeral tape and state counts. -/
def wrapper : Machine 13 34 := AppendOutputFrame.machine raw 7

/-- The docked suffix program. -/
def machine {U : Nat} (slot : Fin 13 → Fin U) : Machine U 34 :=
  RecoveryFocus.machine slot wrapper

/-- The nine physical entry tapes of the framing pass. -/
def rawEntry (capS capD cap : Nat) (mw nw sw iw tw : List Bool) : Fin 9 → List Bool :=
  ![ZeroPadding.pad capS mw,
    ZeroPadding.pad capD (List.replicate mw.length true),
    List.replicate cap false,
    ZeroPadding.pad cap (frame nw),
    ZeroPadding.pad cap (frame sw),
    ZeroPadding.pad cap (frame iw),
    ZeroPadding.pad cap (frame tw),
    [],
    List.replicate cap false]

/-- The thirteen physical entry tapes of the suffix: the nine above, plus the
measurement counter, its rewind log, the framed packet tape and the framer's
own rewind log, all blank. -/
def entry (capS capD cap : Nat) (mw nw sw iw tw : List Bool) : Fin 13 → List Bool :=
  ![ZeroPadding.pad capS mw,
    ZeroPadding.pad capD (List.replicate mw.length true),
    List.replicate cap false,
    ZeroPadding.pad cap (frame nw),
    ZeroPadding.pad cap (frame sw),
    ZeroPadding.pad cap (frame iw),
    ZeroPadding.pad cap (frame tw),
    [],
    List.replicate cap false,
    [], [], [], []]

theorem entry_eq (capS capD cap : Nat) (mw nw sw iw tw : List Bool) :
    AppendOutputFrame.input (rawEntry capS capD cap mw nw sw iw tw)
      = entry capS capD cap mw nw sw iw tw := by
  funext i
  fin_cases i <;> rfl

/-- Fuel for the suffix, in the five actual physical word lengths. -/
def cost (q n s i t : Nat) : Nat := 8 * q + 16 * (n + s + q + i + t) + 75

theorem cost_eq (q n s i t : Nat) :
    2 * RequestFrames.cost q n s i t + 4 * (2 * (n + s + q + i + t) + 5) + 7 = cost q n s i t := by
  simp only [RequestFrames.cost, Frames.cost, cost]
  omega

/-- The assembled packet input word has the length the five retained physical
words give it. -/
theorem input_length (a : DecompositionAlgorithm) (r : Request) {work : Nat}
    (B : Fin (5 + work) → List Bool) (hB : B ⟨4, by omega⟩ = (maskData a r).word) :
    (r.input a).length = 2 * (r.nativeWord.length + (r.supportWord a).length
      + (B ⟨4, by omega⟩).length + (r.indexWord a).length + (r.topWord a).length) + 5 := by
  rw [← RequestFrames.bundle_eq a r B hB, Frames.bundle]
  simp only [List.length_append, frame_length]
  omega

/-- The suffix's physical run. From the mask worker's returned bank and the
four retained framed request fields, one ambient slot physically holds
`frame (r.input a)`, every ambient head is back where it started, and no
ambient tape outside the suffix's own thirteen slots is touched. -/
theorem suffix_step {U : Nat} (slot : Fin 13 → Fin U) (hinj : Function.Injective slot)
    (a : DecompositionAlgorithm) (r : Request) {work : Nat}
    (B : Fin (5 + work) → List Bool) (hB : B ⟨4, by omega⟩ = (maskData a r).word)
    (capS capD cap : Nat)
    (cq : 2 * (B ⟨4, by omega⟩).length + 1 ≤ cap)
    (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs : 2 * (r.supportWord a).length + 1 ≤ cap)
    (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ j, H (slot j) = 0)
    (hA : ∀ j, A (slot j) = entry capS capD cap (B ⟨4, by omega⟩) r.nativeWord
      (r.supportWord a) (r.indexWord a) (r.topWord a) j) :
    ∃ F : Fin U → List Bool,
      Step (machine slot)
        (cost (B ⟨4, by omega⟩).length r.nativeWord.length (r.supportWord a).length
          (r.indexWord a).length (r.topWord a).length) H A H F ∧
      F (slot 11) = frame (r.input a) ∧
      (∀ x, (∀ j, slot j ≠ x) → F x = A x) := by
  classical
  have hraw := RequestFrames.request_frames_step (0 : Fin 9) 1 2 3 4 5 6 7 8 ports_injective
    a r B hB capS capD cap cq cn cs ci ct (fun _ => 0)
    (rawEntry capS capD cap (B ⟨4, by omega⟩) r.nativeWord (r.supportWord a)
      (r.indexWord a) (r.topWord a))
    (fun j => rfl) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨rec0, hrun0, hh0, ht0, hs0⟩ := hraw
  have hrun : run raw
      (RequestFrames.cost (B ⟨4, by omega⟩).length r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length)
      (rawEntry capS capD cap (B ⟨4, by omega⟩) r.nativeWord (r.supportWord a)
        (r.indexWord a) (r.topWord a)) = some rec0 := hrun0
  have htape : rec0.final.tapes 7 = r.input a := by
    rw [ht0, Function.update_self]
  have hhead : rec0.final.heads 7 = (r.input a).length := by
    rw [hh0, Function.update_self]
  obtain ⟨res, hres, hframe, hheads, hsteps⟩ :=
    AppendOutputFrame.frame_run raw 7 raw_forward _ _ rec0 hrun (r.input a) htape hhead
  have hstep0 : Step wrapper (2 * rec0.steps + 4 * (r.input a).length + 7) (fun _ => 0)
      (AppendOutputFrame.input (rawEntry capS capD cap (B ⟨4, by omega⟩) r.nativeWord
        (r.supportWord a) (r.indexWord a) (r.topWord a))) (fun _ => 0) res.final.tapes :=
    Step.of_run hres (funext hheads) rfl
  have hlen := input_length a r B hB
  have hle : 2 * rec0.steps + 4 * (r.input a).length + 7
      ≤ cost (B ⟨4, by omega⟩).length r.nativeWord.length (r.supportWord a).length
          (r.indexWord a).length (r.topWord a).length := by
    rw [hlen, ← cost_eq]
    simp only [RequestFrames.cost, Frames.cost] at hs0 ⊢
    omega
  have hstep1 := hstep0.enlarge hle
  rw [entry_eq] at hstep1
  have hfoc := hstep1.focus slot hinj H A
  rw [SLoad.dockH_existing slot H (fun _ => 0) hH,
    install_existing slot A _ (fun j => hA j)] at hfoc
  refine ⟨install slot A res.final.tapes, hfoc, ?_, ?_⟩
  · rw [install_slot slot hinj]
    have h11 : ((0 : Fin 2).natAdd (9 + 2) : Fin 13) = 11 := rfl
    rw [h11] at hframe
    exact hframe
  · intro x hx
    exact install_other slot A res.final.tapes x hx

end
end SLoad.SuffixFrame
