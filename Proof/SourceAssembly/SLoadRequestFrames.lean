import Proof.SourceAssembly.SLoadMaskFrame

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.RequestFrames
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

theorem ofFn_get_map {α β : Type} (l : List α) (f : α → β) :
    List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn]
  rfl

theorem ofFn_flatten_eq {α : Type} (l : List α) (F : Fin l.length → List Bool)
    (f : α → List Bool) (hF : ∀ i, F i = f (l.get i)) :
    (List.ofFn F).flatten = l.flatMap f := by
  have hFG : F = fun i => f (l.get i) := funext hF
  rw [hFG, ofFn_get_map, ← List.flatMap_def]

/-- The mask worker's support stream is exactly the retained request field:
one retained copy serves both the mask input and the packet input. -/
theorem support_eq (a : DecompositionAlgorithm) (r : Request) :
    (maskData a r).supportWord = r.supportWord a :=
  ofFn_flatten_eq (r.family a).occurrences _
    (fun g => frame (List.ofFn fun i : Fin r.q => decide (i ∈ g.support))) (fun i => rfl)

/-- The framing pass' output word is the packet program's input argument. -/
theorem bundle_eq (a : DecompositionAlgorithm) (r : Request) {work : Nat}
    (B : Fin (5 + work) → List Bool) (hB : B ⟨4, by omega⟩ = (maskData a r).word) :
    Frames.bundle r.nativeWord (r.supportWord a) (B ⟨4, by omega⟩) (r.indexWord a) (r.topWord a)
      = r.input a := by
  rw [Frames.bundle, hB, maskData_word]
  rfl

/-- The nine ambient slots the framing pass occupies: the mask worker's output
slot, a retained unary domain driver, a framing scratch slot, the four retained
request fields, the growing packet-input scratch slot and the shared reset log. -/
def ports {U : Nat} (mskOut drv frm sN sS sI sT out log : Fin U) : Fin 9 → Fin U :=
  ![mskOut, drv, frm, sN, sS, sI, sT, out, log]

/-- The fixed framing program: one raw framer and five frame appenders. -/
noncomputable def machine {U : Nat} (mskOut drv frm sN sS sI sT out log : Fin U) : Machine U 25 :=
  Composition.machine (MaskFrame.machine mskOut drv frm log)
    (Frames.machine sN sS frm sI sT out log)

/-- Fuel for the framing pass, in the physical word lengths. -/
def cost (q n s i t : Nat) : Nat := 4 * q + 4 + 1 + Frames.cost n s q i t

/-- The framing pass on a request. From the mask worker's returned bank and the
four retained framed request fields, the scratch output slot physically holds
`Request.input a r`. -/
theorem request_frames_step {U : Nat} (mskOut drv frm sN sS sI sT out log : Fin U)
    (hinj : Function.Injective (ports mskOut drv frm sN sS sI sT out log))
    (a : DecompositionAlgorithm) (r : Request) {work : Nat}
    (B : Fin (5 + work) → List Bool) (hB : B ⟨4, by omega⟩ = (maskData a r).word)
    (capS capD cap : Nat)
    (cq : 2 * (B ⟨4, by omega⟩).length + 1 ≤ cap)
    (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs : 2 * (r.supportWord a).length + 1 ≤ cap)
    (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hH : ∀ j, H (ports mskOut drv frm sN sS sI sT out log j) = 0)
    (hMask : A mskOut = ZeroPadding.pad capS (B ⟨4, by omega⟩))
    (hDrv : A drv = ZeroPadding.pad capD (List.replicate (B ⟨4, by omega⟩).length true))
    (hFrm : A frm = List.replicate cap false)
    (hN : A sN = ZeroPadding.pad cap (frame r.nativeWord))
    (hS : A sS = ZeroPadding.pad cap (frame (r.supportWord a)))
    (hI : A sI = ZeroPadding.pad cap (frame (r.indexWord a)))
    (hT : A sT = ZeroPadding.pad cap (frame (r.topWord a)))
    (hOut : A out = []) (hLog : A log = List.replicate cap false) :
    Step (machine mskOut drv frm sN sS sI sT out log)
      (cost (B ⟨4, by omega⟩).length r.nativeWord.length (r.supportWord a).length
        (r.indexWord a).length (r.topWord a).length) H A
      (Function.update H out (r.input a).length)
      (Function.update
        (Function.update A frm (ZeroPadding.pad cap (frame (B ⟨4, by omega⟩)))) out (r.input a)) := by
  classical
  have hne : ∀ i j : Fin 9, i ≠ j →
      ports mskOut drv frm sN sS sI sT out log i ≠ ports mskOut drv frm sN sS sI sT out log j :=
    fun i j hij h => hij (hinj h)
  have d01 : mskOut ≠ drv := hne 0 1 (by decide)
  have d02 : mskOut ≠ frm := hne 0 2 (by decide)
  have d08 : mskOut ≠ log := hne 0 8 (by decide)
  have d12 : drv ≠ frm := hne 1 2 (by decide)
  have d18 : drv ≠ log := hne 1 8 (by decide)
  have d28 : frm ≠ log := hne 2 8 (by decide)
  have d27 : frm ≠ out := hne 2 7 (by decide)
  have d37 : sN ≠ out := hne 3 7 (by decide)
  have d47 : sS ≠ out := hne 4 7 (by decide)
  have d57 : sI ≠ out := hne 5 7 (by decide)
  have d67 : sT ≠ out := hne 6 7 (by decide)
  have d38 : sN ≠ log := hne 3 8 (by decide)
  have d48 : sS ≠ log := hne 4 8 (by decide)
  have d58 : sI ≠ log := hne 5 8 (by decide)
  have d68 : sT ≠ log := hne 6 8 (by decide)
  have d78 : out ≠ log := hne 7 8 (by decide)
  have d32 : sN ≠ frm := hne 3 2 (by decide)
  have d42 : sS ≠ frm := hne 4 2 (by decide)
  have d52 : sI ≠ frm := hne 5 2 (by decide)
  have d62 : sT ≠ frm := hne 6 2 (by decide)
  have d72 : out ≠ frm := hne 7 2 (by decide)
  have d82 : log ≠ frm := hne 8 2 (by decide)
  have hH0 : H mskOut = 0 := hH 0
  have hH1 : H drv = 0 := hH 1
  have hH2 : H frm = 0 := hH 2
  have hH3 : H sN = 0 := hH 3
  have hH4 : H sS = 0 := hH 4
  have hH5 : H sI = 0 := hH 5
  have hH6 : H sT = 0 := hH 6
  have hH7 : H out = 0 := hH 7
  have hH8 : H log = 0 := hH 8
  have e0 := MaskFrame.mask_frame_step mskOut drv frm log d01 d02 d08 d12 d18 d28
    capS capD cap cap (B ⟨4, by omega⟩) cq H A hH0 hH1 hH2 hH8 hMask hDrv hFrm hLog
  have e1 := Frames.frames_step sN sS frm sI sT out log
    d37 d47 d27 d57 d67 d38 d48 d28 d58 d68 d78
    cap r.nativeWord (r.supportWord a) (B ⟨4, by omega⟩) (r.indexWord a) (r.topWord a)
    cn cs cq ci ct H (Function.update A frm (ZeroPadding.pad cap (frame (B ⟨4, by omega⟩))))
    hH3 hH4 hH2 hH5 hH6 hH7 hH8
    (by rw [Function.update_of_ne d32]; exact hN)
    (by rw [Function.update_of_ne d42]; exact hS)
    (by rw [Function.update_self])
    (by rw [Function.update_of_ne d52]; exact hI)
    (by rw [Function.update_of_ne d62]; exact hT)
    (by rw [Function.update_of_ne d72]; exact hOut)
    (by rw [Function.update_of_ne d82]; exact hLog)
  rw [bundle_eq a r B hB] at e1
  have joined := e0.seq e1
  exact joined.congr rfl rfl

end
end SLoad.RequestFrames
