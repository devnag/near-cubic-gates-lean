import Proof.Wire_3_5.PrimAsmWriterIface

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- **The writers' output bank, v2**: `frame w` kept on the input tape, the tape word `v` on the output tape, the
residue `J j` on every other tape. -/
def outBankJ {t : ℕ} (i o : Fin t) (w v : List Bool) (J : Fin t → List Bool) : Fin t → List Bool :=
  fun j => if j = i then frame w else if j = o then v else J j

theorem outBankJ_in {t : ℕ} (i o : Fin t) (w v : List Bool) (J : Fin t → List Bool) : outBankJ i o w v J i = frame w := by
  simp [outBankJ]

theorem outBankJ_out {t : ℕ} (i o : Fin t) (hio : i ≠ o) (w v : List Bool) (J : Fin t → List Bool) :
    outBankJ i o w v J o = v := by
  simp [outBankJ, Ne.symm hio]

theorem outBank_eq_J {t : ℕ} (i o : Fin t) (w v : List Bool) : outBank i o w v = outBankJ i o w v (fun _ => []) := rfl

/-- **A writer's run, v2**: from `inBank i w`, within `B` steps, the machine halts with every head at `0`, the input
kept, `v` on the output tape and residues of length at most `B` elsewhere. -/
def WriterRun {t s : ℕ} (M : Machine t s) (B : ℕ) (i o : Fin t) (w v : List Bool) : Prop :=
  ∃ J : Fin t → List Bool, (∀ j, (J j).length ≤ B) ∧ ClockJoin.ReadyRun M B (inBank i w) (outBankJ i o w v J)

theorem WriterRun.of_ready {t s : ℕ} {M : Machine t s} {B : ℕ} {i o : Fin t} {w v : List Bool}
    (h : ClockJoin.ReadyRun M B (inBank i w) (outBank i o w v)) : WriterRun M B i o w v :=
  ⟨fun _ => [], fun _ => Nat.zero_le _, h⟩

section Writers
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EW : Envelope) (cW kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM batch writer, v2**: `frame req.word ↦ symTape`, within the preprocessing class, residues allowed. -/
structure SymWriterAtJ extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      WriterRun M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n)) inS outS
        (symReq n a' ha' Cs carriers translation).word
        (symTape (callInputs l F kclk coef A a ha) hs Cs carriers)

/-- **The THR batch writer, v2**: `frame (req.word ++ frame hashBits) ↦ thrTape`, residues allowed. -/
structure ThrWriterAtJ extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      WriterRun M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n)) inS outS
        ((thrReq n a' ha' Cs carriers translation).word ++
          frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
            (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
            ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
            (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
            (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
            (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
            (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))))
        (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)

/-- **The HASH row writer, v2** (for C4.Hb): `frame req.word ↦ hashTape`, residues allowed. -/
structure HashWriterAtJ extends WriterStage where
  ready : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      WriterRun M (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
          (((gate0 l F).budget kclk coef A a ha).psiOf n)) inS outS
        (thrReq n a' ha' Cs carriers translation).word
        (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)

/-- The three writers at one call family, v2. -/
structure WritersAtJ where
  sym : SymWriterAtJ l F EW cW kclk coef A a ha
  thr : ThrWriterAtJ l F EW cW kclk coef A a ha
  hash : HashWriterAtJ l F EW cW kclk coef A a ha

/-- The v1 writers are v2 writers (the residues empty). -/
def WritersAt.toJ (W : WritersAt l F EW cW kclk coef A a ha) : WritersAtJ l F EW cW kclk coef A a ha where
  sym := { W.sym.toWriterStage with ready := fun n a' ha' Cs c tr hc hs => WriterRun.of_ready (W.sym.ready n a' ha' Cs c tr hc hs) }
  thr := { W.thr.toWriterStage with ready := fun n a' ha' Cs c tr hc hs => WriterRun.of_ready (W.thr.ready n a' ha' Cs c tr hc hs) }
  hash := { W.hash.toWriterStage with
    ready := fun n a' ha' Cs c tr hc hs => WriterRun.of_ready (W.hash.ready n a' ha' Cs c tr hc hs) }

end Writers

/-- **PA's (d) deliverable, v2**, in `SeedFixLeaf`'s order of choice: after the endpoint exponent `fe`, the writers'
floors `E_W` (powers of `n`, `c_r`-free); for every admissible `F`, a coefficient `c_W` and the three
writers at every clock and source work. -/
def WriterLeafJ (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Cost.Envelope, ∀ F : Split.GateFree l, F.filterErrDeg = fe → PrimAsm.Plan.ClassLE EW F.E →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), WritersAtJ l F EW cW kclk coef A a ha

end NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ
