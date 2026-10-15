import Proof.Gates.Setup.CompSpec
import Proof.Gates.Worker.TermsGlue
import Proof.Gates.WorkerArith.TermDefs
import Proof.Gates.WorkerArith.HeaderDefs

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)

noncomputable section

/-! ## The set-up data -/

/-- The tape count of a machine. -/
abbrev tapesOf {t st : ℕ} (_ : Machine t st) : ℕ := t

/-- The sizes the loop entry holds (they bound the term loop's work). -/
noncomputable def setupSizeOf (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) (N0 : ℕ) {N : ℕ}
    (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)) : ℕ :=
  let w := Codec.prefixBits bits (N / 16) ++ List.replicate pad false
  let p0 := 2 * (Worker.Format.readCount w).1 + 1
  let p1 := p0 + 2 * (Worker.Format.readCount (w.drop p0)).1 + 1
  N + pad + N0 + width s g N + gadgets s g N + ((pcpp s P g x B).proofBits + gadgets s g N) +
    (pcpp s P g x B).randomBits + (pcpp s P g x B).word.length + (supportsWord P.code (width s g N)).length +
    (Codec.cwPrefix (Codec.circAt w (width s g N) p1) ((pcpp s P g x B).proofBits + gadgets s g N)).length +
    (mwWord s g N B.src).length + (PCPPNative.descriptor B.src).length + (PCPPNative.descriptor B.pf).length +
    Worker.nu N ^ (g.lenRoot + 1)

structure SetupData (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  cf : CompFull s P g
  tA : ℕ

  flag : Fin tA
  tc : ℕ
  N0 : ℕ
  hN0 : ∀ N, N0 ≤ N → 4 ≤ N ∧ (width s g N).bits.length ≤ N + 1
  /-- The register capacity of the common prefix (before the flag). -/
  capA : ℕ → ℕ → ℕ
  /-- The register capacity the set-up needs. -/
  setupCap : ∀ {N : ℕ}, BitInput N → List Bool → ℕ → Outer.OuterGuess (width s g N) → ℕ
  /-- The cost of the rejecting runs. -/
  rejectCost : ∀ {N : ℕ}, BitInput N → List Bool → ℕ → ℕ
  /-- The cost of the set-up to loop entry. -/
  setupCost : ∀ {N : ℕ}, BitInput N → List Bool → ℕ → Outer.OuterGuess (width s g N) → ℕ
  sizeLe : ∀ {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N)),
    setupSizeOf s P g N0 x bits pad B ≤ setupCost x bits pad B

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- The number of streams minus one (the last `46` streams: a blank tail block, room for the verdict machine's work
tapes at the loop exit). -/
def nsW (D : SetupData s P g) : ℕ := 15 + D.tA + D.cf.t + D.tc + 46

/-- The number of registers. -/
abbrev nrW : ℕ := 128

/-! ## Streams -/

section Streams
variable (D : SetupData s P g)

def fixS (i : ℕ) (h : i < 16) : Fin (nsW D + 1) := ⟨i, by unfold nsW; omega⟩

def sX : Fin (nsW D + 1) := fixS D 0 (by decide)
def sBW : Fin (nsW D + 1) := fixS D 1 (by decide)
def sWT : Fin (nsW D + 1) := fixS D 2 (by decide)
def sCW : Fin (nsW D + 1) := fixS D 3 (by decide)
def sVI : Fin (nsW D + 1) := fixS D 4 (by decide)
def sS1 : Fin (nsW D + 1) := fixS D 5 (by decide)
def sS2 : Fin (nsW D + 1) := fixS D 6 (by decide)
def sTL : Fin (nsW D + 1) := fixS D 7 (by decide)
def sG : Fin (nsW D + 1) := fixS D 8 (by decide)
def sL : Fin (nsW D + 1) := fixS D 9 (by decide)

/-- The block of the set-up's donors before the composite. -/
def aB (j : Fin D.tA) : Fin (nsW D + 1) := ⟨16 + j.val, by have := j.isLt; unfold nsW; omega⟩
/-- The composite's block. -/
def kB (j : Fin D.cf.t) : Fin (nsW D + 1) :=
  ⟨16 + D.tA + j.val, by have := j.isLt; unfold nsW; omega⟩
/-- The counter's block (blank at loop entry). -/
def cB (j : Fin D.tc) : Fin (nsW D + 1) :=
  ⟨16 + D.tA + D.cf.t + j.val, by have := j.isLt; unfold nsW; omega⟩

def sJ : Fin (nsW D + 1) := kB D D.cf.wOut
/-- The supports record (the composite's supports port). -/
def sSUP : Fin (nsW D + 1) := kB D D.cf.sOut

def sFL : Fin (nsW D + 1) := aB D D.flag

def regE : Fin 40 ↪ Fin nrW := ⟨fun i => ⟨i.val, by have := i.isLt; show i.val < 128; omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

def termEnv : WorkerArith.TermEnv (nsW D) nrW where
  CW := sCW D
  SUP := sSUP D
  S1 := sS1 D
  S2 := sS2 D
  TL := sTL D
  G := sG D
  L := sL D
  VI := sVI D
  WT := sWT D
  R := regE

end Streams

/-! ## Registers -/

abbrev rN : Fin nrW := 40
abbrev rM : Fin nrW := 41
abbrev rRB : Fin nrW := 42
abbrev rCL : Fin nrW := 43
abbrev rSC : Fin nrW := 44
abbrev rA : Fin nrW := 45
abbrev rLC : Fin nrW := 46
abbrev rPB : Fin nrW := 47

/-! ## The guess word and its decoded data -/

/-- **The guess word**: the first `⌊N/16⌋` witness bits (blanks past the end of `bits`), then `pad` blanks. The
machine copies only the first `⌊N/16⌋` bits; the blanks are not written (every stream reads blank past its end), so
`pad` is a free parameter of the ideal state, chosen by the consumer so that every field it reads is physical. -/
def guessWord (N : ℕ) (bits : List Bool) (pad : ℕ) : List Bool :=
  Codec.prefixBits bits (N / 16) ++ List.replicate pad false

/-- The position after one circuit field (`readField`: a unary count `ℓ`, then `ℓ` bits). -/
def oracleEnd (w : List Bool) : ℕ := 2 * (Worker.Format.readCount w).1 + 1

/-- The position after the two circuit fields of the pair `(B_src, B_pf)`. -/
def pairEnd (w : List Bool) : ℕ := oracleEnd w + oracleEnd (w.drop (oracleEnd w))

/-- The rest after the two circuit fields is the word after `pairEnd w`. -/
theorem pairEnd_drop (w : List Bool) :
    (Worker.Format.readField (Worker.Format.readField w).2).2 = w.drop (pairEnd w) := by
  rw [Worker.Format.readField_snd, Worker.Format.readField_snd w, List.drop_drop]
  unfold pairEnd oracleEnd
  rfl

/-- The canonical code-support rows at width `q` (`Worker.RowsOK`). -/
noncomputable def suppRows (P : ThreeQueryPCPP) (q : ℕ) (j : ℕ) : List ℕ :=
  if h : j < P.code.length q then (canonList (P.code.support q ⟨j, h⟩)).map Fin.val else []

section Decoded
variable (s P g)
variable {N : ℕ} (x : BitInput N) (B : Outer.OuterGuess (width s g N))

/-- The number of auxiliary names: proof coordinates and one helper per gadget. -/
noncomputable def auxN : ℕ := (pcpp s P g x B).proofBits + gadgets s g N

noncomputable def headerOf : List Bool :=
  marks (WorkerArith.headerWord (width s g N) (gadgets s g N) (nu N ^ (g.lenRoot + 1)) (pcpp s P g x B).randomBits
    (clauseWidth g.clauseDegree (width s g N)))

end Decoded

/-! ## The loop-entry state -/

section Entry
variable (D : SetupData s P g)

open Classical in

noncomputable def LoopEntry (N : ℕ) (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) (jk : Fin (nsW D + 1) → List Bool) : WState (nsW D) nrW :=
  let w := guessWord N bits pad
  let q := width s g N
  let p0 := pairEnd w
  let raw := pcpp s P g x B
  let aux := auxN s P g x B
  let cw := Codec.cwPrefix (Codec.circAt w q p0) aux
  let hd := headerOf s P g x B
  let L := P.code.length q
  { st := fun i =>
      if i = sX D then RepairOrdinary.frame (List.ofFn x)
      else if i = sBW D then RepairOrdinary.frame bits
      else if i = sWT D then w
      else if i = sCW D then cw
      else if i = sVI D then hd
      else if i = sJ D then raw.word
      else if i = sSUP D then RepairOrdinary.frame (supportsWord P.code q)
      else if i = sFL D then [true]
      else if i.val < 16 ∨ 16 + D.tA + D.cf.t ≤ i.val then []
      else jk i
    sh := fun i =>
      if i = sWT D then Codec.circPos w q p0 aux
      else if i = sVI D then hd.length
      else 0
    val := fun r =>
      if r = regE 6 then q
      else if r = regE 7 then cw.length
      else if r = regE 8 then (Codec.rowPrefix (suppRows P q) L).length
      else if r = regE 9 then hd.length
      else if r = rN then N
      else if r = rM then gadgets s g N
      else if r = rRB then raw.randomBits
      else if r = rCL then clauseWidth g.clauseDegree q
      else if r = rSC then q + L
      else if r = rLC then gadgets s g N
      else if r = rPB then raw.proofBits
      else 0
    cell := false }

/-- The cold start (the shared `Verifier.inputTapes`): `frame x` on stream `0`, `frame bits` on stream `1`, every
other stream blank, every head and register `0`, the result cell `false`. -/
def coldState (xs bits : List Bool) : WState (nsW D) nrW where
  st := fun i => if i = sX D then RepairOrdinary.frame xs else if i = sBW D then RepairOrdinary.frame bits else []
  sh := fun _ => 0
  val := fun _ => 0
  cell := false

end Entry

/-! ## Sizes, capacity and cost -/

section Cost
variable (D : SetupData s P g)

/-- The capacity and cost scale of the common prefix (before the flag). -/
noncomputable def capA (N pad : ℕ) : ℕ := D.capA N pad

/-- The sizes the set-up reads and writes. -/
noncomputable def setupSize {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) : ℕ :=
  setupSizeOf s P g D.N0 x bits pad B

/-- The register capacity the set-up needs. -/
noncomputable def setupCap {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) : ℕ := D.setupCap x bits pad B

/-- The cost of the rejecting runs. -/
noncomputable def rejectCost {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) : ℕ := D.rejectCost x bits pad

/-- The cost of the set-up to loop entry. -/
noncomputable def setupCost {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) : ℕ := D.setupCost x bits pad B

theorem setupSize_le_setupCost {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N)) : setupSize D x bits pad B ≤ setupCost D x bits pad B :=
  D.sizeLe x bits pad B

end Cost

/-! ## The statement -/

def SetupSpec (D : SetupData s P g) (prog : WMX (nsW D) nrW) : Prop :=
  ∀ (N : ℕ) (x : BitInput N) (bits : List Bool) (pad cap : ℕ), N / 16 + 1 ≤ pad → capA D N pad ≤ cap →
    (∀ B : Outer.OuterGuess (width s g N), D.N0 ≤ N →
        Worker.Decodes (width s g N) (guessWord N bits pad) B →
        PairOK s g x B →
        setupCap D x bits pad B ≤ cap →
        ∃ jk τ, WXExec cap prog (coldState D (List.ofFn x) bits) τ (setupCost D x bits pad B) ∧
          SimW (LoopEntry D N x bits pad B jk) τ) ∧
    ((N < D.N0 ∨ Worker.setupFlag s P g N x (guessWord N bits pad) = false) →
        ∃ τ, WXExec cap prog (coldState D (List.ofFn x) bits) τ (rejectCost D x bits pad) ∧
          readTapeBit (τ.st (sFL D)) (τ.sh (sFL D)) = false ∧ τ.cell = false)

end

end NearCubicGates.Close.Setup
