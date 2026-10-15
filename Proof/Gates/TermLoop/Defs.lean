import Proof.Gates.Setup.Entry
import Proof.Gates.Worker.Loop
import Proof.Gates.Worker.Terms
import Proof.Gates.Worker.Load
import Proof.Gates.Worker.TermModelLink
import Proof.Gates.CheckedPCPP.ClauseFront
import Proof.Gates.WorkerArith.Header

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd)
open NearCubicGates.Close.WorkerArith (termW1 termW2 entryWord bud1 bud2 termCost TermFit closeW)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)

noncomputable section

/-! ## Witness fields -/

/-- The end of the witness field at position `p` (a unary count `1^ℓ 0`, then `ℓ` bits). -/
def fieldEnd (w : List Bool) (p : ℕ) : ℕ := p + Codec.fieldLen w p + 1 + Codec.fieldLen w p

/-- The position of witness field `k` after position `p`. -/
def fieldPos (w : List Bool) (p k : ℕ) : ℕ := Codec.iter (fieldEnd w) p k

/-- Witness field `k` after position `p`. -/
def fieldAt (w : List Bool) (p k : ℕ) : List Bool := (Worker.Format.readField (w.drop (fieldPos w p k))).1

/-! ## The loop data -/

section Data
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))

/-- The decoded guess (its oracle is `B` when the oracle field decodes to `B`). -/
def theGuess : Worker.Guess (width s g N) := Worker.decodeGuess s P g N x (guessWord N bits pad)

/-- The position of the first witness field: after the oracle field and the `auxN` circuit fields. -/
def fieldsStart : ℕ :=
  Codec.circPos (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)) (auxN s P g x B)

/-- The witness field of term `t` of gadget `a`. -/
def termField (a : ℕ) (t : Fin 10) : List Bool :=
  fieldAt (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * a + t.val)

def circs (N : ℕ) (bits : List Bool) (pad : ℕ) : ℕ → NCircuit (width s g N) :=
  Codec.circAt (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad))

variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- The entries of gadget `a`: `bitWord flip ++ outputWord raw` of its ten terms. -/
def gadgetEntries (a : ℕ) : List Bool :=
  (List.finRange 10).flatMap fun t => entryWord ((theGuess s P g x bits pad).termRaw P x ctr ω a t)

/-- The entries of the gadgets `< i`. -/
def entriesUpTo (i : ℕ) : List Bool := (List.range i).flatMap (gadgetEntries s P g x bits pad ctr ω)

/-- The I-stream after `i` gadgets. -/
def viOf (i : ℕ) : List Bool := headerOf s P g x B ++ marks (entriesUpTo s P g x bits pad ctr ω i)

/-! ## Operand descriptors and counter budgets -/

/-- Clause `a mod 2^{rb}` of the PCPP of `B`. -/
def clauseOf (a : ℕ) : Fin 3 → Literal (sysCount s P g x B + (pcpp s P g x B).proofBits) :=
  (pcpp s P g x B).clause ⟨a % 2 ^ (pcpp s P g x B).randomBits, Nat.mod_lt _ (by positivity)⟩

/-- The descriptor the loader puts in registers for literal `k` of gadget `a`. -/
def litOpd (a : ℕ) (k : Fin 3) : Opd :=
  let l := clauseOf s P g x B a k
  ⟨decide (litNeg l ≠ 0), decide (litVar l < sysCount s P g x B),
    if litVar l < sysCount s P g x B then litVar l else litVar l - sysCount s P g x B⟩

/-- The descriptor of the helper of gadget `a` (auxiliary name `proofBits + a`). -/
def helpOpd (a : ℕ) : Opd := ⟨false, false, (pcpp s P g x B).proofBits + a⟩

/-- The counter budget of term `t` of gadget `a` (`0` for exact terms). -/
def termBud (a : ℕ) (t : Fin 10) : ℕ :=
  let o := litOpd s P g x B a
  let h := helpOpd s P g x B a
  let Cs := circs s g N bits pad
  let rows := suppRows P (width s g N)
  let w := termField s P g x bits pad B a t
  match t.val with
  | 0 => bud1 ctr Cs ω w h
  | 1 => bud1 ctr Cs ω w (o 0)
  | 2 => bud1 ctr Cs ω w (o 1)
  | 3 => bud1 ctr Cs ω w (o 2)
  | 4 => bud2 ctr Cs rows ω w (o 0) (o 1)
  | 5 => bud2 ctr Cs rows ω w (o 0) (o 2)
  | 6 => bud2 ctr Cs rows ω w (o 1) (o 2)
  | 7 => bud2 ctr Cs rows ω w (o 0) h
  | 8 => bud2 ctr Cs rows ω w (o 1) h
  | _ => bud2 ctr Cs rows ω w (o 2) h

/-- The counter budget of gadget `a`. -/
def gadgetBud (a : ℕ) : ℕ := ∑ t : Fin 10, termBud s P g x bits pad B ctr ω a t

/-- The counter budget of the whole loop. -/
def loopBud : ℕ := ∑ a ∈ Finset.range (gadgets s g N), gadgetBud s P g x bits pad B ctr ω a

def frontSize : ℕ :=
  (pcpp s P g x B).word.length + gadgets s g N + sysCount s P g x B + (pcpp s P g x B).proofBits

end Data

/-! ## The states -/

section States
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)

/-- **`LoopIter i`: the state after `i` gadgets.** `LoopEntry` with the I-stream `viOf i` (head and `R 9` at its
end), the witness stream's head at witness field `10 i`, `rA = i`, `rLC = M − i`. -/
def LoopIter (i : ℕ) : WState (nsW D) nrW :=
  let E := LoopEntry D N x bits pad B jk
  let vi := viOf s P g x bits pad B ctr ω i
  { sh := Function.update (Function.update E.sh (sVI D) vi.length) (sWT D)
      (fieldPos (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * i))
    st := Function.update E.st (sVI D) vi
    val := Function.update (Function.update (Function.update E.val (regE 9) vi.length) rA i) rLC
      (gadgets s g N - i)
    cell := false }

/-- The state at the start of the body of pass `i` (the loop counter already decremented). -/
def LoopPre (i : ℕ) : WState (nsW D) nrW :=
  (LoopIter D ctr ω x bits pad B jk i).setv rLC (gadgets s g N - i - 1)

/-- The state after the loop and the close: `false` appended to the I-stream. -/
def LoopExit : WState (nsW D) nrW :=
  appendO (LoopIter D ctr ω x bits pad B jk (gadgets s g N)) (sVI D) (regE 9) [false]

end States

/-! ## The program -/

section Program
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)

/-- The front end's register file: `R 0 = rA`, `R i = 47 + i`. -/
def frontIdx : Fin 18 → Fin nrW := ![45, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64]

theorem frontIdx_inj : Function.Injective frontIdx := by decide

def frontR : Fin 18 ↪ Fin nrW := ⟨frontIdx, frontIdx_inj⟩

/-- The variable, sign, auxiliary-index and systematic-flag registers of literal `k`. -/
def rV (k : Fin 3) : Fin nrW := ⟨48 + k.val, by have := k.isLt; simp only [nrW]; omega⟩
def rS (k : Fin 3) : Fin nrW := ⟨51 + k.val, by have := k.isLt; simp only [nrW]; omega⟩
def rD (k : Fin 3) : Fin nrW := ⟨66 + 2 * k.val, by have := k.isLt; simp only [nrW]; omega⟩
def rF (k : Fin 3) : Fin nrW := ⟨67 + 2 * k.val, by have := k.isLt; simp only [nrW]; omega⟩
abbrev rT1 : Fin nrW := 72
abbrev rT2 : Fin nrW := 73
abbrev rLT : Fin nrW := 74

/-- Classify the three literals. -/
def classifyW : WM (nsW D) nrW :=
  .seq (Worker.ltSubW (rV 0) rSC (rD 0) (rF 0) rT1 rT2)
  (.seq (Worker.ltSubW (rV 1) rSC (rD 1) (rF 1) rT1 rT2) (Worker.ltSubW (rV 2) rSC (rD 2) (rF 2) rT1 rT2))

/-- Load literal `k` into the operand registers `R n, R (n+1), R (n+2)` (`n = 0` or `3`). -/
def litLoad (k : Fin 3) (n : Fin 40) (hn : n.val ≤ 3) : WM (nsW D) nrW :=
  Worker.loadLit (rS k) (rF k) (rV k) (rD k) (regE n) (regE ⟨n.val + 1, by omega⟩) (regE ⟨n.val + 2, by omega⟩) rLT

/-- Load the helper `proofBits + a` into the operand index register `R n` (`n = 2` or `5`). -/
def helpLoad (n : Fin 40) : WM (nsW D) nrW := Worker.loadHelper rPB rA (regE n) rLT

/-- Clear the operand registers `R 0 … R 5`. -/
def clearOps : WM (nsW D) nrW :=
  .seq (WM.clear (regE 0)) (.seq (WM.clear (regE 1)) (.seq (WM.clear (regE 2))
  (.seq (WM.clear (regE 3)) (.seq (WM.clear (regE 4)) (WM.clear (regE 5))))))

variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-- The counter's tapes: the counter block. -/
def ctrMap : Fin ctr.program.program.tapeCount → Fin (nsW D + 1) := fun j => cB D (Fin.cast hct j)

def termStep (t : Fin 10) : WMX (nsW D) nrW :=
  let E := termEnv D
  let T1 := termW1 E ctr (ctrMap D ctr hct) ω
  let T2 := termW2 E ctr (ctrMap D ctr hct) ω
  let run (ld : WM (nsW D) nrW) (T : WMX (nsW D) nrW) : WMX (nsW D) nrW := .seq (.wm ld) (.seq T (.wm (clearOps D)))
  match t.val with
  | 0 => run (helpLoad D 2) T1
  | 1 => run (litLoad D 0 0 (by decide)) T1
  | 2 => run (litLoad D 1 0 (by decide)) T1
  | 3 => run (litLoad D 2 0 (by decide)) T1
  | 4 => run (.seq (litLoad D 0 0 (by decide)) (litLoad D 1 3 (by decide))) T2
  | 5 => run (.seq (litLoad D 0 0 (by decide)) (litLoad D 2 3 (by decide))) T2
  | 6 => run (.seq (litLoad D 1 0 (by decide)) (litLoad D 2 3 (by decide))) T2
  | 7 => run (.seq (litLoad D 0 0 (by decide)) (helpLoad D 5)) T2
  | 8 => run (.seq (litLoad D 1 0 (by decide)) (helpLoad D 5)) T2
  | _ => run (.seq (litLoad D 2 0 (by decide)) (helpLoad D 5)) T2

/-- Clear the gadget registers and advance the gadget index. -/
def finishW : WM (nsW D) nrW :=
  .seq (WM.clear 48) (.seq (WM.clear 49) (.seq (WM.clear 50) (.seq (WM.clear 51) (.seq (WM.clear 52)
  (.seq (WM.clear 53) (.seq (WM.clear 54) (.seq (WM.clear 55)
  (.seq (WM.clear 66) (.seq (WM.clear 67) (.seq (WM.clear 68) (.seq (WM.clear 69) (.seq (WM.clear 70)
  (.seq (WM.clear 71) (.inc rA))))))))))))))

/-- **The gadget body.** -/
def gadgetW : WMX (nsW D) nrW :=
  .seq (ClauseFront.frontW (sJ D) frontR)
  (.seq (.wm (classifyW D))
  (.seq (termStep D ctr hct ω 0) (.seq (termStep D ctr hct ω 1) (.seq (termStep D ctr hct ω 2)
  (.seq (termStep D ctr hct ω 3) (.seq (termStep D ctr hct ω 4) (.seq (termStep D ctr hct ω 5)
  (.seq (termStep D ctr hct ω 6) (.seq (termStep D ctr hct ω 7) (.seq (termStep D ctr hct ω 8)
  (.seq (termStep D ctr hct ω 9) (.wm (finishW D)))))))))))))

/-- **The term loop**: `M` gadget passes (`rLC` counts down), then the close of the I-stream. -/
def termLoopW : WMX (nsW D) nrW :=
  .seq (Worker.repLoopX rLC (gadgetW D ctr hct ω)) (.wm (closeW (sVI D) (regE 9)))

end Program

/-! ## Hypotheses, costs, statements -/

section Statements
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

structure LoopFit {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (cap Z Bc V : ℕ) : Prop where
  dec : Worker.Decodes (width s g N) (guessWord N bits pad) B
  hpad : N / 16 + 1 ≤ pad
  phys : fieldPos (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * gadgets s g N) ≤
    (guessWord N bits pad).length
  fit : ∀ a < gadgets s g N, ∀ t : Fin 10,
    TermFit cap (circs s g N bits pad) (auxN s P g x B) (suppRows P (width s g N))
      (P.code.length (width s g N)) ω (termField s P g x bits pad B a t) Z Bc V
  cwZ : (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length ≤ Z
  supZ : (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length ≤ Z
  idxZ : sysCount s P g x B + auxN s P g x B ≤ Z
  front : 16 * (frontSize s P g x B + 2) ≤ cap
  capT : ∀ a < gadgets s g N, ∀ t : Fin 10,
    (viOf s P g x bits pad B ctr ω (gadgets s g N)).length + 1000 * (Z + 1) +
      8 * termBud s P g x bits pad B ctr ω a t ≤ cap

/-- The cost class of one gadget: a polynomial in the sizes (`tc` counter tapes, `Z`, `Bc`, the front end's sizes
`S`) plus the gadget's counter budget, kept separate. -/
def gadgetCost (tc Z Bc S bud : ℕ) : ℕ :=
  1000000000000000 * (tc + 1) * (Z + S + 1) ^ 4 * (Bc + 1) + (300 * tc + 6000) * bud

/-- The cost class of the loop and the close: `M` gadgets' polynomial parts plus the loop's counter budget. -/
def loopCost (tc Z Bc S M bud : ℕ) : ℕ :=
  M * (1000000000000000 * (tc + 1) * (Z + S + 1) ^ 4 * (Bc + 1) + 4) + (300 * tc + 6000) * bud + 9

/-- **STATEMENT `gadget_ideal`.** Pass `i < M` of the loop: from any state reading like `LoopPre i`, the gadget
body reaches a state reading like `LoopIter (i + 1)`, within the gadget's cost class. -/
def GadgetIdeal : Prop :=
  ∀ {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) (cap Z Bc V : ℕ),
    LoopFit (P := P) ctr ω x bits pad B cap Z Bc V →
    ∀ i < gadgets s g N, ∀ σ, SimW (LoopPre D ctr ω x bits pad B jk i) σ →
      ∃ τ, WXExec cap (gadgetW D ctr hct ω) σ τ
          (gadgetCost D.tc Z Bc (frontSize s P g x B) (gadgetBud s P g x bits pad B ctr ω i)) ∧
        SimW (LoopIter D ctr ω x bits pad B jk (i + 1)) τ

/-- **STATEMENT `termLoop_ideal`.** From any state reading like `LoopEntry`, the term loop and the close reach a
state reading like `LoopExit`, within the loop's cost class. -/
def TermLoopIdeal : Prop :=
  ∀ {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) (cap Z Bc V : ℕ),
    LoopFit (P := P) ctr ω x bits pad B cap Z Bc V →
    ∀ σ, SimW (LoopEntry D N x bits pad B jk) σ →
      ∃ τ, WXExec cap (termLoopW D ctr hct ω) σ τ
          (loopCost D.tc Z Bc (frontSize s P g x B) (gadgets s g N) (loopBud s P g x bits pad B ctr ω)) ∧
        SimW (LoopExit D ctr ω x bits pad B jk) τ

/-- **STATEMENT `loopExit_vi`.** At the exit the I-stream is the verdict machine's request word, framed. -/
def LoopExitVI (hD : Counter.DenOK ctr) : Prop :=
  ∀ {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool),
    Worker.Decodes (width s g N) (guessWord N bits pad) B →
    (LoopExit D ctr ω x bits pad B jk).st (sVI D) =
      RepairOrdinary.frame (Worker.verdictWord ((theGuess s P g x bits pad).verdictReq P x ctr hD ω))

end Statements

end

end NearCubicGates.Close.TermLoop
