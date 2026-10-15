import Proof.Gates.TermLoop.Fields
import Proof.Gates.Codec.PairFrame

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount)
open NearCubicGates.Close.WorkerArith (entryWord headerWord)

noncomputable section

/-- **The request word is the header word, then the entries.** -/
theorem verdictWord_eq (r : Worker.VerdictReq) :
    Worker.verdictWord r = headerWord r.q r.M r.N r.rb r.cl ++ r.I.flatMap entryWord := by
  unfold Worker.verdictWord listWord headerWord
  rw [r.hlen]
  simp only [List.append_assoc]
  rfl

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by
  simp [marks, List.flatMap_append]

section Data
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- **The entries of the gadget-major term list are `entriesUpTo M`.** -/
theorem termList_flatMap :
    ((theGuess s P g x bits pad).termList P x ctr ω).flatMap entryWord =
      entriesUpTo s P g x bits pad ctr ω (gadgets s g N) := by
  unfold Worker.Guess.termList WorkerArith.gmList entriesUpTo gadgetEntries
  rw [List.flatMap_assoc, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun a _ => ?_
  rw [List.flatMap_map]

end Data

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- **`loopExit_vi`: at the exit the I-stream is the verdict machine's request word, framed.** -/
theorem loopExit_vi (hD : Counter.DenOK ctr) : LoopExitVI D ctr ω hD := by
  intro N x bits pad B jk hdec
  have ho := guess_oracle s P g x bits pad B hdec
  have hVI : (LoopIter D ctr ω x bits pad B jk (gadgets s g N)).st (sVI D) =
      viOf s P g x bits pad B ctr ω (gadgets s g N) := by
    simp only [LoopIter]; rw [Function.update_self]
  set R := (theGuess s P g x bits pad).verdictReq P x ctr hD ω with hR
  have h1 : R.rb = (pcpp s P g x B).randomBits := by
    show (pcpp s P g x (theGuess s P g x bits pad).oracle).randomBits = _
    rw [ho]
  have h2 : R.I.flatMap entryWord = entriesUpTo s P g x bits pad ctr ω (gadgets s g N) :=
    termList_flatMap s P g x bits pad ctr ω
  have hq : R.q = width s g N := rfl
  have hM : R.M = gadgets s g N := rfl
  have hN : R.N = Worker.nu N ^ (g.lenRoot + 1) := rfl
  have hc : R.cl = clauseWidth g.clauseDegree (width s g N) := rfl
  rw [LoopExit, appendO_st, Function.update_self, hVI, Codec.frame_eq_marks, verdictWord_eq, marks_app, h1, h2,
    hq, hM, hN, hc]
  unfold viOf headerOf
  rw [List.append_assoc]

end

end NearCubicGates.Close.TermLoop
