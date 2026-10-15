import Proof.Gates.TermLoop.Gadget4

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
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd model1 model2)
open NearCubicGates.Close.WorkerArith (TermFit termW1 termW2 termCost bud1 bud2 entryWord)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-- The witness position of field `k` of the loop. -/
abbrev whOf (k : ℕ) : ℕ := fieldPos (guessWord N bits pad) (fieldsStart s P g x bits pad B) k

theorem whOf_phys (cap Z Bc V : ℕ) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (k : ℕ)
    (hk : k < 10 * gadgets s g N) :
    fieldEnd (guessWord N bits pad) (whOf (P := P) x bits pad B k) ≤ (guessWord N bits pad).length := by
  unfold whOf; rw [← fieldPos_succ]
  exact (fieldPos_mono _ _ (by omega)).trans hL.phys

/-- **Term `t` of gadget `i`.** -/
theorem termStep_ideal (cap Z Bc V : ℕ) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (i : ℕ)
    (hi : i < gadgets s g N) (t : Fin 10) (vi : List Bool)
    (hvi : vi.length ≤ (viOf s P g x bits pad B ctr ω (gadgets s g N)).length) :
    ∃ τ, WXExec cap (termStep D ctr hct ω t)
        (Shape D x bits pad B jk vi (whOf (P := P) x bits pad B (10 * i + t.val)) (vC D x bits pad B jk i)) τ
        (termCost ctr.program.program.tapeCount Z Bc (termBud s P g x bits pad B ctr ω i t) + 200 * (Z + 1)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (termModel s P g x bits pad B ctr ω i t)))
        (whOf (P := P) x bits pad B (10 * i + t.val + 1)) (vC D x bits pad B jk i)) τ := by
  have hwh := whOf_phys x bits pad B ctr ω cap Z Bc V hL (10 * i + t.val) (by have := t.isLt; omega)
  have hfit := hL.fit i hi t
  have hcap := hL.capT i hi t
  have e1 : whOf (P := P) x bits pad B (10 * i + t.val + 1) =
      fieldEnd (guessWord N bits pad) (whOf (P := P) x bits pad B (10 * i + t.val)) := fieldPos_succ _ _ _
  rw [e1]
  fin_cases t
  · exact stepHelp1 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLit1 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 0 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLit1 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 1 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLit1 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 2 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLit2 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 0 1 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLit2 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 0 2 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLit2 D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 1 2 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLitHelp D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 0 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLitHelp D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 1 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)
  · exact stepLitHelp D x bits pad B jk ctr hct ω cap Z Bc V i vi _ hwh hfit hL.cwZ hL.supZ hL.idxZ hi 2 (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hvi _) _) hcap)

end

end NearCubicGates.Close.TermLoop
