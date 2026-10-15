import Proof.Gates.TermLoop.Gadget6
import Proof.Gates.TermLoop.Cost

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
open NearCubicGates.Close.Worker.Format (readField)

noncomputable section

/-! ## Runs in ideal form -/

section Ideal
variable {ns nr : ℕ}

/-- From every state reading like `ι`, `P` reaches a state reading like `ι'` within `c`. -/
def IdealRun (cap : ℕ) (P : WMX ns nr) (ι ι' : WState ns nr) (c : ℕ) : Prop :=
  ∀ σ, SimW ι σ → ∃ τ, WXExec cap P σ τ c ∧ SimW ι' τ

theorem idealRun_of {cap : ℕ} {P : WMX ns nr} {ι ι' : WState ns nr} {c : ℕ}
    (h : ∃ τ, WXExec cap P ι τ c ∧ SimW ι' τ) : IdealRun cap P ι ι' c := by
  intro σ hs
  obtain ⟨τ, e, sm⟩ := h
  obtain ⟨τ', e', s'⟩ := wxexec_sim e σ hs
  exact ⟨τ', e', SimW.trans sm s'⟩

theorem idealRun_exact {cap : ℕ} {P : WMX ns nr} {ι ι' : WState ns nr} {c : ℕ} (h : WXExec cap P ι ι' c) :
    IdealRun cap P ι ι' c :=
  idealRun_of ⟨ι', h, SimW.refl _⟩

theorem idealRun_seq {cap : ℕ} {P Q : WMX ns nr} {ι ι1 ι2 : WState ns nr} {n m : ℕ} (h1 : IdealRun cap P ι ι1 n)
    (h2 : IdealRun cap Q ι1 ι2 m) : IdealRun cap (.seq P Q) ι ι2 (n + 1 + m) := by
  intro σ hs
  obtain ⟨τ1, e1, s1⟩ := h1 σ hs
  obtain ⟨τ2, e2, s2⟩ := h2 τ1 s1
  exact ⟨τ2, WXExec.seq e1 e2, s2⟩

theorem idealRun_mono {cap : ℕ} {P : WMX ns nr} {ι ι' : WState ns nr} {n m : ℕ} (h : IdealRun cap P ι ι' n)
    (hnm : n ≤ m) : IdealRun cap P ι ι' m := by
  intro σ hs
  obtain ⟨τ, e, sm⟩ := h σ hs
  exact ⟨τ, WXExec.mono e hnm, sm⟩

end Ideal

/-! ## The I-stream inside a gadget -/

section Part
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- The model entries of the first `t` terms of gadget `i`. -/
def partE (i t : ℕ) : List Bool :=
  ((List.finRange 10).take t).flatMap fun u => entryWord (termModel s P g x bits pad B ctr ω i u)

/-- The I-stream after the first `t` terms of gadget `i`. -/
def partV (i t : ℕ) : List Bool := viOf s P g x bits pad B ctr ω i ++ marks (partE s P g x bits pad B ctr ω i t)

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by simp [marks]

theorem partV_zero (i : ℕ) : partV s P g x bits pad B ctr ω i 0 = viOf s P g x bits pad B ctr ω i := by
  simp [partV, partE, marks]

theorem finRange_get (t : ℕ) (ht : t < 10) : (List.finRange 10)[t]? = some ⟨t, ht⟩ := by
  interval_cases t <;> rfl

theorem partV_succ (i t : ℕ) (ht : t < 10) :
    partV s P g x bits pad B ctr ω i (t + 1) =
      partV s P g x bits pad B ctr ω i t ++ marks (entryWord (termModel s P g x bits pad B ctr ω i ⟨t, ht⟩)) := by
  simp only [partV, partE, List.take_add_one, finRange_get t ht, Option.toList_some, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, marks_app, List.append_assoc]

theorem entriesUpTo_succ (i : ℕ) :
    entriesUpTo s P g x bits pad ctr ω (i + 1) =
      entriesUpTo s P g x bits pad ctr ω i ++ gadgetEntries s P g x bits pad ctr ω i := by
  simp [entriesUpTo, List.range_succ, List.flatMap_append]

theorem viOf_succ (i : ℕ) :
    viOf s P g x bits pad B ctr ω (i + 1) =
      viOf s P g x bits pad B ctr ω i ++ marks (gadgetEntries s P g x bits pad ctr ω i) := by
  simp only [viOf, entriesUpTo_succ, marks_app, List.append_assoc]

theorem viOf_len_mono {j k : ℕ} (h : j ≤ k) :
    (viOf s P g x bits pad B ctr ω j).length ≤ (viOf s P g x bits pad B ctr ω k).length := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [viOf_succ, List.length_append]; omega

theorem partE_len_le (i t : ℕ) (ht : t ≤ 10) :
    (partE s P g x bits pad B ctr ω i t).length ≤ (partE s P g x bits pad B ctr ω i 10).length := by
  unfold partE
  have e := List.take_append_drop t ((List.finRange 10).take 10)
  rw [List.take_take, Nat.min_eq_left ht] at e
  conv_rhs => rw [← e]
  rw [List.flatMap_append, List.length_append]
  omega

section Ten
variable (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B)
  (hpad : N / 16 + 1 ≤ pad)
include hdec hpad

theorem partE_ten (i : ℕ) (hi : i < gadgets s g N) :
    partE s P g x bits pad B ctr ω i 10 = gadgetEntries s P g x bits pad ctr ω i := by
  unfold partE gadgetEntries
  rw [List.take_of_length_le (by simp)]
  apply List.flatMap_congr
  intro u _
  rw [termModel_eq s P g x bits pad B ctr ω hdec hpad i hi u]

/-- **After the ten terms of gadget `i` the I-stream is `viOf (i + 1)`.** -/
theorem partV_ten (i : ℕ) (hi : i < gadgets s g N) :
    partV s P g x bits pad B ctr ω i 10 = viOf s P g x bits pad B ctr ω (i + 1) := by
  rw [viOf_succ, partV, partE_ten s P g x bits pad B ctr ω hdec hpad i hi]

theorem partV_len (i : ℕ) (hi : i < gadgets s g N) (t : ℕ) (ht : t ≤ 10) :
    (partV s P g x bits pad B ctr ω i t).length ≤ (viOf s P g x bits pad B ctr ω (gadgets s g N)).length := by
  have h1 : (partV s P g x bits pad B ctr ω i t).length ≤ (partV s P g x bits pad B ctr ω i 10).length := by
    unfold partV
    simp only [List.length_append, marks_length]
    have := partE_len_le s P g x bits pad B ctr ω i t ht
    omega
  rw [partV_ten s P g x bits pad B ctr ω hdec hpad i hi] at h1
  exact h1.trans (viOf_len_mono s P g x bits pad B ctr ω (by omega))

end Ten

end Part

/-! ## The gadget -/

section Gadget
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

theorem fit_capZ (cap Z Bc V : ℕ) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (i : ℕ)
    (hi : i < gadgets s g N) : 1000 * (Z + 1) ≤ cap :=
  le_trans (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) (hL.capT i hi 0)

theorem finish_fit (cap Z Bc V : ℕ) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (i : ℕ)
    (hi : i < gadgets s g N) :
    IdealRun cap (.wm (finishW D))
      (Shape D x bits pad B jk (partV s P g x bits pad B ctr ω i 10) (whOf (P := P) x bits pad B (10 * i + 9 + 1))
        (vC D x bits pad B jk i))
      (LoopIter D ctr ω x bits pad B jk (i + 1)) (100 * (Z + frontSize s P g x B + 1)) := by
  have hZ := fit_capZ x bits pad B ctr ω cap Z Bc V hL i hi
  have hS := hL.front
  have hI := hL.idxZ
  have e := finish_shape D x bits pad B jk cap (Z + frontSize s P g x B) i
    (partV s P g x bits pad B ctr ω i 10) (whOf (P := P) x bits pad B (10 * i + 9 + 1))
    (by omega) (by unfold frontSize; omega) hi (by omega)
  rw [loopIter_eq D x bits pad B jk ctr ω (i + 1), ← partV_ten s P g x bits pad B ctr ω hL.dec hL.hpad i hi,
    show 10 * (i + 1) = 10 * i + 9 + 1 by ring]
  exact idealRun_exact (WXExec.wm e)

/-- Term `t` of gadget `i` between the partial I-streams. -/
theorem termStep_part (cap Z Bc V : ℕ) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (i : ℕ)
    (hi : i < gadgets s g N) (t : ℕ) (ht : t < 10) :
    IdealRun cap (termStep D ctr hct ω ⟨t, ht⟩)
      (Shape D x bits pad B jk (partV s P g x bits pad B ctr ω i t) (whOf (P := P) x bits pad B (10 * i + t))
        (vC D x bits pad B jk i))
      (Shape D x bits pad B jk (partV s P g x bits pad B ctr ω i (t + 1)) (whOf (P := P) x bits pad B (10 * i + t + 1))
        (vC D x bits pad B jk i))
      (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i ⟨t, ht⟩) + 200 * (Z + 1)) := by
  obtain ⟨τ, e, sm⟩ := termStep_ideal D x bits pad B jk ctr hct ω cap Z Bc V hL i hi ⟨t, ht⟩
    (partV s P g x bits pad B ctr ω i t) (partV_len s P g x bits pad B ctr ω hL.dec hL.hpad i hi t (by omega))
  rw [← partV_succ s P g x bits pad B ctr ω i t ht] at sm
  exact idealRun_mono (idealRun_of ⟨τ, e, sm⟩) (le_of_eq (by rw [hct]))

theorem terms_ideal (cap Z Bc V : ℕ) (hL : LoopFit (P := P) ctr ω x bits pad B cap Z Bc V) (i : ℕ)
    (hi : i < gadgets s g N) :
    IdealRun cap
      (.seq (termStep D ctr hct ω 0) (.seq (termStep D ctr hct ω 1) (.seq (termStep D ctr hct ω 2)
        (.seq (termStep D ctr hct ω 3) (.seq (termStep D ctr hct ω 4) (.seq (termStep D ctr hct ω 5)
        (.seq (termStep D ctr hct ω 6) (.seq (termStep D ctr hct ω 7) (.seq (termStep D ctr hct ω 8)
        (.seq (termStep D ctr hct ω 9) (.wm (finishW D))))))))))))
      (Shape D x bits pad B jk (viOf s P g x bits pad B ctr ω i) (whOf (P := P) x bits pad B (10 * i))
        (vC D x bits pad B jk i))
      (LoopIter D ctr ω x bits pad B jk (i + 1))
      ((termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 0) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 1) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 2) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 3) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 4) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 5) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 6) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 7) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 8) + 200 * (Z + 1) + 1 +
        (termCost D.tc Z Bc (termBud s P g x bits pad B ctr ω i 9) + 200 * (Z + 1) + 1 +
        100 * (Z + frontSize s P g x B + 1)))))))))))) := by
  have h0 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 0 (by decide)
  have h1 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 1 (by decide)
  have h2 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 2 (by decide)
  have h3 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 3 (by decide)
  have h4 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 4 (by decide)
  have h5 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 5 (by decide)
  have h6 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 6 (by decide)
  have h7 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 7 (by decide)
  have h8 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 8 (by decide)
  have h9 := termStep_part D x bits pad B jk ctr hct ω cap Z Bc V hL i hi 9 (by decide)
  have hf := finish_fit D x bits pad B jk ctr ω cap Z Bc V hL i hi
  rw [partV_zero] at h0
  exact idealRun_seq h0 (idealRun_seq h1 (idealRun_seq h2 (idealRun_seq h3 (idealRun_seq h4 (idealRun_seq h5 (idealRun_seq h6 (idealRun_seq h7 (idealRun_seq h8 (idealRun_seq h9 (hf))))))))))

end Gadget

/-! ## `gadget_ideal` -/

section Main
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

theorem gadget_ideal : GadgetIdeal D ctr hct ω := by
  intro N x bits pad B jk cap Z Bc V hL i hi
  have hZ := fit_capZ x bits pad B ctr ω cap Z Bc V hL i hi
  have hS := hL.front
  have hI := hL.idxZ
  unfold frontSize at hS
  have hF : IdealRun cap (ClauseFront.frontW (sJ D) frontR) (LoopPre D ctr ω x bits pad B jk i)
      (Shape D x bits pad B jk (viOf s P g x bits pad B ctr ω i) (whOf (P := P) x bits pad B (10 * i))
        (vF D x bits pad B jk i))
      (ClauseFront.frontCost ((pcpp s P g x B).word.length + i + sysCount s P g x B + (pcpp s P g x B).proofBits)) := by
    rw [loopPre_eq]
    exact idealRun_exact (front_shape D x bits pad B jk cap i _ _ (by omega))
  have hV : ∀ k, litVar (clauseOf s P g x B i k) ≤ Z := fun k => by
    obtain ⟨b1, -, b3⟩ := lit_bounds (P := P) x B i k
    omega
  have hC : IdealRun cap (.wm (classifyW D))
      (Shape D x bits pad B jk (viOf s P g x bits pad B ctr ω i) (whOf (P := P) x bits pad B (10 * i))
        (vF D x bits pad B jk i))
      (Shape D x bits pad B jk (viOf s P g x bits pad B ctr ω i) (whOf (P := P) x bits pad B (10 * i))
        (vC D x bits pad B jk i)) (200 * (Z + 1)) :=
    idealRun_exact (WXExec.wm (classify_shape D x bits pad B jk cap Z i _ _ hV (by omega) (by omega)))
  have hT := terms_ideal D x bits pad B jk ctr hct ω cap Z Bc V hL i hi
  exact idealRun_mono (idealRun_seq hF (idealRun_seq hC hT))
    (gadget_cost_le D.tc Z Bc (frontSize s P g x B) _ (by unfold frontSize; omega) (termBud s P g x bits pad B ctr ω i))

end Main

end

end NearCubicGates.Close.TermLoop
