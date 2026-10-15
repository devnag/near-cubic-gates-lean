import Proof.Gates.TermLoop.Shape

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
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd)
open NearCubicGates.Close.WorkerArith (TermEnv termIdeal TermPre TermBase)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc)

theorem blank_nil : Worker.Blank [] := fun p => by simp [readTapeBit]

theorem named_nodup :
    [sCW D, sSUP D, sS1 D, sS2 D, sTL D, sG D, sL D, sVI D, sWT D].Nodup := by
  have h := sSUP_range D
  apply List.Nodup.of_map Fin.val
  rw [show List.map Fin.val [sCW D, sSUP D, sS1 D, sS2 D, sTL D, sG D, sL D, sVI D, sWT D] =
    [3, (sSUP D).val, 5, 6, 7, 8, 9, 4, 2] from rfl]
  generalize (sSUP D).val = k at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
  and_intros <;> first | omega | simp

/-- **A shape meets `TermPre`.** -/
theorem termPre_shape (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ)
    (hv6 : v (regE 6) = width s g N)
    (hv7 : v (regE 7) = (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length)
    (hv8 : v (regE 8) = (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length)
    (hz : ∀ i : Fin 40, 10 ≤ i.val → v (regE i) = 0)
    (hwh : fieldEnd (guessWord N bits pad) wh ≤ (guessWord N bits pad).length) :
    TermPre (termEnv D) (ctrMap D ctr hct) (circs s g N bits pad) (auxN s P g x B) (suppRows P (width s g N))
      (P.code.length (width s g N)) (readField ((guessWord N bits pad).drop wh)).1
      ((guessWord N bits pad).take wh) ((guessWord N bits pad).drop (fieldEnd (guessWord N bits pad) wh))
      (Shape D x bits pad B jk vi wh v) := by
  obtain ⟨hsplit, -, hwl⟩ := field_split (guessWord N bits pad) wh hwh
  have hsup := sSUP_range D
  have hS : ∀ i : Fin (nsW D + 1), 5 ≤ i.val → i.val < 16 →
      (Shape D x bits pad B jk vi wh v).st i = [] ∧ (Shape D x bits pad B jk vi wh v).sh i = 0 := by
    intro i h5 h16
    have n1 : i ≠ sWT D := fin_ne (by rw [sWT_val]; omega)
    have n2 : i ≠ sVI D := fin_ne (by rw [sVI_val]; omega)
    exact ⟨by rw [shape_st_other D x bits pad B jk _ _ _ i n2, loopEntry_st_small D x bits pad B jk i h5 h16],
      shape_sh_other D x bits pad B jk _ _ _ i n1 n2⟩
  have hC : ∀ j, (Shape D x bits pad B jk vi wh v).st (ctrMap D ctr hct j) = [] ∧
      (Shape D x bits pad B jk vi wh v).sh (ctrMap D ctr hct j) = 0 := by
    intro j
    have := ctrMap_range D ctr hct j
    have n1 : ctrMap D ctr hct j ≠ sWT D := fin_ne (by rw [sWT_val]; omega)
    have n2 : ctrMap D ctr hct j ≠ sVI D := fin_ne (by rw [sVI_val]; omega)
    exact ⟨by rw [shape_st_other D x bits pad B jk _ _ _ _ n2, loopEntry_st_ctr D x bits pad B jk ctr hct j],
      shape_sh_other D x bits pad B jk _ _ _ _ n1 n2⟩
  have nCW1 : sCW D ≠ sWT D := fin_ne (by simp)
  have nCW2 : sCW D ≠ sVI D := fin_ne (by simp)
  have nSUP1 : sSUP D ≠ sWT D := fin_ne (by rw [sWT_val]; omega)
  have nSUP2 : sSUP D ≠ sVI D := fin_ne (by rw [sVI_val]; omega)
  have r9 : ∀ i : Fin 40, i.val ≠ 9 → regE i ≠ regE 9 := fun i h e => h (by
    have := congrArg Fin.val e; simpa [regE] using this)
  have bl : ∀ i : Fin (nsW D + 1), 5 ≤ i.val → i.val < 16 → Worker.Blank ((Shape D x bits pad B jk vi wh v).st i) :=
    fun i h5 h16 => by rw [(hS i h5 h16).1]; exact blank_nil
  have hh : ∀ i : Fin (nsW D + 1), 5 ≤ i.val → i.val < 16 → (Shape D x bits pad B jk vi wh v).sh i = 0 :=
    fun i h5 h16 => (hS i h5 h16).2
  refine ⟨⟨ctrMap_inj D ctr hct, ?_, named_nodup D, ?_, ?_, ?_, ?_, ?_, ?_,
    bl (sS1 D) (by simp) (by simp), hh (sS1 D) (by simp) (by simp), bl (sS2 D) (by simp) (by simp),
    hh (sS2 D) (by simp) (by simp), fun j => by rw [(hC j).1]; exact blank_nil, fun j => (hC j).2,
    bl (sTL D) (by simp) (by simp), hh (sTL D) (by simp) (by simp), bl (sG D) (by simp) (by simp),
    hh (sG D) (by simp) (by simp), bl (sL D) (by simp) (by simp), hh (sL D) (by simp) (by simp),
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    have := ctrMap_range D ctr hct j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with h | h | h | h | h | h | h | h | h <;>
      first
      | (have := congrArg Fin.val h; simp only [termEnv] at this; simp at this; omega)
      | (have := congrArg Fin.val h; simp only [termEnv] at this; omega)
  · exact ⟨[], by simp only [termEnv]; rw [shape_st_other D x bits pad B jk _ _ _ _ nCW2, loopEntry_st_CW]; simp⟩
  · simp only [termEnv]; exact shape_sh_other D x bits pad B jk _ _ _ _ nCW1 nCW2
  · simp only [termEnv, shape_val]; rw [Function.update_of_ne (r9 7 (by decide)), hv7]
  · refine ⟨[false], ?_⟩
    simp only [termEnv]
    rw [shape_st_other D x bits pad B jk _ _ _ _ nSUP2, loopEntry_st_SUP, frame_supports]
  · simp only [termEnv]; exact shape_sh_other D x bits pad B jk _ _ _ _ nSUP1 nSUP2
  · simp only [termEnv, shape_val]; rw [Function.update_of_ne (r9 8 (by decide)), hv8]
  · simp only [termEnv]
    rw [shape_st_other D x bits pad B jk _ _ _ _ (sWT_ne_sVI D), loopEntry_st_WT]
    exact hsplit
  · simp only [termEnv, shape_sh_WT]; simp; omega
  · simp only [termEnv]; simp
  · simp only [termEnv, shape_val]; rw [Function.update_of_ne (r9 6 (by decide)), hv6]
  · intro i h10 _
    simp only [termEnv, shape_val]
    rw [Function.update_of_ne (r9 i (by omega)), hz i h10]
  · simp only [termEnv, shape_val]; rw [Function.update_of_ne (r9 39 (by decide)), hz 39 (by decide)]

end

end NearCubicGates.Close.TermLoop
