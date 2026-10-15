import Proof.Gates.TermLoop.Fields

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

/-! ## Stream indices -/

section Idx

theorem fin_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

@[simp] theorem sX_val : (sX D).val = 0 := rfl
@[simp] theorem sBW_val : (sBW D).val = 1 := rfl
@[simp] theorem sWT_val : (sWT D).val = 2 := rfl
@[simp] theorem sCW_val : (sCW D).val = 3 := rfl
@[simp] theorem sVI_val : (sVI D).val = 4 := rfl
@[simp] theorem sS1_val : (sS1 D).val = 5 := rfl
@[simp] theorem sS2_val : (sS2 D).val = 6 := rfl
@[simp] theorem sTL_val : (sTL D).val = 7 := rfl
@[simp] theorem sG_val : (sG D).val = 8 := rfl
@[simp] theorem sL_val : (sL D).val = 9 := rfl

/-- The base of the composite's block. -/
def kBase : ℕ := 16 + D.tA

theorem kB_range (j : Fin D.cf.t) : 16 ≤ (kB D j).val ∧ (kB D j).val < kBase D + D.cf.t := by
  have := j.isLt; simp only [kB, kBase]; omega

theorem sJ_range : 16 ≤ (sJ D).val ∧ (sJ D).val < kBase D + D.cf.t := kB_range D _
theorem sSUP_range : 16 ≤ (sSUP D).val ∧ (sSUP D).val < kBase D + D.cf.t := kB_range D _

theorem sFL_range : 16 ≤ (sFL D).val ∧ (sFL D).val < kBase D := by
  have := D.flag.isLt
  simp only [sFL, aB, kBase]; omega

theorem cB_range (j : Fin D.tc) : kBase D + D.cf.t ≤ (cB D j).val := by
  simp only [cB, kBase]; omega

theorem sJ_ne_sSUP : sJ D ≠ sSUP D := by
  intro h
  have hv : D.cf.wOut = D.cf.sOut := by
    have := congrArg Fin.val h; simp only [sJ, sSUP, kB] at this; exact Fin.ext (by omega)
  have nd := D.cf.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
  exact nd.2.2.2.1.1 hv

/-- `LoopEntry` on the scratch streams `5 … 15`: blank. -/
theorem loopEntry_st_small {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) (i : Fin (nsW D + 1)) (h5 : 5 ≤ i.val) (h16 : i.val < 16) :
    (LoopEntry D N x bits pad B jk).st i = [] := by
  have := sJ_range D; have := sSUP_range D; have := sFL_range D
  have e1 : i ≠ sX D := fin_ne (by rw [sX_val]; omega)
  have e2 : i ≠ sBW D := fin_ne (by rw [sBW_val]; omega)
  have e3 : i ≠ sWT D := fin_ne (by rw [sWT_val]; omega)
  have e4 : i ≠ sCW D := fin_ne (by rw [sCW_val]; omega)
  have e5 : i ≠ sVI D := fin_ne (by rw [sVI_val]; omega)
  have e6 : i ≠ sJ D := fin_ne (by omega)
  have e7 : i ≠ sSUP D := fin_ne (by omega)
  have e8 : i ≠ sFL D := fin_ne (by omega)
  simp only [LoopEntry]
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6, if_neg e7, if_neg e8, if_pos (Or.inl h16)]

/-- `LoopEntry` on the counter block: blank. -/
theorem loopEntry_st_cB {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) (j : Fin D.tc) : (LoopEntry D N x bits pad B jk).st (cB D j) = [] := by
  have := sJ_range D; have := sSUP_range D; have := sFL_range D; have hc := cB_range D j
  have e1 : cB D j ≠ sX D := fin_ne (by rw [sX_val]; omega)
  have e2 : cB D j ≠ sBW D := fin_ne (by rw [sBW_val]; omega)
  have e3 : cB D j ≠ sWT D := fin_ne (by rw [sWT_val]; omega)
  have e4 : cB D j ≠ sCW D := fin_ne (by rw [sCW_val]; omega)
  have e5 : cB D j ≠ sVI D := fin_ne (by rw [sVI_val]; omega)
  have e6 : cB D j ≠ sJ D := fin_ne (by omega)
  have e7 : cB D j ≠ sSUP D := fin_ne (by omega)
  have e8 : cB D j ≠ sFL D := fin_ne (by omega)
  have e9 : 16 + D.tA + D.cf.t ≤ (cB D j).val := by unfold kBase at hc; omega
  simp only [LoopEntry]
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e5, if_neg e6, if_neg e7, if_neg e8, if_pos (Or.inr e9)]

theorem loopEntry_sh_other {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (jk : Fin (nsW D + 1) → List Bool) (i : Fin (nsW D + 1)) (h1 : i ≠ sWT D) (h2 : i ≠ sVI D) :
    (LoopEntry D N x bits pad B jk).sh i = 0 := by
  simp only [LoopEntry]; rw [if_neg h1, if_neg h2]

end Idx

/-! ## `LoopEntry`'s named streams and registers -/

section EntryVals
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)

theorem loopEntry_st_WT : (LoopEntry D N x bits pad B jk).st (sWT D) = guessWord N bits pad := by
  simp only [LoopEntry]
  rw [if_neg (fin_ne (by simp)), if_neg (fin_ne (by simp)), if_pos trivial]

theorem loopEntry_st_CW :
    (LoopEntry D N x bits pad B jk).st (sCW D) = Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B) := by
  simp only [LoopEntry]
  rw [if_neg (fin_ne (by simp)), if_neg (fin_ne (by simp)), if_neg (fin_ne (by simp)), if_pos trivial]; rfl

theorem loopEntry_st_J : (LoopEntry D N x bits pad B jk).st (sJ D) = (pcpp s P g x B).word := by
  have := sJ_range D
  simp only [LoopEntry]
  rw [if_neg (fin_ne (by rw [sX_val]; omega)), if_neg (fin_ne (by rw [sBW_val]; omega)),
    if_neg (fin_ne (by rw [sWT_val]; omega)), if_neg (fin_ne (by rw [sCW_val]; omega)),
    if_neg (fin_ne (by rw [sVI_val]; omega)), if_pos trivial]

theorem loopEntry_st_SUP :
    (LoopEntry D N x bits pad B jk).st (sSUP D) = RepairOrdinary.frame (supportsWord P.code (width s g N)) := by
  have := sSUP_range D
  simp only [LoopEntry]
  rw [if_neg (fin_ne (by rw [sX_val]; omega)), if_neg (fin_ne (by rw [sBW_val]; omega)),
    if_neg (fin_ne (by rw [sWT_val]; omega)), if_neg (fin_ne (by rw [sCW_val]; omega)),
    if_neg (fin_ne (by rw [sVI_val]; omega)), if_neg (sJ_ne_sSUP D).symm, if_pos trivial]

theorem loopEntry_sh_WT : (LoopEntry D N x bits pad B jk).sh (sWT D) =
    Codec.circPos (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)) (auxN s P g x B) := by
  simp [LoopEntry]

/-- The register values of `LoopEntry` (by index). -/
theorem loopEntry_val (r : Fin nrW) : (LoopEntry D N x bits pad B jk).val r =
    if r.val = 6 then width s g N
    else if r.val = 7 then (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length
    else if r.val = 8 then (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length
    else if r.val = 9 then (headerOf s P g x B).length
    else if r.val = 40 then N
    else if r.val = 41 then gadgets s g N
    else if r.val = 42 then (pcpp s P g x B).randomBits
    else if r.val = 43 then clauseWidth g.clauseDegree (width s g N)
    else if r.val = 44 then width s g N + P.code.length (width s g N)
    else if r.val = 46 then gadgets s g N
    else if r.val = 47 then (pcpp s P g x B).proofBits
    else 0 := by
  have e : ∀ (k : ℕ) (hk : k < 128), (r = ⟨k, hk⟩) ↔ r.val = k := fun k hk => ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  simp only [LoopEntry]
  rw [show regE 6 = (⟨6, by decide⟩ : Fin nrW) from rfl, show regE 7 = (⟨7, by decide⟩ : Fin nrW) from rfl,
    show regE 8 = (⟨8, by decide⟩ : Fin nrW) from rfl, show regE 9 = (⟨9, by decide⟩ : Fin nrW) from rfl]
  simp only [rN, rM, rRB, rCL, rSC, rLC, rPB]
  simp only [e]
  rfl

end EntryVals

/-! ## Shapes -/

section ShapeDefs
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)

/-- `LoopEntry` with `VI = vi` (head and `R 9` at its end), the head of `WT` at `wh`, registers `v`. -/
def Shape (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) : WState (nsW D) nrW :=
  { sh := Function.update (Function.update (LoopEntry D N x bits pad B jk).sh (sVI D) vi.length) (sWT D) wh
    st := Function.update (LoopEntry D N x bits pad B jk).st (sVI D) vi
    val := Function.update v (regE 9) vi.length
    cell := false }

theorem sWT_ne_sVI : sWT D ≠ sVI D := fin_ne (by simp)

@[simp] theorem shape_st_VI (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).st (sVI D) = vi := by simp [Shape]

theorem shape_st_other (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (i : Fin (nsW D + 1)) (h : i ≠ sVI D) :
    (Shape D x bits pad B jk vi wh v).st i = (LoopEntry D N x bits pad B jk).st i := by
  simp [Shape, Function.update_of_ne h]

@[simp] theorem shape_sh_VI (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).sh (sVI D) = vi.length := by
  simp [Shape, Function.update_of_ne (sWT_ne_sVI D).symm]

@[simp] theorem shape_sh_WT (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).sh (sWT D) = wh := by simp [Shape]

theorem shape_sh_other (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (i : Fin (nsW D + 1)) (h1 : i ≠ sWT D)
    (h2 : i ≠ sVI D) : (Shape D x bits pad B jk vi wh v).sh i = 0 := by
  simp [Shape, Function.update_of_ne h1, Function.update_of_ne h2, loopEntry_sh_other D x bits pad B jk i h1 h2]

@[simp] theorem shape_val (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).val = Function.update v (regE 9) vi.length := rfl

@[simp] theorem shape_cell (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    (Shape D x bits pad B jk vi wh v).cell = false := rfl

/-- Setting a register other than `R 9`. -/
theorem shape_setv (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (r : Fin nrW) (hr : r ≠ regE 9) (y : ℕ) :
    (Shape D x bits pad B jk vi wh v).setv r y = Shape D x bits pad B jk vi wh (Function.update v r y) := by
  apply WState.eq <;> try rfl
  simp only [WState.setv_val, shape_val]
  exact (Function.update_comm hr _ _ _).symm

/-- The register file of a shape is irrelevant at `R 9`. -/
theorem shape_val_R9 (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (y : ℕ) :
    Shape D x bits pad B jk vi wh (Function.update v (regE 9) y) = Shape D x bits pad B jk vi wh v := by
  apply WState.eq <;> try rfl
  simp

/-- Appending to the I-stream. -/
theorem appendO_shape (vi u : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) :
    appendO (Shape D x bits pad B jk vi wh v) (sVI D) (regE 9) u = Shape D x bits pad B jk (vi ++ u) wh v := by
  apply WState.eq
  · funext i
    simp only [appendO_sh]
    by_cases h : i = sVI D
    · subst h; simp
    · rw [Function.update_of_ne h]
      by_cases h' : i = sWT D
      · subst h'; simp
      · rw [shape_sh_other D x bits pad B jk _ _ _ i h' h, shape_sh_other D x bits pad B jk _ _ _ i h' h]
  · funext i
    simp only [appendO_st]
    by_cases h : i = sVI D
    · subst h; simp
    · rw [Function.update_of_ne h, shape_st_other D x bits pad B jk _ _ _ i h, shape_st_other D x bits pad B jk _ _ _ i h]
  · funext r
    simp only [appendO_val, shape_val]
    by_cases h : r = regE 9
    · subst h; simp
    · simp [Function.update_of_ne h]
  · rfl

/-- **`LoopIter` is a shape.** -/
theorem loopIter_eq {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ) (i : ℕ) :
    LoopIter D ctr ω x bits pad B jk i =
      Shape D x bits pad B jk (viOf s P g x bits pad B ctr ω i)
        (fieldPos (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * i))
        (Function.update (Function.update (LoopEntry D N x bits pad B jk).val rA i) rLC (gadgets s g N - i)) := by
  apply WState.eq
  · funext j
    simp only [LoopIter, Shape]
  · rfl
  · funext r
    simp only [LoopIter, Shape]
    by_cases h9 : r = regE 9
    · subst h9
      rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self]
    · rw [Function.update_of_ne h9]
      by_cases hL : r = rLC
      · subst hL; simp
      · rw [Function.update_of_ne hL, Function.update_of_ne hL]
        by_cases hA : r = rA
        · subst hA; simp
        · rw [Function.update_of_ne hA, Function.update_of_ne hA, Function.update_of_ne h9]
  · rfl

end ShapeDefs

/-! ## Term programs on shapes -/

section Terms
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc)

theorem ctrMap_inj : Function.Injective (ctrMap D ctr hct) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [ctrMap, cB] at this
  exact Fin.ext (by simpa using this)

theorem ctrMap_range (j : Fin ctr.program.program.tapeCount) :
    kBase D + D.cf.t ≤ (ctrMap D ctr hct j).val := cB_range D _

theorem ctrMap_ne (j : Fin ctr.program.program.tapeCount) (i : Fin (nsW D + 1))
    (h : i.val < kBase D + D.cf.t) : ctrMap D ctr hct j ≠ i :=
  fin_ne (by have := ctrMap_range D ctr hct j; omega)

theorem loopEntry_st_ctr (j : Fin ctr.program.program.tapeCount) :
    (LoopEntry D N x bits pad B jk).st (ctrMap D ctr hct j) = [] := loopEntry_st_cB D x bits pad B jk _

open Classical in
/-- **A term program's ideal end state on a shape** is the shape with the entry appended and the witness head
moved. -/
theorem termIdeal_shape (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (hWT : ℕ) (e : List Bool) :
    termIdeal (Shape D x bits pad B jk vi wh v) (ctrMap D ctr hct) (termEnv D) hWT e =
      Shape D x bits pad B jk (vi ++ marks e) hWT v := by
  rw [← appendO_shape D x bits pad B jk vi (marks e) hWT v]
  unfold termIdeal
  congr 1
  have hS : ∀ i : Fin (nsW D + 1), ((∃ j, ctrMap D ctr hct j = i) ∨ i = sTL D ∨ i = sG D ∨ i = sS1 D ∨ i = sS2 D) →
      i ≠ sWT D ∧ i ≠ sVI D ∧ (LoopEntry D N x bits pad B jk).st i = [] := by
    intro i hi
    rcases hi with ⟨j, rfl⟩ | rfl | rfl | rfl | rfl
    · have := ctrMap_range D ctr hct j; have := sJ_range D
      exact ⟨fin_ne (by rw [sWT_val]; omega), fin_ne (by rw [sVI_val]; omega), loopEntry_st_ctr D x bits pad B jk ctr hct j⟩
    all_goals exact ⟨fin_ne (by simp), fin_ne (by simp), loopEntry_st_small D x bits pad B jk _ (by simp) (by simp)⟩
  apply WState.eq
  · funext i
    show (if _ then 0 else if i = sWT D then hWT else _) = _
    split_ifs with h1 h2
    · obtain ⟨n1, n2, -⟩ := hS i h1
      rw [shape_sh_other D x bits pad B jk _ _ _ i n1 n2]
    · subst h2; simp
    · by_cases h3 : i = sVI D
      · subst h3; simp
      · rw [shape_sh_other D x bits pad B jk _ _ _ i h2 h3, shape_sh_other D x bits pad B jk _ _ _ i h2 h3]
  · funext i
    show (if _ then [] else _) = _
    split_ifs with h1
    · obtain ⟨-, n2, n3⟩ := hS i h1
      rw [shape_st_other D x bits pad B jk _ _ _ i n2, n3]
    · rfl
  · rfl
  · rfl

end Terms

end

end NearCubicGates.Close.TermLoop
