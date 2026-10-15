import Proof.Gates.TermLoop.Pre
import Proof.Gates.WorkerArith.TermH
import Proof.Gates.WorkerArith.TermK

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
open NearCubicGates.Close.WorkerArith (TermEnv termIdeal TermPre TermBase TermFit termW1 termW2 termCost bud1 bud2
  entryWord opdAt)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-- Registers in the term programs' layout. -/
structure RegOK (v : Fin nrW → ℕ) : Prop where
  r6 : v (regE 6) = width s g N
  r7 : v (regE 7) = (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length
  r8 : v (regE 8) = (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length
  z : ∀ i : Fin 40, 10 ≤ i.val → v (regE i) = 0

theorem regE_ne (i j : Fin 40) (h : i ≠ j) : regE i ≠ regE j := fun e => h (regE.injective e)

theorem regE_ne9 (i : Fin 40) (h : i.val ≠ 9) : regE i ≠ regE 9 := regE_ne i 9 (fun e => h (by rw [e]; rfl))

theorem shape_opdAt (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (a b c : Fin 40) (ha : a.val ≠ 9) (hb : b.val ≠ 9)
    (hc : c.val ≠ 9) :
    opdAt (Shape D x bits pad B jk vi wh v) (regE a) (regE b) (regE c) =
      ⟨decide (v (regE a) ≠ 0), decide (v (regE b) ≠ 0), v (regE c)⟩ := by
  simp only [opdAt, shape_val, Function.update_of_ne (regE_ne9 a ha), Function.update_of_ne (regE_ne9 b hb),
    Function.update_of_ne (regE_ne9 c hc)]

/-- The witness word at the head. -/
def headField (wh : ℕ) : List Bool := (readField ((guessWord N bits pad).drop wh)).1

theorem headField_end (wh : ℕ) (hwh : fieldEnd (guessWord N bits pad) wh ≤ (guessWord N bits pad).length) :
    ((guessWord N bits pad).take wh).length + (headField bits pad (N := N) wh).length + 1 +
      (headField bits pad (N := N) wh).length = fieldEnd (guessWord N bits pad) wh := by
  obtain ⟨-, hl, hp⟩ := field_split (guessWord N bits pad) wh hwh
  unfold headField; rw [hl, List.length_take, Nat.min_eq_left hp]; rfl

/-- **The one-operand term program on a shape.** -/
theorem term1_shape (cap Z Bc V : ℕ) (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ)
    (hR : RegOK (P := P) x bits pad B v)
    (hwh : fieldEnd (guessWord N bits pad) wh ≤ (guessWord N bits pad).length)
    (hfit : TermFit cap (circs s g N bits pad) (auxN s P g x B) (suppRows P (width s g N))
      (P.code.length (width s g N)) ω (headField bits pad (N := N) wh) Z Bc V)
    (hs : v (regE 1) ≠ 0 → v (regE 2) < width s g N + P.code.length (width s g N))
    (ha : v (regE 1) = 0 → v (regE 2) < auxN s P g x B)
    (h7 : (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length ≤ Z)
    (h8 : (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length ≤ Z)
    (h2 : v (regE 2) ≤ Z)
    (hcap : vi.length + 1000 * (Z + 1) + 8 * bud1 ctr (circs s g N bits pad) ω (headField bits pad (N := N) wh)
      ⟨decide (v (regE 0) ≠ 0), decide (v (regE 1) ≠ 0), v (regE 2)⟩ ≤ cap) :
    ∃ τ, WXExec cap (termW1 (termEnv D) ctr (ctrMap D ctr hct) ω) (Shape D x bits pad B jk vi wh v) τ
        (termCost ctr.program.program.tapeCount Z Bc (bud1 ctr (circs s g N bits pad) ω
          (headField bits pad (N := N) wh) ⟨decide (v (regE 0) ≠ 0), decide (v (regE 1) ≠ 0), v (regE 2)⟩)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (model1 ctr (circs s g N bits pad)
        (suppRows P (width s g N)) ω (headField bits pad (N := N) wh)
        ⟨decide (v (regE 0) ≠ 0), decide (v (regE 1) ≠ 0), v (regE 2)⟩)))
        (fieldEnd (guessWord N bits pad) wh) v) τ := by
  have hP := termPre_shape D x bits pad B jk ctr hct vi wh v hR.r6 hR.r7 hR.r8 hR.z hwh
  have hop := shape_opdAt D x bits pad B jk vi wh v 0 1 2 (by decide) (by decide) (by decide)
  have hv : ∀ i : Fin 40, i.val ≠ 9 → (Shape D x bits pad B jk vi wh v).val ((termEnv D).R i) = v (regE i) :=
    fun i hi => by simp only [termEnv, shape_val]; rw [Function.update_of_ne (regE_ne9 i hi)]
  have h9 : (Shape D x bits pad B jk vi wh v).val ((termEnv D).R 9) = vi.length := by
    simp only [termEnv, shape_val, Function.update_self]
  obtain ⟨τ, e, sm⟩ := WorkerArith.termW1_ideal ctr (termEnv D) (ctrMap D ctr hct) (circs s g N bits pad)
    (auxN s P g x B) (suppRows P (width s g N)) (P.code.length (width s g N)) ω (headField bits pad (N := N) wh)
    _ _ cap Z Bc V (Shape D x bits pad B jk vi wh v) hP hfit
    (by rw [hv 1 (by decide), hv 2 (by decide)]; exact hs) (by rw [hv 1 (by decide), hv 2 (by decide)]; exact ha)
    (by rw [hv 7 (by decide), hR.r7]; exact h7) (by rw [hv 8 (by decide), hR.r8]; exact h8)
    (by rw [hv 2 (by decide)]; exact h2) (by rw [h9]; simp only [termEnv] at hop ⊢; rw [hop]; exact hcap)
  refine ⟨τ, ?_, ?_⟩
  · simpa only [termEnv, hop] using e
  · rw [headField_end bits pad (N := N) wh hwh] at sm
    rw [← termIdeal_shape D x bits pad B jk ctr hct vi wh v]
    simpa only [termEnv, hop] using sm

/-- **The two-operand term program on a shape.** -/
theorem term2_shape (cap Z Bc V : ℕ) (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ)
    (hR : RegOK (P := P) x bits pad B v)
    (hwh : fieldEnd (guessWord N bits pad) wh ≤ (guessWord N bits pad).length)
    (hfit : TermFit cap (circs s g N bits pad) (auxN s P g x B) (suppRows P (width s g N))
      (P.code.length (width s g N)) ω (headField bits pad (N := N) wh) Z Bc V)
    (hs1 : v (regE 1) ≠ 0 → v (regE 2) < width s g N + P.code.length (width s g N))
    (ha1 : v (regE 1) = 0 → v (regE 2) < auxN s P g x B)
    (hs2 : v (regE 4) ≠ 0 → v (regE 5) < width s g N + P.code.length (width s g N))
    (ha2 : v (regE 4) = 0 → v (regE 5) < auxN s P g x B)
    (h7 : (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length ≤ Z)
    (h8 : (Codec.rowPrefix (suppRows P (width s g N)) (P.code.length (width s g N))).length ≤ Z)
    (h2 : v (regE 2) ≤ Z) (h5 : v (regE 5) ≤ Z)
    (hcap : vi.length + 1000 * (Z + 1) + 8 * bud2 ctr (circs s g N bits pad) (suppRows P (width s g N)) ω
      (headField bits pad (N := N) wh) ⟨decide (v (regE 0) ≠ 0), decide (v (regE 1) ≠ 0), v (regE 2)⟩
      ⟨decide (v (regE 3) ≠ 0), decide (v (regE 4) ≠ 0), v (regE 5)⟩ ≤ cap) :
    ∃ τ, WXExec cap (termW2 (termEnv D) ctr (ctrMap D ctr hct) ω) (Shape D x bits pad B jk vi wh v) τ
        (termCost ctr.program.program.tapeCount Z Bc (bud2 ctr (circs s g N bits pad) (suppRows P (width s g N)) ω
          (headField bits pad (N := N) wh) ⟨decide (v (regE 0) ≠ 0), decide (v (regE 1) ≠ 0), v (regE 2)⟩
          ⟨decide (v (regE 3) ≠ 0), decide (v (regE 4) ≠ 0), v (regE 5)⟩)) ∧
      SimW (Shape D x bits pad B jk (vi ++ marks (entryWord (model2 ctr (circs s g N bits pad)
        (suppRows P (width s g N)) ω (headField bits pad (N := N) wh)
        ⟨decide (v (regE 0) ≠ 0), decide (v (regE 1) ≠ 0), v (regE 2)⟩
        ⟨decide (v (regE 3) ≠ 0), decide (v (regE 4) ≠ 0), v (regE 5)⟩)))
        (fieldEnd (guessWord N bits pad) wh) v) τ := by
  have hP := termPre_shape D x bits pad B jk ctr hct vi wh v hR.r6 hR.r7 hR.r8 hR.z hwh
  have hop := shape_opdAt D x bits pad B jk vi wh v 0 1 2 (by decide) (by decide) (by decide)
  have hop' := shape_opdAt D x bits pad B jk vi wh v 3 4 5 (by decide) (by decide) (by decide)
  have hv : ∀ i : Fin 40, i.val ≠ 9 → (Shape D x bits pad B jk vi wh v).val ((termEnv D).R i) = v (regE i) :=
    fun i hi => by simp only [termEnv, shape_val]; rw [Function.update_of_ne (regE_ne9 i hi)]
  have h9 : (Shape D x bits pad B jk vi wh v).val ((termEnv D).R 9) = vi.length := by
    simp only [termEnv, shape_val, Function.update_self]
  obtain ⟨τ, e, sm⟩ := WorkerArith.termW2_ideal ctr (termEnv D) (ctrMap D ctr hct) (circs s g N bits pad)
    (auxN s P g x B) (suppRows P (width s g N)) (P.code.length (width s g N)) ω (headField bits pad (N := N) wh)
    _ _ cap Z Bc V (Shape D x bits pad B jk vi wh v) hP hfit
    (by rw [hv 1 (by decide), hv 2 (by decide)]; exact hs1) (by rw [hv 1 (by decide), hv 2 (by decide)]; exact ha1)
    (by rw [hv 4 (by decide), hv 5 (by decide)]; exact hs2) (by rw [hv 4 (by decide), hv 5 (by decide)]; exact ha2)
    (by rw [hv 7 (by decide), hR.r7]; exact h7) (by rw [hv 8 (by decide), hR.r8]; exact h8)
    (by rw [hv 2 (by decide)]; exact h2) (by rw [hv 5 (by decide)]; exact h5)
    (by rw [h9]; simp only [termEnv] at hop hop' ⊢; rw [hop, hop']; exact hcap)
  refine ⟨τ, ?_, ?_⟩
  · simpa only [termEnv, hop, hop'] using e
  · rw [headField_end bits pad (N := N) wh hwh] at sm
    rw [← termIdeal_shape D x bits pad B jk ctr hct vi wh v]
    simpa only [termEnv, hop, hop'] using sm

/-! ## Clearing the operand registers -/

/-- The register file with `R 0 … R 5` cleared. -/
def zeroOps (v : Fin nrW → ℕ) : Fin nrW → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update v
    (regE 0) 0) (regE 1) 0) (regE 2) 0) (regE 3) 0) (regE 4) 0) (regE 5) 0

/-- The sum of the operand registers. -/
def opsSum (v : Fin nrW → ℕ) : ℕ :=
  v (regE 0) + v (regE 1) + v (regE 2) + v (regE 3) + v (regE 4) + v (regE 5)

theorem clearOps_spec (cap : ℕ) (vi : List Bool) (wh : ℕ) (v : Fin nrW → ℕ) (hc : opsSum v ≤ cap) :
    WExec cap (clearOps D) (Shape D x bits pad B jk vi wh v) (Shape D x bits pad B jk vi wh (zeroOps v))
      (3 * opsSum v + 11) := by
  have ne : ∀ i j : Fin 40, i ≠ j → regE i ≠ regE j := regE_ne
  have n9 : ∀ i : Fin 40, i.val < 6 → regE i ≠ regE 9 := fun i h => regE_ne9 i (by omega)
  unfold opsSum at hc
  have val : ∀ (u : Fin nrW → ℕ) (i : Fin 40), i.val < 6 →
      (Shape D x bits pad B jk vi wh u).val (regE i) = u (regE i) := fun u i h => by
    simp only [shape_val]; rw [Function.update_of_ne (n9 i h)]
  have st : ∀ (u : Fin nrW → ℕ) (i : Fin 40), i.val < 6 →
      (Shape D x bits pad B jk vi wh u).setv (regE i) 0 = Shape D x bits pad B jk vi wh (Function.update u (regE i) 0) :=
    fun u i h => shape_setv D x bits pad B jk vi wh u _ (n9 i h) 0
  have c : ∀ (u : Fin nrW → ℕ) (i : Fin 40) (hi : i.val < 6), u (regE i) ≤ cap →
      WExec cap (WM.clear (regE i)) (Shape D x bits pad B jk vi wh u)
        (Shape D x bits pad B jk vi wh (Function.update u (regE i) 0)) (3 * u (regE i) + 1) := by
    intro u i hi hu
    rw [← st u i hi]
    exact wclear_spec cap (regE i) _ _ (val u i hi) (by rw [val u i hi]; exact hu)
  have u1 : ∀ (u : Fin nrW → ℕ) (i j : Fin 40), i ≠ j → Function.update u (regE i) 0 (regE j) = u (regE j) :=
    fun u i j h => Function.update_of_ne (ne j i (Ne.symm h)) _ _
  refine WExec.mono (WExec.seq (c v 0 (by decide) (by omega))
    (WExec.seq (c _ 1 (by decide) (by rw [u1 _ 0 1 (by decide)]; omega))
    (WExec.seq (c _ 2 (by decide) (by rw [u1 _ 1 2 (by decide), u1 _ 0 2 (by decide)]; omega))
    (WExec.seq (c _ 3 (by decide) (by rw [u1 _ 2 3 (by decide), u1 _ 1 3 (by decide), u1 _ 0 3 (by decide)]; omega))
    (WExec.seq (c _ 4 (by decide) (by
        rw [u1 _ 3 4 (by decide), u1 _ 2 4 (by decide), u1 _ 1 4 (by decide), u1 _ 0 4 (by decide)]; omega))
      (c _ 5 (by decide) (by rw [u1 _ 4 5 (by decide), u1 _ 3 5 (by decide), u1 _ 2 5 (by decide),
        u1 _ 1 5 (by decide), u1 _ 0 5 (by decide)]; omega))))))) ?_
  rw [u1 _ 0 1 (by decide), u1 _ 1 2 (by decide), u1 _ 0 2 (by decide), u1 _ 2 3 (by decide), u1 _ 1 3 (by decide),
    u1 _ 0 3 (by decide), u1 _ 3 4 (by decide), u1 _ 2 4 (by decide), u1 _ 1 4 (by decide), u1 _ 0 4 (by decide),
    u1 _ 4 5 (by decide), u1 _ 3 5 (by decide), u1 _ 2 5 (by decide), u1 _ 1 5 (by decide), u1 _ 0 5 (by decide)]
  unfold opsSum; omega

/-- **One term: load, run, clear.** -/
theorem step_ideal (cap : ℕ) (ld : WM (nsW D) nrW) (T : WMX (nsW D) nrW) (vi : List Bool) (wh wh' : ℕ)
    (v v' : Fin nrW → ℕ) (e : List Bool) (c1 c2 : ℕ)
    (hld : WExec cap ld (Shape D x bits pad B jk vi wh v) (Shape D x bits pad B jk vi wh v') c1)
    (hT : ∃ τ, WXExec cap T (Shape D x bits pad B jk vi wh v') τ c2 ∧
      SimW (Shape D x bits pad B jk (vi ++ e) wh' v') τ)
    (hz : zeroOps v' = v) (hc : opsSum v' ≤ cap) :
    ∃ τ, WXExec cap (.seq (.wm ld) (.seq T (.wm (clearOps D)))) (Shape D x bits pad B jk vi wh v) τ
        (c1 + 1 + (c2 + 1 + (3 * opsSum v' + 11))) ∧
      SimW (Shape D x bits pad B jk (vi ++ e) wh' v) τ := by
  obtain ⟨τ1, e1, s1⟩ := hT
  have h2 := clearOps_spec D x bits pad B jk cap (vi ++ e) wh' v' hc
  rw [hz] at h2
  have inner := Worker.seq_sim e1 s1 ⟨_, WXExec.wm h2, SimW.refl _⟩
  exact Worker.seq_sim (WXExec.wm hld) (SimW.refl _) inner

end

end NearCubicGates.Close.TermLoop
