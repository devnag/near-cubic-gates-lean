import Proof.Gates.Codec.FieldCircuitSpec
import Proof.Gates.Codec.Seek

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-- The position of the `j`-th circuit field. -/
def circPos (w : List Bool) (q p0 : ℕ) (j : ℕ) : ℕ := iter (fun p => circuitEnd w p q) p0 j

/-- The `j`-th decoded circuit. -/
def circAt (w : List Bool) (q p0 : ℕ) (j : ℕ) : Interfaces.NCircuit q := (readCircuit q (w.drop (circPos w q p0 j))).1

theorem emitted_cw (w : List Bool) (q p0 m : ℕ) :
    emitted (fun p => (readCircuit q (w.drop p)).1) Interfaces.circuitWord (fun p => circuitEnd w p q) p0 m =
      (List.range m).flatMap fun j => Interfaces.circuitWord (circAt w q p0 j) := by
  simp [emitted, circAt, circPos, List.flatMap_map]

theorem marks_emitted_cw (w : List Bool) (q p0 m : ℕ) :
    marks (emitted (fun p => (readCircuit q (w.drop p)).1) Interfaces.circuitWord (fun p => circuitEnd w p q) p0 m) =
      cwPrefix (circAt w q p0) m := by
  rw [emitted_cw]; simp [cwPrefix, marks_flatMap]

/-- `m` circuit fields. -/
def transcodeW (W o : Fin (ns + 1)) (A : Fin 18 ↪ Fin nr) (C : Fin nr) : WM ns nr := repLoop C (circuitW W o A)

theorem transcodeW_spec (W o : Fin (ns + 1)) (hWo : W ≠ o) (A : Fin 18 ↪ Fin nr) (C : Fin nr) (hC : ∀ i, A i ≠ C)
    (q m cb : ℕ) (σ : WState ns nr) (hq : σ.val (A 6) = q) (hz : ∀ i : Fin 18, i ≠ 6 → i ≠ 13 → σ.val (A i) = 0)
    (ho : σ.sh o = (σ.st o).length) (hC0 : σ.val C = m) (hm : m ≤ cap)
    (hcap1 : (σ.st W).length + q + 1 ≤ cap)
    (hcapO : σ.val (A 13) + 2 * ((List.range m).flatMap fun j => Interfaces.circuitWord (circAt (σ.st W) q (σ.sh W) j)).length +
      q + 7 * (σ.st W).length + 6 * natBitLength q + 20 ≤ cap)
    (hcb : ∀ j < m, circuitWCost q (σ.st W).length (cK (σ.st W) (circPos (σ.st W) q (σ.sh W) j))
      (cL (σ.st W) (circPos (σ.st W) q (σ.sh W) j) q) ≤ cb) :
    WExec cap (transcodeW W o A C) σ
      ((appendO (σ.seth W (circPos (σ.st W) q (σ.sh W) m)) o (A 13)
        (cwPrefix (circAt (σ.st W) q (σ.sh W)) m)).setv C 0) (m * (cb + 4) + 1) := by
  set w := σ.st W with hw
  have e := repEmit_spec cap W o (A 13) C (circuitW W o A) (fun p => (readCircuit q (w.drop p)).1) Interfaces.circuitWord
    (fun p => circuitEnd w p q) cb m σ hWo (hC 13).symm hC0 hm ho
    (fun i hi τ h1 h2 h3 h4 h5 h6 => by
      have hτw : τ.st W = w := h3
      have hpre : CirPre cap W o A τ q := by
        refine ⟨hWo, ?_, ?_, h5, ?_, ?_⟩
        · rw [h1 _ (A.injective.ne (by decide)) (hC 6)]; exact hq
        · intro k hk6 hk13
          rw [h1 _ (A.injective.ne hk13) (hC k)]; exact hz k hk6 hk13
        · rw [hτw]; exact hcap1
        · rw [hτw, h6, h4]
          have hle : (emitted (fun p => (readCircuit q (w.drop p)).1) Interfaces.circuitWord (fun p => circuitEnd w p q) (σ.sh W) i).length +
              (Interfaces.circuitWord (readCircuit q (w.drop (iter (fun p => circuitEnd w p q) (σ.sh W) i))).1).length ≤
              ((List.range m).flatMap fun j => Interfaces.circuitWord (circAt w q (σ.sh W) j)).length := by
            have := emitted_mono (fun p => (readCircuit q (w.drop p)).1) Interfaces.circuitWord (fun p => circuitEnd w p q) (σ.sh W)
              (i + 1) m (by omega)
            rw [emitted_succ, List.length_append, emitted_cw w q (σ.sh W) m] at this
            exact this
          omega
      have e := circuitW_spec W o A τ q hpre
      rw [hτw] at e
      refine WExec.mono e ?_
      rw [h4]
      exact hcb i hi)
  rw [marks_emitted_cw] at e
  exact e

end NearCubicGates.Close.Codec
