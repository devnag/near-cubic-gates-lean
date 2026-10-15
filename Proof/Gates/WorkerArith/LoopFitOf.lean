import Proof.Gates.WorkerArith.FitSpec
import Proof.Gates.Setup.Positions
import Proof.Gates.Setup.ReadBound
import Proof.Gates.Gadget.CheckedSize

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith.WorkerBounds

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Setup NearCubicGates.Close.TermLoop
open NearCubicGates.Close.CheckedPCPP (supportsWord)
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount)

/-- The size bound `Z`. -/
def Zof (SS : ℕ) : ℕ := 40 * (SS + 1) ^ 3 + 10 * (SS + 2) ^ 2 + 4 * SS + 4
/-- The per-circuit width `W`. -/
def Wof (SS : ℕ) : ℕ := Zof SS + SS + 2
/-- The per-item cost bound. -/
def Bcof (SS : ℕ) : ℕ := 100000 * Wof SS ^ 3
/-- The call-frame bound. -/
def Vof (SS : ℕ) : ℕ := 30 * Zof SS + 100

theorem Zof_ge (SS : ℕ) : 40 * (SS + 1) ^ 3 + 10 * (SS + 2) ^ 2 + 4 * SS + 4 ≤ Zof SS := le_rfl

theorem gateFits_mono {n cap cap' : ℕ} (gt : NormalizedThresholdGate n) (h : Codec.GateFits cap gt) (hc : cap ≤ cap') :
    Codec.GateFits cap' gt := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨a.trans hc, b.trans hc, fun z hz => (c z hz).trans hc, d.trans hc⟩

theorem circuitFits_mono {n cap cap' : ℕ} (C : NCircuit n) (h : Codec.CircuitFits cap C) (hc : cap ≤ cap') :
    Codec.CircuitFits cap' C := by
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  exact ⟨fun gt hg => gateFits_mono gt (a gt hg) hc, b.trans hc, c.trans hc, d.trans hc, e.trans hc,
    fun z hz => (f z hz).trans hc, g.trans hc, i.trans hc, j.trans hc⟩

section Fit
variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- The capacity the loop needs. -/
noncomputable def capOf {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (SS : ℕ) : ℕ :=
  Vof SS + 1000 * (Zof SS + 1) + 20 * Wof SS + 20 + 4 * Wof SS + 4 + 16 * (frontSize s P g x B + 2) +
    (viOf s P g x bits pad B ctr ω (gadgets s g N)).length + 8 * loopBud s P g x bits pad B ctr ω

theorem termBud_le_loopBud {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
    (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) :
    termBud s P g x bits pad B ctr ω a t ≤ loopBud s P g x bits pad B ctr ω := by
  have h1 : termBud s P g x bits pad B ctr ω a t ≤ gadgetBud s P g x bits pad B ctr ω a :=
    Finset.single_le_sum (f := fun t => termBud s P g x bits pad B ctr ω a t) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ t)
  have h2 : gadgetBud s P g x bits pad B ctr ω a ≤ loopBud s P g x bits pad B ctr ω :=
    Finset.single_le_sum (f := fun a => gadgetBud s P g x bits pad B ctr ω a) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 ha)
  exact h1.trans h2

/-- **The loop's fit.** -/
theorem loopFit_of (hCF : CircuitSizeFit) (hRF : RowSizeFit) {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ)
    (B : Outer.OuterGuess (width s g N))
    (hdec : Worker.Decodes (width s g N) (guessWord N bits pad) B)
    (hpad : N / 16 + 1 ≤ pad)
    (hphys : N / 16 + 2 + auxN s P g x B * (2 + 2 * (N / 16) * (width s g N + 2)) + 10 * gadgets s g N ≤ pad)
    (SS : ℕ) (hw : (guessWord N bits pad).length ≤ SS) (hq : width s g N ≤ SS) (haux : auxN s P g x B ≤ SS)
    (hL : P.code.length (width s g N) ≤ SS)
    (hcw : (Codec.cwPrefix (circs s g N bits pad) (auxN s P g x B)).length ≤ SS)
    (hsupp : (supportsWord P.code (width s g N)).length ≤ SS) (hsys : sysCount s P g x B ≤ SS)
    (hω : (ratWord ω).length ≤ SS) (cap : ℕ) (hcap : capOf (P := P) ctr ω x bits pad B SS ≤ cap) :
    LoopFit (P := P) ctr ω x bits pad B cap (Zof SS) (Bcof SS) (Vof SS) := by
  have hZ := Zof_ge SS
  have hS1 : SS + 1 ≤ (SS + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hcapd : capOf (P := P) ctr ω x bits pad B SS = Vof SS + 1000 * (Zof SS + 1) + 20 * Wof SS + 20 + 4 * Wof SS + 4 +
      16 * (frontSize s P g x B + 2) + (viOf s P g x bits pad B ctr ω (gadgets s g N)).length +
      8 * loopBud s P g x bits pad B ctr ω := rfl
  -- every transcoded circuit
  have hcirc : ∀ k, (circuitWord (circs s g N bits pad k)).length ≤ 40 * (SS + 1) ^ 3 := by
    intro k
    have h := circuitWord_read_le (width s g N) ((guessWord N bits pad).drop
      (Codec.circPos (guessWord N bits pad) (width s g N) (pairEnd (guessWord N bits pad)) k))
    have hd : ((guessWord N bits pad).drop (Codec.circPos (guessWord N bits pad) (width s g N)
        (pairEnd (guessWord N bits pad)) k)).length + 1 ≤ SS + 1 := by simp; omega
    have h2 : 40 * (((guessWord N bits pad).drop (Codec.circPos (guessWord N bits pad) (width s g N)
        (pairEnd (guessWord N bits pad)) k)).length + 1) ^ 2 * (width s g N + 1) ≤ 40 * (SS + 1) ^ 3 := by
      calc _ ≤ 40 * (SS + 1) ^ 2 * (SS + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2)) (by omega)
        _ = 40 * (SS + 1) ^ 3 := by ring
    exact h.trans h2
  have hW : ∀ k, (circuitWord (circs s g N bits pad k)).length + width s g N + 2 ≤ Wof SS := by
    intro k; have := hcirc k; unfold Wof; omega
  -- every row
  have hrow : ∀ j < P.code.length (width s g N), (∀ y ∈ suppRows P (width s g N) j, y < width s g N) ∧
      (suppRows P (width s g N) j).length ≤ width s g N := by
    intro j hj
    unfold suppRows
    rw [dif_pos hj]
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      exact i.isLt
    · rw [List.length_map]; exact canonList_length_le _
  have hWr : width s g N + 2 ≤ SS + 2 := by omega
  have hrowW : ∀ j < P.code.length (width s g N),
      Codec.rowCost (suppRows P (width s g N) j) ≤ 100000 * (SS + 2) ^ 3 ∧
      (2 ^ (natBitLength (suppRows P (width s g N) j).length + 1) ≤ 4 * (SS + 2) + 4 ∧
        (suppRows P (width s g N) j).length ≤ 4 * (SS + 2) + 4 ∧
        ∀ y ∈ suppRows P (width s g N) j, natBitLength y + 1 ≤ 4 * (SS + 2) + 4) ∧
      (listWord natWord (suppRows P (width s g N) j)).length ≤ 10 * (SS + 2) ^ 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hrow j hj
    exact hRF (width s g N) _ (SS + 2) h1 h2 hWr
  have hSW : SS + 2 ≤ Wof SS := by unfold Wof; omega
  have hSW3 : 100000 * (SS + 2) ^ 3 ≤ Bcof SS := by
    unfold Bcof; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSW 3)
  have hV : 30 * Zof SS + 100 ≤ Vof SS := le_rfl
  refine ⟨hdec, hpad, ?_, fun a ha t => ?_, ?_, ?_, ?_, ?_, fun a ha t => ?_⟩
  · -- phys
    exact phys_of_pad N bits pad (width s g N) (auxN s P g x B) (gadgets s g N) hpad hphys
  · -- TermFit
    refine ⟨fun k _ => ?_, fun k _ => ?_, fun k _ => ?_, fun k _ => ?_, fun k _ => ?_, fun j hj => (hrowW j hj).1.trans
      hSW3, fun j hj => ?_, fun j hj => ?_, by unfold Zof; omega, by unfold Zof; omega, by unfold Zof; omega, ?_,
      by unfold Zof; omega, hV, by rw [hcapd] at hcap; omega⟩
    · exact circuitFits_mono _ (hCF _ _ (Wof SS) (hW k)).1 (by rw [hcapd] at hcap; omega)
    · exact (hCF _ _ (Wof SS) (hW k)).2.1.trans (le_refl _)
    · exact (hCF _ _ (Wof SS) (hW k)).2.2.2 cap (Vof SS) (by rw [hcapd] at hcap; omega)
    · exact (hCF _ _ (Wof SS) (hW k)).2.2.1.trans (le_refl _)
    · have := hcirc k; unfold Zof; omega
    · obtain ⟨-, ⟨a1, a2, a3⟩, -⟩ := hrowW j hj
      have : 4 * (SS + 2) + 4 ≤ cap := by rw [hcapd] at hcap; unfold Wof Zof at hcap; omega
      exact ⟨a1.trans this, a2.trans this, fun y hy => (a3 y hy).trans this⟩
    · obtain ⟨-, -, a4⟩ := hrowW j hj
      unfold Zof; omega
    · -- the term's witness field
      have h := readField_fst_len ((guessWord N bits pad).drop (fieldPos (guessWord N bits pad)
        (fieldsStart s P g x bits pad B) (10 * a + t.val)))
      have hd : ((guessWord N bits pad).drop (fieldPos (guessWord N bits pad)
        (fieldsStart s P g x bits pad B) (10 * a + t.val))).length ≤ (guessWord N bits pad).length := by simp
      show (fieldAt (guessWord N bits pad) (fieldsStart s P g x bits pad B) (10 * a + t.val)).length ≤ Zof SS
      unfold fieldAt
      unfold Zof; omega
  · have := hcw; unfold Zof; omega
  · rw [rowPrefix_supports_length]; unfold Zof; omega
  · unfold Zof; omega
  · rw [hcapd] at hcap; omega
  · have h := termBud_le_loopBud (P := P) ctr ω x bits pad B a ha t
    rw [hcapd] at hcap
    unfold Vof at hcap
    omega

end Fit

end NearCubicGates.Close.WorkerArith.WorkerBounds
