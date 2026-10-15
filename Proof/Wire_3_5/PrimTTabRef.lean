import Proof.Wire_3_5.FinalPassCornerRef
import Proof.Wire_3_5.CompilerMachinePoolConv
import Proof.SourceAssembly.AdmissionInput

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner

/-! ## The native gate words and the table width -/

/-- The native word of one bottom gate, as base's decoder writes it (`Production.bottomWord`). -/
def tabGW {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  thresholdWord (CompilerSemantics.nonStrictAsStrict g)

theorem tabGW_eq {n : ℕ} (g : NormalizedThresholdGate n) :
    tabGW g = natWord n ++ (List.ofFn g.weight).flatMap intWord ++ intWord (g.threshold - 1) := rfl

/-- The framed bottom region of a native circuit word. -/
def tabSeg {n : ℕ} (G : List (NormalizedThresholdGate n)) : List Bool := G.flatMap fun g => frame (tabGW g)

/-- **The table width**: the length of the framed bottom region. -/
def tabH {n : ℕ} (G : List (NormalizedThresholdGate n)) : ℕ := (tabSeg G).length

theorem tabSeg_cons {n : ℕ} (g : NormalizedThresholdGate n) (G : List (NormalizedThresholdGate n)) :
    tabSeg (g :: G) = frame (tabGW g) ++ tabSeg G := rfl

theorem tabSeg_append {n : ℕ} (G G' : List (NormalizedThresholdGate n)) :
    tabSeg (G ++ G') = tabSeg G ++ tabSeg G' := by
  simp [tabSeg, List.flatMap_append]

theorem tabGW_le_tabH {n : ℕ} (G : List (NormalizedThresholdGate n)) (g : NormalizedThresholdGate n) (hg : g ∈ G) :
    2 * (tabGW g).length + 1 ≤ tabH G := by
  induction G with
  | nil => simp at hg
  | cons g' G ih =>
    unfold tabH
    rw [tabSeg_cons, List.length_append, frame_length]
    rcases List.mem_cons.mp hg with rfl | h
    · omega
    · have := ih h
      unfold tabH at this
      omega

/-! ## Every accumulator fits in `h` bits -/

theorem one_le_nbl (v : ℕ) : 1 ≤ natBitLength v := by unfold natBitLength; omega

theorem pow_add_le (a b : ℕ) : 2 ^ a + (2 ^ b - 1) ≤ 2 ^ (a + b) := by
  obtain ⟨x, hx⟩ : ∃ x, 2 ^ a = x + 1 := ⟨2 ^ a - 1, by have := @Nat.one_le_two_pow a; omega⟩
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ b = y + 1 := ⟨2 ^ b - 1, by have := @Nat.one_le_two_pow b; omega⟩
  rw [pow_add, hx, hy, Nat.add_sub_cancel]
  nlinarith

/-- A sum of magnitudes against the bit lengths of their native words. -/
theorem mag_sum_le : ∀ (ws : List ℤ) (a : ℕ),
    (ws.map Int.natAbs).sum + 2 ^ a ≤ 2 ^ (a + (ws.map fun w => natBitLength w.natAbs).sum)
  | [], a => by simp
  | w :: ws, a => by
    have hw := CompilerMachine.Pool.lt_pow_natBitLength w.natAbs
    have ih := mag_sum_le ws (a + natBitLength w.natAbs)
    have hp := pow_add_le a (natBitLength w.natAbs)
    simp only [List.map_cons, List.sum_cons]
    rw [← Nat.add_assoc]
    omega

theorem intWord_length' (z : ℤ) : (intWord z).length = 2 * natBitLength z.natAbs + 2 := by
  simp [intWord, natWord, WilliamsPublishedForm.framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]; omega

theorem natWord_length' (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  simp [natWord, WilliamsPublishedForm.framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]; omega

theorem flatMap_intWord_length (ws : List ℤ) :
    (ws.flatMap intWord).length = (ws.map fun w => 2 * natBitLength w.natAbs + 2).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih, intWord_length', List.map_cons, List.sum_cons]

theorem nbl_sum_le (ws : List ℤ) :
    (ws.map fun w => natBitLength w.natAbs).sum ≤ (ws.map fun w => 2 * natBitLength w.natAbs + 2).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.map_cons, List.sum_cons]; omega

/-- **One gate's accumulators fit in its native word's length.** -/
theorem gate_mag_lt {n : ℕ} (g : NormalizedThresholdGate n) :
    (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ (tabGW g).length ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ (tabGW g).length := by
  set t := g.threshold - 1 with ht
  set a := natBitLength t.natAbs
  have hta : t.natAbs < 2 ^ a := CompilerMachine.Pool.lt_pow_natBitLength t.natAbs
  have hs := mag_sum_le (List.ofFn g.weight) a
  have hlen : a + ((List.ofFn g.weight).map fun w => natBitLength w.natAbs).sum < (tabGW g).length := by
    rw [tabGW_eq, List.length_append, List.length_append, intWord_length', flatMap_intWord_length]
    have := nbl_sum_le (List.ofFn g.weight)
    rw [← ht]
    omega
  have hp : 2 ^ (a + ((List.ofFn g.weight).map fun w => natBitLength w.natAbs).sum) < 2 ^ (tabGW g).length :=
    Nat.pow_lt_pow_right (by norm_num) hlen
  have hth : (-g.threshold).toNat ≤ t.natAbs + 1 ∧ (-(-g.threshold)).toNat ≤ t.natAbs + 1 := by omega
  omega

/-- **`hov` of `cw_spec` at the table width `tabH G`.** -/
theorem tab_hov {n : ℕ} (G : List (NormalizedThresholdGate n)) :
    ∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ tabH G ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ tabH G := by
  intro g hg
  have hle := tabGW_le_tabH G g hg
  have hp : 2 ^ (tabGW g).length ≤ 2 ^ tabH G := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := gate_mag_lt g
  omega

/-- Every weight and `θ − 1` of a gate of `G` is shorter than `h` bits. -/
theorem tab_nbl_le {n : ℕ} (G : List (NormalizedThresholdGate n)) (g : NormalizedThresholdGate n) (hg : g ∈ G) :
    (∀ i, natBitLength (g.weight i).natAbs + 1 ≤ tabH G) ∧ natBitLength (g.threshold - 1).natAbs + 1 ≤ tabH G ∧
      natBitLength n + 1 ≤ tabH G := by
  have hle := tabGW_le_tabH G g hg
  rw [tabGW_eq, List.length_append, List.length_append, intWord_length', natWord_length',
    flatMap_intWord_length] at hle
  refine ⟨fun i => ?_, by omega, by omega⟩
  have hm : 2 * natBitLength (g.weight i).natAbs + 2 ≤
      ((List.ofFn g.weight).map fun w => 2 * natBitLength w.natAbs + 2).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨g.weight i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩)
  omega

/-! ## The words the transducer writes -/

theorem pairW_of_int (h : ℕ) (z : ℤ) :
    pairW h z = if z < 0 then frame (binary h 0) ++ frame (binary h z.natAbs)
      else frame (binary h z.natAbs) ++ frame (binary h 0) := by
  unfold pairW
  split_ifs with hz
  · rw [show z.toNat = 0 by omega, show (-z).toNat = z.natAbs by omega]
  · rw [show z.toNat = z.natAbs by omega, show (-z).toNat = 0 by omega]

/-- The pair of `−θ` from the native word of `t = θ − 1`. -/
theorem pairW_negThr (h : ℕ) (t : ℤ) :
    pairW h (-(t + 1)) = if t < 0 then frame (binary h (t.natAbs - 1)) ++ frame (binary h 0)
      else frame (binary h 0) ++ frame (binary h (t.natAbs + 1)) := by
  unfold pairW
  split_ifs with ht
  · rw [show (-(t + 1)).toNat = t.natAbs - 1 by omega, show (-(-(t + 1))).toNat = 0 by omega]
  · rw [show (-(t + 1)).toNat = 0 by omega, show (-(-(t + 1))).toNat = t.natAbs + 1 by omega]

theorem neg_threshold_eq {n : ℕ} (g : NormalizedThresholdGate n) : -g.threshold = -((g.threshold - 1) + 1) := by ring

theorem frameP_append' (a b : List Bool) : frameP (a ++ b) = frameP a ++ frameP b := by
  simp [frameP, List.flatMap_append]

/-- The framed cells of a native natural word. -/
theorem frameP_natWord (v : ℕ) :
    frameP (natWord v) = frameP (List.replicate (natBitLength v) true) ++ true :: false ::
      frameP (binary (natBitLength v) v) := by
  rw [CompilerMachine.Pool.natWord_eq, frameP_append']
  rfl

/-! ## Increment and decrement as carry maps -/

/-- A 1-bit transducer with a carry, over one word. -/
def cmap (out nxt : Bool → Bool → Bool) : List Bool → Bool → List Bool
  | [], _ => []
  | b :: bs, c => out b c :: cmap out nxt bs (nxt b c)

def incOut (b c : Bool) : Bool := xor b c
def incNxt (b c : Bool) : Bool := b && c
def decOut (b c : Bool) : Bool := xor b c
def decNxt (b c : Bool) : Bool := !b && c
def cpyOut (b _ : Bool) : Bool := b
def cpyNxt (_ _ : Bool) : Bool := false

theorem cmap_length (out nxt : Bool → Bool → Bool) : ∀ (bs : List Bool) (c : Bool),
    (cmap out nxt bs c).length = bs.length
  | [], _ => rfl
  | b :: bs, c => by simp [cmap, cmap_length out nxt bs]

theorem cmap_cpy : ∀ (bs : List Bool) (c : Bool), cmap cpyOut cpyNxt bs c = bs
  | [], _ => rfl
  | b :: bs, c => by simp [cmap, cpyOut, cmap_cpy bs]

theorem cmap_inc_false : ∀ (bs : List Bool), cmap incOut incNxt bs false = bs
  | [] => rfl
  | b :: bs => by simp [cmap, incOut, incNxt, cmap_inc_false bs]

theorem cmap_dec_false : ∀ (bs : List Bool), cmap decOut decNxt bs false = bs
  | [] => rfl
  | b :: bs => by simp [cmap, decOut, decNxt, cmap_dec_false bs]

/-- **Increment** of an `h`-bit word. -/
theorem cmap_inc : ∀ (h v : ℕ), v + 1 < 2 ^ h → cmap incOut incNxt (binary h v) true = binary h (v + 1)
  | 0, v, hv => by simp at hv
  | h + 1, v, hv => by
    simp only [binary, cmap, incOut, incNxt]
    rcases Nat.mod_two_eq_zero_or_one v with he | ho
    · have e1 : (v + 1) % 2 = 1 := by omega
      have e2 : (v + 1) / 2 = v / 2 := by omega
      simp [he, e1, e2, cmap_inc_false]
    · have e1 : (v + 1) % 2 = 0 := by omega
      have e2 : (v + 1) / 2 = v / 2 + 1 := by omega
      have hv' : v / 2 + 1 < 2 ^ h := by rw [pow_succ] at hv; omega
      simp [ho, e1, e2, cmap_inc h (v / 2) hv']

/-- **Decrement** of an `h`-bit word. -/
theorem cmap_dec : ∀ (h v : ℕ), 1 ≤ v → v < 2 ^ h → cmap decOut decNxt (binary h v) true = binary h (v - 1)
  | 0, v, _, hv => by simp at hv; omega
  | h + 1, v, h1, hv => by
    simp only [binary, cmap, decOut, decNxt]
    rcases Nat.mod_two_eq_zero_or_one v with he | ho
    · have e1 : (v - 1) % 2 = 1 := by omega
      have e2 : (v - 1) / 2 = v / 2 - 1 := by omega
      have h1' : 1 ≤ v / 2 := by omega
      have hv' : v / 2 < 2 ^ h := by rw [pow_succ] at hv; omega
      simp [he, e1, e2, cmap_dec h (v / 2) h1' hv']
    · have e1 : (v - 1) % 2 = 0 := by omega
      have e2 : (v - 1) / 2 = v / 2 := by omega
      simp [ho, e1, e2, cmap_dec_false]

/-- The padded word of a magnitude of `k = natBitLength v` bits inside `h` bits (C3's `binary_pad`). -/
theorem binary_pad' (v h : ℕ) (hk : natBitLength v ≤ h) :
    binary h v = binary (natBitLength v) v ++ List.replicate (h - natBitLength v) false := by
  have hv : v < 2 ^ h := lt_of_lt_of_le (CompilerMachine.Pool.lt_pow_natBitLength v)
    (Nat.pow_le_pow_right (by norm_num) hk)
  exact CompilerMachine.Pool.binary_pad v h ((one_le_nbl v).trans hk) hv

end NearCubicWires.WireExponent3_5.PrimT
