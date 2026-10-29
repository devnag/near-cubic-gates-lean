import SourceAdapters.RAMACSP.PackParams
import SourceAdapters.ACSP.Affine
import SourceAdapters.Joins.AffineRouting

/-!
# The affine constraint instance

The instance of `thm:short-pcp-ours`, Step 1, with field modulus chosen by Shoup,
monomial basis of H, neighbor pairs `(1,b)` from the global bank, and the direct
input subspace of `def:acsp`. Its basis lists the column coordinates first and
then the lane coordinates; its offset is the input-record lane `2^τ`.

All data are total on clock requests. In particular, the selected input basis
is printed literally even when n > t; independence and reducedness are proved
only under the length guard. The constraint circuit is a parameter here.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary Polynomial

variable (V : Verifier)

/-- The `app:affine-embedding` layout at the clock `t`: `k = k_N = τ + 1`, `ℓ`, `q = d + ω`; `mH = k + ℓ + q + 4`. -/
def ownLayout (t : ℕ) : Routing.Layout where
  k := laneExp V t
  ell := stageExp V t
  q := colExp V t
  k_pos := by unfold laneExp; omega
  stages_fit := two_laneExp_le V t

theorem ownLayout_m (t : ℕ) : (ownLayout V t).m = domExp V t := rfl

/-- `x̄ = x10^j` of length `2^m` (P02 `padInput`; `def:acsp` `xbar r := x̄`). -/
def ownXbar (r : ClockRequest) : List Bool := padInput (clockConst V) r.2 r.1.2

/-- `m = log₂ |x̄|`, the input exponent. -/
def inExp (r : ClockRequest) : ℕ := Nat.log 2 (ownXbar V r).length

/-- The `f + 1`-bit mask of a polynomial of degree `f` (the modulus; bit `f` set). -/
def modMask (a : (ZMod 2)[X]) (f : ℕ) : ℕ := WireExponent3_5.GF.ofPoly a (f + 1)

/-- The input exponent as the ceiling logarithm, for every request. -/
theorem inExp_eq_clog (r : ClockRequest) :
    inExp V r = Nat.clog 2 (max (r.1.1 + 1) (wordW V r.2)) := by
  unfold inExp ownXbar
  rw [padInput_length _ _ _ (by unfold inputPadLength; exact le_trans (le_max_left _ _) (le_two_pow_clog _))]
  unfold inputPadLength; rw [Nat.log_pow (by norm_num)]; rfl

/-- Padding length is a power of two without a running-time or length promise. -/
theorem ownXbar_length (r : ClockRequest) : (ownXbar V r).length = 2 ^ inExp V r := by
  have hle : r.1.1 + 1 ≤ inputPadLength (clockConst V) r.1.1 r.2 := by
    unfold inputPadLength; exact le_trans (le_max_left _ _) (le_two_pow_clog _)
  unfold ownXbar
  rw [padInput_length _ _ _ hle, inExp_eq_clog]
  rfl

/-- The actual padded input, including its delimiter, for every request. -/
theorem ownXbar_padding (r : ClockRequest) :
    ownXbar V r = List.ofFn r.1.2 ++ true :: List.replicate (2 ^ inExp V r - r.1.1 - 1) false := by
  unfold ownXbar padInput
  rw [inExp_eq_clog]
  rfl

/-- The column portion fits in the selected input dimension on every request. -/
theorem wordExp_le_inExp (r : ClockRequest) : wordExp V r.2 ≤ inExp V r := by
  apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
  rw [inExp_eq_clog]
  have h := (le_max_right (r.1.1 + 1) (wordW V r.2)).trans (le_two_pow_clog _)
  simpa only [wordW_eq] using h

/-- The selected input basis: column coordinates, followed by lane coordinates. -/
def inputBasisMasks (r : ClockRequest) : List ℕ :=
  (List.range (wordExp V r.2)).map (fun j => 2 ^ (laneExp V r.2 + stageExp V r.2 + j)) ++
    (List.range (inExp V r - wordExp V r.2)).map (fun j => 2 ^ j)

/-- The input-record lane offset, independent of the validity guard. -/
def inputOffsetMask (r : ClockRequest) : ℕ := 2 ^ tau V r.2

theorem inputBasisMasks_length (r : ClockRequest) : (inputBasisMasks V r).length = inExp V r := by
  have h := wordExp_le_inExp V r
  simp only [inputBasisMasks, List.length_append, List.length_map, List.length_range]
  omega

/-- The concrete instance with exactly one input subspace. -/
def ownInst (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate) (r : ClockRequest) :
    ACSP.Affine.Instance where
  f := fieldExp V r.2
  irr := modMask (irrPoly (fieldExp V r.2)) (fieldExp V r.2)
  hBasis := (List.range (domExp V r.2)).map (2 ^ ·)
  hOffset := 0
  nbr := (Routing.globalBank (ownLayout V r.2)).map (fun b => (1, b))
  cons := cons r
  iBasis := inputBasisMasks V r
  iOffset := inputOffsetMask V r

theorem ownInst_iOffset_mask (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)
    (r : ClockRequest) : (ownInst V irrPoly cons r).iOffset = 2 ^ tau V r.2 := rfl

theorem ownInst_nbr_list (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)
    (r : ClockRequest) :
    (ownInst V irrPoly cons r).nbr = (Routing.globalBank (ownLayout V r.2)).map (fun b => (1, b)) := rfl

theorem ownInst_iBasis_list (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)
    (r : ClockRequest) : (ownInst V irrPoly cons r).iBasis = inputBasisMasks V r := rfl

/-- The direct input dimension is exact on all requests. -/
theorem ownInst_m (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate)
    (r : ClockRequest) : (ownInst V irrPoly cons r).m = inExp V r :=
  inputBasisMasks_length V r

/-- **The input exponent** for the input subspace of `app:affine-embedding`. The concrete padding
under `2 ≤ n ≤ t` gives `|x̄| = 2^m`, `1 ≤ m`, `ω ≤ m` and `m < τ` (`|x̄| < T`).
The basis of `I` has `ω` column bits followed by `m − ω` lane bits. -/
theorem inExp_facts (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    (ownXbar V r).length = 2 ^ inExp V r ∧ 1 ≤ inExp V r ∧ wordExp V r.2 ≤ inExp V r ∧
      inExp V r < tau V r.2 ∧ 2 ≤ (ownXbar V r).length := by
  obtain ⟨-, hxT, h2, hpow⟩ := padInput_facts V (clockConst V) r.1.1 r.2 le_rfl (by omega) hnt r.1.2
  have h16 := sixteen_le_clockConst V
  obtain ⟨h1, hdvd, -, -⟩ := inputPad_facts (clockConst V) r.1.1 r.2 h16 (by omega) hnt
  have hlen := padInput_length (clockConst V) r.2 r.1.2 h1
  have hpow' : (ownXbar V r).length = 2 ^ inExp V r := hpow
  refine ⟨hpow', ?_, ?_, ?_, h2⟩
  · exact Nat.log_pos (by norm_num) h2
  · have hw : wordWidth (clockConst V) r.2 ≤ (ownXbar V r).length := by
      unfold ownXbar; rw [hlen]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by unfold inputPadLength; positivity)) hdvd
    rw [hpow'] at hw
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hw
  · have h := hxT
    rw [show padInput (clockConst V) r.2 r.1.2 = ownXbar V r from rfl, hpow'] at h
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h

end NearCubicGates.Adapters.RAMACSP
