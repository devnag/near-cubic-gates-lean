import SourceAdapters.Routing.CoordinateMachineInput
import SourceAdapters.Routing.CoordinateMachineInputFrame
import SourceAdapters.ShortPCP.Machines.FLangRun
import SourceAdapters.Code.Preparation

/-!
# Bounds and initial-state contract of the paid coordinate frontend

The construction in `lem:generator`: the physical input determines a
polynomial register width. These lemmas discharge the parser's concrete clamps
and expose the polynomial base used by the actual `flWF` compiler budget.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicGates.Adapters.Joins
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Close.Cells (leadOnes)

theorem prepared_lead (w : List Bool) : leadOnes (preparedInput w) = Nat.size (frame w).length :=
  NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_rep _ _

theorem prepared_lead_pos (w : List Bool) : 1 ≤ leadOnes (preparedInput w) := by
  rw [prepared_lead]
  exact Nat.size_pos.mpr (by simp [frame_length])

theorem prepared_lead_lt (w : List Bool) : leadOnes (preparedInput w) < (preparedInput w).length := by
  rw [prepared_lead]
  simp only [preparedInput, ShortPCP.Time.prefixWord, List.length_append, List.length_replicate,
    List.length_cons]
  omega

theorem prepared_tail (w : List Bool) :
    (globOf (preparedInput w)).inp.drop (s0 (preparedInput w)).ip = frame w := by
  change (preparedInput w).drop (leadOnes (preparedInput w) + 1) = frame w
  rw [prepared_lead]
  simp only [preparedInput, ShortPCP.Time.prefixWord]
  rw [List.drop_append, List.length_replicate, List.drop_eq_nil_of_le (by simp)]
  simp

theorem prepared_K_lower (w : List Bool) : 4 * w.length + 4 ≤ (globOf (preparedInput w)).K := by
  have hn := Nat.lt_size_self (frame w).length
  have hb : 2 ^ Nat.size (frame w).length ≤ 64 ^ Nat.size (frame w).length :=
    Nat.pow_le_pow_left (by norm_num) _
  have hlen := frame_length w
  simp only [globOf, kOf, prepared_lead]
  omega

theorem prepared_K_power_lower (w : List Bool) :
    2 * (2 * w.length + 2) ^ 6 ≤ (globOf (preparedInput w)).K := by
  have hn : 2 * w.length + 2 ≤ 2 ^ Nat.size (frame w).length := by
    have := Nat.lt_size_self (frame w).length
    have hlen := frame_length w
    omega
  have hp := Nat.pow_le_pow_left hn 6
  have he : (2 ^ Nat.size (frame w).length) ^ 6 = 64 ^ Nat.size (frame w).length := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [he] at hp
  simpa only [globOf, kOf, prepared_lead] using Nat.mul_le_mul_left 2 hp

theorem prepared_BdOk (w : List Bool) : BdOk (globOf (preparedInput w)) w.length := by
  let G := globOf (preparedInput w)
  change BdOk G w.length
  have hk : w.length + 2 ≤ G.K := by have := prepared_K_lower w; dsimp [G]; omega
  have he : w.length + 2 * 2 ^ w.length < 2 ^ (w.length + 2) := by
    rw [pow_add]
    norm_num
    have := Nat.lt_two_pow_self (n := w.length)
    omega
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  have hc := cap_add G
  refine ⟨by omega, ?_⟩
  change w.length + 1 ≤ G.K
  omega

theorem coordInput_field_le (p : CoordReq) (h : CoordOk p) : p.f ≤ (coordInput p).length := by
  have hlo := (coordOk_mask_bounds p h).1
  have hhi := NearCubicGates.Close.Cells.lt_natBitLength p.irr
  have hf : p.f < natBitLength p.irr := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : natBitLength p.irr ≤ p.f)
    omega
  simp only [coordInput, List.length_append, natWord_len]
  omega

theorem prepared_coordParse (p : CoordReq) (h : CoordOk p) :
    let inp := preparedInput (coordInput p)
    let t := evalS (globOf inp) coordParse (s0 inp)
    t.env 20 = p.f ∧ t.env 21 = p.irr ∧ t.env 22 = p.m ∧ t.fl = p.f ∧ t.fp = p.irr ∧
      t.out = [] ∧ t.bad = false ∧ ∀ j : Var, 23 ≤ j.val → t.env j = 0 := by
  obtain ⟨h20, h21, h22, hfl, hfp, hout, hbad, _, henv⟩ :=
    coordParse_spec (globOf (preparedInput (coordInput p))) (s0 (preparedInput (coordInput p))) p h []
      (by simpa using prepared_tail (coordInput p)) (prepared_BdOk (coordInput p))
      (by have := coordInput_field_le p h; have := prepared_K_lower (coordInput p); omega)
  exact ⟨h20, h21, h22, hfl, hfp, hout, hbad, henv⟩

theorem prepared_length_le (w : List Bool) : (preparedInput w).length ≤ 4 * (w.length + 1) := by
  have hs : Nat.size (frame w).length ≤ (frame w).length := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [preparedInput, ShortPCP.Time.prefixWord, List.length_append, List.length_replicate,
    List.length_cons, frame_length] at *
  omega

theorem prepared_runtime_base (w : List Bool) :
    64 ^ leadOnes (preparedInput w) + (preparedInput w).length + 1 ≤ 5000 * (w.length + 1) ^ 6 := by
  have hs : 2 ^ Nat.size (frame w).length ≤ 4 * (w.length + 1) := by
    have := Code.Parsing.two_pow_bits_length_le (frame w).length
    rw [Nat.size_eq_bits_len] at this
    have hlen := frame_length w
    omega
  have hp := Nat.pow_le_pow_left hs 6
  have he : (2 ^ Nat.size (frame w).length) ^ 6 = 64 ^ leadOnes (preparedInput w) := by
    rw [prepared_lead, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [he, mul_pow] at hp
  have hlen := prepared_length_le w
  have hn : w.length + 1 ≤ (w.length + 1) ^ 6 := by
    have := Nat.pow_le_pow_right (by omega : 0 < w.length + 1) (by norm_num : 1 ≤ 6)
    simpa using this
  norm_num at hp
  omega

theorem preparedBudget_le (w : List Bool) : preparedBudget w ≤ 2400 * (w.length + 1) ^ 2 := by
  simp only [preparedBudget, framePrepBudget, framePrepCost,
    ShortPCP.Machines.WidthPrefix.prefixBudget, frame_length]
  nlinarith

end NearCubicGates.Adapters.Routing.CoordinateMachine
