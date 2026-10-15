import Proof.Wire_3_5.PrimTCarRound
import Proof.Wire_3_5.FoldBody
import Proof.Wire_3_5.CertSched

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.CarFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.WireExponent3_5.PrimT.CarRound NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- A machine that halts at once. -/
def idle (t : ℕ) : Machine t 1 := ⟨0, 0, fun _ => true, fun _ _ => none⟩

theorem idle_ready (t : ℕ) (X : Fin t → List Bool) : ClockJoin.ReadyRun (idle t) 0 X X :=
  ⟨_, runFrom_zero_of_halted (idle t) _ rfl, rfl, fun _ => rfl, le_refl _⟩

/-- The round's scratch: every tape but the atom stream, the counter and the accumulator. -/
def scr (j : Fin 1038) : Fin 1041 := ⟨j.val + 3, by omega⟩

theorem scr_inj : Function.Injective scr := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [scr] at this; omega)

theorem scr_iff (t : Fin 1041) : (∃ j, scr j = t) ↔ 3 ≤ t.val := by
  constructor
  · rintro ⟨j, rfl⟩; simp [scr]
  · intro h; exact ⟨⟨t.val - 3, by omega⟩, Fin.ext (by simp [scr]; omega)⟩

/-- **The atom loop.** -/
noncomputable def foldM := foldLoop (foldBody worker scr (idle (1041 + 2)))

/-- The round's entry at atom `i`. -/
def Qc {n : ℕ} (W total : ℕ) (X : List (NormalizedThresholdGate n)) (i : ℕ) : Fin 1041 → List Bool :=
  roundIn ((rawAtoms W X).flatMap frame) (ZeroPadding.pad total (List.replicate i true)) (accHdr ++ tabSeg (X.take i))

theorem pad_split (total i : ℕ) (hi : i < total) :
    ZeroPadding.pad total (List.replicate i true) =
      List.replicate i true ++ (false :: List.replicate (total - i - 1) false) := by
  unfold ZeroPadding.pad
  rw [List.length_replicate]
  congr 1
  rw [← List.replicate_succ]
  congr 1
  omega

theorem pad_succ (total i : ℕ) :
    List.replicate (i + 1) true ++ List.replicate (total - i - 1) false =
      ZeroPadding.pad total (List.replicate (i + 1) true) := by
  unfold ZeroPadding.pad; rw [List.length_replicate]; congr 2

/-- One round's uniform fuel: `c` atoms of width `W`, native region of length `T`. -/
def foldCw (W c T : ℕ) : ℕ :=
  1 + 1 + ((2 * (c * (5 * W + 8) + 14 * W + 10) + 2) + 1 + (4000000000000000000001002 * (W + 2) ^ 26 + 1 +
    (2 * (18 * T + 20) + 2)))

theorem tabSeg_take_le {n : ℕ} (X : List (NormalizedThresholdGate n)) (i : ℕ) :
    (tabSeg (X.take i)).length ≤ (tabSeg X).length := by
  conv_rhs => rw [← List.take_append_drop i X]
  rw [tabSeg_append, List.length_append]; omega

theorem roundCost_le {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n)) (i : ℕ) (hi : i < X.length) :
    CarRound.roundCost W X i X[i] ≤ foldCw W X.length (tabSeg X).length := by
  have hb := CarGate.budget_bound (binary W (CarrierFormat.gateCode X[i]))
  rw [binary_length] at hb
  have ht := tabSeg_take_le X i
  have hg := tabGW_le_tabH X X[i] (List.getElem_mem hi)
  have hc : i * (5 * W + 8) ≤ X.length * (5 * W + 8) := Nat.mul_le_mul_right _ hi.le
  unfold CarRound.roundCost foldCw cropCost appendCost
  unfold tabH at hg
  omega

/-- **The atom loop is ready**: from the padded round tapes at atom `0` and the unary count `|X|`, the loop ends at the
padded round tapes at atom `|X|`; its accumulator is `accHdr ++ tabSeg X`. -/
theorem fold_run {n : ℕ} (W : ℕ) (X : List (NormalizedThresholdGate n))
    (hW : ∀ g ∈ X, CarrierFormat.gateCode g < 2 ^ W) (total capT : ℕ) (hcap : total + 1 ≤ capT)
    (hc : X.length ≤ total) (hS : ((rawAtoms W X).flatMap frame).length ≤ total)
    (hT : accHdr.length + (tabSeg X).length ≤ total) (hcw : foldCw W X.length (tabSeg X).length + 1 ≤ total) :
    ClockJoin.ReadyRun foldM
      (1 + 1 + (X.length * (foldCw W X.length (tabSeg X).length + 1 + (2 * total + 4 + 1 + 0) + 2) + X.length + 3 +
        1 + 1))
      (Fin.addCases (roundTapes (padScratch scr total (Qc W total X 0)) total capT)
        (fun _ => CompareMachine.word X.length))
      (Fin.addCases (roundTapes (padScratch scr total (Qc W total X X.length)) total capT)
        (fun _ => CompareMachine.word X.length)) := by
  set c := X.length with hcX
  set cw := foldCw W c (tabSeg X).length with hcw'
  have hround : ∀ i, ∃ out : Fin 1041 → List Bool, i < c →
      ClockJoin.ReadyRun worker cw (Qc W total X i) out ∧
      out 0 = (rawAtoms W X).flatMap frame ∧ out 1 = ZeroPadding.pad total (List.replicate (i + 1) true) ∧
      out 2 = accHdr ++ tabSeg (X.take (i + 1)) := by
    intro i
    by_cases hi : i < c
    · obtain ⟨out, h1, h2, h3, h4⟩ := round_run W X hW i hi (List.replicate (total - i - 1) false)
      refine ⟨out, fun _ => ⟨?_, h2, by rw [h3, pad_succ total i], h4⟩⟩
      unfold Qc; rw [pad_split total i (by omega)]
      exact ClockJoin.enlarge _ _ _ _ _ h1 (roundCost_le W X i hi)
    · exact ⟨fun _ => [], fun h => absurd h hi⟩
  choose Q' hQ' using hround
  have hlenQ : ∀ i, i ≤ c → ∀ t, (Qc W total X i t).length ≤ total := by
    intro i hi t
    unfold Qc roundIn
    split_ifs
    · exact hS
    · simp [ZeroPadding.pad]; omega
    · have := tabSeg_take_le X i; simp; omega
    · simp
  have hwork : ∀ i, i < c → ClockJoin.ReadyRun worker cw (Qc W total X i) (Q' i) := fun i hi => (hQ' i hi).1
  have hmain := uniformFold_ready worker scr scr_inj (idle (1041 + 2)) total capT cw 0 c hcap (Qc W total X) Q'
    hwork
    (fun i hi j => by
      have hl := ready_lengths (hwork i hi) total (hlenQ i hi.le) (scr j)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun i hi => by
      have e : blankScratch scr (Q' i) = Qc W total X (i + 1) := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ j, scr j = t
        · rw [if_pos ht]
          have h3 := (scr_iff t).mp ht
          unfold Qc roundIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg ht]
          have h3 : t.val < 3 := by by_contra hc'; exact ht ((scr_iff t).mpr (by omega))
          obtain ⟨-, o0, o1, o2⟩ := hQ' i hi
          unfold Qc roundIn
          by_cases h0 : t.val = 0
          · rw [if_pos h0, show t = 0 from Fin.ext h0, o0]
          · by_cases h1 : t.val = 1
            · rw [if_neg h0, if_pos h1, show t = 1 from Fin.ext h1, o1]
            · rw [if_neg h0, if_neg h1, if_pos (by omega), show t = 2 from Fin.ext (by omega), o2]
      rw [e]; exact idle_ready _ _)
  exact hmain

end NearCubicWires.WireExponent3_5.PrimT.CarFold
