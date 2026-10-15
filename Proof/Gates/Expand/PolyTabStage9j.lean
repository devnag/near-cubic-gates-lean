import Proof.Gates.Expand.PolyTabStage9i

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.RepairRepresentation (natWord)

variable (E : ExpandMachine) (r : TabReq)

def tri {V : ℕ} (t : Finset (Fin V) × ℤ) : List ℕ × ℕ × ℕ := ((mvars t).map Fin.val, wSign t.2, t.2.natAbs)

def ts9 : List (List ℕ × ℕ × ℕ) := (E.expand ⟨r.V, r.F⟩).map tri

theorem monoN_tri {V : ℕ} (t : Finset (Fin V) × ℤ) : monoN t = fl (tri t) := by
  simp [monoN, fl, tri, mvars, intN, wSign]

theorem termsN_ts9 : termsN (E.expand ⟨r.V, r.F⟩) = (ts9 E r).length :: (ts9 E r).flatMap fl := by
  simp only [termsN, ts9, List.length_map, List.flatMap_map]
  rw [show (monoN : Finset (Fin r.V) × ℤ → List ℕ) = fun a => fl (tri a) from funext monoN_tri]

theorem frame_terms : frame (termsWord (E.expand ⟨r.V, r.F⟩)) =
    encN ((ts9 E r).length :: (ts9 E r).flatMap fl) ++ [false] := by
  rw [Codec.frame_eq_marks, termsWord_eq, encN_eq_marks, termsN_ts9]

theorem blk46_tri (t : Finset (Fin r.V) × ℤ) :
    blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r) (tri t) =
      ((blkRecs (((mvars t).map (occ (tabT E r))).reverse, t.2)).map (binary (Wk E r + 1))).flatMap frame := by
  rw [blkRecs_term]
  simp only [blk46, tri, revOut, List.length_map, List.take_length, List.map_cons, List.flatMap_cons,
    List.length_reverse]
  rw [List.take_of_length_le (by simp)]
  congr 1
  rw [← List.map_reverse, List.flatMap_map, List.map_flatMap, List.flatMap_assoc]
  congr 1; funext v
  rw [vt_seg]; simp [List.flatMap_map]

theorem blk46_eq : (ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r)) =
    ((codeRecs (tsK E r)).map (binary (Wk E r + 1))).flatMap frame := by
  rw [ts9, codeRecs, tsK_eq]
  simp only [List.flatMap_map, List.map_flatMap, List.flatMap_assoc]
  congr 1; funext t; exact (blk46_tri E r t).trans (by simp [List.flatMap_map])

theorem blk56_eq : (ts9 E r).flatMap (blk56 (Wdk E r + 1)) = (coefRecs r.s (Wk E r) (tsK E r)).flatMap frame := by
  rw [ts9, List.flatMap_map, coefRecs, tsK_eq, List.map_map, List.flatMap_map]
  refine congrArg (fun g => List.flatMap g (E.expand ⟨r.V, r.F⟩)) (funext fun t => ?_)
  simp only [blk56, tri, Function.comp, Wdk_succ, encS_eq]

theorem rec46 : (ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r)) ++ [false] =
    recStream ((codeRecs (tsK E r)).map (binary (Wk E r + 1))) := by
  rw [blk46_eq]; unfold recStream; simp [List.flatMap_map]

theorem rec56 : (ts9 E r).flatMap (blk56 (Wdk E r + 1)) ++ [false] = recStream (coefRecs r.s (Wk E r) (tsK E r)) := by
  rw [blk56_eq]; rfl

theorem ts9_length : (ts9 E r).length ≤ 2 ^ r.V := by
  rw [ts9, List.length_map]; exact Q_length E r

theorem mvars_lt {V : ℕ} (t : Finset (Fin V) × ℤ) : ∀ x ∈ (mvars t).map Fin.val, x < V := by
  intro x hx; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx; exact v.isLt

theorem mvars_len {V : ℕ} (t : Finset (Fin V) × ℤ) : ((mvars t).map Fin.val).length ≤ V := by
  simp only [List.length_map, mvars, Finset.length_sort]
  exact (Finset.card_le_univ _).trans (by simp)

theorem V_lt_Wk : r.V < 2 ^ (Wk E r + 1) := by
  have h1 : r.V ≤ Wk E r := by
    have := Wk_ge0 E r
    have : r.V ≤ r.V * (r.s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold Dm at *; omega
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem monoOKs_all (ℓ : ℕ) (hℓ : ∀ x ∈ termsN (E.expand ⟨r.V, r.F⟩), natBitLength x ≤ ℓ) :
    ∀ t ∈ ts9 E r, MonoOKs (Wk E r + 1) (Wdk E r + 1) ℓ r.V r.V (r.k + r.s + 2) (VTn E r) t := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hVW := V_lt_Wk E r
  have hmono : ∀ x ∈ monoN u, natBitLength x ≤ ℓ := fun x hx => hℓ x (by
    simp only [termsN, List.mem_cons, List.mem_flatMap]; right; exact ⟨u, hu, hx⟩)
  rw [monoN_tri] at hmono
  have hc : u.2.natAbs < 2 ^ Cm E r := coef_lt_Cm E r u hu
  have hCm : Cm E r ≤ Wdk E r := by
    have := Wk_le_Wdk E r
    have : Cm E r ≤ Wk E r := by unfold Wk; omega
    omega
  have hc2 : 2 * u.2.natAbs + 1 < 2 ^ (Wdk E r + 1) := by
    have : 2 ^ (Cm E r + 1) ≤ 2 ^ (Wdk E r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  refine ⟨mvars_len u, lt_of_le_of_lt (mvars_len u) hVW, fun x hx => lt_trans (mvars_lt u x hx) hVW,
    fun x hx => (mvars_lt u x hx).le, fun x hx => ?_, by simp [tri, wSign]; split_ifs <;> omega, hc2,
    hmono _ (by simp [fl]), fun x hx => hmono x (by simp [fl, hx]), hmono _ (by simp [fl]), hmono _ (by simp [fl])⟩
  rw [VTn_length]
  have := mvars_lt u x hx
  have : (x + 1) * (r.k + r.s + 2) ≤ r.V * (r.k + r.s + 2) := Nat.mul_le_mul_right _ this
  nlinarith

end NearCubicGates.Close.Expand.PolyTab
