import Proof.Wire_3_5.ListMachineRowFactor

/-! # C2 rows, part 3: the single-factor row (FILTER rows)

A FILTER row is ONE term with ONE factor (`m = 1`, no padding): its output is
`exprWord [(1, [P])]`, where `P` is the interpolation print of the row's Boolean function over GLOBAL pool atoms
(`factorPoly`). The row machine `filterRowM F` is ONE machine per evaluator family:

1. the row record `frame (factorBlock …)` at the input cursor is copied to a work tape (masked, so its head returns);
2. the term's opening `true :: coefWord 1 ++ [true]` is written;
3. the factor stage prints `polyWord P` (`factor_step`);
4. the closing `[false, false]` is written.

**`filterRow_step`** is the per-row stage in the loop-body shape of base's `Cells.ofScrub`: every work
tape enters EMPTY (the log any blank), the input and output are kept ports (input cursor past the record, output
extended by the row's `exprWord`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun atomCode)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5

/-! ## Constant words -/

def putS : List Bool → ℕ
  | [] => 1
  | _ :: w => 2 + putS w

/-- Write a constant word at the output cursor. -/
noncomputable def putW : (w : List Bool) → Machine 1 (putS w)
  | [] => Block.idle 1
  | b :: w => Composition.machine (Put.machine b) (putW w)

def putCost : List Bool → ℕ
  | [] => 0
  | _ :: w => 1 + 1 + putCost w

theorem putW_run (w : List Bool) : ∀ (o B : List Bool),
    Step (putW w) (putCost w) ![o.length] ![overlay o B] ![(o ++ w).length] ![overlay (o ++ w) B] := by
  induction w with
  | nil => intro o B; rw [List.append_nil]; exact idle_step ![o.length] ![overlay o B]
  | cons b w ih =>
    intro o B
    have h := (Put.run b o B).seq (ih (o ++ [b]) B)
    rw [show o ++ [b] ++ w = o ++ b :: w by simp] at h
    exact h

/-! ## The row layout: the input, then the factor layout -/

/-- The input tape. -/
def inR (t : ℕ) : Fin (1 + (1 + (14 + t) + 1)) := Fin.castAdd (1 + (14 + t) + 1) (0 : Fin 1)
/-- The factor layout inside the row layout. -/
def flR (t : ℕ) (i : Fin (1 + (14 + t) + 1)) : Fin (1 + (1 + (14 + t) + 1)) := Fin.natAdd 1 i

theorem flR_inj (t : ℕ) : Function.Injective (flR t) := by
  intro a b h; have := congrArg Fin.val h; simp [flR] at this; exact Fin.ext this

theorem flR_ne_in (t : ℕ) (i : Fin (1 + (14 + t) + 1)) : flR t i ≠ inR t := by
  intro h; have := congrArg Fin.val h; simp [flR, inR] at this

theorem rcover (t : ℕ) (i : Fin (1 + (1 + (14 + t) + 1))) : i = inR t ∨ ∃ j, i = flR t j := by
  by_cases h : i.val = 0
  · exact Or.inl (Fin.ext (by simp [inR, h]))
  · exact Or.inr ⟨⟨i.val - 1, by omega⟩, Fin.ext (by simp [flR]; omega)⟩

/-- Row heads: the input cursor, then the factor layout's. -/
def rH (t p : ℕ) (H : Fin (1 + (14 + t) + 1) → ℕ) : Fin (1 + (1 + (14 + t) + 1)) → ℕ :=
  Fin.addCases (fun _ : Fin 1 => p) H
/-- Row tapes: the input, then the factor layout's. -/
def rA (t : ℕ) (inp : List Bool) (A : Fin (1 + (14 + t) + 1) → List Bool) : Fin (1 + (1 + (14 + t) + 1)) → List Bool :=
  Fin.addCases (fun _ : Fin 1 => inp) A

theorem rH_in (t p : ℕ) (H : Fin (1 + (14 + t) + 1) → ℕ) : rH t p H (inR t) = p := by simp [rH, inR]
theorem rH_fl (t p : ℕ) (H : Fin (1 + (14 + t) + 1) → ℕ) (j : Fin (1 + (14 + t) + 1)) : rH t p H (flR t j) = H j := by
  simp [rH, flR]
theorem rA_in (t : ℕ) (inp : List Bool) (A : Fin (1 + (14 + t) + 1) → List Bool) : rA t inp A (inR t) = inp := by
  simp [rA, inR]
theorem rA_fl (t : ℕ) (inp : List Bool) (A : Fin (1 + (14 + t) + 1) → List Bool) (j : Fin (1 + (14 + t) + 1)) :
    rA t inp A (flR t j) = A j := by simp [rA, flR]

/-! ## The stages -/

/-- The record read: input → record tape, the record tape rewound. -/
def s1 (t : ℕ) : Fin (2 + 1) → Fin (1 + (1 + (14 + t) + 1)) := ![inR t, flR t (srcO t), flR t (logI t)]

theorem srcO_ne_logI (t : ℕ) : srcO t ≠ logI t := by
  intro h; have := congrArg Fin.val h; simp [srcO, srcI, logI] at this; omega

theorem srcO_ne_outI (t : ℕ) : srcO t ≠ outI t := by
  intro h; have := congrArg Fin.val h; simp [srcO, srcI, outI, bankI] at this

theorem logI_ne_outI (t : ℕ) : logI t ≠ outI t := by
  intro h; have := congrArg Fin.val h; simp [logI, outI, bankI] at this; omega

theorem s1_inj (t : ℕ) : Function.Injective (s1 t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [s1, (flR_inj t).eq_iff, srcO_ne_logI, (srcO_ne_logI t).symm,
    flR_ne_in, (flR_ne_in t _).symm]

noncomputable def readM (t : ℕ) := RecoveryFocus.machine (s1 t) (MaskedReset.machine Unframe.machine ![false, true])

/-- The output slot. -/
def sO (t : ℕ) : Fin 1 → Fin (1 + (1 + (14 + t) + 1)) := ![flR t (outI t)]

theorem sO_inj (t : ℕ) : Function.Injective (sO t) := by
  intro a b _; exact Subsingleton.elim a b

/-- The opening of the one term with coefficient `1`: its marker, `coefWord 1`, the factor's marker. -/
def filterPre : List Bool := true :: Rec.coefWord 1 ++ [true]
/-- The closing: the term's end, the expression's end. -/
def filterSuf : List Bool := [false, false]

/-- **The FILTER row machine**: ONE machine per evaluator family. -/
noncomputable def filterRowM (F : EvalFam) :=
  Composition.machine (Composition.machine (Composition.machine (readM F.t)
    (RecoveryFocus.machine (sO F.t) (putW filterPre))) (RecoveryFocus.machine (flR F.t) (factorM F)))
    (RecoveryFocus.machine (sO F.t) (putW filterSuf))

/-- The reference: one term, one factor. -/
def filterRef (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) : List (ℤ × List (List (List ℕ))) :=
  [(1, [factorPoly f L d labs])]

theorem exprWord_filterRef (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) :
    Rec.exprWord (filterRef f L d labs) = filterPre ++ Rec.polyWord (factorPoly f L d labs) ++ filterSuf := by
  simp [Rec.exprWord, Rec.termWord, filterRef, filterPre, filterSuf]

/-- The row record of a FILTER row: the factor block. -/
def filterRecord {t : ℕ} (L d : ℕ) (labs : List ℕ) (cap1 cap2 : ℕ) (data : Fin t → List Bool) : List Bool :=
  factorBlock L d labs cap1 cap2 data

noncomputable def filterRowCost (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (d : ℕ)
    (labs : List ℕ) (cap1 cap2 : ℕ) : ℕ :=
  (2 * (2 * (filterRecord L d labs cap1 cap2 m.data).length + 1) + 2) + 1 + putCost filterPre + 1 +
    factorCost F m d labs cap1 cap2 + 1 + putCost filterSuf

/-! ## Docking by characterization -/

theorem dockH_eq_of {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (H : Fin u → ℕ)
    (v : Fin t → ℕ) (G : Fin u → ℕ) (h1 : ∀ j, G (slots j) = v j) (h2 : ∀ i, (∀ j, slots j ≠ i) → G i = H i) :
    dockH slots H v = G := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [dockH_slot _ hi, h1]
  · have hn : ∀ j, slots j ≠ i := fun j hj => h ⟨j, hj⟩
    rw [dockH_other _ _ _ _ hn, h2 i hn]

theorem install_eq_of {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (v : Fin t → List Bool) (G : Fin u → List Bool) (h1 : ∀ j, G (slots j) = v j)
    (h2 : ∀ i, (∀ j, slots j ≠ i) → G i = A i) : install slots A v = G := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [install_slot _ hi, h1]
  · have hn : ∀ j, slots j ≠ i := fun j hj => h ⟨j, hj⟩
    rw [install_other _ _ _ _ hn, h2 i hn]

/-! ## Stage 1: the record read -/

theorem read_step (t : ℕ) (pre w rest out B : List Bool) (k : ℕ) :
    ∃ m, Step (readM t) (2 * (2 * w.length + 1) + 2)
      (rH t pre.length (fH t 0 out.length)) (rA t (pre ++ frame w ++ rest) (fA [] (entryBank out B) (fun _ => [])
        (List.replicate k false)))
      (rH t (pre.length + (2 * w.length + 1)) (fH t 0 out.length))
      (rA t (pre ++ frame w ++ rest) (fA w (entryBank out B) (fun _ => []) (List.replicate m false))) := by
  have hu := Unframe.run pre w rest [] []
  obtain ⟨m, hm⟩ := maskBlank hu ![false, true] (by intro i hi; fin_cases i <;> simp_all) k
  have hd := dockRun hm (s1 t) (s1_inj t) (rH t pre.length (fH t 0 out.length))
    (rA t (pre ++ frame w ++ rest) (fA [] (entryBank out B) (fun _ => []) (List.replicate k false)))
    (by intro j; fin_cases j
        · simp [s1, rH_in]; rfl
        · simp [s1, rH_fl, fH_srcO]; rfl
        · simp [s1, rH_fl, fH_logI]; rfl)
    (by intro j; fin_cases j
        · simp [s1, rA_in]; rfl
        · simp [s1, rA_fl, fA_srcO, overlay_nil]; rfl
        · simp [s1, rA_fl]; simp [fA, logI]; rfl)
  refine ⟨m, hd.congr ?_ ?_⟩
  · apply dockH_eq_of _ (s1_inj t)
    · intro j; fin_cases j
      · simp [s1, rH_in]; rfl
      · simp [s1, rH_fl, fH_srcO]; rfl
      · simp [s1, rH_fl, fH_logI]; rfl
    · intro i hi
      rcases rcover t i with rfl | ⟨j, rfl⟩
      · exact absurd rfl (hi 0)
      · rw [rH_fl, rH_fl]
  · apply install_eq_of _ (s1_inj t)
    · intro j; fin_cases j
      · simp [s1, rA_in]; rfl
      · simp [s1, rA_fl, fA_srcO, overlay_nil]; rfl
      · simp [s1, rA_fl]; simp [fA, logI]; rfl
    · intro i hi
      rcases rcover t i with rfl | ⟨j, rfl⟩
      · exact absurd rfl (hi 0)
      · rw [rA_fl, rA_fl]
        rcases cover t j with rfl | ⟨c, rfl⟩ | ⟨j', rfl⟩ | rfl
        · exact absurd rfl (hi 1)
        · rw [fA_prSlot, fA_prSlot]
        · rw [fA_prSlot, fA_prSlot]
        · exact absurd rfl (hi 2)

/-! ## Writing at the output -/

theorem outI_eq (t : ℕ) : outI t = prSlot t (Fin.castAdd t 10) := rfl

theorem putO_step (t : ℕ) (w o B : List Bool) (H : Fin (1 + (1 + (14 + t) + 1)) → ℕ)
    (A : Fin (1 + (1 + (14 + t) + 1)) → List Bool) (hH : H (flR t (outI t)) = o.length)
    (hA : A (flR t (outI t)) = overlay o B) :
    Step (RecoveryFocus.machine (sO t) (putW w)) (putCost w) H A
      (Function.update H (flR t (outI t)) (o ++ w).length) (Function.update A (flR t (outI t)) (overlay (o ++ w) B)) := by
  have h := dockRun (putW_run w o B) (sO t) (sO_inj t) H A
    (by intro j; fin_cases j; simpa [sO] using hH) (by intro j; fin_cases j; simpa [sO] using hA)
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ (sO_inj t)
    · intro j; fin_cases j; simp [sO]
    · intro i hi; exact Function.update_of_ne (fun e => hi 0 (by simp [sO, e])) _ _
  · apply install_eq_of _ (sO_inj t)
    · intro j; fin_cases j; simp [sO]
    · intro i hi; exact Function.update_of_ne (fun e => hi 0 (by simp [sO, e])) _ _

theorem rH_update (t p : ℕ) (H : Fin (1 + (14 + t) + 1) → ℕ) (j : Fin (1 + (14 + t) + 1)) (x : ℕ) :
    Function.update (rH t p H) (flR t j) x = rH t p (Function.update H j x) := by
  funext i
  rcases rcover t i with rfl | ⟨j', rfl⟩
  · rw [Function.update_of_ne (flR_ne_in t j).symm, rH_in, rH_in]
  · rw [rH_fl]
    by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h ((flR_inj t) e)), Function.update_of_ne h, rH_fl]

theorem rA_update (t : ℕ) (inp : List Bool) (A : Fin (1 + (14 + t) + 1) → List Bool) (j : Fin (1 + (14 + t) + 1))
    (x : List Bool) : Function.update (rA t inp A) (flR t j) x = rA t inp (Function.update A j x) := by
  funext i
  rcases rcover t i with rfl | ⟨j', rfl⟩
  · rw [Function.update_of_ne (flR_ne_in t j).symm, rA_in, rA_in]
  · rw [rA_fl]
    by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h ((flR_inj t) e)), Function.update_of_ne h, rA_fl]

theorem fH_update (t p o o' : ℕ) : Function.update (fH t p o) (outI t) o' = fH t p o' := by
  funext i
  rcases cover t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (srcO_ne_outI t), fH_srcO, fH_srcO]
  · rw [outI_eq]
    by_cases hc : c = 10
    · subst hc; rw [Function.update_self, fH_prSlot]; simp [bh]
    · rw [Function.update_of_ne (fun e => hc (Fin.castAdd_inj.mp ((prSlot_inj t) e))), fH_prSlot, fH_prSlot]
      fin_cases c <;> simp_all [bh]
  · rw [outI_eq, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [prSlot] at this; omega),
      fH_prSlot, fH_prSlot]
    simp
  · rw [Function.update_of_ne (logI_ne_outI t), fH_logI, fH_logI]

theorem fA_update {t : ℕ} (src : List Bool) (o o' B : List Bool) (data : Fin t → List Bool) (log : List Bool) :
    Function.update (fA src (entryBank o B) data log) (outI t) (overlay o' B) = fA src (entryBank o' B) data log := by
  funext i
  rcases cover t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (srcO_ne_outI t), fA_srcO, fA_srcO]
  · rw [outI_eq]
    by_cases hc : c = 10
    · subst hc; rw [Function.update_self, fA_prSlot]; simp [Bank.tapes, entryBank]
    · rw [Function.update_of_ne (fun e => hc (Fin.castAdd_inj.mp ((prSlot_inj t) e))), fA_prSlot, fA_prSlot]
      fin_cases c <;> simp_all [Bank.tapes, entryBank]
  · rw [outI_eq, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp [prSlot] at this; omega),
      fA_prSlot, fA_prSlot]
    simp
  · rw [Function.update_of_ne (logI_ne_outI t)]; simp [fA, logI]

/-! ## The FILTER row -/

/-- **The FILTER row, as a loop body**: from the input cursor at `frame` of the row record, EMPTY work
tapes and a blank log of any length, the output receives the row's `exprWord` (one term, one factor: the
interpolation print over GLOBAL pool atoms); the input cursor passes the record. -/
theorem filterRow_step (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (labs : List ℕ) (d : ℕ)
    (hd : 1 ≤ d) (hlabs : L ≤ labs.length) (cap1 cap2 : ℕ) (hc1 : 2 * L + 1 ≤ cap1)
    (hc2 : ∀ xs : List Bool, xs.length = L → recInnerLCost xs labs ≤ cap1) (pre rest out B : List Bool) (k : ℕ) :
    ∃ A', Step (filterRowM F) (filterRowCost F m d labs cap1 cap2) (rH F.t pre.length (fH F.t 0 out.length))
      (rA F.t (pre ++ frame (filterRecord L d labs cap1 cap2 m.data) ++ rest)
        (fA [] (entryBank out B) (fun _ => []) (List.replicate k false)))
      (rH F.t (pre.length + (2 * (filterRecord L d labs cap1 cap2 m.data).length + 1))
        (fH F.t (filterRecord L d labs cap1 cap2 m.data).length (out ++ Rec.exprWord (filterRef f L d labs)).length))
      A' ∧ A' (inR F.t) = pre ++ frame (filterRecord L d labs cap1 cap2 m.data) ++ rest ∧
      A' (flR F.t (outI F.t)) = overlay (out ++ Rec.exprWord (filterRef f L d labs)) B := by
  obtain ⟨m1, h1⟩ := read_step F.t pre (factorBlock L d labs cap1 cap2 m.data) rest out B k
  have h2 := putO_step F.t filterPre out B
    (rH F.t (pre.length + (2 * (factorBlock L d labs cap1 cap2 m.data).length + 1)) (fH F.t 0 out.length))
    (rA F.t (pre ++ frame (factorBlock L d labs cap1 cap2 m.data) ++ rest)
      (fA (factorBlock L d labs cap1 cap2 m.data) (entryBank out B) (fun _ => []) (List.replicate m1 false)))
    (by rw [rH_fl, outI_eq, fH_prSlot]; simp [bh])
    (by rw [rA_fl, outI_eq, fA_prSlot]; simp [Bank.tapes, entryBank])
  rw [rH_update, fH_update, rA_update, fA_update] at h2
  obtain ⟨A3, h3, h3s, h3o⟩ := factor_step F m labs d hd hlabs [] [] (out ++ filterPre) B cap1 cap2 m1 hc1 hc2
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h3 h3s
  have h3d := dockRun h3 (flR F.t) (flR_inj F.t)
    (rH F.t (pre.length + (2 * (factorBlock L d labs cap1 cap2 m.data).length + 1)) (fH F.t 0 (out ++ filterPre).length))
    (rA F.t (pre ++ frame (factorBlock L d labs cap1 cap2 m.data) ++ rest)
      (fA (factorBlock L d labs cap1 cap2 m.data) (entryBank (out ++ filterPre) B) (fun _ => []) (List.replicate m1 false)))
    (fun j => rH_fl F.t _ _ j) (fun j => rA_fl F.t _ _ j)
  rw [dockH_eq_of (flR F.t) (flR_inj F.t) _ _
    (rH F.t (pre.length + (2 * (factorBlock L d labs cap1 cap2 m.data).length + 1))
      (fH F.t (factorBlock L d labs cap1 cap2 m.data).length
        (out ++ filterPre ++ Rec.polyWord (factorPoly f L d labs)).length))
    (fun j => rH_fl F.t _ _ j)
    (fun i hi => by
      rcases rcover F.t i with rfl | ⟨j, rfl⟩
      · rw [rH_in, rH_in]
      · exact absurd rfl (hi j))] at h3d
  have hA3in : install (flR F.t) (rA F.t (pre ++ frame (factorBlock L d labs cap1 cap2 m.data) ++ rest)
      (fA (factorBlock L d labs cap1 cap2 m.data) (entryBank (out ++ filterPre) B) (fun _ => [])
        (List.replicate m1 false))) A3 (inR F.t) = pre ++ frame (factorBlock L d labs cap1 cap2 m.data) ++ rest := by
    rw [install_other _ _ _ _ (fun j => flR_ne_in F.t j), rA_in]
  have hA3o : install (flR F.t) (rA F.t (pre ++ frame (factorBlock L d labs cap1 cap2 m.data) ++ rest)
      (fA (factorBlock L d labs cap1 cap2 m.data) (entryBank (out ++ filterPre) B) (fun _ => [])
        (List.replicate m1 false))) A3 (flR F.t (outI F.t)) =
      overlay (out ++ filterPre ++ Rec.polyWord (factorPoly f L d labs)) B := by
    rw [install_slot _ (flR_inj F.t), h3o]
  have h4 := putO_step F.t filterSuf (out ++ filterPre ++ Rec.polyWord (factorPoly f L d labs)) B
    (rH F.t (pre.length + (2 * (factorBlock L d labs cap1 cap2 m.data).length + 1))
      (fH F.t (factorBlock L d labs cap1 cap2 m.data).length
        (out ++ filterPre ++ Rec.polyWord (factorPoly f L d labs)).length))
    (install (flR F.t) (rA F.t (pre ++ frame (factorBlock L d labs cap1 cap2 m.data) ++ rest)
      (fA (factorBlock L d labs cap1 cap2 m.data) (entryBank (out ++ filterPre) B) (fun _ => [])
        (List.replicate m1 false))) A3)
    (by rw [rH_fl, outI_eq, fH_prSlot]; simp [bh]) hA3o
  rw [rH_update, fH_update] at h4
  have ew : out ++ filterPre ++ Rec.polyWord (factorPoly f L d labs) ++ filterSuf =
      out ++ Rec.exprWord (filterRef f L d labs) := by
    rw [exprWord_filterRef]; simp [List.append_assoc]
  rw [ew] at h4
  refine ⟨_, ((h1.seq h2).seq h3d).seq h4, ?_, ?_⟩
  · rw [Function.update_of_ne (flR_ne_in F.t _).symm, hA3in]; rfl
  · rw [Function.update_self]

end NearCubicWires.WireExponent3_5.ListMachine.Row
