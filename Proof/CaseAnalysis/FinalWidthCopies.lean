import Proof.CaseAnalysis.FinalBodyWidths
import Proof.CaseAnalysis.FinalWordEngines

/-! Paper C.10's fixed decision tail reads the three records at their own widths.
The six unary widths retained at block tapes 274/275 are copied into tail tapes
2..7. Tape 8 is the restored blank second input; tapes 9..14 are six fresh logs.
Each copy uses the named `copy_dock` budget 2*r+6; all five joins are paid. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10WidthCopies

open LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10WordEngines
open C10TailCompose C10BodyWidths C10TailSlotsUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (e : ℕ) (he : 58 ≤ e)

def phaseOf (k : Fin 6) : Phase :=
  if k.val < 2 then .penalty else if k.val < 4 then .moment else .clause

def partOf (k : Fin 6) : Fin 2 := ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩

def source (k : Fin 6) : Fin (bigOf e) := bslot e (phaseOf k) (retained e he (partOf k))
def dest (k : Fin 6) : Fin (bigOf e) := ⟨2+k.val, by have := k.isLt; clear he; unfold bigOf; omega⟩
def logSlot (k : Fin 6) : Fin (bigOf e) := ⟨9+k.val, by have := k.isLt; clear he; unfold bigOf; omega⟩
def blank : Fin (bigOf e) := ⟨8, by clear he; unfold bigOf; omega⟩

theorem source_ge (k : Fin 6) : 475 ≤ (source e he k).val := by
  rw [source, bslot_val, retained_val]
  have := (partOf k).isLt
  cases phaseOf k <;> simp only [baseOf, scrVal] <;> split_ifs <;> omega

def slots (k : Fin 6) : Fin 4 → Fin (bigOf e) :=
  ![source e he k, blank e, dest e k, logSlot e k]

theorem slots_inj (k : Fin 6) : Function.Injective (slots e he k) := by
  have hs := source_ge e he k
  have hk := k.isLt
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> dsimp [slots, dest, logSlot, blank] at hv ⊢ <;> first | rfl | omega

def program (k : Fin 6) := RecoveryFocus.machine (slots e he k) ClockUnarySum.machine

def charge (r : ℕ) : ℕ := 2*(r+0)+6

/-- The copier restores its two inputs. Only its destination and fresh log can change. -/
theorem copy_step (k : Fin 6) (r : ℕ) (A : Fin (bigOf e) → List Bool)
    (hsource : A (source e he k) = List.replicate r true)
    (hblank : A (blank e) = []) (hdest : A (dest e k) = []) (hlog : A (logSlot e k) = []) :
    ∃ A', Step (program e he k) (charge r) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (dest e k) = List.replicate r true ∧
      (∀ i, i ≠ dest e k → i ≠ logSlot e k → A' i = A i) := by
  obtain ⟨H', A', hs, hH, h0, h1, h2, hf⟩ :=
    copy_dock r (slots e he k) (slots_inj e he k) (fun _ => 0) A (fun _ => rfl)
      hsource hblank hdest hlog
  have hHz : H' = (fun _ => 0) := funext hH
  rw [hHz] at hs
  refine ⟨A', hs, h2, ?_⟩
  intro i hd hl
  by_cases hsi : i = source e he k
  · subst i; exact h0.trans hsource.symm
  by_cases hbi : i = blank e
  · subst i; exact h1.trans hblank.symm
  apply hf
  intro j h
  fin_cases j
  · exact hsi h.symm
  · exact hbi h.symm
  · exact hd h.symm
  · exact hl h.symm

structure Ready (W : Fin 6 → ℕ) (r : ℕ) (A : Fin (bigOf e) → List Bool) : Prop where
  sources : ∀ k, A (source e he k) = List.replicate (W k) true
  dests : ∀ k, A (dest e k) = if k.val < r then List.replicate (W k) true else []
  blank : A (blank e) = []
  logs : ∀ k, r ≤ k.val → A (logSlot e k) = []

theorem advance (W : Fin 6 → ℕ) (k : Fin 6) (A : Fin (bigOf e) → List Bool)
    (h : Ready e he W k.val A) :
    ∃ A', Step (program e he k) (charge (W k)) (fun _ => 0) A (fun _ => 0) A' ∧
      Ready e he W (k.val+1) A' ∧
      (∀ i, 15 ≤ i.val → A' i = A i) := by
  obtain ⟨A', hs, hd, hf⟩ := copy_step e he k (W k) A (h.sources k) h.blank
    (by simpa using h.dests k) (h.logs k (by omega))
  have hk := k.isLt
  have hdv : (dest e k).val = 2+k.val := rfl
  have hlv : (logSlot e k).val = 9+k.val := rfl
  have frame (i : Fin (bigOf e)) (hdi : i.val ≠ 2+k.val) (hli : i.val ≠ 9+k.val) :
      A' i = A i := hf i (Fin.ne_of_val_ne hdi) (Fin.ne_of_val_ne hli)
  refine ⟨A', hs, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    rw [frame _ (by have := source_ge e he j; omega) (by have := source_ge e he j; omega)]
    exact h.sources j
  · intro j
    have hj := j.isLt
    by_cases hjk : j = k
    · subst j; simpa using hd
    · have hv : j.val ≠ k.val := fun hv => hjk (Fin.ext hv)
      rw [frame _ (by show 2+j.val ≠ 2+k.val; omega) (by show 2+j.val ≠ 9+k.val; omega), h.dests]
      by_cases hjr : j.val < k.val
      · rw [if_pos hjr, if_pos (by omega)]
      · rw [if_neg hjr, if_neg (by omega)]
  · rw [frame _ (by show (8:ℕ) ≠ 2+k.val; omega) (by show (8:ℕ) ≠ 9+k.val; omega)]
    exact h.blank
  · intro j hj
    rw [frame _ (by show 9+j.val ≠ 2+k.val; omega) (by show 9+j.val ≠ 9+k.val; omega)]
    exact h.logs j (by omega)
  · intro i hi
    exact frame i (by omega) (by omega)

def copies := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (program e he 0) (program e he 1)) (program e he 2))
      (program e he 3)) (program e he 4)) (program e he 5)

def budget (W : Fin 6 → ℕ) : ℕ :=
  ((((charge (W 0)+1+charge (W 1))+1+charge (W 2))+1+charge (W 3))+1+charge (W 4))+1+charge (W 5)

theorem copies_step (W : Fin 6 → ℕ) (A : Fin (bigOf e) → List Bool)
    (h : Ready e he W 0 A) :
    ∃ A', Step (copies e he) (budget W) (fun _ => 0) A (fun _ => 0) A' ∧
      (∀ k, A' (dest e k) = List.replicate (W k) true) ∧
      (∀ i, 15 ≤ i.val → A' i = A i) := by
  obtain ⟨A1, s1, r1, f1⟩ := advance e he W 0 A h
  obtain ⟨A2, s2, r2, f2⟩ := advance e he W 1 A1 r1
  obtain ⟨A3, s3, r3, f3⟩ := advance e he W 2 A2 r2
  obtain ⟨A4, s4, r4, f4⟩ := advance e he W 3 A3 r3
  obtain ⟨A5, s5, r5, f5⟩ := advance e he W 4 A4 r4
  obtain ⟨A6, s6, r6, f6⟩ := advance e he W 5 A5 r5
  refine ⟨A6, ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6, ?_, ?_⟩
  · intro k
    exact (r6.dests k).trans (if_pos k.isLt)
  · intro i hi
    exact (f6 i hi).trans ((f5 i hi).trans ((f4 i hi).trans ((f3 i hi).trans ((f2 i hi).trans (f1 i hi)))))

end
end NearCubicWires.RepairSource.CloseoutFinal.C10WidthCopies
