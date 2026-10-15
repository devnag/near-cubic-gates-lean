import Proof.Wire_3_5.ListMachineRowPop

/-! # C2 rows, part 8: the POP row, as a loop body

A POP row prints one population's amplified state (`pop_run`) from a self-contained row record, in the loop-body
shape of base's `Cells.ofScrub`: every work tape enters EMPTY, the input and the output are kept ports.

1. the record `frame rec` at the input cursor is copied to the record tape (masked, the record head returns);
2. the setup fields are loaded (the scrub's driver `1^R` and log `0^L`; the rows' counter, zero word, unary `θ`,
   cells, coefficient word and log), masked;
3. the factor layout's work tapes are blanked to the capacity `R` by base's scrub of the idle stage;
4. the population printer runs from the record's population part.

The layout: the input, the population layout (`PL`), a setup log. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun atomCode monoBits recW polyWord coefWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5
open NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- The input and the population layout. -/
abbrev IPL (u : ℕ) : ℕ := 1 + (SL u + 8)

def inQ (u : ℕ) : Fin (IPL u) := Fin.castAdd (SL u + 8) (0 : Fin 1)
def pQ (u : ℕ) (i : Fin (SL u + 8)) : Fin (IPL u) := Fin.natAdd 1 i

@[simp] theorem inQ_val (u : ℕ) : (inQ u).val = 0 := rfl
@[simp] theorem pQ_val (u : ℕ) (i : Fin (SL u + 8)) : (pQ u i).val = 1 + i.val := rfl

theorem pQ_inj (u : ℕ) : Function.Injective (pQ u) := fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
theorem pQ_ne_in (u : ℕ) (i : Fin (SL u + 8)) : pQ u i ≠ inQ u := by
  intro h; have := congrArg Fin.val h; simp at this

/-- Heads and tapes of the input and population layout. -/
def qH (u p : ℕ) (H : Fin (SL u + 8) → ℕ) : Fin (IPL u) → ℕ := Fin.addCases (fun _ : Fin 1 => p) H
def qA (u : ℕ) (inp : List Bool) (A : Fin (SL u + 8) → List Bool) : Fin (IPL u) → List Bool :=
  Fin.addCases (fun _ : Fin 1 => inp) A

theorem qH_in (u p : ℕ) (H : Fin (SL u + 8) → ℕ) : qH u p H (inQ u) = p := by simp [qH, inQ]
theorem qH_p (u p : ℕ) (H : Fin (SL u + 8) → ℕ) (i : Fin (SL u + 8)) : qH u p H (pQ u i) = H i := by simp [qH, pQ]
theorem qA_in (u : ℕ) (inp : List Bool) (A : Fin (SL u + 8) → List Bool) : qA u inp A (inQ u) = inp := by
  simp [qA, inQ]
theorem qA_p (u : ℕ) (inp : List Bool) (A : Fin (SL u + 8) → List Bool) (i : Fin (SL u + 8)) :
    qA u inp A (pQ u i) = A i := by simp [qA, pQ]

theorem qcover (u : ℕ) (i : Fin (IPL u)) : i = inQ u ∨ ∃ j, i = pQ u j := by
  have hi := i.isLt
  simp only [IPL] at hi
  by_cases h : i.val = 0
  · exact Or.inl (Fin.ext (by simp [h]))
  · exact Or.inr ⟨⟨i.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩

theorem qH_update (u p : ℕ) (H : Fin (SL u + 8) → ℕ) (j : Fin (SL u + 8)) (x : ℕ) :
    Function.update (qH u p H) (pQ u j) x = qH u p (Function.update H j x) := by
  funext i
  rcases qcover u i with rfl | ⟨j', rfl⟩
  · rw [Function.update_of_ne (pQ_ne_in u j).symm, qH_in, qH_in]
  · rw [qH_p]
    by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h ((pQ_inj u) e)), Function.update_of_ne h, qH_p]

theorem qA_update (u : ℕ) (inp : List Bool) (A : Fin (SL u + 8) → List Bool) (j : Fin (SL u + 8)) (x : List Bool) :
    Function.update (qA u inp A) (pQ u j) x = qA u inp (Function.update A j x) := by
  funext i
  rcases qcover u i with rfl | ⟨j', rfl⟩
  · rw [Function.update_of_ne (pQ_ne_in u j).symm, qA_in, qA_in]
  · rw [qA_p]
    by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h ((pQ_inj u) e)), Function.update_of_ne h, qA_p]

/-! ## Stage 1: the record read -/

/-- The read's slots: the input, the record tape. -/
def sRd (u : ℕ) : Fin 2 → Fin (IPL u) := ![inQ u, pQ u (srcP u)]
theorem sRd_inj (u : ℕ) : Function.Injective (sRd u) := by
  intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [sRd] at this)

/-- Only the record tape's head is rewound. -/
def selRd (u : ℕ) (i : Fin (IPL u)) : Bool := decide (i = pQ u (srcP u))

noncomputable def readQM (u : ℕ) := MaskedReset.machine (RecoveryFocus.machine (sRd u) Unframe.machine) (selRd u)

theorem readQ_step (u : ℕ) (pre w rest : List Bool) (H : Fin (SL u + 8) → ℕ) (A : Fin (SL u + 8) → List Bool)
    (hH : H (srcP u) = 0) (hA : A (srcP u) = []) :
    ∃ m, Step (readQM u) (2 * (2 * w.length + 1) + 2)
      (Fin.addCases (qH u pre.length H) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA u (pre ++ frame w ++ rest) A) (fun _ : Fin 1 => []))
      (Fin.addCases (qH u (pre.length + (2 * w.length + 1)) H) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA u (pre ++ frame w ++ rest) (Function.update A (srcP u) w)) (fun _ : Fin 1 => List.replicate m false)) := by
  have hu := Unframe.run pre w rest [] []
  simp only [List.nil_append, List.length_nil, overlay_nil] at hu
  have hd := dockRun hu (sRd u) (sRd_inj u) (qH u pre.length H) (qA u (pre ++ frame w ++ rest) A)
    (by intro j; fin_cases j
        · simp [sRd, qH_in]
        · simp [sRd, qH_p, hH])
    (by intro j; fin_cases j
        · simp [sRd, qA_in]
        · simp [sRd, qA_p, hA])
  obtain ⟨m, hm⟩ := maskBlank hd (selRd u) (by
    intro i hi
    have e : i = pQ u (srcP u) := of_decide_eq_true hi
    subst e; simp [qH_p, hH]) 0
  have eH : (fun i => if selRd u i = true then 0 else dockH (sRd u) (qH u pre.length H)
      ![pre.length + (2 * w.length + 1), w.length] i) = qH u (pre.length + (2 * w.length + 1)) H := by
    funext i
    rcases qcover u i with rfl | ⟨j, rfl⟩
    · have hs : selRd u (inQ u) = false := by simp [selRd, (pQ_ne_in u _).symm]
      rw [if_neg (by simp [hs]), qH_in]
      have := dockH_slot (sRd u) (sRd_inj u) (qH u pre.length H) ![pre.length + (2 * w.length + 1), w.length] 0
      simpa [sRd] using this
    · by_cases hj : j = srcP u
      · subst hj
        rw [if_pos (by simp [selRd]), qH_p, hH]
      · rw [if_neg (by simp [selRd, (pQ_inj u).eq_iff, hj]), qH_p]
        rw [dockH_other _ _ _ _ (by
          intro k; fin_cases k
          · exact (pQ_ne_in u j).symm
          · simp [sRd]; exact fun e => hj ((pQ_inj u) e).symm), qH_p]
  have eA : install (sRd u) (qA u (pre ++ frame w ++ rest) A) ![pre ++ frame w ++ rest, w] =
      qA u (pre ++ frame w ++ rest) (Function.update A (srcP u) w) := by
    funext i
    rcases qcover u i with rfl | ⟨j, rfl⟩
    · show install (sRd u) _ _ (sRd u 0) = _
      rw [install_slot _ (sRd_inj u)]
      simp [qA_in]
    · by_cases hj : j = srcP u
      · subst hj
        show install (sRd u) _ _ (sRd u 1) = _
        rw [install_slot _ (sRd_inj u)]
        simp [qA_p]
      · rw [install_other _ _ _ _ (by
          intro k; fin_cases k
          · exact (pQ_ne_in u j).symm
          · simp [sRd]; exact fun e => hj ((pQ_inj u) e).symm), qA_p, qA_p, Function.update_of_ne hj]
  refine ⟨m, hm.congr ?_ ?_⟩
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => ℕ) g (fun _ : Fin 1 => 0)) eH
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => List Bool) g (fun _ : Fin 1 => List.replicate m false)) eA

/-! ## Stage 2: the setup fields -/

/-- The setup targets: the scrub's driver and log, the extras but the output. -/
def targetsQ (u : ℕ) : List (Fin (IPL u)) :=
  [pQ u (sI u Scrub.driverTape), pQ u (sI u Scrub.logTape), pQ u (eI u 0), pQ u (eI u 1), pQ u (eI u 2),
    pQ u (eI u 3), pQ u (eI u 4), pQ u (eI u 5), pQ u (eI u 7)]

theorem targetsQ_vals (u : ℕ) : (targetsQ u).map Fin.val =
    [1 + (1 + (14 + u) + 1 + 1), 1 + (1 + (14 + u) + 1), 1 + (SL u + 0), 1 + (SL u + 1), 1 + (SL u + 2),
      1 + (SL u + 3), 1 + (SL u + 4), 1 + (SL u + 5), 1 + (SL u + 7)] := rfl

theorem targetsQ_nodup (u : ℕ) : (targetsQ u).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [targetsQ_vals]
  simp only [SL, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
  repeat' constructor
  all_goals first | omega | exact not_false

theorem mem_targetsQ_val (u : ℕ) (i : Fin (IPL u)) (h : i ∈ targetsQ u) : 1 + (1 + (14 + u) + 1) ≤ i.val := by
  have := List.mem_map_of_mem (f := Fin.val) h
  rw [targetsQ_vals] at this
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

theorem rec_not_mem (u : ℕ) : pQ u (srcP u) ∉ targetsQ u := by
  intro h; have := mem_targetsQ_val u _ h; simp at this

/-- The setup fields' values at the targets. -/
def setupF (u n θ R L cap : ℕ) : Fin (IPL u) → List Bool := fun i =>
  if i = pQ u (sI u Scrub.driverTape) then List.replicate R true
  else if i = pQ u (sI u Scrub.logTape) then List.replicate L false
  else if i = pQ u (eI u 0) then frame (binary n 0)
  else if i = pQ u (eI u 1) then frame (List.replicate n false)
  else if i = pQ u (eI u 2) then List.replicate θ true ++ [false]
  else if i = pQ u (eI u 3) then [false]
  else if i = pQ u (eI u 4) then [false]
  else if i = pQ u (eI u 5) then []
  else List.replicate cap false

/-- The setup fields, in record order. -/
def setupFields (u n θ R L cap : ℕ) : List (List Bool) := (targetsQ u).map (setupF u n θ R L cap)

theorem inner_not_mem (u : ℕ) (k : Fin (1 + (14 + u) + 1)) : pQ u (sI u (Scrub.inner k)) ∉ targetsQ u := by
  intro h
  have := mem_targetsQ_val u _ h
  have hk := k.isLt
  simp [Scrub.inner] at this
  omega

theorem eI_mem (u : ℕ) (k : Fin 8) : pQ u (eI u k) ∈ targetsQ u ↔ k ≠ 6 := by
  constructor
  · intro h e
    subst e
    have := List.mem_map_of_mem (f := Fin.val) h
    rw [targetsQ_vals] at this
    simp only [SL, List.mem_cons, List.not_mem_nil, or_false, pQ_val, eI_val] at this
    omega
  · intro hk
    fin_cases k <;> simp_all [targetsQ]

/-- The population layout after the setup load. -/
def setupA (u n θ R L cap : ℕ) (rec out B : List Bool) : Fin (SL u + 8) → List Bool :=
  Fin.addCases (Scrub.bank (fun j => if j = srcO u then rec else []) R L)
    ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false], [false], [false], [],
      overlay out B, List.replicate cap false]

/-- The population layout's entry (the output kept). -/
def entryA (u : ℕ) (out B : List Bool) : Fin (SL u + 8) → List Bool := fun i => if i = eI u 6 then overlay out B else []

theorem sI_driver_ne_log (u : ℕ) : sI u (Scrub.driverTape (t := 1 + (14 + u) + 1)) ≠ sI u Scrub.logTape := by
  intro h; exact Scrub.driver_ne_log ((sI_inj u) h)

theorem setupF_driver (u n θ R L cap : ℕ) : setupF u n θ R L cap (pQ u (sI u Scrub.driverTape)) = List.replicate R true := by
  simp [setupF]
theorem setupF_log (u n θ R L cap : ℕ) : setupF u n θ R L cap (pQ u (sI u Scrub.logTape)) = List.replicate L false := by
  have h : pQ u (sI u Scrub.logTape) ≠ pQ u (sI u (Scrub.driverTape (t := 1 + (14 + u) + 1))) :=
    fun e => sI_driver_ne_log u ((pQ_inj u) e).symm
  simp [setupF, h]
theorem setupF_e (u n θ R L cap : ℕ) (k : Fin 8) :
    setupF u n θ R L cap (pQ u (eI u k)) = ![frame (binary n 0), frame (List.replicate n false),
      List.replicate θ true ++ [false], [false], [false], [], List.replicate cap false, List.replicate cap false] k := by
  have h1 : ∀ a, pQ u (eI u k) ≠ pQ u (sI u a) := fun a e => sI_ne_eI u a k ((pQ_inj u) e).symm
  unfold setupF
  rw [if_neg (h1 _), if_neg (h1 _)]
  fin_cases k <;> simp [(pQ_inj u).eq_iff, (eI_inj u).eq_iff]

theorem popH_zero_other (u : ℕ) (o : ℕ) (i : Fin (SL u + 8)) (hi : i ≠ eI u 6) :
    popH u 0 ![0, 0, 0, 0, 0, 0, o, 0] i = 0 := by
  rcases pcover u i with ⟨a, rfl⟩ | ⟨k, rfl⟩
  · rw [popH_sI]
    refine Scrub.cover (motive := fun a => Scrub.heads (fH u 0 0) a = 0) (fun k => ?_) (by simp) (by simp) a
    rw [Scrub.heads_inner]
    rcases cover u k with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [fH_srcO]
    · rw [fH_prSlot]; fin_cases c <;> rfl
    · rw [fH_prSlot]; simp
    · rw [fH_logI]
  · rw [popH_eI]
    have : k ≠ 6 := fun e => hi (by rw [e])
    fin_cases k <;> simp_all

theorem popH_q_zero (u q o : ℕ) (j : Fin (SL u + 8)) (hj : j ≠ srcP u) (h6 : j ≠ eI u 6) :
    popH u q ![0, 0, 0, 0, 0, 0, o, 0] j = 0 := by
  rw [popH_other u q 0 _ j hj]; exact popH_zero_other u o j h6

theorem loadQ_heads (u P o q : ℕ) (g : Fin (IPL u) → ℕ) :
    (fun i => if decide (i ∈ targetsQ u) = true then 0 else (if i = pQ u (srcP u) then ([] : List Bool).length + q
      else if i ∈ targetsQ u then g i else qH u P (popH u 0 ![0, 0, 0, 0, 0, 0, o, 0]) i)) =
      qH u P (popH u q ![0, 0, 0, 0, 0, 0, o, 0]) := by
  funext i
  rcases qcover u i with rfl | ⟨j, rfl⟩
  · have hn : inQ u ∉ targetsQ u := fun h => by have := mem_targetsQ_val u _ h; simp at this
    simp [hn, (pQ_ne_in u _).symm, qH_in]
  · simp only [qH_p]
    by_cases hj : j = srcP u
    · subst hj
      simp [rec_not_mem, popH_src]
    · by_cases hm : pQ u j ∈ targetsQ u
      · rw [if_pos (by simp [hm])]
        refine (popH_q_zero u q o j hj ?_).symm
        intro e; subst e; exact absurd hm (by rw [eI_mem]; simp)
      · rw [if_neg (by simp [hm]), if_neg (fun e => hj ((pQ_inj u) e)), if_neg hm]
        exact popH_other u 0 q _ j hj

theorem loadQ_tapes (u n θ R L cap : ℕ) (inp rec out B : List Bool) :
    (fun i => if i ∈ targetsQ u then setupF u n θ R L cap i
      else qA u inp (Function.update (entryA u out B) (srcP u) rec) i) =
      qA u inp (setupA u n θ R L cap rec out B) := by
  funext i
  rcases qcover u i with rfl | ⟨j, rfl⟩
  · have hn : inQ u ∉ targetsQ u := fun h => by have := mem_targetsQ_val u _ h; simp at this
    simp [hn, qA_in]
  · simp only [qA_p]
    rcases pcover u j with ⟨a, rfl⟩ | ⟨k, rfl⟩
    · refine Scrub.cover (motive := fun a => (if pQ u (sI u a) ∈ targetsQ u then setupF u n θ R L cap (pQ u (sI u a))
        else Function.update (entryA u out B) (srcP u) rec (sI u a)) = setupA u n θ R L cap rec out B (sI u a))
        (fun k => ?_) ?_ ?_ a
      · rw [if_neg (inner_not_mem u k)]
        simp only [setupA, sI, Fin.addCases_left, Scrub.bank_inner]
        by_cases hk : k = srcO u
        · subst hk; simp [srcP, sI]
        · rw [Function.update_of_ne (fun e => hk (by
            have := congrArg Fin.val ((sI_inj u) e)
            exact Fin.ext (by simpa [Scrub.inner, srcP, sI] using this)))]
          simp only [entryA, hk, if_false]
          exact if_neg (sI_ne_eI u _ 6)
      · have hm : pQ u (sI u Scrub.logTape) ∈ targetsQ u := by simp [targetsQ]
        rw [if_pos hm, setupF_log]
        simp [setupA, sI]
      · have hm : pQ u (sI u Scrub.driverTape) ∈ targetsQ u := by simp [targetsQ]
        rw [if_pos hm, setupF_driver]
        simp [setupA, sI]
    · by_cases h6 : k = 6
      · subst h6
        rw [if_neg (by rw [eI_mem]; simp), Function.update_of_ne (show eI u 6 ≠ srcP u from (sI_ne_eI u _ 6).symm)]
        simp [entryA, setupA, eI]
      · rw [if_pos ((eI_mem u k).mpr h6), setupF_e]
        fin_cases k <;> simp_all [setupA, eI]

noncomputable def loadQM (u : ℕ) := MaskedReset.machine (loadL (pQ u (srcP u)) (targetsQ u))
  (fun i => decide (i ∈ targetsQ u))

/-- **The setup load**: the scrub's driver and log and the rows' extras are loaded from the record, rewound. -/
theorem loadQ_step (u n θ R L cap : ℕ) (P : ℕ) (inp rest out B : List Bool) (m1 : ℕ) :
    ∃ m2, Step (loadQM u) (2 * loadCost (setupFields u n θ R L cap) + 2)
      (Fin.addCases (qH u P (popH u 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA u inp (Function.update (entryA u out B) (srcP u) (fieldsWord (setupFields u n θ R L cap) ++ rest)))
        (fun _ : Fin 1 => List.replicate m1 false))
      (Fin.addCases (qH u P (popH u (fieldsWord (setupFields u n θ R L cap)).length ![0, 0, 0, 0, 0, 0, out.length, 0]))
        (fun _ : Fin 1 => 0))
      (Fin.addCases (qA u inp (setupA u n θ R L cap (fieldsWord (setupFields u n θ R L cap) ++ rest) out B))
        (fun _ : Fin 1 => List.replicate m2 false)) := by
  set rec := fieldsWord (setupFields u n θ R L cap) ++ rest with hrec
  set A1 := Function.update (entryA u out B) (srcP u) rec with hA1
  set H1 := popH u 0 ![0, 0, 0, 0, 0, 0, out.length, 0] with hH1
  have hl := loadL_run (pQ u (srcP u)) (setupF u n θ R L cap) (targetsQ u) (targetsQ_nodup u) (rec_not_mem u) []
    rest (qH u P H1) (qA u inp A1) (by rw [qH_p, hH1, popH_src]; rfl)
    (by rw [qA_p, hA1, Function.update_self]; rfl)
    (by
      intro i hi
      rcases qcover u i with rfl | ⟨j, rfl⟩
      · have := mem_targetsQ_val u _ hi; simp at this
      · rw [qH_p, hH1]
        apply popH_zero_other
        intro e; subst e
        exact absurd hi (by rw [eI_mem]; simp))
    (by
      intro i hi
      rcases qcover u i with rfl | ⟨j, rfl⟩
      · have := mem_targetsQ_val u _ hi; simp at this
      · rw [qA_p, hA1]
        have hjs : j ≠ srcP u := fun e => rec_not_mem u (e ▸ hi)
        rw [Function.update_of_ne hjs]
        unfold entryA
        rw [if_neg]
        intro e; subst e
        exact absurd hi (by rw [eI_mem]; simp))
  obtain ⟨m2, hm⟩ := maskBlank hl (fun i => decide (i ∈ targetsQ u)) (by
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases qcover u i with rfl | ⟨j, rfl⟩
    · have := mem_targetsQ_val u _ hi; simp at this
    · rw [qH_p, hH1]
      apply popH_zero_other
      intro e; subst e
      exact absurd hi (by rw [eI_mem]; simp)) m1
  refine ⟨m2, hm.congr ?_ ?_⟩
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => ℕ) g (fun _ : Fin 1 => 0)) (loadQ_heads u P out.length
      (fieldsWord (setupFields u n θ R L cap)).length _)
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => List Bool) g (fun _ : Fin 1 => List.replicate m2 false))
      (loadQ_tapes u n θ R L cap inp rec out B)

/-! ## Lifting stages -/

theorem liftQ {u s n : ℕ} {p : Machine (SL u + 8) s} {H H' : Fin (SL u + 8) → ℕ} {A A' : Fin (SL u + 8) → List Bool}
    (h : Step p n H A H' A') (pin : ℕ) (inp : List Bool) :
    Step (RecoveryFocus.machine (pQ u) p) n (qH u pin H) (qA u inp A) (qH u pin H') (qA u inp A') := by
  have d := dockRun h (pQ u) (pQ_inj u) (qH u pin H) (qA u inp A) (fun j => qH_p u pin H j) (fun j => qA_p u inp A j)
  refine d.congr ?_ ?_
  · apply dockH_eq_of _ (pQ_inj u)
    · intro j; rw [qH_p]
    · intro i hi
      rcases qcover u i with rfl | ⟨j, rfl⟩
      · rw [qH_in, qH_in]
      · exact absurd rfl (hi j)
  · apply install_eq_of _ (pQ_inj u)
    · intro j; rw [qA_p]
    · intro i hi
      rcases qcover u i with rfl | ⟨j, rfl⟩
      · rw [qA_in, qA_in]
      · exact absurd rfl (hi j)

theorem liftC {N k s n : ℕ} {p : Machine N s} {H H' : Fin N → ℕ} {A A' : Fin N → List Bool}
    (h : Step p n H A H' A') (e : Fin k → ℕ) (d : Fin k → List Bool) :
    Step (RecoveryFocus.machine (Fin.castAdd k) p) n (Fin.addCases H e) (Fin.addCases A d)
      (Fin.addCases H' e) (Fin.addCases A' d) := by
  have hd := dockRun h (Fin.castAdd k) (castAdd_inj N k) (Fin.addCases H e) (Fin.addCases A d)
    (fun j => Fin.addCases_left j) (fun j => Fin.addCases_left j)
  rwa [dockH_castAdd, install_castAdd] at hd

/-! ## Stage 3: the work tapes blanked -/

noncomputable def blankM (u : ℕ) := Scrub.machine (Block.idle (1 + (14 + u) + 1)) (scr u) (scr u)

/-- The factor layout before the blanking: the record, everything else empty. -/
def recOnly (u : ℕ) (rec : List Bool) : Fin (1 + (14 + u) + 1) → List Bool := fun j => if j = srcO u then rec else []

theorem blank_step (u : ℕ) (P : ℕ) (rec : List Bool) (R L : ℕ) (hR : 1 ≤ R) (hL : R + 1 ≤ L) :
    Step (blankM u) (2 * 0 + 2 + 1 + (2 * R + 4)) (Scrub.heads (fH u P 0)) (Scrub.bank (recOnly u rec) R L)
      (Scrub.heads (fH u P 0)) (Scrub.bank (restA u rec [] R) R L) := by
  have h := Scrub.step (Print.idle_step (fH u P 0) (recOnly u rec)) (scr u) (scr u) R L
    (by
      intro i hi
      rcases cover u i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
      · simp [scr] at hi
      · rw [fH_prSlot]
        by_cases hc : c = 10
        · subst hc; simp [scr, outI_eq] at hi
        · fin_cases c <;> simp_all [bh]
      · rw [fH_prSlot]; simp
      · exact fH_logI u _ _)
    (fun i hi => hi)
    (by intro i hi; simp [recOnly, scr] at hi ⊢; simp [hi.1])
    (by omega) hL
  have e1 : Scrub.rewound (scr u) (fH u P 0) = fH u P 0 := by
    funext i
    unfold Scrub.rewound
    by_cases hi : scr u i = true
    · rw [if_pos hi]
      rcases cover u i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
      · simp [scr] at hi
      · rw [fH_prSlot]
        by_cases hc : c = 10
        · subst hc; simp [scr, outI_eq] at hi
        · fin_cases c <;> simp_all [bh]
      · rw [fH_prSlot]; simp
      · exact (fH_logI u _ _).symm
    · rw [if_neg hi]
  have e2 : Scrub.blank (scr u) (recOnly u rec) R = restA u rec [] R :=
    blank_exit u _ rec [] R (by simp [recOnly]) (by simp [recOnly, (srcO_ne_outI u).symm])
  rw [e1, e2] at h
  exact h

/-! ## The POP row -/

/-- **The POP row machine**: ONE machine per evaluator family. -/
noncomputable def popRowM (F : EvalFam) :=
  Composition.machine (Composition.machine (Composition.machine (readQM F.t) (loadQM F.t))
    (RecoveryFocus.machine (Fin.castAdd 1) (RecoveryFocus.machine (pQ F.t)
      (RecoveryFocus.machine (Fin.castAdd 8) (blankM F.t)))))
    (RecoveryFocus.machine (Fin.castAdd 1) (RecoveryFocus.machine (pQ F.t) (popM F)))

/-- **The POP row record**: the setup fields, then the population's record. -/
def popRowRec {F : EvalFam} (n θ R L cap : ℕ) (oneW : List Bool) (sts : List (SSpec F)) : List Bool :=
  fieldsWord (setupFields F.t n θ R L cap) ++ popRec oneW sts

noncomputable def popRowCost {F : EvalFam} (n θ R L cap : ℕ) (oneW : List Bool) (sts : List (SSpec F)) : ℕ :=
  (((2 * (2 * (popRowRec n θ R L cap oneW sts).length + 1) + 2) + 1 + (2 * loadCost (setupFields F.t n θ R L cap) + 2)) +
    1 + (2 * 0 + 2 + 1 + (2 * R + 4))) + 1 + popCost oneW n θ sts R

/-- **The POP row, as a loop body**: from the input cursor at `frame` of the row record, EMPTY
work tapes, the output receives the population's `exprWord` (`popOut`); the input cursor passes the record. -/
theorem popRow_step (F : EvalFam) (n θ : ℕ) (oneW : List Bool) (sts : List (SSpec F)) (pre rest out B : List Bool)
    (R L cap : ℕ) (hR1 : 1 ≤ R) (hL : R + 1 ≤ L) (hok : ∀ st ∈ sts, StateOk n R cap st) :
    ∃ A', Step (popRowM F) (popRowCost n θ R L cap oneW sts)
      (Fin.addCases (qH F.t pre.length (popH F.t 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA F.t (pre ++ frame (popRowRec n θ R L cap oneW sts) ++ rest) (entryA F.t out B)) (fun _ : Fin 1 => []))
      (Fin.addCases (qH F.t (pre.length + (2 * (popRowRec n θ R L cap oneW sts).length + 1))
        (popH F.t (popRowRec n θ R L cap oneW sts).length ![0, 0, 0, 0, 0, 0, (out ++ popOut oneW n θ sts).length, 0]))
        (fun _ : Fin 1 => 0)) A' ∧
      A' (Fin.castAdd 1 (inQ F.t)) = pre ++ frame (popRowRec n θ R L cap oneW sts) ++ rest ∧
      A' (Fin.castAdd 1 (pQ F.t (eI F.t 6))) = overlay (out ++ popOut oneW n θ sts) B := by
  set u := F.t with hu
  set rec := popRowRec n θ R L cap oneW sts with hrec
  set inp := pre ++ frame rec ++ rest with hinp
  set P := pre.length + (2 * rec.length + 1) with hP
  set fw := fieldsWord (setupFields u n θ R L cap) with hfw
  obtain ⟨m1, h1⟩ := readQ_step u pre rec rest (popH u 0 ![0, 0, 0, 0, 0, 0, out.length, 0]) (entryA u out B)
    (popH_src u 0 _) (by simp [entryA, show srcP u ≠ eI u 6 from sI_ne_eI u _ 6])
  obtain ⟨m2, h2⟩ := loadQ_step u n θ R L cap P inp (popRec oneW sts) out B m1
  rw [← hfw] at h2
  have hrec' : fw ++ popRec oneW sts = rec := by rw [hrec, popRowRec, hfw]
  rw [hrec'] at h2
  have h3 := liftC (liftQ (liftC (blank_step u fw.length rec R L hR1 hL)
    ![0, 0, 0, 0, 0, 0, out.length, 0]
    ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false], [false], [false], [],
      overlay out B, List.replicate cap false]) P inp) (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate m2 false)
  have hp := pop_run F n θ oneW sts fw [] [] [] out B R L cap false false hL hok
  rw [List.append_nil, hrec'] at hp
  have h4 := liftC (liftQ hp P inp) (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate m2 false)
  have t := ((h1.seq h2).seq h3).seq h4
  have el : fw.length + (popRec oneW sts).length = rec.length := by rw [← hrec']; simp
  rw [el] at t
  refine ⟨_, t, ?_, ?_⟩
  · simp [inQ, qA]
  · simp only [Fin.addCases_left, qA_p, popA_eI]
    rfl

end NearCubicWires.WireExponent3_5.ListMachine.Row
