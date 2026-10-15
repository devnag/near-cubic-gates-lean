import Proof.Wire_3_5.ListMachineRowRadixRows

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun atomCode monoBits recW polyWord coefWord)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5
open NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm (regTape regTape_zero)

/-! ## The tuple loop, docked on the population layout -/

/-- The odometer's registers: two printer-bank tapes, blank of length `R` at rest. -/
def rFP (t : ℕ) : Fin (SL t + 8) := sI t (Scrub.inner (prSlot t (Fin.castAdd t 0)))
def rGP (t : ℕ) : Fin (SL t + 8) := sI t (Scrub.inner (prSlot t (Fin.castAdd t 1)))

@[simp] theorem rFP_val (t : ℕ) : (rFP t).val = 1 := rfl
@[simp] theorem rGP_val (t : ℕ) : (rGP t).val = 2 := rfl

theorem prSlot_ne_so (t : ℕ) (c : Fin 14) (hc : c ≠ 10) : prSlot t (Fin.castAdd t c) ≠ srcO t ∧
    prSlot t (Fin.castAdd t c) ≠ outI t := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg Fin.val h; simp [prSlot] at this
  · have := congrArg Fin.val h; simp [prSlot] at this; exact hc (Fin.ext (by simp; omega))

theorem popA_reg (t R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) (c : Fin 14) (hc : c ≠ 10) :
    popA t R L src st e (sI t (Scrub.inner (prSlot t (Fin.castAdd t c)))) = List.replicate R false := by
  rw [popA_sI, Scrub.bank_inner]
  simp [restA, (prSlot_ne_so t c hc).1, (prSlot_ne_so t c hc).2]

theorem popH_reg (t p : ℕ) (e : Fin 8 → ℕ) (c : Fin 14) (hc : c ≠ 10) :
    popH t p e (sI t (Scrub.inner (prSlot t (Fin.castAdd t c)))) = 0 := by
  rw [popH_sI, Scrub.heads_inner, fH_prSlot, Fin.addCases_left]
  fin_cases c <;> simp_all [bh]

def radSlots (t : ℕ) : Fin 10 → Fin (SL t + 8) :=
  ![eI t 0, eI t 1, eI t 2, eI t 3, eI t 4, stP t, eI t 6, eI t 7, rFP t, rGP t]

theorem radSlots_val (t : ℕ) (j : Fin 10) :
    (radSlots t j).val = ![SL t, SL t + 1, SL t + 2, SL t + 3, SL t + 4, 11, SL t + 6, SL t + 7, 1, 2] j := by
  fin_cases j <;> rfl

theorem radSlots_inj (t : ℕ) : Function.Injective (radSlots t) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [radSlots_val, radSlots_val] at hv
  fin_cases a <;> fin_cases b <;> first | rfl | (simp [SL] at hv <;> omega)

noncomputable def radPM (t : ℕ) := RecoveryFocus.machine (radSlots t) radLoop

/-- The population heads at the tuple loop's slots. -/
theorem radH_slots (u p o : ℕ) (j : Fin 10) :
    popH u p ![0, 0, 0, 0, 0, 0, o, 0] (radSlots u j) = rxH o j := by
  fin_cases j
  · exact popH_eI u p _ 0
  · exact popH_eI u p _ 1
  · exact popH_eI u p _ 2
  · exact popH_eI u p _ 3
  · exact popH_eI u p _ 4
  · exact popH_st u p _
  · exact popH_eI u p _ 6
  · exact popH_eI u p _ 7
  · exact popH_reg u p _ 0 (by decide)
  · exact popH_reg u p _ 1 (by decide)

/-- The population tapes at the tuple loop's slots. -/
theorem radA_slots (u R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) (j : Fin 10) :
    popA u R L src st e (radSlots u j) =
      ![e 0, e 1, e 2, e 3, e 4, st, e 6, e 7, List.replicate R false, List.replicate R false] j := by
  fin_cases j
  · exact popA_eI u R L src st e 0
  · exact popA_eI u R L src st e 1
  · exact popA_eI u R L src st e 2
  · exact popA_eI u R L src st e 3
  · exact popA_eI u R L src st e 4
  · exact popA_st u R L src st e
  · exact popA_eI u R L src st e 6
  · exact popA_eI u R L src st e 7
  · exact popA_reg u R L src st e 0 (by decide)
  · exact popA_reg u R L src st e 1 (by decide)

theorem not_slot_eI (u : ℕ) (k : Fin 8) (hi : ∀ j, radSlots u j ≠ eI u k) : k = 5 := by
  fin_cases k
  · exact absurd rfl (hi 0)
  · exact absurd rfl (hi 1)
  · exact absurd rfl (hi 2)
  · exact absurd rfl (hi 3)
  · exact absurd rfl (hi 4)
  · rfl
  · exact absurd rfl (hi 6)
  · exact absurd rfl (hi 7)

/-- The tuple loop's bank at entry and exit, in closed form. -/
theorem radA_zero (K P : ℕ) (cs : List ℕ) (T : List Bool) (fs : List (List (List ℕ))) (Zw st o B : List Bool)
    (cap R : ℕ) (hR : 1 ≤ R) :
    (radA K P cs T fs Zw st o B cap (R - 1) 0).tapes = ![frame (encT K (List.replicate P 0)), Zw, fieldsU cs, T,
      [true], st, overlay o B, List.replicate cap false, List.replicate R false, List.replicate R false] := by
  have hreg : regTape (R - 1) 0 = List.replicate R false := by rw [regTape_zero, Nat.sub_add_cancel hR]
  have hN : 0 < (K + 1) ^ P := by positivity
  have ea : radAt K P cs T fs 0 = [] := by simp [radAt]
  funext j
  fin_cases j <;> simp [radA, RX.tapes, tupAt_zero, ea, hN, hreg]

theorem radA_end (K P : ℕ) (cs : List ℕ) (T : List Bool) (fs : List (List (List ℕ))) (Zw st o B : List Bool)
    (cap R : ℕ) (hR : 1 ≤ R) :
    (radA K P cs T fs Zw st o B cap (R - 1) ((K + 1) ^ P)).tapes = ![frame (encT K (List.replicate P 0)), Zw,
      fieldsU cs, T, [false], st, overlay (o ++ radW K P cs T fs) B, List.replicate cap false,
      List.replicate R false, List.replicate R false] := by
  have hreg : regTape (R - 1) 0 = List.replicate R false := by rw [regTape_zero, Nat.sub_add_cancel hR]
  have eN : tupAt K P ((K + 1) ^ P) = List.replicate P 0 := tupAt_out K P _ le_rfl
  funext j
  fin_cases j <;> simp [radA, RX.tapes, eN, radW, hreg]

/-- The tuple loop on the population layout. -/
theorem radP_step (u K P : ℕ) (cs : List ℕ) (T : List Bool) (fs : List (List (List ℕ))) (hP : 1 ≤ P)
    (hcs : cs.length = P * (K + 1)) (hfs : fs.length = P * (K + 1)) (o B : List Bool) (cap R : ℕ) (hR : 2 ≤ R)
    (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost fs ≤ cap) (hc3 : incCost K P ≤ cap) (L p : ℕ) (src : List Bool)
    (x5 : List Bool) :
    Step (radPM u) (radCost K P cs fs) (popH u p ![0, 0, 0, 0, 0, 0, o.length, 0])
      (popA u R L src (stF fs) ![frame (encT K (List.replicate P 0)), zW K (P * (K + 1)), fieldsU cs, T, [true], x5,
        overlay o B, List.replicate cap false])
      (popH u p ![0, 0, 0, 0, 0, 0, (o ++ radW K P cs T fs).length, 0])
      (popA u R L src (stF fs) ![frame (encT K (List.replicate P 0)), zW K (P * (K + 1)), fieldsU cs, T, [false], x5,
        overlay (o ++ radW K P cs T fs) B, List.replicate cap false]) := by
  have hr := radLoop_run K P cs T fs hP hcs hfs [] o B cap (R - 1) (by omega) hc1 hc2 hc3
  rw [List.append_nil, radA_zero _ _ _ _ _ _ _ _ _ _ _ (by omega), radA_end _ _ _ _ _ _ _ _ _ _ _ (by omega)] at hr
  have h := dockRun hr (radSlots u) (radSlots_inj u) (popH u p ![0, 0, 0, 0, 0, 0, o.length, 0])
    (popA u R L src (stF fs) ![frame (encT K (List.replicate P 0)), zW K (P * (K + 1)), fieldsU cs, T, [true], x5,
        overlay o B, List.replicate cap false])
    (fun j => radH_slots u p o.length j) (fun j => by rw [radA_slots]; fin_cases j <;> simp)
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ (radSlots_inj u)
    · intro j; exact radH_slots u p _ j
    · intro i hi
      rcases pcover u i with ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [popH_sI, popH_sI]
      · rw [popH_eI, popH_eI, not_slot_eI u k hi]; simp
  · apply install_eq_of _ (radSlots_inj u)
    · intro j; rw [radA_slots]; fin_cases j <;> simp
    · intro i hi
      rcases pcover u i with ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [popA_sI, popA_sI]
      · rw [popA_eI, popA_eI, not_slot_eI u k hi]; simp

/-! ## The RADIX printer on the population layout -/

/-- The store's contents are the prints. -/
theorem storeW_stF {F : EvalFam} (xs : List (FSpec F)) : storeW xs = stF (xs.map FSpec.poly) := by
  simp [storeW, stF, List.flatMap_map]

/-- **The RADIX printer**: the factor store, the tuple loop, the terminator. ONE machine per evaluator family. -/
noncomputable def radPopM (F : EvalFam) := Composition.machine (Composition.machine (mStoreM F) (radPM F.t)) (putEM F.t false)

noncomputable def radPopCost {F : EvalFam} (K P : ℕ) (cs : List ℕ) (xs : List (FSpec F)) (R : ℕ) : ℕ :=
  ((2 * storeCost xs R + 2) + 1 + radCost K P cs (xs.map FSpec.poly)) + 1 + 1

theorem radPop_run (F : EvalFam) (K P : ℕ) (cs : List ℕ) (T : List Bool) (xs : List (FSpec F)) (hP : 1 ≤ P)
    (hcs : cs.length = P * (K + 1)) (hxs : xs.length = P * (K + 1)) (pre out B : List Bool) (R L cap : ℕ)
    (hR2 : 2 ≤ R) (hRx : ∀ x ∈ xs, x.cost + 1 ≤ R) (hL : R + 1 ≤ L) (hc0 : storeCost xs R ≤ cap)
    (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost (xs.map FSpec.poly) ≤ cap) (hc3 : incCost K P ≤ cap) :
    Step (radPopM F) (radPopCost K P cs xs R) (popH F.t pre.length ![0, 0, 0, 0, 0, 0, out.length, 0])
      (popA F.t R L (pre ++ storeRec xs) [] ![frame (encT K (List.replicate P 0)), zW K (P * (K + 1)), fieldsU cs, T,
        [true], [], overlay out B, List.replicate cap false])
      (popH F.t (pre.length + (xs.flatMap fun x => true :: x.block).length)
        ![0, 0, 0, 0, 0, 0, (out ++ (radW K P cs T (xs.map FSpec.poly) ++ [false])).length, 0])
      (popA F.t R L (pre ++ storeRec xs) (stF (xs.map FSpec.poly)) ![frame (encT K (List.replicate P 0)),
        zW K (P * (K + 1)), fieldsU cs, T, [false], [], overlay (out ++ (radW K P cs T (xs.map FSpec.poly) ++ [false])) B,
        List.replicate cap false]) := by
  have s1 := mStore_step F xs pre [] [] R L cap hRx hL hc0 (frame (encT K (List.replicate P 0))) (zW K (P * (K + 1)))
    (fieldsU cs) T [true] [] (overlay out B) out.length
  rw [List.append_nil] at s1
  have e1 : overlay (storeW xs) [] = stF (xs.map FSpec.poly) := by rw [storeW_stF]; simp [overlay]
  rw [e1] at s1
  have s2 := radP_step F.t K P cs T (xs.map FSpec.poly) hP hcs (by simp [hxs]) out B cap R hR2 hc1 hc2 hc3 L
    (pre.length + (xs.flatMap fun x => true :: x.block).length) (pre ++ storeRec xs) []
  have s3 := putE_step F.t R L (pre.length + (xs.flatMap fun x => true :: x.block).length) (pre ++ storeRec xs)
    (stF (xs.map FSpec.poly)) (frame (encT K (List.replicate P 0))) (zW K (P * (K + 1))) (fieldsU cs) T [false] []
    (out ++ radW K P cs T (xs.map FSpec.poly)) B (List.replicate cap false) false
  have t := (s1.seq s2).seq s3
  rw [List.append_assoc] at t
  exact t

/-! ## The setup fields, with general values -/

/-- The setup fields' values at the targets (the scrub's driver and log, the extras but the output). -/
def setupG (u R L : ℕ) (ev : Fin 8 → List Bool) : Fin (IPL u) → List Bool := fun i =>
  if i = pQ u (sI u Scrub.driverTape) then List.replicate R true
  else if i = pQ u (sI u Scrub.logTape) then List.replicate L false
  else if i = pQ u (eI u 0) then ev 0
  else if i = pQ u (eI u 1) then ev 1
  else if i = pQ u (eI u 2) then ev 2
  else if i = pQ u (eI u 3) then ev 3
  else if i = pQ u (eI u 4) then ev 4
  else if i = pQ u (eI u 5) then ev 5
  else ev 7

/-- The setup fields, in record order. -/
def setupFieldsG (u R L : ℕ) (ev : Fin 8 → List Bool) : List (List Bool) := (targetsQ u).map (setupG u R L ev)

/-- The population layout after the setup load. -/
def setupAG (u R L : ℕ) (ev : Fin 8 → List Bool) (rec out B : List Bool) : Fin (SL u + 8) → List Bool :=
  Fin.addCases (Scrub.bank (fun j => if j = srcO u then rec else []) R L)
    ![ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, overlay out B, ev 7]

theorem setupG_driver (u R L : ℕ) (ev : Fin 8 → List Bool) :
    setupG u R L ev (pQ u (sI u Scrub.driverTape)) = List.replicate R true := by simp [setupG]

theorem setupG_log (u R L : ℕ) (ev : Fin 8 → List Bool) :
    setupG u R L ev (pQ u (sI u Scrub.logTape)) = List.replicate L false := by
  have h : pQ u (sI u Scrub.logTape) ≠ pQ u (sI u (Scrub.driverTape (t := 1 + (14 + u) + 1))) :=
    fun e => sI_driver_ne_log u ((pQ_inj u) e).symm
  simp [setupG, h]

theorem setupG_e (u R L : ℕ) (ev : Fin 8 → List Bool) (k : Fin 8) (hk : k ≠ 6) :
    setupG u R L ev (pQ u (eI u k)) = ev k := by
  have h1 : ∀ a, pQ u (eI u k) ≠ pQ u (sI u a) := fun a e => sI_ne_eI u a k ((pQ_inj u) e).symm
  unfold setupG
  rw [if_neg (h1 _), if_neg (h1 _)]
  fin_cases k <;> simp_all [(pQ_inj u).eq_iff, (eI_inj u).eq_iff]

theorem loadG_tapes (u R L : ℕ) (ev : Fin 8 → List Bool) (inp rec out B : List Bool) :
    (fun i => if i ∈ targetsQ u then setupG u R L ev i
      else qA u inp (Function.update (entryA u out B) (srcP u) rec) i) =
      qA u inp (setupAG u R L ev rec out B) := by
  funext i
  rcases qcover u i with rfl | ⟨j, rfl⟩
  · have hn : inQ u ∉ targetsQ u := fun h => by have := mem_targetsQ_val u _ h; simp at this
    simp [hn, qA_in]
  · simp only [qA_p]
    rcases pcover u j with ⟨a, rfl⟩ | ⟨k, rfl⟩
    · refine Scrub.cover (motive := fun a => (if pQ u (sI u a) ∈ targetsQ u then setupG u R L ev (pQ u (sI u a))
        else Function.update (entryA u out B) (srcP u) rec (sI u a)) = setupAG u R L ev rec out B (sI u a))
        (fun k => ?_) ?_ ?_ a
      · rw [if_neg (inner_not_mem u k)]
        simp only [setupAG, sI, Fin.addCases_left, Scrub.bank_inner]
        by_cases hk : k = srcO u
        · subst hk; simp [srcP, sI]
        · rw [Function.update_of_ne (fun e => hk (by
            have := congrArg Fin.val ((sI_inj u) e)
            exact Fin.ext (by simpa [Scrub.inner, srcP, sI] using this)))]
          simp only [entryA, hk, if_false]
          exact if_neg (sI_ne_eI u _ 6)
      · have hm : pQ u (sI u Scrub.logTape) ∈ targetsQ u := by simp [targetsQ]
        rw [if_pos hm, setupG_log]
        simp [setupAG, sI]
      · have hm : pQ u (sI u Scrub.driverTape) ∈ targetsQ u := by simp [targetsQ]
        rw [if_pos hm, setupG_driver]
        simp [setupAG, sI]
    · by_cases h6 : k = 6
      · subst h6
        rw [if_neg (by rw [eI_mem]; simp), Function.update_of_ne (show eI u 6 ≠ srcP u from (sI_ne_eI u _ 6).symm)]
        simp [entryA, setupAG, eI]
      · rw [if_pos ((eI_mem u k).mpr h6), setupG_e u R L ev k h6]
        fin_cases k <;> simp_all [setupAG, eI]

/-- **The setup load** with general values. -/
theorem loadG_step (u R L : ℕ) (ev : Fin 8 → List Bool) (P : ℕ) (inp rest out B : List Bool) (m1 : ℕ) :
    ∃ m2, Step (loadQM u) (2 * loadCost (setupFieldsG u R L ev) + 2)
      (Fin.addCases (qH u P (popH u 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA u inp (Function.update (entryA u out B) (srcP u) (fieldsWord (setupFieldsG u R L ev) ++ rest)))
        (fun _ : Fin 1 => List.replicate m1 false))
      (Fin.addCases (qH u P (popH u (fieldsWord (setupFieldsG u R L ev)).length ![0, 0, 0, 0, 0, 0, out.length, 0]))
        (fun _ : Fin 1 => 0))
      (Fin.addCases (qA u inp (setupAG u R L ev (fieldsWord (setupFieldsG u R L ev) ++ rest) out B))
        (fun _ : Fin 1 => List.replicate m2 false)) := by
  set rec := fieldsWord (setupFieldsG u R L ev) ++ rest with hrec
  set A1 := Function.update (entryA u out B) (srcP u) rec with hA1
  set H1 := popH u 0 ![0, 0, 0, 0, 0, 0, out.length, 0] with hH1
  have hl := loadL_run (pQ u (srcP u)) (setupG u R L ev) (targetsQ u) (targetsQ_nodup u) (rec_not_mem u) []
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
      (fieldsWord (setupFieldsG u R L ev)).length _)
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => List Bool) g (fun _ : Fin 1 => List.replicate m2 false))
      (loadG_tapes u R L ev inp rec out B)

/-! ## The RADIX row -/

/-- The RADIX row's setup values: the zero tuple's word, the position word, the contribution fields, the residue
pattern, the loop flag, and the log. -/
def radEv (K P : ℕ) (cs : List ℕ) (T : List Bool) (cap : ℕ) : Fin 8 → List Bool :=
  ![frame (encT K (List.replicate P 0)), zW K (P * (K + 1)), fieldsU cs, T, [true], [], [], List.replicate cap false]

/-- **The RADIX row machine**: ONE machine per evaluator family. -/
noncomputable def radRowM (F : EvalFam) :=
  Composition.machine (Composition.machine (Composition.machine (readQM F.t) (loadQM F.t))
    (RecoveryFocus.machine (Fin.castAdd 1) (RecoveryFocus.machine (pQ F.t)
      (RecoveryFocus.machine (Fin.castAdd 8) (blankM F.t)))))
    (RecoveryFocus.machine (Fin.castAdd 1) (RecoveryFocus.machine (pQ F.t) (radPopM F)))

/-- **The RADIX row record**: the setup fields, then the factor blocks. -/
def radRowRec {F : EvalFam} (K P : ℕ) (cs : List ℕ) (T : List Bool) (R L cap : ℕ) (xs : List (FSpec F)) : List Bool :=
  fieldsWord (setupFieldsG F.t R L (radEv K P cs T cap)) ++ storeRec xs

noncomputable def radRowCost {F : EvalFam} (K P : ℕ) (cs : List ℕ) (T : List Bool) (R L cap : ℕ) (xs : List (FSpec F)) :
    ℕ :=
  (((2 * (2 * (radRowRec K P cs T R L cap xs).length + 1) + 2) + 1 +
    (2 * loadCost (setupFieldsG F.t R L (radEv K P cs T cap)) + 2)) + 1 + (2 * 0 + 2 + 1 + (2 * R + 4))) + 1 +
    radPopCost K P cs xs R

/-- What the RADIX row writes. -/
def radOut (K P : ℕ) (cs : List ℕ) (T : List Bool) (fs : List (List (List ℕ))) : List Bool := radW K P cs T fs ++ [false]

/-- **The RADIX row, as a loop body**: from the input cursor at `frame` of the row record, EMPTY
work tapes, the output receives `radOut`; the input cursor passes the record. -/
theorem radRow_step (F : EvalFam) (K P : ℕ) (cs : List ℕ) (T : List Bool) (xs : List (FSpec F)) (hP : 1 ≤ P)
    (hcs : cs.length = P * (K + 1)) (hxs : xs.length = P * (K + 1)) (pre rest out B : List Bool) (R L cap : ℕ)
    (hR2 : 2 ≤ R) (hRx : ∀ x ∈ xs, x.cost + 1 ≤ R) (hL : R + 1 ≤ L) (hc0 : storeCost xs R ≤ cap)
    (hc1 : resLoopCost cs + 3 ≤ cap) (hc2 : mselCost (xs.map FSpec.poly) ≤ cap) (hc3 : incCost K P ≤ cap) :
    ∃ A', Step (radRowM F) (radRowCost K P cs T R L cap xs)
      (Fin.addCases (qH F.t pre.length (popH F.t 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0))
      (Fin.addCases (qA F.t (pre ++ frame (radRowRec K P cs T R L cap xs) ++ rest) (entryA F.t out B))
        (fun _ : Fin 1 => []))
      (Fin.addCases (qH F.t (pre.length + (2 * (radRowRec K P cs T R L cap xs).length + 1))
        (popH F.t ((fieldsWord (setupFieldsG F.t R L (radEv K P cs T cap))).length +
          (xs.flatMap fun x => true :: x.block).length)
          ![0, 0, 0, 0, 0, 0, (out ++ radOut K P cs T (xs.map FSpec.poly)).length, 0]))
        (fun _ : Fin 1 => 0)) A' ∧
      A' (Fin.castAdd 1 (inQ F.t)) = pre ++ frame (radRowRec K P cs T R L cap xs) ++ rest ∧
      A' (Fin.castAdd 1 (pQ F.t (eI F.t 6))) = overlay (out ++ radOut K P cs T (xs.map FSpec.poly)) B := by
  set u := F.t with hu
  set ev := radEv K P cs T cap with hev
  set rec := radRowRec K P cs T R L cap xs with hrec
  set inp := pre ++ frame rec ++ rest with hinp
  set Q := pre.length + (2 * rec.length + 1) with hQ
  set fw := fieldsWord (setupFieldsG u R L ev) with hfw
  obtain ⟨m1, h1⟩ := readQ_step u pre rec rest (popH u 0 ![0, 0, 0, 0, 0, 0, out.length, 0]) (entryA u out B)
    (popH_src u 0 _) (by simp [entryA, show srcP u ≠ eI u 6 from sI_ne_eI u _ 6])
  obtain ⟨m2, h2⟩ := loadG_step u R L ev Q inp (storeRec xs) out B m1
  rw [← hfw] at h2
  have hrec' : fw ++ storeRec xs = rec := by rw [hrec, radRowRec, hfw, hev]
  rw [hrec'] at h2
  have h3 := liftC (liftQ (liftC (blank_step u fw.length rec R L (by omega) hL)
    ![0, 0, 0, 0, 0, 0, out.length, 0]
    ![ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, overlay out B, ev 7]) Q inp) (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => List.replicate m2 false)
  have hp := radPop_run F K P cs T xs hP hcs hxs fw out B R L cap hR2 hRx hL hc0 hc1 hc2 hc3
  rw [hrec'] at hp
  have hev' : (![ev 0, ev 1, ev 2, ev 3, ev 4, ev 5, overlay out B, ev 7] : Fin 8 → List Bool) =
      ![frame (encT K (List.replicate P 0)), zW K (P * (K + 1)), fieldsU cs, T, [true], [], overlay out B,
        List.replicate cap false] := by
    funext k; fin_cases k <;> simp [hev, radEv]
  rw [hev'] at h3
  have h4 := liftC (liftQ hp Q inp) (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate m2 false)
  have t := ((h1.seq h2).seq h3).seq h4
  refine ⟨_, t, ?_, ?_⟩
  · simp [inQ, qA]
  · simp only [Fin.addCases_left, qA_p, popA_eI]
    simp [radOut]

end NearCubicWires.WireExponent3_5.ListMachine.Row
