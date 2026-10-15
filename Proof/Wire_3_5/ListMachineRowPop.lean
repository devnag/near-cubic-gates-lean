import Proof.Wire_3_5.ListMachineRowStore

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

/-- The scrubbed factor layout's size. -/
abbrev SL (t : ℕ) : ℕ := 1 + (14 + t) + 1 + 1 + 1

/-- A tape of the scrubbed factor layout inside the population layout. -/
def sI (t : ℕ) (i : Fin (SL t)) : Fin (SL t + 8) := Fin.castAdd 8 i
/-- An extra tape. -/
def eI (t : ℕ) (k : Fin 8) : Fin (SL t + 8) := Fin.natAdd (SL t) k

/-- The record, the store. -/
def srcP (t : ℕ) : Fin (SL t + 8) := sI t (Scrub.inner (srcO t))
def stP (t : ℕ) : Fin (SL t + 8) := sI t (Scrub.inner (outI t))

@[simp] theorem sI_val (t : ℕ) (i : Fin (SL t)) : (sI t i).val = i.val := rfl
@[simp] theorem eI_val (t : ℕ) (k : Fin 8) : (eI t k).val = SL t + k.val := rfl
@[simp] theorem srcP_val (t : ℕ) : (srcP t).val = 0 := rfl
@[simp] theorem stP_val (t : ℕ) : (stP t).val = 11 := rfl

theorem sI_inj (t : ℕ) : Function.Injective (sI t) := fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
theorem eI_inj (t : ℕ) : Function.Injective (eI t) := fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
theorem sI_ne_eI (t : ℕ) (i : Fin (SL t)) (k : Fin 8) : sI t i ≠ eI t k := by
  intro h; have := congrArg Fin.val h; simp at this; omega

/-- Population heads: the scrubbed layout's (record cursor `p`, store cursor `0`), the extras'. -/
def popH (t p : ℕ) (e : Fin 8 → ℕ) : Fin (SL t + 8) → ℕ := Fin.addCases (Scrub.heads (fH t p 0)) e

/-- Population tapes: the scrubbed layout at rest, the extras. -/
def popA (t R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) : Fin (SL t + 8) → List Bool :=
  Fin.addCases (Scrub.bank (restA t src st R) R L) e

theorem popH_sI (t p : ℕ) (e : Fin 8 → ℕ) (i : Fin (SL t)) : popH t p e (sI t i) = Scrub.heads (fH t p 0) i := by
  simp [popH, sI]
theorem popH_eI (t p : ℕ) (e : Fin 8 → ℕ) (k : Fin 8) : popH t p e (eI t k) = e k := by simp [popH, eI]
theorem popA_sI (t R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) (i : Fin (SL t)) :
    popA t R L src st e (sI t i) = Scrub.bank (restA t src st R) R L i := by simp [popA, sI]
theorem popA_eI (t R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) (k : Fin 8) :
    popA t R L src st e (eI t k) = e k := by simp [popA, eI]

/-- Every population tape is a scrubbed-layout tape or an extra. -/
theorem pcover (t : ℕ) (i : Fin (SL t + 8)) : (∃ a, i = sI t a) ∨ ∃ k, i = eI t k := by
  refine Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun k => Or.inr ⟨k, rfl⟩) i

theorem popH_src (t p : ℕ) (e : Fin 8 → ℕ) : popH t p e (srcP t) = p := by
  simp [srcP, popH_sI, fH_srcO]
theorem popH_st (t p : ℕ) (e : Fin 8 → ℕ) : popH t p e (stP t) = 0 := by
  simp only [stP, popH_sI, Scrub.heads_inner]; rw [outI_eq, fH_prSlot]; simp [bh]
theorem popA_src (t R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) : popA t R L src st e (srcP t) = src := by
  simp [srcP, popA_sI, restA]
theorem popA_st (t R L : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) : popA t R L src st e (stP t) = st := by
  simp [stP, popA_sI, restA, (srcO_ne_outI t).symm]

/-- Only the record cursor differs. -/
theorem popH_other (t p p' : ℕ) (e : Fin 8 → ℕ) (i : Fin (SL t + 8)) (hi : i ≠ srcP t) :
    popH t p e i = popH t p' e i := by
  rcases pcover t i with ⟨a, rfl⟩ | ⟨k, rfl⟩
  · rw [popH_sI, popH_sI]
    refine Scrub.cover (motive := fun a => sI t a ≠ srcP t → Scrub.heads (fH t p 0) a = Scrub.heads (fH t p' 0) a)
      (fun k hk => ?_) (fun _ => by simp) (fun _ => by simp) a hi
    rw [Scrub.heads_inner, Scrub.heads_inner]
    exact fH_src_ne t p p' 0 k (fun e => hk (by rw [e]; rfl))
  · rw [popH_eI, popH_eI]

/-! ## Small stages -/

theorem popA_eq_of_extras (t R L : ℕ) (src st : List Bool) (e e' : Fin 8 → List Bool) (i : Fin (SL t + 8))
    (h : ∀ k, i = eI t k → e k = e' k) : popA t R L src st e i = popA t R L src st e' i := by
  rcases pcover t i with ⟨a, rfl⟩ | ⟨k, rfl⟩
  · rw [popA_sI, popA_sI]
  · rw [popA_eI, popA_eI]; exact h k rfl

theorem popH_eq_of_extras (t p : ℕ) (e e' : Fin 8 → ℕ) (i : Fin (SL t + 8))
    (h : ∀ k, i = eI t k → e k = e' k) : popH t p e i = popH t p e' i := by
  rcases pcover t i with ⟨a, rfl⟩ | ⟨k, rfl⟩
  · rw [popH_sI, popH_sI]
  · rw [popH_eI, popH_eI]; exact h k rfl

/-- The slots of a record field copied to the output. -/
def sOT (t : ℕ) : Fin 2 → Fin (SL t + 8) := ![srcP t, eI t 6]
theorem sOT_inj (t : ℕ) : Function.Injective (sOT t) := by
  intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [sOT] at this)

noncomputable def oneTM (t : ℕ) := RecoveryFocus.machine (sOT t) Unframe.machine

/-- A record field copied to the output. -/
theorem oneT_step (t R L p : ℕ) (pre w rest st : List Bool) (x z th c fo cw out B lg : List Bool) (hp : p = pre.length) :
    Step (oneTM t) (2 * w.length + 1) (popH t p ![0, 0, 0, 0, 0, 0, out.length, 0])
      (popA t R L (pre ++ frame w ++ rest) st ![x, z, th, c, fo, cw, overlay out B, lg])
      (popH t (p + (2 * w.length + 1)) ![0, 0, 0, 0, 0, 0, (out ++ w).length, 0])
      (popA t R L (pre ++ frame w ++ rest) st ![x, z, th, c, fo, cw, overlay (out ++ w) B, lg]) := by
  subst hp
  have h := dockRun (Unframe.run pre w rest out B) (sOT t) (sOT_inj t) (popH t pre.length ![0, 0, 0, 0, 0, 0, out.length, 0])
    (popA t R L (pre ++ frame w ++ rest) st ![x, z, th, c, fo, cw, overlay out B, lg])
    (by intro j; fin_cases j
        · simp [sOT, popH_src]
        · simp [sOT, popH_eI])
    (by intro j; fin_cases j
        · simp [sOT, popA_src]
        · simp [sOT, popA_eI])
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ (sOT_inj t)
    · intro j; fin_cases j
      · simp [sOT, popH_src]
      · simp [sOT, popH_eI]
    · intro i hi
      have h1 : i ≠ srcP t := fun e => hi 0 (by simp [sOT, e])
      have h2 : i ≠ eI t 6 := fun e => hi 1 (by simp [sOT, e])
      rw [popH_other t _ pre.length _ i h1]
      apply popH_eq_of_extras
      intro k hk; subst hk
      fin_cases k <;> simp_all
  · apply install_eq_of _ (sOT_inj t)
    · intro j; fin_cases j
      · simp [sOT, popA_src]
      · simp [sOT, popA_eI]
    · intro i hi
      have h2 : i ≠ eI t 6 := fun e => hi 1 (by simp [sOT, e])
      apply popA_eq_of_extras
      intro k hk; subst hk
      fin_cases k <;> simp_all

noncomputable def skipM (t : ℕ) := RecoveryFocus.machine ![srcP t] Rec.Skip.machine

theorem skipM_step (t R L p : ℕ) (src st : List Bool) (e : Fin 8 → List Bool) (he : Fin 8 → ℕ) :
    Step (skipM t) 1 (popH t p he) (popA t R L src st e) (popH t (p + 1) he) (popA t R L src st e) := by
  have hi : Function.Injective ![srcP t] := by intro a b _; exact Subsingleton.elim a b
  have h := dockRun (Rec.Skip.run src p) ![srcP t] hi (popH t p he) (popA t R L src st e)
    (by intro j; fin_cases j; simp [popH_src]) (by intro j; fin_cases j; simp [popA_src])
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ hi
    · intro j; fin_cases j; simp [popH_src]
    · intro i hi'
      exact popH_other t (p + 1) p he i (fun e => hi' 0 (by simp [e]))
  · apply install_eq_of _ hi
    · intro j; fin_cases j; simp [popA_src]
    · intro i _; rfl

/-- The slots of the coefficient field's load. -/
def sCW (t : ℕ) : Fin (2 + 1) → Fin (SL t + 8) := ![srcP t, eI t 5, eI t 7]
theorem sCW_inj (t : ℕ) : Function.Injective (sCW t) := by
  intro a b h; fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [sCW] at this)

noncomputable def loadCWM (t : ℕ) := RecoveryFocus.machine (sCW t) (MaskedReset.machine Unframe.machine ![false, true])

/-- The coefficient field loaded over the stale coefficient word; the coefficient cursor rewound. -/
theorem loadCW_step (t R L p cap : ℕ) (pre w rest st : List Bool) (x z th c fo cw out : List Bool) (ho : ℕ)
    (hp : p = pre.length) (hcap : 2 * w.length + 1 ≤ cap) :
    Step (loadCWM t) (2 * (2 * w.length + 1) + 2) (popH t p ![0, 0, 0, 0, 0, 0, ho, 0])
      (popA t R L (pre ++ frame w ++ rest) st ![x, z, th, c, fo, cw, out, List.replicate cap false])
      (popH t (p + (2 * w.length + 1)) ![0, 0, 0, 0, 0, 0, ho, 0])
      (popA t R L (pre ++ frame w ++ rest) st ![x, z, th, c, fo, overlay w cw, out, List.replicate cap false]) := by
  subst hp
  have hu := Unframe.run pre w rest [] cw
  simp only [List.nil_append, List.length_nil] at hu
  have hm := maskRun hu ![false, true] (by intro j hj; fin_cases j <;> simp_all) hcap
  have hc' : Step (MaskedReset.machine Unframe.machine ![false, true]) (2 * (2 * w.length + 1) + 2)
      ![pre.length, 0, 0] ![pre ++ frame w ++ rest, overlay [] cw, List.replicate cap false]
      ![pre.length + (2 * w.length + 1), 0, 0] ![pre ++ frame w ++ rest, overlay w cw, List.replicate cap false] :=
    (hm.congr_in (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)).congr
      (by funext j; fin_cases j <;> rfl) (by funext j; fin_cases j <;> rfl)
  have ecw : overlay [] cw = cw := by simp [overlay]
  rw [ecw] at hc'
  have h := dockRun hc' (sCW t) (sCW_inj t) (popH t pre.length ![0, 0, 0, 0, 0, 0, ho, 0])
    (popA t R L (pre ++ frame w ++ rest) st ![x, z, th, c, fo, cw, out, List.replicate cap false])
    (by intro j; fin_cases j
        · simp [sCW, popH_src]
        · simp [sCW, popH_eI]
        · simp [sCW, popH_eI])
    (by intro j; fin_cases j
        · simp [sCW, popA_src]
        · simp [sCW, popA_eI]
        · simp [sCW, popA_eI])
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ (sCW_inj t)
    · intro j; fin_cases j
      · simp [sCW, popH_src]
      · simp [sCW, popH_eI]
      · simp [sCW, popH_eI]
    · intro i hi
      have h1 : i ≠ srcP t := fun e => hi 0 (by simp [sCW, e])
      rw [popH_other t _ pre.length _ i h1]
  · apply install_eq_of _ (sCW_inj t)
    · intro j; fin_cases j
      · simp [sCW, popA_src]
      · simp [sCW, popA_eI]
      · simp [sCW, popA_eI]
    · intro i hi
      have h2 : i ≠ eI t 5 := fun e => hi 1 (by simp [sCW, e])
      apply popA_eq_of_extras
      intro k hk; subst hk
      fin_cases k <;> simp_all

/-! ## Setting a cell, closing the expression -/

namespace SetCell

def machine (b : Bool) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, ![some b], ![.stay]⟩ else none

theorem run (b x : Bool) : Step (machine b) 1 ![0] ![[x]] ![0] ![[b]] := by
  have hs := One.step_cfg (machine b) 0 1 [x] 0 (some b) .stay (by simp [machine])
  simp only [HeadMove.apply, NearCubicWires.WireExponent3_5.GF2.Two.wr] at hs
  obtain ⟨r, hr, hf, _⟩ := (Timed.single (p := machine b) rfl hs).run rfl
  refine ⟨r, hr, by rw [hf]; rfl, ?_, by omega⟩
  rw [hf]; funext i; fin_cases i; rfl

end SetCell

noncomputable def setFOM (t : ℕ) := RecoveryFocus.machine ![eI t 4] (SetCell.machine true)

theorem setFO_step (t R L p : ℕ) (src st : List Bool) (x z th c cw out lg : List Bool) (f0 : Bool) (ho : ℕ) :
    Step (setFOM t) 1 (popH t p ![0, 0, 0, 0, 0, 0, ho, 0]) (popA t R L src st ![x, z, th, c, [f0], cw, out, lg])
      (popH t p ![0, 0, 0, 0, 0, 0, ho, 0]) (popA t R L src st ![x, z, th, c, [true], cw, out, lg]) := by
  have hi : Function.Injective ![eI t 4] := by intro a b _; exact Subsingleton.elim a b
  have hr : Step (SetCell.machine true) 1 (fun _ => 0) ![[f0]] (fun _ => 0) ![[true]] :=
    ((SetCell.run true f0).congr_in (by funext i; fin_cases i; rfl) rfl).congr (by funext i; fin_cases i; rfl) rfl
  have h := Block.dockKeep hr ![eI t 4] hi (popH t p ![0, 0, 0, 0, 0, 0, ho, 0])
    (popA t R L src st ![x, z, th, c, [f0], cw, out, lg]) (by intro j; fin_cases j; simp [popH_eI])
    (by intro j; fin_cases j; simp [popA_eI])
  refine h.congr rfl ?_
  apply install_eq_of _ hi
  · intro j; fin_cases j; simp [popA_eI]
  · intro i hi'
    apply popA_eq_of_extras
    intro k hk; subst hk
    have h4 : k ≠ 4 := fun e => hi' 0 (by simp [e])
    fin_cases k <;> simp_all

noncomputable def putEM (t : ℕ) (b : Bool) := RecoveryFocus.machine ![eI t 6] (Put.machine b)

theorem putE_step (t R L p : ℕ) (src st : List Bool) (x z th c fo cw o B lg : List Bool) (b : Bool) :
    Step (putEM t b) 1 (popH t p ![0, 0, 0, 0, 0, 0, o.length, 0]) (popA t R L src st ![x, z, th, c, fo, cw, overlay o B, lg])
      (popH t p ![0, 0, 0, 0, 0, 0, (o ++ [b]).length, 0])
      (popA t R L src st ![x, z, th, c, fo, cw, overlay (o ++ [b]) B, lg]) := by
  have hi : Function.Injective ![eI t 6] := by intro a b _; exact Subsingleton.elim a b
  have h := dockRun (Put.run b o B) ![eI t 6] hi (popH t p ![0, 0, 0, 0, 0, 0, o.length, 0])
    (popA t R L src st ![x, z, th, c, fo, cw, overlay o B, lg]) (by intro j; fin_cases j; simp [popH_eI])
    (by intro j; fin_cases j; simp [popA_eI])
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ hi
    · intro j; fin_cases j; simp [popH_eI]
    · intro i hi'
      apply popH_eq_of_extras
      intro k hk; subst hk
      have h6 : k ≠ 6 := fun e => hi' 0 (by simp [e])
      fin_cases k <;> simp_all
  · apply install_eq_of _ hi
    · intro j; fin_cases j; simp [popA_eI]
    · intro i hi'
      apply popA_eq_of_extras
      intro k hk; subst hk
      have h6 : k ≠ 6 := fun e => hi' 0 (by simp [e])
      fin_cases k <;> simp_all

/-! ## The store, rewound -/

/-- The store's cursor is the one rewound. -/
def selSt (t : ℕ) (i : Fin (SL t)) : Bool := decide (i = Scrub.inner (outI t))

/-- The masked store's slots: the scrubbed layout, then the extras' log. -/
def mA (t : ℕ) : Fin (SL t + 1) → Fin (SL t + 8) := Fin.addCases (sI t) (fun _ : Fin 1 => eI t 7)

theorem mA_inj (t : ℕ) : Function.Injective (mA t) := by
  intro a b h
  revert h
  refine Fin.addCases (fun a' => ?_) (fun a' => ?_) a <;> refine Fin.addCases (fun b' => ?_) (fun b' => ?_) b <;>
    intro h <;> simp only [mA, Fin.addCases_left, Fin.addCases_right] at h
  · rw [sI_inj t h]
  · exact absurd h (sI_ne_eI t _ _)
  · exact absurd h.symm (sI_ne_eI t _ _)
  · rw [Fin.eq_zero a', Fin.eq_zero b']

noncomputable def mStoreM (F : EvalFam) := RecoveryFocus.machine (mA F.t) (MaskedReset.machine (storeM F) (selSt F.t))

theorem fH_out_ne (t p o o' : ℕ) (k : Fin (1 + (14 + t) + 1)) (hk : k ≠ outI t) : fH t p o k = fH t p o' k := by
  rcases cover t k with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
  · rw [fH_srcO, fH_srcO]
  · rw [fH_prSlot, fH_prSlot]
    have hc : c ≠ 10 := fun e => hk (by rw [e]; rfl)
    fin_cases c <;> simp_all [bh]
  · rw [fH_prSlot, fH_prSlot]; simp
  · rw [fH_logI, fH_logI]

theorem rewound_store (t p o : ℕ) :
    (fun i => if selSt t i then 0 else Scrub.heads (fH t p o) i) = Scrub.heads (fH t p 0) := by
  funext i
  by_cases h : selSt t i = true
  · rw [if_pos h]
    have e : i = Scrub.inner (outI t) := of_decide_eq_true h
    subst e
    rw [Scrub.heads_inner, outI_eq, fH_prSlot]; simp [bh]
  · rw [if_neg h]
    refine Scrub.cover (motive := fun i => ¬selSt t i = true → Scrub.heads (fH t p o) i = Scrub.heads (fH t p 0) i)
      (fun k hk => ?_) (fun _ => by simp) (fun _ => by simp) i h
    rw [Scrub.heads_inner, Scrub.heads_inner]
    exact fH_out_ne t p o 0 k (fun e => hk (by simp [selSt, e]))

/-- **The factor store of one state**, its cursor rewound. -/
theorem mStore_step (F : EvalFam) (xs : List (FSpec F)) (pre rest stOld : List Bool) (R L cap : ℕ)
    (hR : ∀ x ∈ xs, x.cost + 1 ≤ R) (hL : R + 1 ≤ L) (hcap : storeCost xs R ≤ cap)
    (x z th c fo cw out : List Bool) (ho : ℕ) :
    Step (mStoreM F) (2 * storeCost xs R + 2) (popH F.t pre.length ![0, 0, 0, 0, 0, 0, ho, 0])
      (popA F.t R L (pre ++ storeRec xs ++ rest) stOld ![x, z, th, c, fo, cw, out, List.replicate cap false])
      (popH F.t (pre.length + (xs.flatMap fun x => true :: x.block).length) ![0, 0, 0, 0, 0, 0, ho, 0])
      (popA F.t R L (pre ++ storeRec xs ++ rest) (overlay (storeW xs) stOld)
        ![x, z, th, c, fo, cw, out, List.replicate cap false]) := by
  have hs := store_run F xs pre rest [] stOld R L hR hL
  have e0 : overlay [] stOld = stOld := by simp [overlay]
  simp only [List.length_nil, List.nil_append, e0] at hs
  have hm := maskRun hs (selSt F.t) (by
    intro i hi
    have e : i = Scrub.inner (outI F.t) := of_decide_eq_true hi
    subst e
    rw [Scrub.heads_inner, outI_eq, fH_prSlot]; simp [bh]) hcap
  rw [rewound_store] at hm
  have h := dockRun hm (mA F.t) (mA_inj F.t) (popH F.t pre.length ![0, 0, 0, 0, 0, 0, ho, 0])
    (popA F.t R L (pre ++ storeRec xs ++ rest) stOld ![x, z, th, c, fo, cw, out, List.replicate cap false])
    (by intro j; refine Fin.addCases (fun a => ?_) (fun a => ?_) j
        · simp only [mA, Fin.addCases_left, popH_sI]
        · simp only [mA, Fin.addCases_right, popH_eI]; rfl)
    (by intro j; refine Fin.addCases (fun a => ?_) (fun a => ?_) j
        · simp only [mA, Fin.addCases_left, popA_sI]
        · simp only [mA, Fin.addCases_right, popA_eI]; rfl)
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ (mA_inj F.t)
    · intro j; refine Fin.addCases (fun a => ?_) (fun a => ?_) j
      · simp only [mA, Fin.addCases_left, popH_sI]
      · simp only [mA, Fin.addCases_right, popH_eI]; rfl
    · intro i hi
      rcases pcover F.t i with ⟨a, rfl⟩ | ⟨k, rfl⟩
      · exact absurd (by simp [mA]) (hi (Fin.castAdd 1 a))
      · rw [popH_eI, popH_eI]
  · apply install_eq_of _ (mA_inj F.t)
    · intro j; refine Fin.addCases (fun a => ?_) (fun a => ?_) j
      · simp only [mA, Fin.addCases_left, popA_sI]
      · simp only [mA, Fin.addCases_right, popA_eI]; rfl
    · intro i hi
      rcases pcover F.t i with ⟨a, rfl⟩ | ⟨k, rfl⟩
      · exact absurd (by simp [mA]) (hi (Fin.castAdd 1 a))
      · rw [popA_eI, popA_eI]

/-! ## The rows, docked -/

def rbSlots (t : ℕ) : Fin 9 → Fin (SL t + 8) := ![eI t 0, eI t 1, eI t 2, eI t 3, eI t 4, eI t 5, stP t, eI t 6, eI t 7]

theorem rbSlots_val (t : ℕ) (j : Fin 9) :
    (rbSlots t j).val = if j.val = 6 then 11 else if j.val < 6 then SL t + j.val else SL t + j.val - 1 := by
  fin_cases j <;> rfl

theorem rbSlots_inj (t : ℕ) : Function.Injective (rbSlots t) := by
  intro a b h
  have hv := congrArg Fin.val h
  have h1 := rbSlots_val t a
  have h2 := rbSlots_val t b
  rw [h1, h2] at hv
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  simp only [SL] at hv
  by_cases a6 : a.val = 6 <;> by_cases b6 : b.val = 6 <;> by_cases a5 : a.val < 6 <;> by_cases b5 : b.val < 6 <;>
    simp only [a6, b6, a5, b5, if_true, if_false] at hv <;> omega

noncomputable def rowsPM (t : ℕ) := RecoveryFocus.machine (rbSlots t) rowsM

theorem rowsP_step (u t θ : ℕ) (c : ℤ) (ps : List (List (List ℕ) × List (List ℕ))) (hps : ps.length = t)
    (tailC tailS o B : List Bool) (cap : ℕ) (c0 : Bool) (hcap0 : 2 * t + 1 ≤ cap)
    (hc1 : 2 * (decide (c < 0) :: Nat.bits c.natAbs).length + 1 ≤ cap)
    (hc2 : ((List.range t).map fun j => selPass ps j + 2).sum + 1 ≤ cap) (R L p : ℕ) (src : List Bool) :
    Step (rowsPM u) (rowsCost t θ c ps) (popH u p ![0, 0, 0, 0, 0, 0, o.length, 0])
      (popA u R L src (stW ps ++ tailS) ![frame (binary t 0), frame (List.replicate t false),
        List.replicate θ true ++ [false], [c0], [true], coefWord c ++ tailC, overlay o B, List.replicate cap false])
      (popH u p ![0, 0, 0, 0, 0, 0, (o ++ rowsW t θ c ps).length, 0])
      (popA u R L src (stW ps ++ tailS) ![frame (binary t (2 ^ t)), frame (List.replicate t false),
        List.replicate θ true ++ [false], [cAt t θ c0 (2 ^ t)], [false], coefWord c ++ tailC,
        overlay (o ++ rowsW t θ c ps) B, List.replicate cap false]) := by
  have hr := rows_run t θ c ps hps tailC tailS o B cap c0 hcap0 hc1 hc2
  have h := dockRun hr (rbSlots u) (rbSlots_inj u) (popH u p ![0, 0, 0, 0, 0, 0, o.length, 0])
    (popA u R L src (stW ps ++ tailS) ![frame (binary t 0), frame (List.replicate t false),
        List.replicate θ true ++ [false], [c0], [true], coefWord c ++ tailC, overlay o B, List.replicate cap false])
    (by intro j; fin_cases j <;> simp [rbSlots, popH_eI, popH_st, rbH])
    (by intro j; fin_cases j <;> simp [rbSlots, popA_eI, popA_st, rbAt, RB.tapes, cAt, rowsAt])
  refine h.congr ?_ ?_
  · apply dockH_eq_of _ (rbSlots_inj u)
    · intro j; fin_cases j <;> simp [rbSlots, popH_eI, popH_st, rbH]
    · intro i hi
      rcases pcover u i with ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [popH_sI, popH_sI]
      · exfalso
        fin_cases k
        · exact hi 0 rfl
        · exact hi 1 rfl
        · exact hi 2 rfl
        · exact hi 3 rfl
        · exact hi 4 rfl
        · exact hi 5 rfl
        · exact hi 7 rfl
        · exact hi 8 rfl
  · apply install_eq_of _ (rbSlots_inj u)
    · intro j; fin_cases j <;> simp [rbSlots, popA_eI, popA_st, rbAt, RB.tapes, rowsW]
    · intro i hi
      rcases pcover u i with ⟨a, rfl⟩ | ⟨k, rfl⟩
      · rw [popA_sI, popA_sI]
      · exfalso
        fin_cases k
        · exact hi 0 rfl
        · exact hi 1 rfl
        · exact hi 2 rfl
        · exact hi 3 rfl
        · exact hi 4 rfl
        · exact hi 5 rfl
        · exact hi 7 rfl
        · exact hi 8 rfl

/-! ## One visited state -/

/-- Consecutive pairs `(N_k, P_k)` of a list of prints. -/
def pairsOf : List (List (List ℕ)) → List (List (List ℕ) × List (List ℕ))
  | a :: b :: rest => (a, b) :: pairsOf rest
  | _ => []

theorem stW_pairsOf : ∀ (n : ℕ) (l : List (List (List ℕ))), l.length = 2 * n → stW (pairsOf l) = l.flatMap polyWord
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | n + 1, a :: b :: rest, h => by
    simp only [pairsOf, stW, List.flatMap_cons] at *
    have := stW_pairsOf n rest (by simp at h; omega)
    unfold stW at this
    rw [this]; simp [List.append_assoc]
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

theorem length_pairsOf : ∀ (n : ℕ) (l : List (List (List ℕ))), l.length = 2 * n → (pairsOf l).length = n
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | n + 1, a :: b :: rest, h => by
    simp only [pairsOf, List.length_cons]
    rw [length_pairsOf n rest (by simp at h; omega)]
  | n + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega

/-- A visited state's record: marker, coefficient field, factor blocks. -/
def stateRec {F : EvalFam} (c : ℤ) (fs : List (FSpec F)) : List Bool := true :: (frame (coefWord c) ++ storeRec fs)

/-- The state body. -/
noncomputable def stateBody (F : EvalFam) := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (skipM F.t) (loadCWM F.t)) (setFOM F.t)) (mStoreM F)) (skipM F.t))
  (rowsPM F.t)

/-- The pairs of a state's prints. -/
def statePairs {F : EvalFam} (fs : List (FSpec F)) : List (List (List ℕ) × List (List ℕ)) := pairsOf (fs.map FSpec.poly)

/-- The cost of a state. -/
noncomputable def stateCost {F : EvalFam} (t θ : ℕ) (c : ℤ) (fs : List (FSpec F)) (R : ℕ) : ℕ :=
  ((((1 + 1 + (2 * (2 * (coefWord c).length + 1) + 2)) + 1 + 1) + 1 + (2 * storeCost fs R + 2)) + 1 + 1) + 1 +
    rowsCost t θ c (statePairs fs)

/-- The value of the majority cell after a state's rows. -/
def cEnd (t θ : ℕ) : Bool := decide (θ ≤ Interp.pop (binary t (2 ^ t - 1)))

theorem cAt_end (t θ : ℕ) (c0 : Bool) : cAt t θ c0 (2 ^ t) = cEnd t θ := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ t = k + 1 := ⟨2 ^ t - 1, by have := Nat.one_le_two_pow (n := t); omega⟩
  rw [hk]; simp [cAt, cEnd, hk]

theorem overlay_eq_append (w B : List Bool) : overlay w B = w ++ B.drop w.length := rfl

theorem storeW_eq {F : EvalFam} (fs : List (FSpec F)) (n : ℕ) (hfs : fs.length = 2 * n) :
    storeW fs = stW (statePairs fs) := by
  unfold statePairs storeW
  rw [stW_pairsOf n _ (by simp [hfs])]
  simp [List.flatMap_map]

/-- **One visited state**: the output receives its truth-table rows, from the prints of its visit factors stored
once; the record cursor passes the state's record. -/
theorem state_step (F : EvalFam) (n θ : ℕ) (c : ℤ) (fs : List (FSpec F)) (hfs : fs.length = 2 * n)
    (pre rest stOld cwOld o B : List Bool) (R L cap : ℕ) (c0 f0 : Bool)
    (hR : ∀ x ∈ fs, x.cost + 1 ≤ R) (hL : R + 1 ≤ L) (hcapS : storeCost fs R ≤ cap)
    (hcw : 2 * (coefWord c).length + 1 ≤ cap) (hcap0 : 2 * n + 1 ≤ cap)
    (hc2 : ((List.range n).map fun j => selPass (statePairs fs) j + 2).sum + 1 ≤ cap) :
    Step (stateBody F) (stateCost n θ c fs R) (popH F.t pre.length ![0, 0, 0, 0, 0, 0, o.length, 0])
      (popA F.t R L (pre ++ stateRec c fs ++ rest) stOld ![frame (binary n 0), frame (List.replicate n false),
        List.replicate θ true ++ [false], [c0], [f0], cwOld, overlay o B, List.replicate cap false])
      (popH F.t (pre.length + (stateRec c fs).length)
        ![0, 0, 0, 0, 0, 0, (o ++ rowsW n θ c (statePairs fs)).length, 0])
      (popA F.t R L (pre ++ stateRec c fs ++ rest) (overlay (storeW fs) stOld) ![frame (binary n 0),
        frame (List.replicate n false), List.replicate θ true ++ [false], [cEnd n θ], [false],
        overlay (coefWord c) cwOld, overlay (o ++ rowsW n θ c (statePairs fs)) B, List.replicate cap false]) := by
  set src := pre ++ stateRec c fs ++ rest with hsrc
  have e1 : src = (pre ++ [true]) ++ frame (coefWord c) ++ (storeRec fs ++ rest) := by
    rw [hsrc, stateRec]; simp [List.append_assoc]
  have e2 : src = (pre ++ [true] ++ frame (coefWord c)) ++ storeRec fs ++ rest := by
    rw [hsrc, stateRec]; simp [List.append_assoc]
  have s1 := skipM_step F.t R L pre.length src stOld ![frame (binary n 0), frame (List.replicate n false),
    List.replicate θ true ++ [false], [c0], [f0], cwOld, overlay o B, List.replicate cap false]
    ![0, 0, 0, 0, 0, 0, o.length, 0]
  have s2 := loadCW_step F.t R L (pre.length + 1) cap (pre ++ [true]) (coefWord c) (storeRec fs ++ rest) stOld
    (frame (binary n 0)) (frame (List.replicate n false)) (List.replicate θ true ++ [false]) [c0] [f0] cwOld
    (overlay o B) o.length (by simp) (by rw [coefWord] at hcw ⊢; simpa using hcw)
  rw [← e1] at s2
  have s3 := setFO_step F.t R L (pre.length + 1 + (2 * (coefWord c).length + 1)) src stOld (frame (binary n 0))
    (frame (List.replicate n false)) (List.replicate θ true ++ [false]) [c0] (overlay (coefWord c) cwOld) (overlay o B)
    (List.replicate cap false) f0 o.length
  have s4 := mStore_step F fs (pre ++ [true] ++ frame (coefWord c)) rest stOld R L cap hR hL hcapS
    (frame (binary n 0)) (frame (List.replicate n false)) (List.replicate θ true ++ [false]) [c0] [true]
    (overlay (coefWord c) cwOld) (overlay o B) o.length
  rw [← e2] at s4
  have e3 : (pre ++ [true] ++ frame (coefWord c)).length = pre.length + 1 + (2 * (coefWord c).length + 1) := by
    simp [frame_length]; omega
  rw [e3] at s4
  have s5 := skipM_step F.t R L (pre.length + 1 + (2 * (coefWord c).length + 1) +
    (fs.flatMap fun x => true :: x.block).length) src (overlay (storeW fs) stOld)
    ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false], [c0], [true],
      overlay (coefWord c) cwOld, overlay o B, List.replicate cap false] ![0, 0, 0, 0, 0, 0, o.length, 0]
  have hps : (statePairs fs).length = n := by
    unfold statePairs; rw [length_pairsOf n _ (by simp [hfs])]
  have s6 := rowsP_step F.t n θ c (statePairs fs) hps (cwOld.drop (coefWord c).length)
    (stOld.drop (storeW fs).length) o B cap c0 hcap0 (by rw [coefWord] at hcw; simp [frame_length] at hcw ⊢; omega) hc2 R L
    (pre.length + 1 + (2 * (coefWord c).length + 1) + (fs.flatMap fun x => true :: x.block).length + 1) src
  have eST : stW (statePairs fs) ++ stOld.drop (storeW fs).length = overlay (storeW fs) stOld := by
    rw [overlay_eq_append, storeW_eq fs n hfs]
  have eCW : coefWord c ++ cwOld.drop (coefWord c).length = overlay (coefWord c) cwOld := rfl
  rw [eST, eCW] at s6
  have eX : binary n (2 ^ n) = binary n 0 := by rw [Interp.binary_pow, Interp.binary_zero]
  rw [eX, cAt_end] at s6
  have t := ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6
  have eP : pre.length + 1 + (2 * (coefWord c).length + 1) + (fs.flatMap fun x => true :: x.block).length + 1 =
      pre.length + (stateRec c fs).length := by
    simp [stateRec, storeRec, frame_length]; omega
  rw [eP] at t
  exact t

/-! ## The loop over the visited states -/

/-- A visited state: its coefficient and its visit factors `[N_0, P_0, …]`. -/
abbrev SSpec (F : EvalFam) := ℤ × List (FSpec F)

def srec {F : EvalFam} (st : SSpec F) : List Bool := stateRec st.1 st.2

/-- The stale store and coefficient word after the first `j` states. -/
def stAt {F : EvalFam} (st0 : List Bool) (sts : List (SSpec F)) (j : ℕ) : List Bool :=
  (sts.take j).foldl (fun acc s => overlay (storeW s.2) acc) st0
def cwAt {F : EvalFam} (cw0 : List Bool) (sts : List (SSpec F)) (j : ℕ) : List Bool :=
  (sts.take j).foldl (fun acc s => overlay (coefWord s.1) acc) cw0

theorem foldl_take_succ {α β : Type} (f : β → α → β) (b : β) (l : List α) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).foldl f b = f ((l.take j).foldl f b) l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The output of the first `j` states. -/
def outAt {F : EvalFam} (n θ : ℕ) (sts : List (SSpec F)) (j : ℕ) : List Bool :=
  (sts.take j).flatMap fun st => rowsW n θ st.1 (statePairs st.2)

noncomputable def statesM (F : EvalFam) := StreamController.machine (stateBody F) (srcP F.t)

noncomputable def statePass {F : EvalFam} (n θ : ℕ) (sts : List (SSpec F)) (R j : ℕ) : ℕ :=
  (sts[j]?.map fun st => stateCost n θ st.1 st.2 R).getD 0

noncomputable def statesCost {F : EvalFam} (n θ : ℕ) (sts : List (SSpec F)) (R : ℕ) : ℕ :=
  ((List.range sts.length).map fun j => statePass n θ sts R j + 2).sum + 1

/-- The side conditions of one state at the capacities `R`, `cap`. -/
def StateOk {F : EvalFam} (n : ℕ) (R cap : ℕ) (st : SSpec F) : Prop :=
  st.2.length = 2 * n ∧ (∀ x ∈ st.2, x.cost + 1 ≤ R) ∧ storeCost st.2 R ≤ cap ∧
    2 * (coefWord st.1).length + 1 ≤ cap ∧ 2 * n + 1 ≤ cap ∧
    ((List.range n).map fun j => selPass (statePairs st.2) j + 2).sum + 1 ≤ cap

theorem states_run (F : EvalFam) (n θ : ℕ) (sts : List (SSpec F)) (pre rest st0 cw0 o B : List Bool) (R L cap : ℕ)
    (c0 f0 : Bool) (hL : R + 1 ≤ L) (hok : ∀ st ∈ sts, StateOk n R cap st) :
    Step (statesM F) (statesCost n θ sts R) (popH F.t pre.length ![0, 0, 0, 0, 0, 0, o.length, 0])
      (popA F.t R L (pre ++ (sts.flatMap srec ++ [false]) ++ rest) st0 ![frame (binary n 0),
        frame (List.replicate n false), List.replicate θ true ++ [false], [c0], [f0], cw0, overlay o B,
        List.replicate cap false])
      (popH F.t (pre.length + (sts.flatMap srec).length) ![0, 0, 0, 0, 0, 0, (o ++ outAt n θ sts sts.length).length, 0])
      (popA F.t R L (pre ++ (sts.flatMap srec ++ [false]) ++ rest) (stAt st0 sts sts.length)
        ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false],
          [if sts.length = 0 then c0 else cEnd n θ], [if sts.length = 0 then f0 else false], cwAt cw0 sts sts.length,
          overlay (o ++ outAt n θ sts sts.length) B, List.replicate cap false]) := by
  set src := pre ++ (sts.flatMap srec ++ [false]) ++ rest with hsrc
  let pos : ℕ → ℕ := fun j => pre.length + ((sts.take j).flatMap srec).length
  let E : ℕ → Fin 8 → List Bool := fun j => ![frame (binary n 0), frame (List.replicate n false),
    List.replicate θ true ++ [false], [if j = 0 then c0 else cEnd n θ], [if j = 0 then f0 else false],
    cwAt cw0 sts j, overlay (o ++ outAt n θ sts j) B, List.replicate cap false]
  have hW := Block.WhileBody.run ({
    body := stateBody F
    tape := srcP F.t
    bound := sts.length
    H := fun j => popH F.t (pos j) ![0, 0, 0, 0, 0, 0, (o ++ outAt n θ sts j).length, 0]
    A := fun j => popA F.t R L src (stAt st0 sts j) (E j)
    cost := statePass n θ sts R
    step := by
      intro j hj
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hok sts[j] (List.getElem_mem hj)
      have hsp : src = (pre ++ (sts.take j).flatMap srec) ++ stateRec sts[j].1 sts[j].2 ++
          ((sts.drop (j + 1)).flatMap srec ++ [false] ++ rest) := by
        conv_lhs => rw [hsrc, ← List.take_append_drop j sts, List.drop_eq_getElem_cons hj]
        simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc, srec]
      have s := state_step F n θ sts[j].1 sts[j].2 h1 (pre ++ (sts.take j).flatMap srec)
        ((sts.drop (j + 1)).flatMap srec ++ [false] ++ rest) (stAt st0 sts j) (cwAt cw0 sts j)
        (o ++ outAt n θ sts j) B R L cap (if j = 0 then c0 else cEnd n θ) (if j = 0 then f0 else false) h2 hL h3 h4 h5 h6
      rw [← hsp] at s
      have ep : (pre ++ (sts.take j).flatMap srec).length = pos j := by simp [pos]
      have ep' : (pre ++ (sts.take j).flatMap srec).length + (stateRec sts[j].1 sts[j].2).length = pos (j + 1) := by
        simp only [pos, flatMap_take_succ' _ sts j hj, List.length_append, srec]; omega
      rw [ep', ep] at s
      have eo : o ++ outAt n θ sts j ++ rowsW n θ sts[j].1 (statePairs sts[j].2) = o ++ outAt n θ sts (j + 1) := by
        simp only [outAt, flatMap_take_succ' _ sts j hj, List.append_assoc]
      have est : overlay (storeW sts[j].2) (stAt st0 sts j) = stAt st0 sts (j + 1) := by
        simp only [stAt, foldl_take_succ _ _ sts j hj]
      have ecw : overlay (coefWord sts[j].1) (cwAt cw0 sts j) = cwAt cw0 sts (j + 1) := by
        simp only [cwAt, foldl_take_succ _ _ sts j hj]
      rw [eo, est, ecw] at s
      refine (s.congr rfl ?_).enlarge (le_of_eq ?_)
      · simp [E]
      · simp [statePass, List.getElem?_eq_getElem hj]
    cont := by
      intro j hj
      simp only [popA_src, popH_src]
      have e : src = (pre ++ (sts.take j).flatMap srec) ++ true ::
          (frame (coefWord sts[j].1) ++ storeRec sts[j].2 ++ ((sts.drop (j + 1)).flatMap srec ++ [false] ++ rest)) := by
        conv_lhs => rw [hsrc, ← List.take_append_drop j sts, List.drop_eq_getElem_cons hj]
        simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc, srec, stateRec, List.cons_append]
      rw [e]
      have := Streaming.read_append (pre ++ (sts.take j).flatMap srec)
        (frame (coefWord sts[j].1) ++ storeRec sts[j].2 ++ ((sts.drop (j + 1)).flatMap srec ++ [false] ++ rest)) true
      rwa [List.length_append] at this
    halt := by
      simp only [popA_src, popH_src, pos, List.take_length]
      have e : src = (pre ++ sts.flatMap srec) ++ false :: rest := by rw [hsrc]; simp [List.append_assoc]
      rw [e]
      have := Streaming.read_append (pre ++ sts.flatMap srec) rest false
      rwa [List.length_append] at this } : Block.WhileBody _ _)
  have hW' : Step (statesM F) (((List.range (sts.length - 0)).map fun i => statePass n θ sts R (0 + i) + 2).sum + 1)
      (popH F.t (pos 0) ![0, 0, 0, 0, 0, 0, (o ++ outAt n θ sts 0).length, 0])
      (popA F.t R L src (stAt st0 sts 0) (E 0))
      (popH F.t (pos sts.length) ![0, 0, 0, 0, 0, 0, (o ++ outAt n θ sts sts.length).length, 0])
      (popA F.t R L src (stAt st0 sts sts.length) (E sts.length)) := hW
  have e0 : E 0 = ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false], [c0], [f0],
      cw0, overlay o B, List.replicate cap false] := by
    simp [E, cwAt, outAt]
  have eL : E sts.length = ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false],
      [if sts.length = 0 then c0 else cEnd n θ], [if sts.length = 0 then f0 else false], cwAt cw0 sts sts.length,
      overlay (o ++ outAt n θ sts sts.length) B, List.replicate cap false] := rfl
  rw [e0, eL] at hW'
  simp only [Nat.sub_zero, Nat.zero_add, pos, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero,
    List.take_length, stAt, outAt, List.append_nil] at hW'
  simpa [stAt, outAt, statesCost] using hW'

/-! ## The population printer -/

/-- A population's record: the constant term's field, the visited states, the end marker. -/
def popRec {F : EvalFam} (oneW : List Bool) (sts : List (SSpec F)) : List Bool := frame oneW ++ (sts.flatMap srec ++ [false])

/-- What the population printer writes. -/
def popOut {F : EvalFam} (oneW : List Bool) (n θ : ℕ) (sts : List (SSpec F)) : List Bool :=
  oneW ++ outAt n θ sts sts.length ++ [false]

/-- **The population printer**: ONE machine per evaluator family. -/
noncomputable def popM (F : EvalFam) :=
  Composition.machine (Composition.machine (Composition.machine (oneTM F.t) (statesM F)) (skipM F.t)) (putEM F.t false)

noncomputable def popCost {F : EvalFam} (oneW : List Bool) (n θ : ℕ) (sts : List (SSpec F)) (R : ℕ) : ℕ :=
  (((2 * oneW.length + 1) + 1 + statesCost n θ sts R) + 1 + 1) + 1 + 1

/-- **One population**: the output receives `popOut`; the record cursor passes the population's record. -/
theorem pop_run (F : EvalFam) (n θ : ℕ) (oneW : List Bool) (sts : List (SSpec F)) (pre rest st0 cw0 o B : List Bool)
    (R L cap : ℕ) (c0 f0 : Bool) (hL : R + 1 ≤ L) (hok : ∀ st ∈ sts, StateOk n R cap st) :
    Step (popM F) (popCost oneW n θ sts R) (popH F.t pre.length ![0, 0, 0, 0, 0, 0, o.length, 0])
      (popA F.t R L (pre ++ popRec oneW sts ++ rest) st0 ![frame (binary n 0), frame (List.replicate n false),
        List.replicate θ true ++ [false], [c0], [f0], cw0, overlay o B, List.replicate cap false])
      (popH F.t (pre.length + (popRec oneW sts).length) ![0, 0, 0, 0, 0, 0, (o ++ popOut oneW n θ sts).length, 0])
      (popA F.t R L (pre ++ popRec oneW sts ++ rest) (stAt st0 sts sts.length)
        ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false],
          [if sts.length = 0 then c0 else cEnd n θ], [if sts.length = 0 then f0 else false], cwAt cw0 sts sts.length,
          overlay (o ++ popOut oneW n θ sts) B, List.replicate cap false]) := by
  set src := pre ++ popRec oneW sts ++ rest with hsrc
  have e1 : src = pre ++ frame oneW ++ (sts.flatMap srec ++ [false] ++ rest) := by
    rw [hsrc, popRec]; simp [List.append_assoc]
  have e2 : src = (pre ++ frame oneW) ++ (sts.flatMap srec ++ [false]) ++ rest := by
    rw [hsrc, popRec]; simp [List.append_assoc]
  have s1 := oneT_step F.t R L pre.length pre oneW (sts.flatMap srec ++ [false] ++ rest) st0 (frame (binary n 0))
    (frame (List.replicate n false)) (List.replicate θ true ++ [false]) [c0] [f0] cw0 o B (List.replicate cap false) rfl
  rw [← e1] at s1
  have s2 := states_run F n θ sts (pre ++ frame oneW) rest st0 cw0 (o ++ oneW) B R L cap c0 f0 hL hok
  rw [← e2] at s2
  have el : (pre ++ frame oneW).length = pre.length + (2 * oneW.length + 1) := by simp [frame_length]
  rw [el] at s2
  have s3 := skipM_step F.t R L (pre.length + (2 * oneW.length + 1) + (sts.flatMap srec).length) src
    (stAt st0 sts sts.length) ![frame (binary n 0), frame (List.replicate n false), List.replicate θ true ++ [false],
      [if sts.length = 0 then c0 else cEnd n θ], [if sts.length = 0 then f0 else false], cwAt cw0 sts sts.length,
      overlay (o ++ oneW ++ outAt n θ sts sts.length) B, List.replicate cap false]
    ![0, 0, 0, 0, 0, 0, (o ++ oneW ++ outAt n θ sts sts.length).length, 0]
  have s4 := putE_step F.t R L (pre.length + (2 * oneW.length + 1) + (sts.flatMap srec).length + 1) src
    (stAt st0 sts sts.length) (frame (binary n 0)) (frame (List.replicate n false)) (List.replicate θ true ++ [false])
    [if sts.length = 0 then c0 else cEnd n θ] [if sts.length = 0 then f0 else false] (cwAt cw0 sts sts.length)
    (o ++ oneW ++ outAt n θ sts sts.length) B (List.replicate cap false) false
  have t := ((s1.seq s2).seq s3).seq s4
  have eo : o ++ oneW ++ outAt n θ sts sts.length ++ [false] = o ++ popOut oneW n θ sts := by
    simp [popOut, List.append_assoc]
  have ep : pre.length + (2 * oneW.length + 1) + (sts.flatMap srec).length + 1 = pre.length + (popRec oneW sts).length := by
    simp [popRec, frame_length]; omega
  rw [eo, ep] at t
  exact t

end NearCubicWires.WireExponent3_5.ListMachine.Row
