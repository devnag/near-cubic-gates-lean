import Proof.Wire_3_5.PrimAsmDataSetup
import Proof.Wire_3_5.PrimAsmDockW
import Proof.Wire_3_5.PrimTTabSym
import Proof.Wire_3_5.PrimTCarTable
import Proof.Wire_3_5.BlockJoin
import Proof.Wire_3_5.ListMachinePrintBank

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

noncomputable def symT (i : Fin 4) :=
  Block.branchM (sTape (nr := DR) (sSym i 0))
    (RecoveryFocus.machine (fun j => sTape (nr := DR) (sSym i j)) PrimT.SymTab.symTableM) (Block.idle (DS + 2 + DR))

/-- **A carrier slot's stage**. -/
noncomputable def carT (k : Fin 2) :=
  Block.branchM (sTape (nr := DR) (sCar k 0))
    (RecoveryFocus.machine (fun j => sTape (nr := DR) (sCar k j)) PrimT.CarTable.carTableM) (Block.idle (DS + 2 + DR))

theorem frame_natWord_head (x : ℕ) : readTapeBit (RepairOrdinary.frame (RepairRepresentation.natWord x)) 0 = true := by
  have hne : RepairRepresentation.natWord x ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [ParseNat.natWord_length] at this
    simp at this
  obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
  rw [hb]
  rfl

section Stage
variable (cap : ℕ)

/-- **A filled SYM slot**: T's machine docked on the slot; the table on `3`, the count on `5`. -/
theorem symT_on {n : ℕ} (i : Fin 4) (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L)
    (h2 : 2 ≤ n + L) (σ : WState DS DR) (hd : Done σ (symTrip i) (encodeNormalizedSymmetricThresholdCircuit C) n L)
    (hb : ∀ j : Fin 1789, 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0) :
    ∃ tout : Fin 1789 → List Bool, Step (symT i) (PrimT.SymTab.symTableCost C L + 2) (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updS (sSym i) σ (fun _ => 0) tout)).H (wenc cap (updS (sSym i) σ (fun _ => 0) tout)).A ∧
      tout 0 = RepairOrdinary.frame (RepairRepresentation.natWord (encodeNormalizedSymmetricThresholdCircuit C)) ∧
      tout 3 = FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates C)) (Stars.symGates C) ∧
      tout 5 = List.replicate (Stars.symGates C).length true := by
  obtain ⟨tout, hs, t0, _, _, t3, _, t5⟩ := PrimT.SymTab.symTable_step C L hL h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  simp only [symTrip] at d1 d2 d3 d4 d5 d6
  have hin : (fun j => σ.st (sSym i j)) = PrimT.SymTab.symIn (encodeNormalizedSymmetricThresholdCircuit C) n L := by
    funext j
    unfold PrimT.SymTab.symIn
    by_cases j0 : j.val = 0
    · rw [if_pos j0, show j = 0 from Fin.ext j0, d1]
    · by_cases j1 : j.val = 1
      · rw [if_neg j0, if_pos j1, show j = 1 from Fin.ext j1, d3]
      · by_cases j2 : j.val = 2
        · rw [if_neg j0, if_neg j1, if_pos j2, show j = 2 from Fin.ext j2, d5]
        · rw [if_neg j0, if_neg j1, if_neg j2]
          exact (hb j (by omega)).1
  have hh : (fun j => σ.sh (sSym i j)) = fun _ => 0 := by
    funext j
    by_cases j0 : j.val = 0
    · rw [show j = 0 from Fin.ext j0, d2]
    · by_cases j1 : j.val = 1
      · rw [show j = 1 from Fin.ext j1, d4]
      · by_cases j2 : j.val = 2
        · rw [show j = 2 from Fin.ext j2, d6]
        · exact (hb j (by omega)).2
  have hs' : Step PrimT.SymTab.symTableM (PrimT.SymTab.symTableCost C L) (fun j => σ.sh (sSym i j))
      (fun j => σ.st (sSym i j)) (fun _ => 0) tout := by
    rw [hh, hin]
    exact hs
  have d := dockS cap (sSym i) (sSym_inj i) σ hs'
  refine ⟨tout, Block.branch_true _ _ d ?_, t0, t3, t5⟩
  rw [wenc_A_s, wenc_H_s, d1, d2]
  exact frame_natWord_head _

/-- **An empty SYM slot**: nothing happens. -/
theorem symT_off (i : Fin 4) (σ : WState DS DR) (hb : Blank σ (symTrip i)) :
    Step (symT i) 2 (wenc cap σ).H (wenc cap σ).A (wenc cap σ).H (wenc cap σ).A := by
  obtain ⟨b1, b2, _, _, _, _⟩ := hb
  simp only [symTrip] at b1 b2
  refine Block.branch_false _ _ (ListMachine.Print.idle_step _ _) ?_
  rw [wenc_A_s, wenc_H_s, b1]
  rfl

/-- **A filled carrier slot**. -/
theorem carT_on {n : ℕ} (k : Fin 2) (X : Stars.Carrier n) (L : ℕ) (hL : ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L) (σ : WState DS DR) (hd : Done σ (carTrip k) X.code n L)
    (hb : ∀ j : Fin 1357, 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0) :
    ∃ tout : Fin 1357 → List Bool, Step (carT k) (PrimT.CarTable.carTableCost X L + 2) (wenc cap σ).H
      (wenc cap σ).A (wenc cap (updS (sCar k) σ (fun _ => 0) tout)).H
      (wenc cap (updS (sCar k) σ (fun _ => 0) tout)).A ∧
      tout 0 = RepairOrdinary.frame (RepairRepresentation.natWord X.code) ∧
      tout 3 = FinalPass.Corner.gatesW (PrimT.tabH X) (FinalPass.Corner.maskGates X) ∧
      tout 5 = List.replicate X.length true := by
  obtain ⟨tout, hs, t0, _, _, t3, _, t5⟩ := PrimT.CarTable.carTable_step X L hL h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  simp only [carTrip] at d1 d2 d3 d4 d5 d6
  have hin : (fun j => σ.st (sCar k j)) = PrimT.CarTable.carIn X.code n L := by
    funext j
    unfold PrimT.CarTable.carIn
    by_cases j0 : j.val = 0
    · rw [if_pos j0, show j = 0 from Fin.ext j0, d1]
    · by_cases j1 : j.val = 1
      · rw [if_neg j0, if_pos j1, show j = 1 from Fin.ext j1, d3]
      · by_cases j2 : j.val = 2
        · rw [if_neg j0, if_neg j1, if_pos j2, show j = 2 from Fin.ext j2, d5]
        · rw [if_neg j0, if_neg j1, if_neg j2]
          exact (hb j (by omega)).1
  have hh : (fun j => σ.sh (sCar k j)) = fun _ => 0 := by
    funext j
    by_cases j0 : j.val = 0
    · rw [show j = 0 from Fin.ext j0, d2]
    · by_cases j1 : j.val = 1
      · rw [show j = 1 from Fin.ext j1, d4]
      · by_cases j2 : j.val = 2
        · rw [show j = 2 from Fin.ext j2, d6]
        · exact (hb j (by omega)).2
  have hs' : Step PrimT.CarTable.carTableM (PrimT.CarTable.carTableCost X L) (fun j => σ.sh (sCar k j))
      (fun j => σ.st (sCar k j)) (fun _ => 0) tout := by
    rw [hh, hin]
    exact hs
  have d := dockS cap (sCar k) (sCar_inj k) σ hs'
  refine ⟨tout, Block.branch_true _ _ d ?_, t0, t3, t5⟩
  rw [wenc_A_s, wenc_H_s, d1, d2]
  exact frame_natWord_head _

/-- **An empty carrier slot**. -/
theorem carT_off (k : Fin 2) (σ : WState DS DR) (hb : Blank σ (carTrip k)) :
    Step (carT k) 2 (wenc cap σ).H (wenc cap σ).A (wenc cap σ).H (wenc cap σ).A := by
  obtain ⟨b1, b2, _, _, _, _⟩ := hb
  simp only [carTrip] at b1 b2
  refine Block.branch_false _ _ (ListMachine.Print.idle_step _ _) ?_
  rw [wenc_A_s, wenc_H_s, b1]
  rfl

theorem updS_st_slot {t : ℕ} (tmap : Fin t → Fin (DS + 1)) (hinj : Function.Injective tmap) (σ : WState DS DR)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) (j : Fin t) : (updS tmap σ hout tout).st (tmap j) = tout j := by
  simp [updS, install_slot _ hinj]

theorem updS_sh_slot {t : ℕ} (tmap : Fin t → Fin (DS + 1)) (hinj : Function.Injective tmap) (σ : WState DS DR)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) (j : Fin t) : (updS tmap σ hout tout).sh (tmap j) = hout j := by
  simp [updS, dockH_slot _ hinj]

theorem updS_st_other {t : ℕ} (tmap : Fin t → Fin (DS + 1)) (σ : WState DS DR) (hout : Fin t → ℕ)
    (tout : Fin t → List Bool) (s : Fin (DS + 1)) (hs : ∀ j, tmap j ≠ s) : (updS tmap σ hout tout).st s = σ.st s := by
  simp [updS, install_other _ _ _ _ hs]

theorem updS_sh_other {t : ℕ} (tmap : Fin t → Fin (DS + 1)) (σ : WState DS DR) (hout : Fin t → ℕ)
    (tout : Fin t → List Bool) (s : Fin (DS + 1)) (hs : ∀ j, tmap j ≠ s) : (updS tmap σ hout tout).sh s = σ.sh s := by
  simp [updS, dockH_other _ _ _ _ hs]

end Stage

/-! ## Collecting the counts -/

/-- The counts as one word: each count in unary, closed by `0`. -/
def unaryList (cs : List ℕ) : List Bool := cs.flatMap fun c => List.replicate c true ++ [false]

def dataWord (cs : List ℕ) : List Bool := false :: RepairOrdinary.frame (unaryList cs)

/-- Emit the unary count on `S` as marked pairs. -/
def emitUW (S : Fin (DS + 1)) : WM DS DR := .whs S (.seq (emitPair sOUT rOP true) (.fwd S))

/-- One slot's count, if the slot is filled (its code stream's first cell). -/
def slotC (t : Fin (DS + 1) × Fin (DS + 1)) : WM DS DR := .ifs t.1 (.seq (emitUW t.2) (emitPair sOUT rOP false)) .skip

/-- The slots' counts in order. -/
def slotsC : List (Fin (DS + 1) × Fin (DS + 1)) → WM DS DR
  | [] => .skip
  | t :: l => .seq (slotC t) (slotsC l)

/-- The collection's cost. -/
def slotsCost : List (Fin (DS + 1) × Fin (DS + 1)) → List ℕ → ℕ
  | [], _ => 0
  | _ :: l, [] => 1 + 1 + slotsCost l []
  | _ :: l, c :: cs => c * 19 + 1 + 1 + 15 + 1 + 1 + slotsCost l cs

section Collect
variable (cap : ℕ)

theorem aseth (S : Fin (DS + 1)) (hS : S ≠ sOUT) (x : WState DS DR) (k : ℕ) (u : List Bool) :
    appendO (x.seth S k) sOUT rOP u = (appendO x sOUT rOP u).seth S k := by
  apply WState.eq
  · funext j
    by_cases hjS : j = S
    · subst hjS; simp [Function.update_apply, hS]
    · by_cases hjO : j = sOUT
      · subst hjO; simp [Function.update_apply, Ne.symm hS]
      · simp [Function.update_apply, hjS, hjO]
  · funext j; simp
  · funext r; simp
  · simp

theorem marks_rep_succ (k : ℕ) : marks (List.replicate (k + 1) true) = marks (List.replicate k true) ++ [true, true] := by
  rw [List.replicate_succ', marks_append]
  rfl

theorem emitUW_spec (S : Fin (DS + 1)) (hS : S ≠ sOUT) (c : ℕ) (σ : WState DS DR) (hst : σ.st S = List.replicate c true)
    (hsh : σ.sh S = 0) (ho : σ.sh sOUT = (σ.st sOUT).length) (hc : σ.val rOP + 2 * c ≤ cap) :
    WExec cap (emitUW S) σ ((appendO σ sOUT rOP (marks (List.replicate c true))).seth S c) (c * 19 + 1) := by
  set T : ℕ → WState DS DR := fun k => (appendO σ sOUT rOP (marks (List.replicate k true))).seth S k with hT
  have tst : ∀ k, (T k).st S = List.replicate c true := fun k => by
    simp only [hT, WState.seth_st, appendO_st, Function.update_apply, if_neg hS, hst]
  have tsh : ∀ k, (T k).sh S = k := fun k => by
    simp [hT]
  have l := whsLoop cap S (.seq (emitPair sOUT rOP true) (.fwd S)) 17 c T
    (fun k hk => by simp only [wbit, tst, tsh, rep_read]; simp [hk])
    (by simp only [wbit, tst, tsh, rep_read]; simp)
    (fun k hk => by
      have hml := RepairOrdinary.Streaming.marks_length (List.replicate k true)
      have h1 := emitPair_spec cap sOUT rOP true (T k)
        (by simp [hT, Function.update_apply, Ne.symm hS, ho])
        (by simp [hT] at hml ⊢; omega)
      have h2 := WExec.fwd (cap := cap) S (appendO (T k) sOUT rOP [true, true])
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      have e1 : appendO (T k) sOUT rOP [true, true] =
          (appendO σ sOUT rOP (marks (List.replicate (k + 1) true))).seth S k := by
        rw [hT]
        dsimp only
        rw [aseth S hS, appendO_append, marks_rep_succ]
      rw [e1]
      simp [FinalPass.Tm.wseth_seth, hT])
  have e0 : T 0 = σ := by
    simp only [hT, List.replicate_zero]
    rw [show marks ([] : List Bool) = [] from rfl, appendO_nil, ← hsh, FinalPass.Tm.wseth_same]
  rw [e0] at l
  exact WExec.mono l (by nlinarith)

theorem unaryList_cons (c : ℕ) (cs : List ℕ) :
    unaryList (c :: cs) = List.replicate c true ++ [false] ++ unaryList cs := by
  simp [unaryList]

theorem marks_unary_cons (c : ℕ) (cs : List ℕ) :
    marks (unaryList (c :: cs)) = marks (List.replicate c true) ++ [true, false] ++ marks (unaryList cs) := by
  rw [unaryList_cons, marks_append, marks_append]
  rfl

/-- **The counts of a run of slots**: the filled slots (a prefix) append their counts to the output, in order. -/
theorem slotsC_spec : ∀ (l : List (Fin (DS + 1) × Fin (DS + 1))) (cs : List ℕ) (σ : WState DS DR),
    cs.length ≤ l.length →
    (∀ i (h : i < cs.length) (hl : i < l.length), readTapeBit (σ.st (l.get ⟨i, hl⟩).1) (σ.sh (l.get ⟨i, hl⟩).1) = true ∧
      σ.st (l.get ⟨i, hl⟩).2 = List.replicate (cs.get ⟨i, h⟩) true ∧ σ.sh (l.get ⟨i, hl⟩).2 = 0) →
    (∀ i (hl : i < l.length), cs.length ≤ i → readTapeBit (σ.st (l.get ⟨i, hl⟩).1) (σ.sh (l.get ⟨i, hl⟩).1) = false) →
    (∀ t ∈ l, t.1 ≠ sOUT ∧ t.2 ≠ sOUT) → l.Pairwise (fun t t' => t.2 ≠ t'.1 ∧ t.2 ≠ t'.2) →
    σ.sh sOUT = (σ.st sOUT).length → σ.val rOP + 2 * (unaryList cs).length ≤ cap →
    ∃ τ : WState DS DR, WExec cap (slotsC l) σ τ (slotsCost l cs) ∧
      τ.st sOUT = σ.st sOUT ++ marks (unaryList cs) ∧ τ.sh sOUT = (τ.st sOUT).length ∧
      τ.val rOP = σ.val rOP + 2 * (unaryList cs).length ∧
      (∀ s, s ≠ sOUT → τ.st s = σ.st s) ∧ (∀ s, s ≠ sOUT → (∀ t ∈ l, s ≠ t.2) → τ.sh s = σ.sh s) ∧
      (∀ r, r ≠ rOP → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro cs σ hlen _ _ _ _ ho _
    have hc0 : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hc0
    exact ⟨σ, WExec.skip σ, by simp [unaryList, marks], ho, by simp [unaryList], fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  | cons t l ih =>
    intro cs σ hlen hon hoff hno hpw ho hcap
    have hpw' := List.pairwise_cons.mp hpw
    have hnoT := hno t (by simp)
    cases cs with
    | nil =>
      have hb := hoff 0 (by simp) (by simp)
      simp only [List.get_eq_getElem, List.getElem_cons_zero] at hb
      have e1 : WExec cap (slotC t) σ σ 1 := WExec.mono (WExec.ifsF (P := .seq (emitUW t.2) (emitPair sOUT rOP false))
        (by simpa [wbit] using hb) (WExec.skip σ)) (by omega)
      obtain ⟨τ, hτ, a1, a2, a3, a4, a7, a5, a6⟩ := ih [] σ (by simp)
        (fun i h => by simp at h)
        (fun i hl _ => by
          have := hoff (i + 1) (by simpa using hl) (by simp)
          simpa using this)
        (fun t' ht' => hno t' (by simp [ht'])) hpw'.2 ho (by simpa [unaryList] using hcap)
      exact ⟨τ, WExec.cast cap (WExec.seq e1 hτ) rfl (by simp [slotsCost]), a1, a2, a3, a4,
        fun s hs hs' => a7 s hs (fun t' ht' => hs' t' (by simp [ht'])), a5, a6⟩
    | cons c cs =>
      obtain ⟨b1, b2, b3⟩ := hon 0 (by simp) (by simp)
      simp only [List.get_eq_getElem, List.getElem_cons_zero] at b1 b2 b3
      have hml := RepairOrdinary.Streaming.marks_length (List.replicate c true)
      have hlen1 : (unaryList (c :: cs)).length = c + 1 + (unaryList cs).length := by
        rw [unaryList_cons]; simp; omega
      have e1 := emitUW_spec cap t.2 hnoT.2 c σ b2 b3 ho (by omega)
      set σ1 := (appendO σ sOUT rOP (marks (List.replicate c true))).seth t.2 c with hσ1
      have e2 := emitPair_spec cap sOUT rOP false σ1
        (by simp [hσ1, Function.update_apply, Ne.symm hnoT.2, ho])
        (by simp [hσ1] at hml ⊢; omega)
      set σ2 := appendO σ1 sOUT rOP [true, false] with hσ2
      have ex : WExec cap (slotC t) σ σ2 (c * 19 + 1 + 1 + 15 + 1) :=
        WExec.ifsT (Q := .skip) (by simpa [wbit] using b1) (WExec.seq e1 e2)
      have st2 : ∀ s, s ≠ sOUT → σ2.st s = σ.st s := fun s hs => by
        simp [hσ2, hσ1, Function.update_apply, hs]
      have sh2 : ∀ s, s ≠ sOUT → s ≠ t.2 → σ2.sh s = σ.sh s := fun s hs hs' => by
        simp [hσ2, hσ1, Function.update_apply, hs, hs']
      have kept : ∀ i (hl : i < l.length), σ2.st (l.get ⟨i, hl⟩).1 = σ.st (l.get ⟨i, hl⟩).1 ∧
          σ2.sh (l.get ⟨i, hl⟩).1 = σ.sh (l.get ⟨i, hl⟩).1 ∧ σ2.st (l.get ⟨i, hl⟩).2 = σ.st (l.get ⟨i, hl⟩).2 ∧
          σ2.sh (l.get ⟨i, hl⟩).2 = σ.sh (l.get ⟨i, hl⟩).2 := by
        intro i hl
        have hm := List.get_mem l ⟨i, hl⟩
        have hd := hpw'.1 _ hm
        have hn := hno _ (List.mem_cons_of_mem t hm)
        exact ⟨st2 _ hn.1, sh2 _ hn.1 (Ne.symm hd.1), st2 _ hn.2, sh2 _ hn.2 (Ne.symm hd.2)⟩
      obtain ⟨τ, hτ, a1, a2, a3, a4, a7, a5, a6⟩ := ih cs σ2 (by simpa using hlen)
        (fun i h hl => by
          obtain ⟨c1, c2, c3⟩ := hon (i + 1) (by simpa using h) (by simpa using hl)
          simp only [List.get_eq_getElem, List.getElem_cons_succ] at c1 c2 c3
          obtain ⟨k1, k2, k3, k4⟩ := kept i hl
          simp only [List.get_eq_getElem] at k1 k2 k3 k4 ⊢
          refine ⟨by rw [k1, k2]; exact c1, by rw [k3]; simpa using c2, by rw [k4]; exact c3⟩)
        (fun i hl hi => by
          have c1 := hoff (i + 1) (by simpa using hl) (by simpa using hi)
          simp only [List.get_eq_getElem, List.getElem_cons_succ] at c1
          obtain ⟨k1, k2, _, _⟩ := kept i hl
          simp only [List.get_eq_getElem] at k1 k2 ⊢
          rw [k1, k2]
          exact c1)
        (fun t' ht' => hno t' (by simp [ht'])) hpw'.2
        (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hnoT.2, ho] at hml ⊢; omega)
        (by simp [hσ2, hσ1] at hml ⊢; omega)
      refine ⟨τ, WExec.cast cap (WExec.seq ex hτ) rfl (by simp [slotsCost]), ?_, a2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [a1, marks_unary_cons]
        simp [hσ2, hσ1, List.append_assoc]
      · rw [a3, hlen1]
        simp [hσ2, hσ1] at hml ⊢
        omega
      · intro s hs
        rw [a4 s hs, st2 s hs]
      · intro s hs hs'
        rw [a7 s hs (fun t' ht' => hs' t' (by simp [ht'])), sh2 s hs (hs' t (by simp))]
      · intro r hr
        rw [a5 r hr]
        simp [hσ2, hσ1, Function.update_apply, hr]
      · rw [a6]
        simp [hσ2, hσ1]

end Collect

end NearCubicWires.WireExponent3_5.PrimAsm.Data
