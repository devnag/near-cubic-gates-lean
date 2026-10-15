import Proof.Wire_3_5.PrimAsmCellLoop
import Proof.Wire_3_5.PrimAsmDataSetup
import Proof.Wire_3_5.PrimAsmShellLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The copy-in -/

/-- Copy the framed word after the sentinel on stream `0` onto stream `1`, then walk both heads back. -/
def cpW : WM 1 0 :=
  .seq (.fwd 0) (.seq (.whs 0 (.seq (.fwd 0) (.seq (.ifs 0 (.wr 1 true) (.wr 1 false)) (.seq (.fwd 1) (.fwd 0)))))
    (.seq (.bwd 0) (.seq (.bwd 0) (.whs 0 (.seq (.bwd 0) (.seq (.bwd 0) (.bwd 1)))))))

/-- The copy-in's cost. -/
def cpCost (m : ℕ) : ℕ := 1 + 1 + (m * (8 + 2) + 1 + 1 + (1 + 1 + (1 + 1 + (m * (5 + 2) + 1))))

theorem read_dw_zero (u : List Bool) : readTapeBit (false :: (marks u ++ [false])) 0 = false := rfl

theorem read_dw_mark (u : List Bool) (k : ℕ) (hk : k < u.length) :
    readTapeBit (false :: (marks u ++ [false])) (2 * k + 1) = true := by
  have := read_pre [false] (marks u ++ [false]) (2 * k)
  simp only [List.singleton_append, List.length_singleton] at this
  rw [show 2 * k + 1 = 1 + 2 * k by ring, this]
  exact read_marks_mark [false] u k hk

theorem read_dw_bit (u : List Bool) (k : ℕ) (hk : k < u.length) :
    readTapeBit (false :: (marks u ++ [false])) (2 * k + 2) = u.getD k false := by
  have := read_pre [false] (marks u ++ [false]) (2 * k + 1)
  simp only [List.singleton_append, List.length_singleton] at this
  rw [show 2 * k + 2 = 1 + (2 * k + 1) by ring, this]
  exact read_marks_bit [false] u k hk

theorem read_dw_end (u : List Bool) : readTapeBit (false :: (marks u ++ [false])) (2 * u.length + 1) = false := by
  have := read_pre (false :: marks u) [false] 0
  have hl : (false :: marks u).length = 2 * u.length + 1 := by simp [RepairOrdinary.Streaming.marks_length]
  rw [hl, Nat.add_zero, List.cons_append] at this
  rw [this]
  rfl

theorem take_succ_getD (u : List Bool) (k : ℕ) (hk : k < u.length) :
    u.take (k + 1) = u.take k ++ [u.getD k false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.getD_eq_getElem _ _ hk]

section Cp
variable (cap : ℕ)

/-- **The copy-in**: from `false :: (marks u ++ [false])` on `0` (head `0`) and a blank `1`, the word `u` on `1`, both heads
back at `0`. -/
theorem cpW_spec (u : List Bool) (σ : WState 1 0) (h0 : σ.st 0 = false :: (marks u ++ [false])) (h0h : σ.sh 0 = 0)
    (h1 : σ.st 1 = []) (h1h : σ.sh 1 = 0) :
    WExec cap cpW σ (σ.sets 1 u) (cpCost u.length) := by
  set m := u.length with hm
  set Lk : ℕ → WState 1 0 := fun k => ((σ.seth 0 (2 * k + 1)).sets 1 (u.take k)).seth 1 k with hLk
  have e0 := WExec.fwd (cap := cap) 0 σ
  have eL0 : σ.seth 0 (σ.sh 0 + 1) = Lk 0 := by
    apply WState.eq
    · funext j; fin_cases j <;> simp [hLk, h0h, h1h, Function.update_apply]
    · funext j; fin_cases j <;> simp [hLk, h1, Function.update_apply]
    · funext r; exact r.elim0
    · simp [hLk]
  rw [eL0] at e0
  have l1 := Data.whsLoop cap 0 (.seq (.fwd 0) (.seq (.ifs 0 (.wr 1 true) (.wr 1 false)) (.seq (.fwd 1) (.fwd 0)))) 8 m Lk
    (fun k hk => by simp [wbit, hLk, h0, read_dw_mark u k hk])
    (by simp [wbit, hLk, h0, hm, read_dw_end])
    (fun k hk => by
      have a1 := WExec.fwd (cap := cap) 0 (Lk k)
      set A := (Lk k).seth 0 ((Lk k).sh 0 + 1) with hA
      have hbit : wbit A 0 = u.getD k false := by
        have e1 : A.st 0 = σ.st 0 := by simp [hA, hLk, Function.update_apply]
        have e2 : A.sh 0 = 2 * k + 2 := by simp [hA, hLk, Function.update_apply]
        rw [wbit, e1, e2, h0]
        exact read_dw_bit u k hk
      have gen : ∀ b, wbit A 0 = b →
          WExec cap (.ifs 0 (.wr 1 true) (.wr 1 false)) A (A.sets 1 (writeTapeBit (A.st 1) (A.sh 1) b)) 2 := by
        intro b hb
        cases b
        · exact WExec.ifsF hb (WExec.wr 1 false A)
        · exact WExec.ifsT hb (WExec.wr 1 true A)
      set B := A.sets 1 (writeTapeBit (A.st 1) (A.sh 1) (u.getD k false)) with hB
      have a2 : WExec cap (.ifs 0 (.wr 1 true) (.wr 1 false)) A B 2 := gen _ hbit
      have a3 := WExec.fwd (cap := cap) 1 B
      have a4 := WExec.fwd (cap := cap) 0 (B.seth 1 (B.sh 1 + 1))
      refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 a4))) ?_ (by omega)
      have hlt : (u.take k).length = k := by simp [List.length_take]; omega
      apply WState.eq
      · funext j; fin_cases j
        · simp [hB, hA, hLk, Function.update_apply]; ring
        · simp [hB, hA, hLk, Function.update_apply]
      · funext j; fin_cases j
        · simp [hB, hA, hLk, Function.update_apply]
        · have hw : writeTapeBit (u.take k) k (u.getD k false) = u.take k ++ [u.getD k false] := by
            have := Data.wtb_end (u.take k) (u.getD k false)
            rwa [hlt] at this
          have e1 : A.st 1 = u.take k := by simp [hA, hLk, Function.update_apply]
          have e2 : A.sh 1 = k := by simp [hA, hLk, Function.update_apply]
          simp only [hB, WState.seth_st, WState.sets_st, Function.update_apply, if_pos rfl, e1, e2, hw,
            take_succ_getD u k hk]
          simp [hLk, Function.update_apply]
          rw [take_succ_getD u k hk]
          rfl
      · funext r; exact r.elim0
      · simp [hB, hA, hLk])
  -- rewind
  have b1 := WExec.bwd (cap := cap) 0 (Lk m)
  have b2 := WExec.bwd (cap := cap) 0 ((Lk m).seth 0 ((Lk m).sh 0 - 1))
  set Rq : ℕ → WState 1 0 := fun q => ((Lk m).seth 0 (2 * (m - q) - 1)).seth 1 (m - q) with hRq
  have eR0 : ((Lk m).seth 0 ((Lk m).sh 0 - 1)).seth 0 (((Lk m).seth 0 ((Lk m).sh 0 - 1)).sh 0 - 1) = Rq 0 := by
    apply WState.eq
    · funext j; fin_cases j
      · simp [hRq, hLk, Function.update_apply] <;> omega
      · simp [hRq, hLk, Function.update_apply]
    · funext j; simp [hRq, hLk]
    · funext r; exact r.elim0
    · simp [hRq, hLk]
  rw [eR0] at b2
  have l2 := Data.whsLoop cap 0 (.seq (.bwd 0) (.seq (.bwd 0) (.bwd 1))) 5 m Rq
    (fun q hq => by
      have := read_dw_mark u (m - q - 1) (by omega)
      rw [show 2 * (m - q - 1) + 1 = 2 * (m - q) - 1 by omega] at this
      simp [wbit, hRq, hLk, h0, this])
    (by simp [wbit, hRq, hLk, h0, read_dw_zero])
    (fun q hq => by
      have a1 := WExec.bwd (cap := cap) 0 (Rq q)
      have a2 := WExec.bwd (cap := cap) 0 ((Rq q).seth 0 ((Rq q).sh 0 - 1))
      have a3 := WExec.bwd (cap := cap) 1 (((Rq q).seth 0 ((Rq q).sh 0 - 1)).seth 0
        (((Rq q).seth 0 ((Rq q).sh 0 - 1)).sh 0 - 1))
      refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 a3)) ?_ (by omega)
      apply WState.eq
      · funext j; fin_cases j
        · simp [hRq, hLk, Function.update_apply]; omega
        · simp [hRq, hLk, Function.update_apply]; omega
      · funext j; simp [hRq, hLk]
      · funext r; exact r.elim0
      · simp [hRq, hLk])
  have eF : Rq m = σ.sets 1 u := by
    apply WState.eq
    · funext j; fin_cases j
      · simp [hRq, hLk, Function.update_apply, h0h]
      · simp [hRq, hLk, Function.update_apply, h1h]
    · funext j; fin_cases j
      · simp [hRq, hLk, Function.update_apply]
      · simp [hRq, hLk, Function.update_apply, hm]
    · funext r; exact r.elim0
    · simp [hRq, hLk]
  rw [eF] at l2
  exact WExec.cast cap (WExec.seq e0 (WExec.seq l1 (WExec.seq b1 (WExec.seq b2 l2)))) rfl (by unfold cpCost; omega)

end Cp

/-! ## The loop with the data tape -/

section Loop
variable (cap : ℕ)

/-- A cell tape in the loop body's layout. -/
def cellP {x e : ℕ} (i : Fin (TT x)) : Fin ((TT x + 1) + e) := Fin.castAdd e (Fin.castAdd 1 i)

/-- The data tape. -/
def dataP {x e : ℕ} : Fin ((TT x + 1) + e) := Fin.castAdd e (Fin.natAdd (TT x) (0 : Fin 1))

/-- The copy-in's tapes: the data tape, the cell's result cell, the cell's stream `113`. -/
def cpSlots (x e : ℕ) : Fin (1 + 2 + 0) → Fin ((TT x + 1) + e) :=
  ![dataP, cellP (cTape (ns := LNS x) (nr := LNR)), cellP (sTape (nr := LNR) (sk x 113))]

theorem cellP_val {x e : ℕ} (i : Fin (TT x)) : (cellP (e := e) i).val = i.val := rfl
theorem dataP_val {x e : ℕ} : (dataP (x := x) (e := e)).val = TT x := rfl

theorem cpSlots_inj (x e : ℕ) : Function.Injective (cpSlots x e) := by
  intro a b h
  have hv := congrArg Fin.val h
  have h113 : (sTape (nr := LNR) (sk x 113)).val = 114 := rfl
  have hc : (cTape (ns := LNS x) (nr := LNR)).val = 1 := rfl
  have hT : 115 ≤ TT x := by unfold TT LNS LNR; omega
  fin_cases a <;> fin_cases b <;> simp [cpSlots, cellP_val, dataP_val, h113, hc] at hv ⊢ <;> omega

/-- The copy-in, docked. -/
noncomputable def cpM (x e : ℕ) := RecoveryFocus.machine (cpSlots x e) cpW.toProg.compile

/-- **The loop body**: copy-in, then the unit machine (next to the data tape and the workspace). -/
noncomputable def bodyD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (e : ℕ) :=
  Composition.machine (cpM W.x e) (TapeEmbedding.machine e (TapeEmbedding.machine 1 (unitM W decW)))

/-- The unit's entry state: `blankCell` with the call's counts on stream `113`. -/
def blankCellD (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) : WState (LNS x) LNR :=
  (blankCell x w out j).sets (sk x 113) u

/-- The kept tapes: the cell's request, output and counter, and the data tape. -/
def keptD (x : ℕ) : Fin (TT x + 1) → Bool := Fin.addCases (kept x) (fun _ => true)

def scrSD (x e : ℕ) : Fin ((TT x + 1) + e) → Bool := Fin.addCases (fun i => !keptD x i) (fun _ => false)

def scrResetD (x e : ℕ) : Fin ((TT x + 1) + e) → Bool :=
  Fin.addCases (fun i => !decide (i = Fin.castAdd 1 (sTape (nr := LNR) (sk x 1)))) (fun _ => true)

def loopHD (x e : ℕ) (out : List Bool) : Fin ((TT x + 1) + e) → ℕ :=
  Fin.addCases (Fin.addCases (fun i => if i = sTape (nr := LNR) (sk x 1) then out.length else 0) (fun _ : Fin 1 => 0))
    (fun _ => 0)

def loopAD (x e R : ℕ) (w dw : List Bool) (Wk : Fin e → List Bool) (j : ℕ) (out : List Bool) :
    Fin ((TT x + 1) + e) → List Bool :=
  Fin.addCases (Fin.addCases (fun i => if kept x i then (wenc cap (blankCell x w out j)).A i else List.replicate R false)
    (fun _ : Fin 1 => dw)) Wk

theorem blankCellD_A (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) (i : Fin (TT x))
    (hi : i ≠ sTape (sk x 113)) : (wenc cap (blankCellD x w out j u)).A i = (wenc cap (blankCell x w out j)).A i := by
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · have hs : s ≠ sk x 113 := fun h => hi (by rw [h])
    rw [wenc_A_s, wenc_A_s]
    simp [blankCellD, Function.update_apply, hs]
  · rw [wenc_A_c, wenc_A_c]; rfl
  · rw [wenc_A_r, wenc_A_r]; rfl

theorem blankCellD_H (x : ℕ) (w out : List Bool) (j : ℕ) (u : List Bool) :
    (wenc cap (blankCellD x w out j u)).H = (wenc cap (blankCell x w out j)).H := by
  funext i
  rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s, wenc_H_s]; rfl
  · rw [wenc_H_c, wenc_H_c]
  · rw [wenc_H_r, wenc_H_r]; rfl

/-- **One unit with its copy-in, as a loop stage.** -/
theorem loop_stageD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) {e : ℕ} (R nU : ℕ) (w u : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (j : ℕ) (out : List Bool) (hcap : cap + 1 ≤ R)
    (hdec : ∃ σD m Bp, WExec cap decW (blankCellD W.x w out j u) σD m ∧ DecOK cap W σD out (emit j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      cpCost u.length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU) :
    ∃ H' A', Step (bodyD W decW e) nU (loopHD W.x e out) (loopAD cap W.x e R w (false :: (marks u ++ [false])) Wk j out)
      H' A' ∧
      (∀ i, scrSD W.x e i = false →
        A' i = loopAD cap W.x e R w (false :: (marks u ++ [false])) Wk (j + 1) (out ++ emit j) i) ∧
      (∀ i, scrResetD W.x e i = false → H' i = loopHD W.x e (out ++ emit j) i) := by
  obtain ⟨σD, m, Bp, hd, hok, hIN, hC, hCh, hn⟩ := hdec
  have n0 : sk W.x 113 ≠ sk W.x 0 := fun h => absurd (sk_inj W.x h) (by decide)
  have n1 : sk W.x 113 ≠ sk W.x 1 := fun h => absurd (sk_inj W.x h) (by decide)
  have n2 : sk W.x 113 ≠ sk W.x 2 := fun h => absurd (sk_inj W.x h) (by decide)
  have eH0 : (Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).H (fun _ : Fin 1 => 0)) (fun _ => 0) :
      Fin ((TT W.x + 1) + e) → ℕ) = loopHD W.x e out := by
    rw [blank_H]
    rfl
  -- 1: the copy-in
  have cp := cpW_spec 0 u (⟨fun _ => 0, ![false :: (marks u ++ [false]), []], fun r => r.elim0, false⟩ : WState 1 0)
    rfl rfl rfl rfl
  have cps := (WExec.exec 0 cp).step
  have dk := Rec.dockRun cps (cpSlots W.x e) (cpSlots_inj W.x e)
    (Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).H (fun _ : Fin 1 => 0)) (fun _ => 0))
    (Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).A (fun _ : Fin 1 => false :: (marks u ++ [false])))
      Wk)
    (by
      intro k
      fin_cases k
      · show _ = (wenc 0 _).H (sTape 0)
        rw [wenc_H_s]; simp [cpSlots, dataP]
      · show _ = (wenc 0 _).H cTape
        rw [wenc_H_c]; simp [cpSlots, cellP, wenc_H_c]
      · show _ = (wenc 0 _).H (sTape 1)
        rw [wenc_H_s]; simp [cpSlots, cellP, wenc_H_s, blankCell, n1])
    (by
      intro k
      fin_cases k
      · show _ = (wenc 0 _).A (sTape 0)
        rw [wenc_A_s]; simp [cpSlots, dataP]
      · show _ = (wenc 0 _).A cTape
        rw [wenc_A_c]; simp [cpSlots, cellP, wenc_A_c, blankCell]
      · show _ = (wenc 0 _).A (sTape 1)
        rw [wenc_A_s]; simp [cpSlots, cellP, wenc_A_s, blankCell, n0, n1, n2])
  have eH : dockH (cpSlots W.x e) (Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).H
      (fun _ : Fin 1 => 0)) (fun _ => 0))
      (wenc 0 ((⟨fun _ => 0, ![false :: (marks u ++ [false]), []], fun r => r.elim0, false⟩ : WState 1 0).sets 1 u)).H =
      Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).H (fun _ : Fin 1 => 0)) (fun _ => 0) := by
    refine Shell.dockH_eq _ (cpSlots_inj W.x e) _ _ _ ?_ (fun _ _ => rfl)
    intro k
    fin_cases k
    · show _ = (wenc 0 _).H (sTape 0)
      rw [wenc_H_s]; simp [cpSlots, dataP]
    · show _ = (wenc 0 _).H cTape
      rw [wenc_H_c]; simp [cpSlots, cellP, wenc_H_c]
    · show _ = (wenc 0 _).H (sTape 1)
      rw [wenc_H_s]; simp [cpSlots, cellP, wenc_H_s, blankCell, n1]
  have eA : install (cpSlots W.x e) (Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).A
      (fun _ : Fin 1 => false :: (marks u ++ [false]))) Wk)
      (wenc 0 ((⟨fun _ => 0, ![false :: (marks u ++ [false]), []], fun r => r.elim0, false⟩ : WState 1 0).sets 1 u)).A =
      Fin.addCases (Fin.addCases (wenc cap (blankCellD W.x w out j u)).A
        (fun _ : Fin 1 => false :: (marks u ++ [false]))) Wk := by
    refine Shell.install_eq _ (cpSlots_inj W.x e) _ _ _ ?_ ?_
    · intro k
      fin_cases k
      · show _ = (wenc 0 _).A (sTape 0)
        rw [wenc_A_s]; simp [cpSlots, dataP]
      · show _ = (wenc 0 _).A cTape
        rw [wenc_A_c]; simp [cpSlots, cellP, wenc_A_c, blankCellD, blankCell]
      · show _ = (wenc 0 _).A (sTape 1)
        rw [wenc_A_s]; simp [cpSlots, cellP, wenc_A_s, blankCellD]
    · intro i hi
      revert hi
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hc : c ≠ sTape (sk W.x 113) := fun h => hi 2 (by rw [h]; rfl)
          simp only [Fin.addCases_left]
          exact blankCellD_A cap W.x w out j u c hc
        · intro _
          simp
      · intro _
        simp
  rw [eH, eA] at dk
  -- 2: the unit
  obtain ⟨σE, sU, e0, e1, e1h, e2⟩ := unit_step cap W decW (blankCellD W.x w out j u) σD m j Bp out (emit j) w hd hok
    hIN hC hCh
  have su := (sU.embed (fun _ : Fin 1 => 0) (fun _ => false :: (marks u ++ [false]))).embed (fun _ : Fin e => 0) Wk
  rw [blankCellD_H] at su
  have whole := dk.seq su
  -- 3: from the cleared state
  have c := Scrub.cleared_entry whole (scrSD W.x e) R (by
    intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · intro hc
        have hk : kept W.x c = false := by simpa [scrSD, keptD] using hc
        obtain ⟨k, hk1, hk2⟩ := blank_scratch cap W.x w out j c hk
        exact ⟨k, by omega, by simpa using hk2⟩
      · intro hv
        simp [scrSD, keptD] at hv
    · intro hk
      simp [scrSD] at hk)
  have ce := c.enlarge hn
  have eB0 : Scrub.blank (scrSD W.x e) (Fin.addCases (Fin.addCases (wenc cap (blankCell W.x w out j)).A
      (fun _ : Fin 1 => false :: (marks u ++ [false]))) Wk) R =
      loopAD cap W.x e R w (false :: (marks u ++ [false])) Wk j out := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · simp only [Scrub.blank, scrSD, keptD, loopAD, Fin.addCases_left]
        cases hk : kept W.x c <;> simp [hk]
      · simp [Scrub.blank, scrSD, keptD, loopAD]
    · simp [Scrub.blank, scrSD, loopAD]
  rw [eH0, eB0] at ce
  refine ⟨_, _, ce, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · intro hi
        have hk : kept W.x c = true := by simpa [scrSD, keptD] using hi
        simp only [Fin.addCases_left, loopAD, hk, if_true, Bool.not_true, Bool.false_eq_true, if_false,
          ZeroPadding.pad_zero, scrSD, keptD]
        have hk' := hk
        simp only [kept, Bool.or_eq_true, decide_eq_true_eq] at hk'
        rcases hk' with (rfl | rfl) | rfl
        · rw [wenc_A_s, wenc_A_s, e0, blankCell_st0]
        · rw [wenc_A_s, wenc_A_s, e1, blankCell_st1]
        · rw [wenc_A_s, wenc_A_s, e2, blankCell_st2]
      · intro _
        simp [loopAD, scrSD, keptD]
    · intro _
      simp [loopAD, scrSD]
  · intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · intro hi
        have ha : c = sTape (sk W.x 1) := by simpa [scrResetD] using hi
        subst ha
        simp only [Fin.addCases_left, loopHD, if_true]
        rw [wenc_H_s, e1h]
      · intro hi
        exfalso
        have he : Fin.natAdd (TT W.x) v = Fin.castAdd 1 (sTape (nr := LNR) (sk W.x 1)) := by
          simpa [scrResetD] using hi
        have hv := congrArg Fin.val he
        have h2 : (sTape (nr := LNR) (sk W.x 1)).val = 2 := rfl
        simp only [Fin.val_natAdd, Fin.val_castAdd, h2] at hv
        have hT : 3 ≤ TT W.x := by unfold TT LNS LNR; omega
        omega
    · intro hi
      simp [scrResetD] at hi

end Loop

section Cells
variable (cap : ℕ)

/-- **The writer's loop with the data tape** as base `Cells`. -/
noncomputable def loopCellsD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) {e : ℕ} (R nU bound : ℕ) (w u : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (hcap : cap + 1 ≤ R) (hR : nU + 1 ≤ R)
    (hdec : ∀ j < bound, ∀ out : List Bool, ∃ σD m Bp, WExec cap decW (blankCellD W.x w out j u) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧ cpCost u.length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU) :=
  Cells.ofScrub (bodyD W decW e) (scrResetD W.x e) (scrSD W.x e) R (R + 2) bound
    (fun _ out => loopHD W.x e out) (fun j out => loopAD cap W.x e R w (false :: (marks u ++ [false])) Wk j out) emit
    (fun i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hk : kept W.x c = false := by simpa [scrSD, keptD] using hi
          have hne : c ≠ sTape (sk W.x 1) := fun h => by subst h; simp [kept] at hk
          simp [scrResetD, hne]
        · intro hi
          simp [scrSD, keptD] at hi
      · intro hi
        simp [scrSD] at hi)
    hR (by omega)
    (fun j _ out i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hne : c ≠ sTape (sk W.x 1) := by simpa [scrResetD] using hi
          simp [loopHD, hne]
        · intro _
          simp [loopHD]
      · intro _
        simp [loopHD])
    (fun j _ out i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hk : kept W.x c = false := by simpa [scrSD, keptD] using hi
          simp [loopAD, hk]
        · intro hi
          simp [scrSD, keptD] at hi
      · intro hi
        simp [scrSD] at hi)
    (fun j hj out => loop_stageD cap W decW R nU w u Wk emit j out hcap (hdec j hj out))

/-- **The writer's loop with the data tape, as one `Step`** (base `Cells.loopStep`). -/
theorem loop_stepD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) {e : ℕ} (R nU bound : ℕ) (w u : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (hcap : cap + 1 ≤ R) (hR : nU + 1 ≤ R)
    (hdec : ∀ j < bound, ∀ out : List Bool, ∃ σD m Bp, WExec cap decW (blankCellD W.x w out j u) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧ cpCost u.length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU) :
    Step (CloseoutRowsDegreeLoop.machine (Scrub.machine (bodyD W decW e) (scrResetD W.x e) (scrSD W.x e)))
      (bound * ((2 * nU + 2 + 1 + (2 * R + 4)) + 3) + 3)
      (Fin.addCases (Scrub.heads (loopHD W.x e [])) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (loopAD cap W.x e R w (false :: (marks u ++ [false])) Wk 0 []) R (R + 2))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound))
      (Fin.addCases (Scrub.heads (loopHD W.x e ([] ++ (List.range bound).flatMap emit))) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (loopAD cap W.x e R w (false :: (marks u ++ [false])) Wk bound
        ([] ++ (List.range bound).flatMap emit)) R (R + 2))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound)) :=
  Cells.loopStep (loopCellsD cap W decW R nU bound w u Wk emit hcap hR hdec) []

end Cells

end NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
