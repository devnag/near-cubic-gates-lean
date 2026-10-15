import Proof.Wire_3_5.PrimAsmShellDPre
import Proof.Wire_3_5.PrimAsmWriterIfaceJ

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline

section Regions
variable {x D D1 D2 : ℕ}

/-- A stage tape of the scrub (the cell's, then the data tape). -/
def sT (c : Fin (TT x + 1)) : Fin (STd x D D1 D2) :=
  Fin.castAdd _ (Fin.castAdd 1 (Scrub.inner (Fin.castAdd (Scrub.wk D) c)))

/-- An extension tape (the bound's run, the width run, the data stage). -/
def xT (k : Fin (E1 D1 + E2 D2 + E3)) : Fin (STd x D D1 D2) := Fin.natAdd (LTd x D) k

theorem xT_val (k : Fin (E1 D1 + E2 D2 + E3)) : (xT (x := x) (D := D) k).val = TT x + 1 + Scrub.wk D + 3 + k.val :=
  rfl

/-- **A bank is determined by its loop regions and its extension.** -/
theorem regionsX {α : Type} (B B' : Fin (STd x D D1 D2) → α) (hc : ∀ i, B (cT i) = B' (cT i))
    (hdt : B dT = B' dT) (hw : ∀ j, B (wT j) = B' (wT j)) (hl : B lgT = B' lgT) (hd : B drT = B' drT)
    (hk : B kT = B' kT) (hx : ∀ k, B (xT k) = B' (xT k)) : B = B' :=
  regions B B' hc hdt hw hl hd hk (fun _ => hx _) (fun _ => hx _) (fun _ => hx _)

theorem hK_ne (i : Fin (STd x D D1 D2)) (h : i ≠ kT) : hK x D D1 D2 i = 0 := by
  unfold hK
  rw [if_neg h]

theorem hK_kT : hK x D D1 D2 kT = 1 := by
  unfold hK
  rw [if_pos rfl]

theorem cT_ne_kT (i : Fin (TT x)) : cT (D := D) (D1 := D1) (D2 := D2) i ≠ kT := by
  apply ne_of_val
  rw [cT_val, kT_val]
  have := i.isLt
  omega

theorem dT_ne_kT : dT (x := x) (D := D) (D1 := D1) (D2 := D2) ≠ kT := by
  apply ne_of_val
  rw [dT_val, kT_val]
  omega

theorem wT_ne_kT (j : Fin (Scrub.wk D)) : wT (x := x) (D1 := D1) (D2 := D2) j ≠ kT := by
  apply ne_of_val
  rw [wT_val, kT_val]
  have := j.isLt
  omega

theorem lgT_ne_kT : lgT (x := x) (D := D) (D1 := D1) (D2 := D2) ≠ kT := by
  apply ne_of_val
  rw [lgT_val, kT_val]
  omega

theorem drT_ne_kT : drT (x := x) (D := D) (D1 := D1) (D2 := D2) ≠ kT := by
  apply ne_of_val
  rw [drT_val, kT_val]
  omega

theorem xT_ne_kT (k : Fin (E1 D1 + E2 D2 + E3)) : xT (x := x) (D := D) k ≠ kT := by
  apply ne_of_val
  rw [xT_val, kT_val]
  omega

/-- The framed word is its marks and the closing `0`. -/
theorem frame_marks (u : List Bool) : RepairOrdinary.frame u = RepairOrdinary.Streaming.marks u ++ [false] := by
  have := RepairOrdinary.Streaming.frame_append u []
  simpa [RepairOrdinary.frame] using this

/-- The data word is the copy-in's input format. -/
theorem dataWord_eq (cs : List ℕ) :
    Data.dataWord cs = false :: (RepairOrdinary.Streaming.marks (Data.unaryList cs) ++ [false]) := by
  rw [Data.dataWord, frame_marks]

end Regions

section Run
variable {x D D1 D2 : ℕ}

/-- The scrub entry over the cell and the data tape, embedded next to the counter and the extension. -/
noncomputable def entryED (x D D1 D2 C : ℕ) :=
  TapeEmbedding.machine (E1 D1 + E2 D2 + E3) (TapeEmbedding.machine 1
    (Scrub.entryMachine (TT x + 1) D C (fun i => !keptD x i)))

/-- The loop's heads (before or after the units), in the shell's layout. -/
def loopHSd (x D D1 D2 : ℕ) (out : List Bool) : Fin (STd x D D1 D2) → ℕ :=
  Fin.addCases (Fin.addCases (Scrub.heads (loopHD x (Scrub.wk D) out)) (fun _ : Fin 1 => 1)) (fun _ => 0)

/-- The loop's tapes before unit `j` after the output `out`, in the shell's layout (`dw` the data tape). -/
def loopASd (cap x D D1 D2 R : ℕ) (w dw : List Bool) (Wk : Fin (Scrub.wk D) → List Bool) (j b : ℕ)
    (out : List Bool) (ext : Fin (E1 D1 + E2 D2 + E3) → List Bool) : Fin (STd x D D1 D2) → List Bool :=
  Fin.addCases (Fin.addCases (Scrub.bank (loopAD cap x (Scrub.wk D) R w dw Wk j out) R (R + 2))
    (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word b)) ext

/-- **The scrub entry in the shell with data**: from the data phase's exit (request kept, `OUT = [false]`, unit counter
blank, the cell's scratch within `R = C(n+1)^D`, workspace `Scrub.calcIn D n`, log and driver blank, counter `word b`,
data tape `dw`) to the loop's entry bank before unit `0`, the data tape kept. -/
theorem entry_runD (cap C n b : ℕ) (w dw : List Bool) (B : Fin (STd x D D1 D2) → List Bool)
    (h0 : B (cs 0) = frame w) (h1 : B (cs 1) = [false]) (h2 : B (cs 2) = [])
    (hs : ∀ c, kept x c = false → (B (cT c)).length ≤ UnaryCalc.value D C n)
    (hw : ∀ j, B (wT j) = Scrub.calcIn D n j) (hl : B lgT = []) (hd : B drT = [])
    (hk : B kT = RepairSource.VerifierDecoding.CompareMachine.word b) (hdt : B dT = dw) :
    ∃ Wk : Fin (Scrub.wk D) → List Bool, Step (entryED x D D1 D2 C) (Scrub.entryCost D C n)
      (hK x D D1 D2) B (loopHSd x D D1 D2 [])
      (loopASd cap x D D1 D2 (UnaryCalc.value D C n) w dw Wk 0 b [] (fun k => B (xT k))) := by
  obtain ⟨Wk, _, he⟩ := Scrub.entry_step (TT x + 1) D C n (fun i => !keptD x i) (fun _ => 0)
    (fun c => B (sT c)) (fun _ _ => rfl) (by
      intro i
      refine Fin.addCases (fun c => ?_) (fun v => ?_) i
      · intro hc
        have hk' : kept x c = false := by simpa [keptD] using hc
        exact hs c hk'
      · intro hv
        simp [keptD] at hv)
  have he2 := (he.embed (fun _ : Fin 1 => 1) (fun _ => RepairSource.VerifierDecoding.CompareMachine.word b)).embed
    (fun _ : Fin (E1 D1 + E2 D2 + E3) => 0) (fun k => B (xT k))
  refine ⟨Wk, he2.congr_in ?_ ?_ |>.congr ?_ ?_⟩
  · apply regionsX
    · intro i
      rw [hK_ne _ (cT_ne_kT i)]
      simp [cT]
    · rw [hK_ne _ dT_ne_kT]
      simp [dT]
    · intro j
      rw [hK_ne _ (wT_ne_kT j)]
      simp [wT]
    · rw [hK_ne _ lgT_ne_kT]
      simp [lgT]
    · rw [hK_ne _ drT_ne_kT]
      simp [drT]
    · rw [hK_kT]
      simp [kT]
    · intro k
      rw [hK_ne _ (xT_ne_kT k)]
      simp [xT]
  · apply regionsX
    · intro i
      simp [cT, sT]
    · simp [dT, sT]
    · intro j
      rw [hw j]
      simp [wT]
    · rw [hl]
      simp [lgT]
    · rw [hd]
      simp [drT]
    · rw [hk]
      simp [kT]
    · intro k
      simp [xT]
  · apply regionsX
    · intro i
      simp [cT, loopHSd, loopHD]
    · simp [dT, loopHSd, loopHD]
    · intro j
      simp [wT, loopHSd, loopHD]
    · simp [lgT, loopHSd]
    · simp [drT, loopHSd]
    · simp [kT, loopHSd]
    · intro k
      simp [xT, loopHSd]
  · apply regionsX
    · intro c
      simp only [cT, loopASd, loopAD, Fin.addCases_left, Scrub.bank_inner, Scrub.blank, keptD]
      cases hkc : kept x c
      · simp
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
        have hk' := hkc
        simp only [kept, Bool.or_eq_true, decide_eq_true_eq] at hk'
        rcases hk' with (rfl | rfl) | rfl
        · rw [wenc_A_s, blankCell_st0]
          exact h0
        · rw [wenc_A_s, blankCell_st1]
          exact h1
        · rw [wenc_A_s, blankCell_st2]
          exact h2
    · simp only [dT, loopASd, loopAD, Fin.addCases_left, Fin.addCases_right, Scrub.bank_inner, Scrub.blank, keptD,
        Bool.not_true, Bool.false_eq_true, if_false]
      exact hdt
    · intro j
      simp [wT, loopASd, loopAD]
    · simp [lgT, loopASd]
    · simp [drT, loopASd]
    · simp [kT, loopASd]
    · intro k
      simp [xT, loopASd]

/-! ## The shell machine and its run -/

/-- The unit loop with the data tape (`CellLoopD.loop_stepD`'s machine), next to the extension. -/
noncomputable def loopED (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D D1 D2 : ℕ) :=
  TapeEmbedding.machine (E1 D1 + E2 D2 + E3) (CloseoutRowsDegreeLoop.machine (Scrub.machine
    (bodyD W decW (Scrub.wk D)) (scrResetD W.x (Scrub.wk D)) (scrSD W.x (Scrub.wk D))))

/-- The writer before its teardown: boot and data phase, scrub entry, unit loop. -/
noncomputable def innerMD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D1 C1 D2 C2 : ℕ) :=
  Composition.machine (Composition.machine (preM W.x D D1 D2 C1 C2) (entryED W.x D D1 D2 C)) (loopED W decW D D1 D2)

/-- **The shell machine with per-call data**: the writer under one masked reset (every head back at `0`). One machine
per unit machine and per `(D, C, D₁, C₁, D₂, C₂)`, independent of the request. -/
noncomputable def shellMD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D1 C1 D2 C2 : ℕ) :=
  MaskedReset.machine (innerMD W decW D C D1 C1 D2 C2) (fun _ => true)

/-- The shell's request port. -/
def shellInD (x D D1 D2 : ℕ) : Fin (STd x D D1 D2 + 1) := Fin.castAdd 1 (cs 0)

/-- The shell's output port. -/
def shellOutD (x D D1 D2 : ℕ) : Fin (STd x D D1 D2 + 1) := Fin.castAdd 1 (cs 1)

theorem shellInD_ne_out : shellInD x D D1 D2 ≠ shellOutD x D D1 D2 := by
  intro h
  have := Fin.castAdd_injective _ _ h
  exact absurd ((cs_eq_iff _ _).mp this) (by decide)

/-- The shell's cost before the teardown: boot and data phase, entry, loop and two bridges (`cc` the data stage's
core cost). -/
def shellCostD (w : List Bool) (n D C D1 C1 D2 C2 cc nU : ℕ) : ℕ :=
  preCost w n D1 C1 D2 C2 cc + 1 + Scrub.entryCost D C n + 1 +
    (UnaryCalc.value D1 C1 n * ((2 * nU + 2 + 1 + (2 * UnaryCalc.value D C n + 4)) + 3) + 3)

theorem loopASd_cs0 (cap R : ℕ) (w dw : List Bool) (Wk : Fin (Scrub.wk D) → List Bool) (j b : ℕ) (out : List Bool)
    (ext : Fin (E1 D1 + E2 D2 + E3) → List Bool) : loopASd cap x D D1 D2 R w dw Wk j b out ext (cs 0) = frame w := by
  simp [loopASd, cs, cT, loopAD, kept, blankCell_st0]

theorem loopASd_cs1 (cap R : ℕ) (w dw : List Bool) (Wk : Fin (Scrub.wk D) → List Bool) (j b : ℕ) (out : List Bool)
    (ext : Fin (E1 D1 + E2 D2 + E3) → List Bool) :
    loopASd cap x D D1 D2 R w dw Wk j b out ext (cs 1) = out ++ [false] := by
  simp [loopASd, cs, cT, loopAD, kept, blankCell_st1]

/-- **The writer shell's run with per-call data** (`WriterIfaceJ.WriterRun`): from `inBank (frame w)` with `w` the SYM
call's request word, the output tape `(List.range b).flatMap emit ++ [false]` (`b = C₁(n+1)^{D₁}`), within the
budget, all heads back at `0`, the request kept, residues within the budget; for any unit machine whose decode (after
the copy-in of the call's counts `Data.unaryList (Data.symCounts a' Cs carriers)`) meets `CellUnit.DecOK` at every
unit `j < b` within `nU` steps. -/
theorem shell_runD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (cap D C D1 C1 D2 C2 nU Bud : ℕ) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (tl w : List Bool)
    (emit : ℕ → List Bool)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n))
    (hcap : cap + 1 ≤ UnaryCalc.value D C n) (hR : nU + 1 ≤ UnaryCalc.value D C n)
    (hboot : bootCost w n D1 C1 ≤ UnaryCalc.value D C n)
    (hdec : ∀ j < UnaryCalc.value D1 C1 n, ∀ out : List Bool, ∃ σD m Bp,
      WExec cap decW (blankCellD W.x w out j (Data.unaryList (Data.symCounts a' Cs carriers))) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧
      cpCost (Data.unaryList (Data.symCounts a' Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU)
    (hB : 2 * shellCostD w n D C D1 C1 D2 C2
      (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (shellMD W decW D C D1 C1 D2 C2) Bud (shellInD W.x D D1 D2) (shellOutD W.x D D1 D2) w
      ((List.range (UnaryCalc.value D1 C1 n)).flatMap emit ++ [false]) := by
  set u := Data.unaryList (Data.symCounts a' Cs carriers) with hu
  obtain ⟨B8, sp, h0, h1, h2, hwk, hl, hd, hk, hdt, hs⟩ :=
    pre_step (x := W.x) (D := D) (D1 := D1) (D2 := D2) Cs carriers tl w C1 C2 hw hD
  obtain ⟨Wk, se⟩ := entry_runD (x := W.x) (D := D) (D1 := D1) (D2 := D2) cap C n (UnaryCalc.value D1 C1 n) w
    (false :: (RepairOrdinary.Streaming.marks u ++ [false])) B8 h0 h1 h2
    (fun c hc => le_trans (hs c hc) hboot) hwk hl hd hk (by rw [hdt, dataWord_eq])
  have sl := (loop_stepD cap W decW (UnaryCalc.value D C n) nU (UnaryCalc.value D1 C1 n) w u Wk emit hcap hR
    hdec).embed (fun _ : Fin (E1 D1 + E2 D2 + E3) => 0) (fun k => B8 (xT k))
  have sl' : Step (loopED W decW D D1 D2) (UnaryCalc.value D1 C1 n * ((2 * nU + 2 + 1 +
      (2 * UnaryCalc.value D C n + 4)) + 3) + 3) (loopHSd W.x D D1 D2 [])
      (loopASd cap W.x D D1 D2 (UnaryCalc.value D C n) w (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0
        (UnaryCalc.value D1 C1 n) [] (fun k => B8 (xT k)))
      (loopHSd W.x D D1 D2 ([] ++ (List.range (UnaryCalc.value D1 C1 n)).flatMap emit))
      (loopASd cap W.x D D1 D2 (UnaryCalc.value D C n) w (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk
        (UnaryCalc.value D1 C1 n) (UnaryCalc.value D1 C1 n)
        ([] ++ (List.range (UnaryCalc.value D1 C1 n)).flatMap emit) (fun k => B8 (xT k))) := sl
  have si := (sp.seq se).seq sl'
  obtain ⟨m, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (STd W.x D D1 D2 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have e2 : (Fin.addCases (B0 w) (fun _ : Fin 1 => List.replicate 0 false) : Fin (STd W.x D D1 D2 + 1) → List Bool) =
      WriterIface.inBank (shellInD W.x D D1 D2) w := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · by_cases ha : a = cs 0
      · subst ha
        simp [B0, WriterIface.inBank, shellInD]
      · have hne : Fin.castAdd 1 a ≠ shellInD W.x D D1 D2 := fun e => ha (Fin.castAdd_injective _ _ e)
        simp [B0, WriterIface.inBank, ha, hne]
    · have hne : Fin.natAdd (STd W.x D D1 D2) u ≠ shellInD W.x D D1 D2 := by
        apply ne_of_val
        simp only [Fin.val_natAdd, shellInD, Fin.val_castAdd]
        have := (cs (x := W.x) (D := D) (D1 := D1) (D2 := D2) 0).isLt
        omega
      simp [WriterIface.inBank, hne]
  have e3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else
      loopHSd W.x D D1 D2 ([] ++ (List.range (UnaryCalc.value D1 C1 n)).flatMap emit) i) (fun _ : Fin 1 => 0) :
      Fin (STd W.x D D1 D2 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  set Tf : Fin (STd W.x D D1 D2 + 1) → List Bool := Fin.addCases (loopASd cap W.x D D1 D2 (UnaryCalc.value D C n) w
    (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value D1 C1 n) (UnaryCalc.value D1 C1 n)
    ([] ++ (List.range (UnaryCalc.value D1 C1 n)).flatMap emit) (fun k => B8 (xT k)))
    (fun _ : Fin 1 => List.replicate m false) with hTf
  have hstep : Step (shellMD W decW D C D1 C1 D2 C2) Bud (fun _ => 0) (WriterIface.inBank (shellInD W.x D D1 D2) w)
      (fun _ => 0) Tf := ((sm.congr_in e1 e2).congr e3 rfl).enlarge (by unfold shellCostD at hB; omega)
  refine ⟨fun j => if j = shellInD W.x D D1 D2 ∨ j = shellOutD W.x D D1 D2 then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : j = shellInD W.x D D1 D2 ∨ j = shellOutD W.x D D1 D2
    · simp [hj]
    · have hin : j ≠ shellInD W.x D D1 D2 := fun e => hj (Or.inl e)
      have := Shell.Step.len hstep j 0 (le_refl _) (by simp [WriterIface.inBank, hin])
      simp only [hj, if_false]
      omega
  · have eo : Tf = WriterIfaceJ.outBankJ (shellInD W.x D D1 D2) (shellOutD W.x D D1 D2) w
        ((List.range (UnaryCalc.value D1 C1 n)).flatMap emit ++ [false])
        (fun j => if j = shellInD W.x D D1 D2 ∨ j = shellOutD W.x D D1 D2 then [] else Tf j) := by
      funext j
      unfold WriterIfaceJ.outBankJ
      by_cases hi : j = shellInD W.x D D1 D2
      · subst hi
        simp only [if_true, hTf, shellInD, Fin.addCases_left]
        exact loopASd_cs0 _ _ _ _ _ _ _ _ _
      · by_cases ho : j = shellOutD W.x D D1 D2
        · subst ho
          rw [if_neg hi, if_pos rfl]
          simp only [hTf, shellOutD, Fin.addCases_left]
          rw [loopASd_cs1, List.nil_append]
        · simp [hi, ho]
    rw [← eo]
    exact Shell.ready_of_step hstep

/-- **The writer shell with per-call data as a `WriterStage`** (request and output ports distinct). -/
noncomputable def shellStageD (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D1 C1 D2 C2 : ℕ) :
    WriterIface.WriterStage :=
  ⟨STd W.x D D1 D2 + 1, _, shellMD W decW D C D1 C1 D2 C2, shellInD W.x D D1 D2, shellOutD W.x D D1 D2,
    shellInD_ne_out⟩

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellD
