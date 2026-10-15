import Proof.Wire_3_5.PrimAsmShellXBoot

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline

section Run
variable {x D D2 Dv DL : ℕ}

/-- The scrub entry, on the real layout. -/
noncomputable def entryEX (x D D2 Dv DL C : ℕ) := TapeEmbedding.machine (EX x D D2 Dv DL) (entryED x D 0 D2 C)

/-- The unit loop with the data tape, on the real layout. -/
noncomputable def loopEX (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D D2 Dv DL : ℕ) :=
  TapeEmbedding.machine (EX W.x D D2 Dv DL) (loopED W decW D 0 D2)

/-- The writer before its teardown. -/
noncomputable def innerMX (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D2 C2 Dv Cv cr DL CL : ℕ) :=
  Composition.machine (Composition.machine (bootXM W.x D D2 Dv DL C2 Cv cr CL) (entryEX W.x D D2 Dv DL C))
    (loopEX W decW D D2 Dv DL)

/-- **ShellX's machine**: the writer under one masked reset. One machine per unit machine and per
`(D, C, D₂, C₂, Dv, Cv, c_r, DL, CL)`, independent of the request. -/
noncomputable def shellMX (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D2 C2 Dv Cv cr DL CL : ℕ) :=
  MaskedReset.machine (innerMX W decW D C D2 C2 Dv Cv cr DL CL) (fun _ => true)

/-- The shell's request port. -/
def shellInX (x D D2 Dv DL : ℕ) : Fin (STx x D D2 Dv DL + 1) := Fin.castAdd 1 (T0 x D D2 Dv DL)

/-- The shell's output port. -/
def shellOutX (x D D2 Dv DL : ℕ) : Fin (STx x D D2 Dv DL + 1) :=
  Fin.castAdd 1 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1))

theorem shellInX_ne_out : shellInX x D D2 Dv DL ≠ shellOutX x D D2 Dv DL := by
  intro h
  have := congrArg Fin.val h
  simp only [shellInX, shellOutX, Fin.val_castAdd, T0_val, lo_val, cs1_val] at this
  omega

/-- The shell's cost before the teardown. -/
def shellCostX (w : List Bool) (n D C D2 C2 cc Dv Cv cr W m DL CL nU : ℕ) : ℕ :=
  bootXCost w n D2 C2 cc Dv Cv cr W m DL CL + 1 + Scrub.entryCost D C (2 ^ m) + 1 +
    (UnaryCalc.value DL CL (2 ^ m) * ((2 * nU + 2 + 1 + (2 * UnaryCalc.value D C (2 ^ m) + 4)) + 3) + 3)

theorem HF_lo (i : Fin (SD x D D2)) : HF x D D2 Dv DL (lo i) = hK x D 0 D2 i := by
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hJ : lo (Dv := Dv) (DL := DL) i ≠ TJ x D D2 Dv DL := by
    intro e
    have := congrArg Fin.val e
    rw [lo_val, TJ_val] at this
    have := i.isLt
    omega
  unfold HF hK
  by_cases hi : i = kT
  · subst hi
    exact (if_pos rfl).trans (if_pos rfl).symm
  · have hne : lo (Dv := Dv) (DL := DL) i ≠ TK x D D2 Dv DL := fun e => hi (lo_inj e)
    rw [if_neg hne, if_neg hJ, if_neg hi]

/-- **ShellX's run** (`WriterIfaceJ.WriterRun`): from `inBank (frame w)` with `w` the SYM call's request word, the
output tape `(List.range b).flatMap emit ++ [false]`, `b = CL(n'+1)^DL`, `n' = 2^(2·kh + L)`, within the budget, all
heads back at `0`, the request kept, residues within the budget; for any unit machine whose decode (after the copy-in
of the call's counts) meets `CellUnit.DecOK` at every unit `j < b` within `nU` steps, with the scrub capacity
`R = C(n'+1)^D`. -/
theorem shell_runX (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (cap D C D2 C2 Dv Cv cr DL CL nU Bud : ℕ)
    {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (emit : ℕ → List Bool) (P : Shared.StarParams) (hPn : P.n = n)
    (hrP : P.r = Ledger.rowBr cr P.n)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n)) (hW : 2 * n + cr + 16 ≤ UnaryCalc.value Dv Cv n)
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hboot : bootCost w n 0 0 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hdec : ∀ j < UnaryCalc.value DL CL (2 ^ NumsX.mOf P), ∀ out : List Bool, ∃ σD m Bp,
      WExec cap decW (blankCellD W.x w out j (Data.unaryList (Data.symCounts a' Cs carriers))) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧
      cpCost (Data.unaryList (Data.symCounts a' Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU)
    (hB : 2 * shellCostX w n D C D2 C2
      (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv cr
      (UnaryCalc.value Dv Cv n) (NumsX.mOf P) DL CL nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (shellMX W decW D C D2 C2 Dv Cv cr DL CL) Bud (shellInX W.x D D2 Dv DL)
      (shellOutX W.x D D2 Dv DL) w ((List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit ++ [false]) := by
  set u := Data.unaryList (Data.symCounts a' Cs carriers) with hu
  obtain ⟨Bf, sb, f0, f1, f2, fscr, fwk, flg, fdr, fk, fdt⟩ :=
    bootX_step (x := W.x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Cs carriers tl w C2 Cv cr CL P hPn hrP hw hD hW
  obtain ⟨Wk, se⟩ := entry_runD (x := W.x) (D := D) (D1 := 0) (D2 := D2) cap C (2 ^ NumsX.mOf P)
    (UnaryCalc.value DL CL (2 ^ NumsX.mOf P)) w (false :: (RepairOrdinary.Streaming.marks u ++ [false]))
    (fun i => Bf (lo i)) f0 f1 f2 (fun c hc => le_trans (fscr c hc) hboot) fwk flg fdr fk (by rw [fdt, dataWord_eq])
  have se2 := se.embed (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k))
    (fun k => Bf (Fin.natAdd _ k))
  have eBf : (Fin.addCases (fun i => Bf (lo i)) (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k)) :
      Fin (STx W.x D D2 Dv DL) → List Bool) = Bf := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun z => ?_) i
    · simp only [Fin.addCases_left]; rfl
    · simp only [Fin.addCases_right]
  have eHF : (Fin.addCases (hK W.x D 0 D2) (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)) :
      Fin (STx W.x D D2 Dv DL) → ℕ) = HF W.x D D2 Dv DL := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun z => ?_) i
    · simp only [Fin.addCases_left]; exact (HF_lo a).symm
    · simp only [Fin.addCases_right]
  have se3 : Step (entryEX W.x D D2 Dv DL C) (Scrub.entryCost D C (2 ^ NumsX.mOf P)) (HF W.x D D2 Dv DL) Bf
      (Fin.addCases (loopHSd W.x D 0 D2 []) (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ NumsX.mOf P)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0 (UnaryCalc.value DL CL (2 ^ NumsX.mOf P)) []
        (fun k => Bf (lo (xT k)))) (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k))) :=
    se2.congr_in eHF eBf
  have sl := ((loop_stepD cap W decW (UnaryCalc.value D C (2 ^ NumsX.mOf P)) nU (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
    w u Wk emit hcap hR hdec).embed (fun _ : Fin (E1 0 + E2 D2 + E3) => 0) (fun k => Bf (lo (xT k)))).embed
    (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)) (fun k => Bf (Fin.natAdd _ k))
  have sl' : Step (loopEX W decW D D2 Dv DL) (UnaryCalc.value DL CL (2 ^ NumsX.mOf P) * ((2 * nU + 2 + 1 +
      (2 * UnaryCalc.value D C (2 ^ NumsX.mOf P) + 4)) + 3) + 3)
      (Fin.addCases (loopHSd W.x D 0 D2 []) (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ NumsX.mOf P)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0 (UnaryCalc.value DL CL (2 ^ NumsX.mOf P)) []
        (fun k => Bf (lo (xT k)))) (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k)))
      (Fin.addCases (loopHSd W.x D 0 D2 ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit))
        (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ NumsX.mOf P)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
        (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
        ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit) (fun k => Bf (lo (xT k))))
        (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k))) := sl
  have si := (sb.seq se3).seq sl'
  obtain ⟨m, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (STx W.x D D2 Dv DL + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have e2 : (Fin.addCases (A0 w) (fun _ : Fin 1 => List.replicate 0 false) : Fin (STx W.x D D2 Dv DL + 1) → List Bool) =
      WriterIface.inBank (shellInX W.x D D2 Dv DL) w := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · by_cases ha : a = T0 W.x D D2 Dv DL
      · subst ha
        simp [A0, WriterIface.inBank, shellInX, T0]
      · have hne : Fin.castAdd 1 a ≠ shellInX W.x D D2 Dv DL := fun e => ha (Fin.castAdd_injective _ _ e)
        have ha' : a ≠ lo (cs 0) := ha
        simp [A0, WriterIface.inBank, ha', hne]
    · have hne : Fin.natAdd (STx W.x D D2 Dv DL) u ≠ shellInX W.x D D2 Dv DL := by
        intro e
        have := congrArg Fin.val e
        simp only [Fin.val_natAdd, shellInX, Fin.val_castAdd] at this
        have := (T0 W.x D D2 Dv DL).isLt
        omega
      simp [WriterIface.inBank, hne]
  have e3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else
      Fin.addCases (loopHSd W.x D 0 D2 ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit))
        (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)) i) (fun _ : Fin 1 => 0) :
      Fin (STx W.x D D2 Dv DL + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  set Tf : Fin (STx W.x D D2 Dv DL + 1) → List Bool := Fin.addCases
    (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ NumsX.mOf P)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
        (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
        ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit) (fun k => Bf (lo (xT k))))
      (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k)))
    (fun _ : Fin 1 => List.replicate m false) with hTf
  have hstep : Step (shellMX W decW D C D2 C2 Dv Cv cr DL CL) Bud (fun _ => 0)
      (WriterIface.inBank (shellInX W.x D D2 Dv DL) w) (fun _ => 0) Tf :=
    ((sm.congr_in e1 e2).congr e3 rfl).enlarge (by unfold shellCostX at hB; omega)
  refine ⟨fun j => if j = shellInX W.x D D2 Dv DL ∨ j = shellOutX W.x D D2 Dv DL then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : j = shellInX W.x D D2 Dv DL ∨ j = shellOutX W.x D D2 Dv DL
    · simp [hj]
    · have hin : j ≠ shellInX W.x D D2 Dv DL := fun e => hj (Or.inl e)
      have := Shell.Step.len hstep j 0 (le_refl _) (by simp [WriterIface.inBank, hin])
      simp only [hj, if_false]
      omega
  · have eo : Tf = WriterIfaceJ.outBankJ (shellInX W.x D D2 Dv DL) (shellOutX W.x D D2 Dv DL) w
        ((List.range (UnaryCalc.value DL CL (2 ^ NumsX.mOf P))).flatMap emit ++ [false])
        (fun j => if j = shellInX W.x D D2 Dv DL ∨ j = shellOutX W.x D D2 Dv DL then [] else Tf j) := by
      funext j
      unfold WriterIfaceJ.outBankJ
      by_cases hi : j = shellInX W.x D D2 Dv DL
      · subst hi
        simp only [if_true, hTf, shellInX, Fin.addCases_left, T0, lo]
        exact loopASd_cs0 _ _ _ _ _ _ _ _ _
      · by_cases ho : j = shellOutX W.x D D2 Dv DL
        · subst ho
          rw [if_neg hi, if_pos rfl]
          simp only [hTf, shellOutX, Fin.addCases_left, lo]
          rw [loopASd_cs1, List.nil_append]
        · simp [hi, ho]
    rw [← eo]
    exact Shell.ready_of_step hstep

/-- **ShellX as a `WriterStage`** (request and output ports distinct). -/
noncomputable def shellStageX (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D2 C2 Dv Cv cr DL CL : ℕ) :
    WriterIface.WriterStage :=
  ⟨STx W.x D D2 Dv DL + 1, _, shellMX W decW D C D2 C2 Dv Cv cr DL CL, shellInX W.x D D2 Dv DL,
    shellOutX W.x D D2 Dv DL, shellInX_ne_out⟩

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellX
