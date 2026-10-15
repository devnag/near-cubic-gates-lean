import Proof.Wire_3_5.PrimAsmSymLayout
import Proof.Wire_3_5.PrimAsmPopCellW
import Proof.Wire_3_5.PrimTWalkBankIface
import Proof.Wire_3_5.FinalPassFlatTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierWalk Theorem25Completion
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-! ## The walk stage -/

section Walk
variable (cap : ℕ) (W : WalkBankProducer)

/-- The walk stage's machine: the producer on the streams `tmapT`. -/
noncomputable def walkM := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tmapT W.x j)) W.M

/-- **The walk stage**: the producer docked on the cell layout's streams. -/
theorem walkStage (σ : WState (LNS W.x) LNR) (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1))
    (hR : 2 * r + 1 ≤ R) (hLW : 2 * r + 1 ≤ LW)
    (hin : ∀ j : Fin 14, σ.st (sk W.x (portT j)) = inPorts r n R LW (seedIndexWord r n sample) j)
    (hh : ∀ j : Fin 14, σ.sh (sk W.x (portT j)) = 0)
    (hsc : ∀ k : Fin W.x, σ.st (sT W.x k) = []) (hsh : ∀ k : Fin W.x, σ.sh (sT W.x k) = 0) :
    ∃ J : Fin W.x → List Bool, (∀ k, (J k).length ≤ walkBankCost r n R LW) ∧
      Step (walkM W) (walkBankCost r n R LW) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (updS (tmapT W.x) σ (Fin.addCases (motive := fun _ => ℕ) (outHeads n) (fun _ => 0))
          (Fin.addCases (motive := fun _ => List Bool) (outPorts r n R LW sample) J))).H
        (wenc cap (updS (tmapT W.x) σ (Fin.addCases (motive := fun _ => ℕ) (outHeads n) (fun _ => 0))
          (Fin.addCases (motive := fun _ => List Bool) (outPorts r n R LW sample) J))).A := by
  obtain ⟨J, hJ, hs⟩ := W.run r n R LW sample hR hLW
  have e1 : (fun _ : Fin (14 + W.x) => (0 : ℕ)) = fun j => σ.sh (tmapT W.x j) := by
    funext j
    refine Fin.addCases (fun j1 => ?_) (fun k => ?_) j
    · simp only [tmapT, Fin.addCases_left]
      exact (hh j1).symm
    · simp only [tmapT, Fin.addCases_right]
      exact (hsh k).symm
  have e2 : Fin.addCases (motive := fun _ => List Bool) (inPorts r n R LW (seedIndexWord r n sample))
      (fun _ => []) = fun j => σ.st (tmapT W.x j) := by
    funext j
    refine Fin.addCases (fun j1 => ?_) (fun k => ?_) j
    · simp only [tmapT, Fin.addCases_left]
      exact (hin j1).symm
    · simp only [tmapT, Fin.addCases_right]
      exact (hsc k).symm
  rw [e1, e2] at hs
  exact ⟨J, hJ, dockS cap (tmapT W.x) (tmapT_inj W.x) σ hs⟩

end Walk

section WalkReads
variable {x : ℕ}

theorem tmapT_port (j : Fin 14) : tmapT x (Fin.castAdd x j) = sk x (portT j) := by
  simp only [tmapT, Fin.addCases_left]

theorem tmapT_ne (k : Fin 161) (hk : ∀ j : Fin 14, portT j ≠ k) (j : Fin (14 + x)) : tmapT x j ≠ sk x k := by
  refine Fin.addCases (fun j1 => ?_) (fun k' => ?_) j
  · rw [tmapT_port]
    exact fun h => hk j1 (sk_inj x h)
  · simp only [tmapT, Fin.addCases_right]
    exact fun h => sk_ne_sT x k k' h.symm

theorem updT_st_port (σ : WState (LNS x) LNR) (hout : Fin (14 + x) → ℕ) (tout : Fin (14 + x) → List Bool)
    (j : Fin 14) : (updS (tmapT x) σ hout tout).st (sk x (portT j)) = tout (Fin.castAdd x j) := by
  show install (tmapT x) σ.st tout (sk x (portT j)) = _
  rw [← tmapT_port]
  exact install_slot _ (tmapT_inj x) _ _ _

theorem updT_sh_port (σ : WState (LNS x) LNR) (hout : Fin (14 + x) → ℕ) (tout : Fin (14 + x) → List Bool)
    (j : Fin 14) : (updS (tmapT x) σ hout tout).sh (sk x (portT j)) = hout (Fin.castAdd x j) := by
  show dockH (tmapT x) σ.sh hout (sk x (portT j)) = _
  rw [← tmapT_port]
  exact dockH_slot _ (tmapT_inj x) _ _ _

theorem updT_st_other (σ : WState (LNS x) LNR) (hout : Fin (14 + x) → ℕ) (tout : Fin (14 + x) → List Bool)
    (k : Fin 161) (hk : ∀ j : Fin 14, portT j ≠ k) : (updS (tmapT x) σ hout tout).st (sk x k) = σ.st (sk x k) :=
  install_other _ _ _ _ (tmapT_ne k hk)

theorem updT_sh_other (σ : WState (LNS x) LNR) (hout : Fin (14 + x) → ℕ) (tout : Fin (14 + x) → List Bool)
    (k : Fin 161) (hk : ∀ j : Fin 14, portT j ≠ k) : (updS (tmapT x) σ hout tout).sh (sk x k) = σ.sh (sk x k) :=
  dockH_other _ _ _ _ (tmapT_ne k hk)

theorem updT_val (σ : WState (LNS x) LNR) (hout : Fin (14 + x) → ℕ) (tout : Fin (14 + x) → List Bool) :
    (updS (tmapT x) σ hout tout).val = σ.val := rfl

theorem updT_cell (σ : WState (LNS x) LNR) (hout : Fin (14 + x) → ℕ) (tout : Fin (14 + x) → List Bool) :
    (updS (tmapT x) σ hout tout).cell = σ.cell := rfl

end WalkReads

/-! ## The table stage -/

section Build
open NearCubicWires.WireExponent3_5.FinalPass.Flat
variable (cap : ℕ) (x : ℕ)

/-- The table stage's machine: C5's builder docked by `dockW`. -/
noncomputable def buildM := RecoveryFocus.machine (wq (fsC x) frC (emC x)) builderML

/-- **The table stage**: C5's builder docked on the cell layout. -/
theorem buildStage (σ : WState (LNS x) LNR) (m lb L tf nJ : ℕ) {n : ℕ} (R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ m) (n + 1)) (hR : 2 * m + 1 ≤ R) (hLW : 2 * m + 1 ≤ LW)
    (hpad : tf ≤ 1) (hps : tf ≤ m) (hsd : 2 * lb - 1 + lb ≤ 2 * m - tf) (hlb : 1 ≤ lb) (hnJ : nJ ≤ lb + 1)
    (hcap : 8 * m + 8 * lb + 8 ≤ cap) (hO : (n + 1) * (1 + nJ * (2 * L + 1)) + 7 < cap)
    (hsh : ∀ i, σ.sh (fsC x i) = (canonAt m lb L tf nJ R LW sample [] 0 (owAt m lb L tf nJ sample 0)).w.sh i)
    (hst : ∀ i, σ.st (fsC x i) = (canonAt m lb L tf nJ R LW sample [] 0 (owAt m lb L tf nJ sample 0)).w.st i)
    (hv : ∀ r, σ.val (frC r) = (canonAt m lb L tf nJ R LW sample [] 0 (owAt m lb L tf nJ sample 0)).w.val r)
    (hc : σ.cell = (canonAt m lb L tf nJ R LW sample [] 0 (owAt m lb L tf nJ sample 0)).w.cell)
    (hqh : ∀ k, σ.sh (emC x k) =
      Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n 0 k.succ.succ) (fun _ => 1) k)
    (hqt : ∀ k, σ.st (emC x k) =
      Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool) (fun k => WalkTimeLoop.A R LW sample [] 0 k.succ.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n) k) :
    Step (buildM x) (n * (bodyCostL m lb L nJ R + 3) + 3 + 1 + lastCostL m lb L nJ n) (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updW (fsC x) frC (emC x) σ
        (finalWL m lb L tf nJ (swAt m tf sample (n + 1)) (WalkTimeLoop.A R LW sample [] n 0)
          (WalkTimeLoop.A R LW sample [] n 1) (owAt m lb L tf nJ sample (n + 1) ++ [false]))
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n n k.succ.succ) (fun _ => 1))
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample [] n k.succ.succ)
          (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n)))).H
      (wenc cap (updW (fsC x) frC (emC x) σ
        (finalWL m lb L tf nJ (swAt m tf sample (n + 1)) (WalkTimeLoop.A R LW sample [] n 0)
          (WalkTimeLoop.A R LW sample [] n 1) (owAt m lb L tf nJ sample (n + 1) ++ [false]))
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n n k.succ.succ) (fun _ => 1))
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample [] n k.succ.succ)
          (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n)))).A := by
  have hb := builderStepL cap m lb L tf nJ R LW sample [] hR hLW hpad hps hsd hlb hnJ hcap hO
  have e1 : Fin.addCases (m := 11 + 2 + 19 + 6) (n := 1) (motive := fun _ => ℕ)
      (loopHL cap m lb L tf nJ R LW sample [] 0) (fun _ : Fin 1 => 1) =
      Fin.addCases (m := 11 + 2 + 19) (n := 7) (motive := fun _ => ℕ)
        (wenc cap (canonAt m lb L tf nJ R LW sample [] 0 (owAt m lb L tf nJ sample 0)).w).H
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n 0 k.succ.succ)
          (fun _ => 1)) := by
    unfold loopHL cHL
    exact addCases_assoc6 _ _ _
  have e2 : Fin.addCases (m := 11 + 2 + 19 + 6) (n := 1) (motive := fun _ => List Bool)
      (loopAL cap m lb L tf nJ R LW sample [] 0) (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word n) =
      Fin.addCases (m := 11 + 2 + 19) (n := 7) (motive := fun _ => List Bool)
        (wenc cap (canonAt m lb L tf nJ R LW sample [] 0 (owAt m lb L tf nJ sample 0)).w).A
        (Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample [] 0 k.succ.succ)
          (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n)) := by
    unfold loopAL cAL
    exact addCases_assoc6 _ _ _
  rw [e1, e2] at hb
  exact dockW cap (fsC x) frC (emC x) (gsC_inj x) frC_inj σ _ _ _ _ _ _ hb hsh hst hv hc hqh hqt

end Build

/-! ## The POP row stage -/

section PopRowS
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
variable (cap : ℕ) {x : ℕ}

theorem eI6_val : (eI (negFam F35).t 6).val = 44 := rfl

theorem IPL_val : IPL (negFam F35).t = 47 := rfl

theorem IPL1 : IPL (negFam F35).t + 1 = 48 := rfl

variable (x) in
/-- The POP row machine's tapes on the cell layout (`tmapP` at the machine's own index type). -/
noncomputable def tmapQ (j : Fin (IPL (negFam F35).t + 1)) : Fin (LNS x + 1) := tmapP x (Fin.cast IPL1 j)

theorem tmapQ_inj : Function.Injective (tmapQ x) := fun a b h => by
  have h1 := tmapP_inj x h
  exact Fin.ext (congrArg Fin.val h1)

theorem tmapQ_in : tmapQ x (Fin.castAdd 1 (inQ (negFam F35).t)) = sk x 3 := congrArg (sk x) (Fin.ext rfl)

theorem tmapQ_out : tmapQ x (Fin.castAdd 1 (pQ (negFam F35).t (eI (negFam F35).t 6))) = sk x 1 :=
  congrArg (sk x) (Fin.ext rfl)

theorem overlay_self (out : List Bool) : overlay out (out ++ [false]) = out ++ [false] := by
  unfold overlay
  rw [List.drop_left]

theorem overlay_ext (out w : List Bool) (hw : 1 ≤ w.length) : overlay (out ++ w) (out ++ [false]) = out ++ w := by
  unfold overlay
  rw [List.drop_eq_nil_of_le (by simp; omega), List.append_nil]

theorem popRow_entryH (σ : WState (LNS x) LNR) (out : List Bool) (hrec0 : σ.sh (sk x 3) = 0)
    (houth : σ.sh (sk x 1) = out.length)
    (hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      σ.st (tmapQ x j) = [] ∧ σ.sh (tmapQ x j) = 0) :
    (Fin.addCases (motive := fun _ => ℕ) (qH (negFam F35).t ([] : List Bool).length
      (popH (negFam F35).t 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0)) =
      fun j => σ.sh (tmapQ x j) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun z => ?_) j
  · rw [Fin.addCases_left]
    rcases qcover _ a with rfl | ⟨i, rfl⟩
    · rw [qH_in, tmapQ_in, hrec0]
      rfl
    · rw [qH_p]
      by_cases hi : i = eI _ 6
      · subst hi
        rw [popH_eI, tmapQ_out, houth]
        rfl
      · have h44 : i.val ≠ 44 := fun h => hi (Fin.ext (h.trans eI6_val.symm))
        rw [popH_zero_other _ _ i hi]
        exact (hscr _ (by simp only [Fin.val_castAdd, pQ_val]; omega)
          (by simp only [Fin.val_castAdd, pQ_val]; omega)).2.symm
  · rw [Fin.addCases_right]
    exact (hscr _ (by simp only [Fin.val_natAdd, IPL_val]; omega)
      (by simp only [Fin.val_natAdd, IPL_val]; omega)).2.symm

theorem popRow_entryA (σ : WState (LNS x) LNR) (rec out : List Bool) (hrec : σ.st (sk x 3) = frame rec)
    (hout : σ.st (sk x 1) = out ++ [false])
    (hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      σ.st (tmapQ x j) = [] ∧ σ.sh (tmapQ x j) = 0) :
    (Fin.addCases (motive := fun _ => List Bool) (qA (negFam F35).t ([] ++ frame rec ++ [])
      (entryA (negFam F35).t out (out ++ [false]))) (fun _ : Fin 1 => [])) = fun j => σ.st (tmapQ x j) := by
  funext j
  refine Fin.addCases (fun a => ?_) (fun z => ?_) j
  · rw [Fin.addCases_left]
    rcases qcover _ a with rfl | ⟨i, rfl⟩
    · rw [qA_in, tmapQ_in, hrec, List.nil_append, List.append_nil]
    · rw [qA_p]
      unfold entryA
      by_cases hi : i = eI _ 6
      · subst hi
        rw [if_pos rfl, tmapQ_out, hout, overlay_self]
      · have h44 : i.val ≠ 44 := fun h => hi (Fin.ext (h.trans eI6_val.symm))
        rw [if_neg hi]
        exact (hscr _ (by simp only [Fin.val_castAdd, pQ_val]; omega)
          (by simp only [Fin.val_castAdd, pQ_val]; omega)).1.symm
  · rw [Fin.addCases_right]
    exact (hscr _ (by simp only [Fin.val_natAdd, IPL_val]; omega)
      (by simp only [Fin.val_natAdd, IPL_val]; omega)).1.symm

variable (x) in
/-- The POP row stage's machine: C2's POP row machine on the streams `tmapQ`. -/
noncomputable def popRowDM := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tmapQ x j)) (popRowM (negFam F35))

theorem exprWord_len (ex : ListMachine.Expr) : 1 ≤ (ListMachine.Rec.exprWord ex).length := by
  unfold ListMachine.Rec.exprWord
  simp

/-- **The POP row stage**: C2's POP row machine (at any capacities its states satisfy) docked on the cell layout,
the record on the record stream and the output `out ++ [false]` with its head at `|out|`: the output becomes
`out ++ exprWord (popRefC …)` with its head after it. -/
theorem popRowStage (σ : WState (LNS x) LNR) (Pl : FlatListParams) (e : Pl.FlatSeed) (L : ℕ) (sgn : Bool)
    (labs : List ℕ) (hlabs : 4 * L ≤ labs.length)
    (hnest : ∀ h j i, Pl.base.inLevel h (j + 1) i = true → Pl.base.inLevel h j i = true) (s : Fin (Pl.M + 1))
    (R Lg cp : ℕ) (hR1 : 1 ≤ R) (hL : R + 1 ≤ Lg)
    (hok : ∀ st ∈ popStates Pl e L sgn labs hlabs s, StateOk Pl.walkLen R cp st) (out : List Bool)
    (hrec : σ.st (sk x 3) = frame (popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R Lg cp
      (oneWC Pl s) (popStates Pl e L sgn labs hlabs s)))
    (hrec0 : σ.sh (sk x 3) = 0) (hout : σ.st (sk x 1) = out ++ [false]) (houth : σ.sh (sk x 1) = out.length)
    (hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      σ.st (tmapQ x j) = [] ∧ σ.sh (tmapQ x j) = 0) :
    ∃ Ho To, Step (popRowDM x) (popRowCost Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R Lg cp
        (oneWC Pl s) (popStates Pl e L sgn labs hlabs s))
        (wenc cap σ).H (wenc cap σ).A (wenc cap (updS (tmapQ x) σ Ho To)).H (wenc cap (updS (tmapQ x) σ Ho To)).A ∧
      (updS (tmapQ x) σ Ho To).st (sk x 1) = out ++ ListMachine.Rec.exprWord (popRefC Pl e L sgn labs s) ∧
      (updS (tmapQ x) σ Ho To).sh (sk x 1) = (out ++ ListMachine.Rec.exprWord (popRefC Pl e L sgn labs s)).length := by
  have hrec' : σ.st (sk x 3) = frame (popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R Lg cp
      ((popOne Pl s.val).flatMap fun t => true :: ListMachine.Rec.termWord t) (popStates Pl e L sgn labs hlabs s)) :=
    hrec
  obtain ⟨⟨A', hs, -, hA'⟩, -⟩ :=
    popRow_correct Pl e L sgn labs hlabs hnest s [] [] out (out ++ [false]) R Lg cp hR1 hL hok
  rw [popRow_entryH σ out hrec0 houth hscr, popRow_entryA σ _ out hrec' hout hscr] at hs
  refine ⟨_, A', dockS cap (tmapQ x) tmapQ_inj σ hs, ?_, ?_⟩
  · show install (tmapQ x) σ.st A' (sk x 1) = _
    rw [← tmapQ_out (x := x), install_slot _ tmapQ_inj, hA', popExprOf_eq, overlay_ext out _ (exprWord_len _)]
  · dsimp only [updS]
    rw [← tmapQ_out (x := x), dockH_slot _ tmapQ_inj, Fin.addCases_left, qH_p, popH_eI, popExprOf_eq]
    rfl

end PopRowS

/-! ## Transports across the table stage, and the table's form -/

section BuildReads
variable {x : ℕ}

theorem gsC_val (c : Fin (12 + 7)) :
    (gs (fsC x) (emC x) c).val = if c.val < 12 then 5 + c.val else 17 + (c.val - 12) := by
  refine Fin.addCases (fun c1 => ?_) (fun c2 => ?_) c
  · simp only [gs, Fin.addCases_left, fsC, sk_val, Fin.val_castAdd]
    rw [if_pos c1.isLt]
  · simp only [gs, Fin.addCases_right, emC, sk_val, Fin.val_natAdd]
    rw [if_neg (by omega)]
    omega

theorem gsC_ne (k : Fin 161) (hk : k.val < 5 ∨ 23 < k.val) (c : Fin (12 + 7)) : gs (fsC x) (emC x) c ≠ sk x k := by
  intro h
  have hv := congrArg Fin.val h
  rw [gsC_val, sk_val] at hv
  have := c.isLt
  split_ifs at hv <;> omega

theorem updC_st_other (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (k : Fin 161) (hk : k.val < 5 ∨ 23 < k.val) :
    (updW (fsC x) frC (emC x) σ y hq tq).st (sk x k) = σ.st (sk x k) :=
  install_other _ _ _ _ (gsC_ne k hk)

theorem updC_sh_other (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (k : Fin 161) (hk : k.val < 5 ∨ 23 < k.val) :
    (updW (fsC x) frC (emC x) σ y hq tq).sh (sk x k) = σ.sh (sk x k) :=
  dockH_other _ _ _ _ (gsC_ne k hk)

theorem updC_st_T (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (k : Fin x) : (updW (fsC x) frC (emC x) σ y hq tq).st (sT x k) = σ.st (sT x k) :=
  install_other _ _ _ _ fun c h => by
    have hv := congrArg Fin.val h
    rw [gsC_val, sT_val] at hv
    split_ifs at hv <;> omega

theorem updC_sh_T (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (k : Fin x) : (updW (fsC x) frC (emC x) σ y hq tq).sh (sT x k) = σ.sh (sT x k) :=
  dockH_other _ _ _ _ fun c h => by
    have hv := congrArg Fin.val h
    rw [gsC_val, sT_val] at hv
    split_ifs at hv <;> omega

theorem updC_st_fs (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (i : Fin 12) : (updW (fsC x) frC (emC x) σ y hq tq).st (fsC x i) = y.st i := by
  show install (gs (fsC x) (emC x)) σ.st _ (fsC x i) = _
  have e : fsC x i = gs (fsC x) (emC x) (Fin.castAdd 7 i) := by simp only [gs, Fin.addCases_left]
  rw [e, install_slot _ (gsC_inj x), Fin.addCases_left]

theorem updC_sh_fs (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (i : Fin 12) : (updW (fsC x) frC (emC x) σ y hq tq).sh (fsC x i) = y.sh i := by
  show dockH (gs (fsC x) (emC x)) σ.sh _ (fsC x i) = _
  have e : fsC x i = gs (fsC x) (emC x) (Fin.castAdd 7 i) := by simp only [gs, Fin.addCases_left]
  rw [e, dockH_slot _ (gsC_inj x), Fin.addCases_left]

theorem updC_val_other (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool)
    (r : Fin LNR) (hr : 19 ≤ r.val) : (updW (fsC x) frC (emC x) σ y hq tq).val r = σ.val r :=
  dockH_other _ _ _ _ fun r' h => by
    have hv := congrArg Fin.val h
    have e : (frC r').val = r'.val := rfl
    rw [e] at hv
    have := r'.isLt
    omega

theorem updC_cell (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 7 → ℕ) (tq : Fin 7 → List Bool) :
    (updW (fsC x) frC (emC x) σ y hq tq).cell = y.cell := rfl

end BuildReads

section TableForm
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.PopRecW
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink

/-- **C5's table is the record writer's table word, closed** (`Flat.flatTable`, `PopRecW.tableW`). -/
theorem flatTable_eq (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) :
    FinalPass.Flat.flatTable P e L = tableW P.walkLen P.base.J (rowKP P e L) ++ [false] := by
  unfold FinalPass.Flat.flatTable tableW
  congr 1
  refine finRange_flatMap _ _ fun k => ?_
  unfold rowKP
  rw [dif_pos k.isLt]
  rfl

end TableForm

/-! ## Index facts for the pipeline -/

section Idx
open NearCubicWires.WireExponent3_5.ListMachine.Row
variable {x : ℕ}

theorem sk_ne (a b : Fin 161) (h : a ≠ b) : sk x a ≠ sk x b := fun e => h (sk_inj x e)

theorem portT_ne_fs : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 2 → ∀ j : Fin 14, (portT j).val ≠ 5 + i.val := by decide

theorem portT_le : ∀ j : Fin 14, (portT j).val ≤ 28 := by decide

theorem portT_bank : ∀ k : Fin 7, (portT ⟨k.val + 2, by omega⟩).val = 17 + k.val := by decide

theorem fsC0 : fsC x 0 = sk x (portT 0) := congrArg (sk x) (Fin.ext rfl)

theorem fsC2 : fsC x 2 = sk x (portT 1) := congrArg (sk x) (Fin.ext rfl)

theorem fsC1 : fsC x 1 = sk x 6 := congrArg (sk x) (Fin.ext rfl)

theorem emC_port (k : Fin 7) : emC x k = sk x (portT ⟨k.val + 2, by omega⟩) :=
  congrArg (sk x) (Fin.ext (portT_bank k).symm)

theorem portP_cast_val (j : Fin (IPL (negFam F35).t + 1)) (h0 : j.val ≠ 0) (h45 : j.val ≠ 45) :
    (portP (Fin.cast IPL1 j)).val = 29 + j.val := by
  rw [portP_val, Fin.val_cast, if_neg h0, if_neg h45]

theorem tmapQ_ne (k : Fin 161) (hk : k.val = 0 ∨ k.val = 2) (j : Fin (IPL (negFam F35).t + 1)) :
    tmapQ x j ≠ sk x k := by
  intro h
  have hv := congrArg Fin.val h
  have e : (tmapQ x j).val = (portP (Fin.cast IPL1 j)).val := rfl
  rw [e, portP_val, Fin.val_cast, sk_val] at hv
  split_ifs at hv <;> omega

theorem outHeads_bank (n : ℕ) (k : Fin 7) :
    outHeads n ⟨k.val + 2, by omega⟩ =
      Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n 0 k.succ.succ) (fun _ => 1) k := by
  fin_cases k <;> rfl

theorem outPorts_bank (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) (k : Fin 7) :
    outPorts r n R LW sample ⟨k.val + 2, by omega⟩ =
      Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool) (fun k => WalkTimeLoop.A R LW sample [] 0 k.succ.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n) k := by
  fin_cases k <;> rfl

end Idx

/-! ## C5's builder states at the list's numbers -/

section YC
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists

/-- C5's builder state before the first visit, at the list's numbers. -/
noncomputable def yC (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) : WState 11 19 :=
  (canonAt (n := 2 * (Pl.errExp / 4)) (sideB Pl.base.rank) Pl.base.rank L (padB Pl.base.rank) (Pl.base.J + 1) R LW e []
    0 (owAt (n := 2 * (Pl.errExp / 4)) (sideB Pl.base.rank) Pl.base.rank L (padB Pl.base.rank) (Pl.base.J + 1) e 0)).w

theorem yC_st0 (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) :
    (yC Pl e L R LW).st 0 = WalkTimeLoop.A (r := sideB Pl.base.rank) (n := 2 * (Pl.errExp / 4)) R LW e [] 0 0 := rfl

theorem yC_st2 (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) :
    (yC Pl e L R LW).st 2 = WalkTimeLoop.A (r := sideB Pl.base.rank) (n := 2 * (Pl.errExp / 4)) R LW e [] 0 1 := rfl

theorem yC_sh (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) (i : Fin 12) : (yC Pl e L R LW).sh i = 0 := by
  fin_cases i <;> simp [yC, LSt.w, canonAt, canonL, owAt]

/-- C5's builder state after the last visit (the table on stream `1`, its head at `0`). -/
noncomputable def yF (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) : WState 11 19 :=
  finalWL (sideB Pl.base.rank) Pl.base.rank L (padB Pl.base.rank) (Pl.base.J + 1)
    (swAt (n := 2 * (Pl.errExp / 4)) (sideB Pl.base.rank) (padB Pl.base.rank) e (2 * (Pl.errExp / 4) + 1))
    (WalkTimeLoop.A (r := sideB Pl.base.rank) (n := 2 * (Pl.errExp / 4)) R LW e [] (2 * (Pl.errExp / 4)) 0)
    (WalkTimeLoop.A (r := sideB Pl.base.rank) (n := 2 * (Pl.errExp / 4)) R LW e [] (2 * (Pl.errExp / 4)) 1)
    (owAt (n := 2 * (Pl.errExp / 4)) (sideB Pl.base.rank) Pl.base.rank L (padB Pl.base.rank) (Pl.base.J + 1) e
      (2 * (Pl.errExp / 4) + 1) ++ [false])

theorem yF_st1 (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) (hr : 1 ≤ Pl.base.rank) :
    (yF Pl e L R LW).st 1 =
      PopRecW.tableW Pl.walkLen Pl.base.J (PopLink.rowKP Pl e L) ++ [false] := by
  have hft := owAt_flatTable Pl e L hr
  rw [flatTable_eq] at hft
  exact hft

theorem yF_sh1 (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ) : (yF Pl e L R LW).sh 1 = 0 := by
  simp [yF, finalWL]

end YC

/-! ## The whole pipeline -/

section Pipe
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.PrimAsm.PopCellW
open NearCubicWires.WireExponent3_5.PrimAsm.PopRecW NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.WireExponent3_5.PrimAsm.PopCellNum NearCubicWires.WireExponent3_5.PrimAsm.PopBlockW
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.PrimAsm.PopParams
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW NearCubicWires.WireExponent3_5.PrimAsm.Arith
variable (cap : ℕ) (W : WalkBankProducer)

variable (x : ℕ) in
/-- The record stage's machine: the POP cell's word program compiled. -/
noncomputable def cellM := (popCellW Pe (sk x 3) (sk x 6) (sk x 4)).toProg.compile

variable (x : ℕ) in
/-- The output head, one cell back. -/
noncomputable def bwdM := (WM.bwd (ns := LNS x) (nr := LNR) (sk x 1)).toProg.compile

/-- **The POP cell's pipeline machine**: walk, table, record, POP row, output head back. -/
noncomputable def popPipeM := Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (walkM W) (buildM W.x)) (cellM W.x)) (popRowDM W.x)) (bwdM W.x)

theorem exprWord_eq (ex : ListMachine.Expr) :
    ListMachine.Rec.exprWord ex = ex.flatMap (fun t => true :: ListMachine.Rec.termWord t) ++ [false] := rfl

theorem portT_ge : ∀ j : Fin 14, 5 ≤ (portT j).val := by decide

theorem Pe_ge (j : Fin 200) : 19 ≤ (Pe j).val := by
  rw [Pe_val]
  omega

theorem Xe_ge (k : Fin 64) : 19 ≤ (Xe Pe k).val := by
  rw [Xe_apply, Pe_val]
  omega

/-- A bound on the POP pipeline's cost. -/
noncomputable def popPipeBound (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off Mlab lw R cp RW LW : ℕ)
    (sgn : Bool) (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) : ℕ :=
  walkBankCost (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW + 1 +
    ((2 * (Pl.errExp / 4)) * (bodyCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1) RW + 3) + 3 + 1 +
      lastCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1) (2 * (Pl.errExp / 4))) + 1 +
    popCellBound cap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.M L r4 G off
      Pl.walkLen (3 * lbP Pl) Mlab lw (SupplierWalk.majorityThreshold Pl.walkLen) R cp (capP Pl L)
      (frame (popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R (R + 1) cp (oneWC Pl s)
        (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s))).length + 1 +
    popRowCost Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R (R + 1) cp (oneWC Pl s)
      (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s) + 1 + 1

/-- **The POP cell's pipeline**: from a POP-ready state (the walk-bank producer's inputs, C5's builder state, the
POP cell's numbers in its register block, the record stream empty, the output `out ++ [false]` at `|out|`), the
output becomes `out ++ body ++ [false]` at `|out ++ body|`, `body` the POP row's printed expression
(`popRefC`, C2's reference expression of the population point); the request and counter streams are kept. -/
theorem popPipe (σ : WState (LNS W.x) LNR) (out : List Bool)
    (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off Mlab lw CAP LL R cp RW LW : ℕ) (sgn : Bool)
    (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length)
    (hlen : (sliceLabs r4 G off L).length = 4 * L)
    (hnest : ∀ h j i, Pl.base.inLevel h (j + 1) i = true → Pl.base.inLevel h j i = true)
    (hlw : lw = lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J L + Pl.M + 2)
    (hCAP : CAP = labSum (sliceLabs r4 G off L)) (hLL : LL = ((sliceLabs r4 G off L).flatMap labE).length)
    (hR : R = PopCap.popKc L (3 * lbP Pl) (capP Pl L) CAP (PopNums.blF L (3 * lbP Pl) (capP Pl L) CAP LL lw Pl.M) + 1)
    (hcp : cp = PopCap.popCapB Pl.walkLen R (PopCap.popPW L (3 * lbP Pl) Mlab))
    (hok : ∀ st ∈ popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s, StateOk Pl.walkLen R cp st)
    (hRW : 2 * sideB Pl.base.rank + 1 ≤ RW) (hLW : 2 * sideB Pl.base.rank + 1 ≤ LW)
    (hpad : padB Pl.base.rank ≤ 1) (hps : padB Pl.base.rank ≤ sideB Pl.base.rank)
    (hsd : 2 * Pl.base.rank - 1 + Pl.base.rank ≤ 2 * sideB Pl.base.rank - padB Pl.base.rank)
    (hlb : 1 ≤ Pl.base.rank) (hnJ : Pl.base.J + 1 ≤ Pl.base.rank + 1)
    (hcapC : 8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap)
    (hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap)
    (hout : σ.st (sk W.x 1) = out ++ [false]) (houth : σ.sh (sk W.x 1) = out.length)
    (hrec : σ.st (sk W.x 3) = []) (hrec0 : σ.sh (sk W.x 3) = 0) (hD : σ.sh (sk W.x 4) = (σ.st (sk W.x 4)).length)
    (hin : ∀ j : Fin 14, σ.st (sk W.x (portT j)) = inPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW
      (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e) j)
    (hh : ∀ j : Fin 14, σ.sh (sk W.x (portT j)) = 0)
    (hsc : ∀ k : Fin W.x, σ.st (sT W.x k) = []) (hsh : ∀ k : Fin W.x, σ.sh (sT W.x k) = 0)
    (hC5 : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 2 →
      σ.st (fsC W.x i) = (yC Pl e L RW LW).st i ∧ σ.sh (fsC W.x i) = 0)
    (hC5r : ∀ r, σ.val (frC r) = (yC Pl e L RW LW).val r) (hcell : σ.cell = (yC Pl e L RW LW).cell)
    (hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      σ.st (tmapQ W.x j) = [] ∧ σ.sh (tmapQ W.x j) = 0)
    (h0 : σ.val (Xe Pe 0) = 0) (h1 : σ.val (Xe Pe 1) = r4) (h2 : σ.val (Xe Pe 2) = G) (h3 : σ.val (Xe Pe 3) = off)
    (h4 : σ.val (Xe Pe 4) = L)
    (h20 : σ.val (Xe Pe 20) = CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B))
    (h21 : σ.val (Xe Pe 21) = Pl.base.J) (h44 : σ.val (Xe Pe 44) = Pl.M) (h45 : σ.val (Xe Pe 45) = L)
    (h50 : σ.val (Xe Pe 50) = if sgn then 1 else 0) (h52 : σ.val (Xe Pe 52) = Pl.walkLen)
    (h53 : σ.val (Xe Pe 53) = SupplierWalk.majorityThreshold Pl.walkLen) (h63 : σ.val (Xe Pe 63) = s.val)
    (hzA : ∀ k : Fin 64, (5 ≤ k.val ∧ k.val ≤ 19) ∨ (22 ≤ k.val ∧ k.val ≤ 43) ∨ (46 ≤ k.val ∧ k.val ≤ 49) ∨
      k.val = 51 ∨ (54 ≤ k.val ∧ k.val ≤ 62) → σ.val (Xe Pe k) = 0)
    (hz : ∀ j : Fin 200, 64 ≤ j.val → j.val ≤ 170 → σ.val (Pe j) = 0) (h180 : σ.val (Pe 180) = Mlab)
    (hM : off + L + (r4 + 4) * G ≤ Mlab)
    (hcap : lvCap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.base.J ≤ cap)
    (hdc : 3 * lbP Pl ≤ cap) (hJc : Pl.base.J + 1 ≤ cap)
    (hSc : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤ cap) (hlwc : lw ≤ cap) (hMc : Pl.M ≤ cap)
    (hcL : 4 * L ≤ cap)
    (hcap3 : L * (4 * (4 * Mlab + 4)) + 5 + L * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) +
      4 * (2 * Mlab + 10) + 7 * Mlab + r4 + G + off + L + 20 ≤ cap) (hac3 : CAP + LL ≤ cap)
    (hQc : (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) + 2 ≤ cap) (hc4 : capP Pl L + 8 ≤ cap)
    (hin2 : L + capP Pl L + Pl.M + Mlab + Pl.walkLen ≤ cap)
    (hnum : ∀ i, evalL (vIn L (3 * lbP Pl) (capP Pl L) CAP LL Pl.M Mlab Pl.walkLen lw ((8 * L + 2) ^ (3 * lbP Pl)))
      PopNums.numOps i ≤ cap)
    (h2c : 2 ≤ cap) (hcV : (Pl.base.J + 1) * (2 * L + 1) + 1 ≤ cap)
    (hcT : Pl.walkLen * ((Pl.base.J + 1) * (2 * L + 1) + 1) ≤ cap)
    (hθc : SupplierWalk.majorityThreshold Pl.walkLen ≤ cap) (hRc1 : R + 1 ≤ cap) (hcpc : cp ≤ cap)
    (hbig : (frame (popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) R (R + 1) cp (oneWC Pl s)
      (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s))).length + 2 + labCapA (4 * L) (3 * lbP Pl) +
      (pieceA (4 * L) (3 * lbP Pl)).length + labCapB r4 G off L Mlab ≤ cap) :
    ∃ σF m, Step (popPipeM W) m (wenc cap σ).H (wenc cap σ).A (wenc cap σF).H (wenc cap σF).A ∧
      σF.st (sk W.x 1) = out ++ (popRefC Pl e L sgn (sliceLabs r4 G off L) s).flatMap
        (fun t => true :: ListMachine.Rec.termWord t) ++ [false] ∧
      σF.sh (sk W.x 1) = (out ++ (popRefC Pl e L sgn (sliceLabs r4 G off L) s).flatMap
        (fun t => true :: ListMachine.Rec.termWord t)).length ∧
      (∀ k : Fin 161, (k.val = 0 ∨ k.val = 2) → σF.st (sk W.x k) = σ.st (sk W.x k) ∧ σF.sh (sk W.x k) = σ.sh (sk W.x k)) ∧
      m ≤ popPipeBound cap Pl e L r4 G off Mlab lw R cp RW LW sgn s hlabs := by
  -- the walk stage
  obtain ⟨J, -, sB⟩ := walkStage cap W σ (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW e hRW hLW hin hh hsc hsh
  obtain ⟨σB, hσB⟩ : ∃ τ, τ = updS (tmapT W.x) σ (Fin.addCases (motive := fun _ => ℕ)
      (outHeads (2 * (Pl.errExp / 4))) (fun _ => 0)) (Fin.addCases (motive := fun _ => List Bool)
      (outPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW e) J) := ⟨_, rfl⟩
  have sB' : Step (walkM W) (walkBankCost (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW)
      (wenc cap σ).H (wenc cap σ).A (wenc cap σB).H (wenc cap σB).A := by
    rw [hσB]
    exact sB
  have hB_other : ∀ k : Fin 161, (∀ j : Fin 14, portT j ≠ k) →
      σB.st (sk W.x k) = σ.st (sk W.x k) ∧ σB.sh (sk W.x k) = σ.sh (sk W.x k) := fun k hk => by
    rw [hσB]
    exact ⟨updT_st_other σ _ _ k hk, updT_sh_other σ _ _ k hk⟩
  have hB_pst : ∀ j : Fin 14, σB.st (sk W.x (portT j)) = outPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) RW LW e j :=
    fun j => by rw [hσB, updT_st_port, Fin.addCases_left]
  have hB_psh : ∀ j : Fin 14, σB.sh (sk W.x (portT j)) = outHeads (2 * (Pl.errExp / 4)) j :=
    fun j => by rw [hσB, updT_sh_port, Fin.addCases_left]
  have hB_val : σB.val = σ.val := by rw [hσB]; rfl
  have hB_cell : σB.cell = σ.cell := by rw [hσB]; rfl
  -- the table stage
  have hshC : ∀ i, σB.sh (fsC W.x i) = (yC Pl e L RW LW).sh i := by
    intro i
    rw [yC_sh]
    by_cases h0 : i.val = 0
    · have : i = 0 := Fin.ext h0
      subst this
      rw [fsC0, hB_psh]
      rfl
    · by_cases h2 : i.val = 2
      · have : i = 2 := Fin.ext h2
        subst this
        rw [fsC2, hB_psh]
        rfl
      · exact (hB_other _ (fun j hj => portT_ne_fs i h0 h2 j (congrArg Fin.val hj))).2.trans (hC5 i h0 h2).2
  have hstC : ∀ i, σB.st (fsC W.x i) = (yC Pl e L RW LW).st i := by
    intro i
    by_cases h0 : i.val = 0
    · have : i = 0 := Fin.ext h0
      subst this
      rw [fsC0, hB_pst, yC_st0]
      rfl
    · by_cases h2 : i.val = 2
      · have : i = 2 := Fin.ext h2
        subst this
        rw [fsC2, hB_pst, yC_st2]
        rfl
      · exact (hB_other _ (fun j hj => portT_ne_fs i h0 h2 j (congrArg Fin.val hj))).1.trans (hC5 i h0 h2).1
  have sC := buildStage cap W.x σB (sideB Pl.base.rank) Pl.base.rank L (padB Pl.base.rank) (Pl.base.J + 1)
    (n := 2 * (Pl.errExp / 4)) RW LW e hRW hLW hpad hps hsd hlb hnJ hcapC hO hshC hstC
    (fun r => (congrFun hB_val _).trans (hC5r r)) (hB_cell.trans hcell)
    (fun k => by rw [emC_port, hB_psh, outHeads_bank]) (fun k => by rw [emC_port, hB_pst, outPorts_bank])
  obtain ⟨σC, hσC⟩ : ∃ τ, τ = updW (fsC W.x) frC (emC W.x) σB (yF Pl e L RW LW)
      (Fin.addCases (m := 6) (n := 1) (motive := fun _ => ℕ)
        (fun k => WalkTimeLoop.H (2 * (Pl.errExp / 4)) (2 * (Pl.errExp / 4)) k.succ.succ) (fun _ => 1))
      (Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool)
        (fun k => WalkTimeLoop.A (r := sideB Pl.base.rank) (n := 2 * (Pl.errExp / 4)) RW LW e []
          (2 * (Pl.errExp / 4)) k.succ.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (Pl.errExp / 4)))) := ⟨_, rfl⟩
  have sC' : Step (buildM W.x) ((2 * (Pl.errExp / 4)) * (bodyCostL (sideB Pl.base.rank) Pl.base.rank L
      (Pl.base.J + 1) RW + 3) + 3 + 1 + lastCostL (sideB Pl.base.rank) Pl.base.rank L (Pl.base.J + 1)
      (2 * (Pl.errExp / 4))) (wenc cap σB).H (wenc cap σB).A (wenc cap σC).H (wenc cap σC).A := by
    rw [hσC]
    exact sC
  have hC_other : ∀ k : Fin 161, (k.val < 5 ∨ 23 < k.val) →
      σC.st (sk W.x k) = σB.st (sk W.x k) ∧ σC.sh (sk W.x k) = σB.sh (sk W.x k) := fun k hk => by
    rw [hσC]
    exact ⟨updC_st_other σB _ _ _ k hk, updC_sh_other σB _ _ _ k hk⟩
  have hC_tab : σC.st (sk W.x 6) = tableW Pl.walkLen Pl.base.J (rowKP Pl e L) ++ [false] ∧ σC.sh (sk W.x 6) = 0 := by
    rw [hσC, ← fsC1, updC_st_fs, updC_sh_fs, yF_st1 Pl e L RW LW hlb, yF_sh1]
    exact ⟨rfl, rfl⟩
  have hC_val : ∀ r : Fin LNR, 19 ≤ r.val → σC.val r = σ.val r := fun r hr => by
    rw [hσC]
    exact (updC_val_other σB _ _ _ r hr).trans (congrFun hB_val r)
  have hXC : ∀ k : Fin 64, σC.val (Xe Pe k) = σ.val (Xe Pe k) := fun k => hC_val _ (Xe_ge k)
  -- the record stage
  obtain ⟨mD, τ, eD, hτO, hτO0, hτK, bD⟩ := popCellW_spec cap Pe (sk W.x 3) (sk W.x 6) (sk W.x 4)
    (sk_ne 3 6 (by decide)) (sk_ne 3 4 (by decide)) (sk_ne 6 4 (by decide)) σC Pl e L r4 G off Mlab
    (SupplierWalk.majorityThreshold Pl.walkLen) lw CAP LL R cp sgn s hlabs hlen hlw hCAP hLL hR hcp
    ((hXC 0).trans h0) ((hXC 1).trans h1) ((hXC 2).trans h2) ((hXC 3).trans h3) ((hXC 4).trans h4)
    ((hXC 20).trans h20) ((hXC 21).trans h21) ((hXC 44).trans h44) ((hXC 45).trans h45) ((hXC 50).trans h50)
    ((hXC 52).trans h52) ((hXC 53).trans h53) ((hXC 63).trans h63) (fun k hk => (hXC k).trans (hzA k hk))
    (fun j a b => (hC_val _ (Pe_ge j)).trans (hz j a b)) ((hC_val _ (Pe_ge 180)).trans h180)
    (((hC_other 3 (by decide)).1.trans (hB_other 3 (by decide)).1).trans hrec)
    (((hC_other 3 (by decide)).2.trans (hB_other 3 (by decide)).2).trans hrec0)
    (by rw [(hC_other 4 (by decide)).1, (hC_other 4 (by decide)).2, (hB_other 4 (by decide)).1,
      (hB_other 4 (by decide)).2]; exact hD)
    (fun i hi => by
      rw [hC_tab.1, hC_tab.2, Nat.zero_add]
      unfold readTapeBit
      rw [List.getD_append _ _ _ _ hi])
    hM hcap hdc hJc hSc hlwc hMc hcL hcap3 hac3 hQc hc4 hin2 hnum h2c hcV hcT hθc hRc1 hcpc hbig
  have sD := (WExec.exec cap eD).step
  -- the POP row stage
  have hscr' : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      τ.st (tmapQ W.x j) = [] ∧ τ.sh (tmapQ W.x j) = 0 := by
    intro j j0 j45
    have hv := portP_cast_val j j0 j45
    have hj48 : j.val < 48 := j.isLt
    have n3 : portP (Fin.cast IPL1 j) ≠ 3 := fun h => by
      have h' := congrArg Fin.val h
      have e3 : (3 : Fin 161).val = 3 := rfl
      rw [hv, e3] at h'
      omega
    have n4 : portP (Fin.cast IPL1 j) ≠ 4 := fun h => by
      have h' := congrArg Fin.val h
      have e4 : (4 : Fin 161).val = 4 := rfl
      rw [hv, e4] at h'
      omega
    obtain ⟨k1, k2⟩ := hτK (tmapQ W.x j) (sk_ne _ _ n3) (sk_ne _ _ n4)
    obtain ⟨c1, c2⟩ := hC_other (portP (Fin.cast IPL1 j)) (Or.inr (by omega))
    obtain ⟨b1, b2⟩ := hB_other (portP (Fin.cast IPL1 j)) (fun j' h => by
      have := portT_le j'
      rw [h, hv] at this
      omega)
    obtain ⟨s1, s2⟩ := hscr j j0 j45
    exact ⟨k1.trans (c1.trans (b1.trans s1)), k2.trans (c2.trans (b2.trans s2))⟩
  obtain ⟨Ho, To, sE, hE1, hE2⟩ := popRowStage cap τ Pl e L sgn (sliceLabs r4 G off L) hlabs hnest s R (R + 1) cp
    (by rw [hR]; omega) le_rfl hok out hτO hτO0
    (((hτK _ (sk_ne 1 3 (by decide)) (sk_ne 1 4 (by decide))).1.trans
      ((hC_other 1 (by decide)).1.trans (hB_other 1 (by decide)).1)).trans hout)
    (((hτK _ (sk_ne 1 3 (by decide)) (sk_ne 1 4 (by decide))).2.trans
      ((hC_other 1 (by decide)).2.trans (hB_other 1 (by decide)).2)).trans houth) hscr'
  -- the output head back
  have eF := WExec.bwd (cap := cap) (sk W.x 1) (updS (tmapQ W.x) τ Ho To)
  have sF := (WExec.exec cap eF).step
  refine ⟨_, _, Step.seq (Step.seq (Step.seq (Step.seq sB' sC') sD) sE) sF, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]
    rw [hE1, exprWord_eq, List.append_assoc]
  · simp only [WState.seth_sh, Function.update_self]
    rw [hE2, exprWord_eq]
    simp
  · intro k hk
    have nO : k ≠ 3 := fun h => by rw [h] at hk; revert hk; decide
    have nD : k ≠ 4 := fun h => by rw [h] at hk; revert hk; decide
    have n1 : sk W.x k ≠ sk W.x 1 := sk_ne _ _ (fun h => by rw [h] at hk; revert hk; decide)
    obtain ⟨k1, k2⟩ := hτK (sk W.x k) (sk_ne _ _ nO) (sk_ne _ _ nD)
    obtain ⟨c1, c2⟩ := hC_other k (Or.inl (by omega))
    obtain ⟨b1, b2⟩ := hB_other k (fun j h => by
      have := portT_ge j
      rw [h] at this
      omega)
    refine ⟨?_, ?_⟩
    · simp only [WState.seth_st]
      show install (tmapQ W.x) τ.st To (sk W.x k) = _
      rw [install_other _ _ _ _ (tmapQ_ne k hk)]
      exact k1.trans (c1.trans b1)
    · simp only [WState.seth_sh, Function.update_apply, if_neg n1]
      show dockH (tmapQ W.x) τ.sh Ho (sk W.x k) = _
      rw [dockH_other _ _ _ _ (tmapQ_ne k hk)]
      exact k2.trans (c2.trans b2)
  · unfold popPipeBound
    omega

end Pipe

end NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
