import Proof.Wire_3_5.PrimAsmPopPipe
import Proof.Wire_3_5.PrimAsmModulus
import Proof.Wire_3_5.PrimTTau
import Proof.Wire_3_5.FinalPassFiltTabBlock

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierWalk Theorem25Completion
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.PopPipe

/-! ## The FILTER cell's streams and registers -/

section Layout

/-- C5's stage-6 builder streams: its walk stream on `5`, the others on `80 … 90`. -/
def fsF (x : ℕ) (i : Fin 12) : Fin (LNS x + 1) :=
  sk x ⟨if i.val = 0 then 5 else 79 + i.val, by split_ifs <;> omega⟩

theorem fsF_val (x : ℕ) (i : Fin 12) : (fsF x i).val = if i.val = 0 then 5 else 79 + i.val := rfl

/-- The stage-6 builder's extra tapes (the walk bank's `1 … 8`) on the producer's ports. -/
def emF (x : ℕ) (k : Fin 8) : Fin (LNS x + 1) := sk x (portT ⟨k.val + 1, by omega⟩)

theorem portT_succ : ∀ k : Fin 8, (portT ⟨k.val + 1, by omega⟩).val = if k.val = 0 then 7 else 16 + k.val := by
  decide

theorem gsF_val (x : ℕ) (c : Fin (12 + 8)) :
    (gs (fsF x) (emF x) c).val =
      if c.val < 12 then (if c.val = 0 then 5 else 79 + c.val) else (if c.val = 12 then 7 else 16 + (c.val - 12)) := by
  refine Fin.addCases (fun c1 => ?_) (fun c2 => ?_) c
  · simp only [gs, Fin.addCases_left, fsF, sk_val, Fin.val_castAdd]
    rw [if_pos c1.isLt]
  · simp only [gs, Fin.addCases_right, emF, sk_val, Fin.val_natAdd]
    rw [portT_succ]
    split_ifs <;> omega

theorem gsF_inj (x : ℕ) : Function.Injective (gs (fsF x) (emF x)) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [gsF_val, gsF_val] at hv
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at hv <;> omega

/-- The modulus search's tapes: its unary degree on `91`, its answer tape `12` on the modulus stream `82`, the others
on `92 … 107`. -/
def tmapM (x : ℕ) (j : Fin 17) : Fin (LNS x + 1) :=
  sk x ⟨if j.val = 12 then 82 else 91 + j.val, by split_ifs <;> omega⟩

theorem tmapM_val (x : ℕ) (j : Fin 17) : (tmapM x j).val = if j.val = 12 then 82 else 91 + j.val := rfl

theorem tmapM_inj (x : ℕ) : Function.Injective (tmapM x) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [tmapM_val, tmapM_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The trace mask's streams: the modulus `82`, the mask `81`, scratch `108 … 112`. -/
def smv : Fin 7 → Fin 161 := ![82, 81, 108, 109, 110, 111, 112]

theorem smv_inj : Function.Injective smv := by decide

def SmT (x : ℕ) : Fin 7 ↪ Fin (LNS x + 1) := ⟨fun i => sk x (smv i), fun _ _ h => smv_inj (sk_inj x h)⟩

/-- The trace mask's registers `219 … 227`. -/
def RgT : Fin 9 ↪ Fin LNR := ⟨fun i => ⟨219 + i.val, by unfold LNR; omega⟩, fun _ _ h => Fin.ext (by
  have := congrArg Fin.val h
  simp only at this
  omega)⟩

/-- The FILTER record writer's registers `230 … 249`. -/
def FR : Fin 20 ↪ Fin LNR := ⟨fun i => ⟨230 + i.val, by unfold LNR; omega⟩, fun _ _ h => Fin.ext (by
  have := congrArg Fin.val h
  simp only at this
  omega)⟩

end Layout

/-! ## The modulus stage -/

section Mod
variable (cap : ℕ) {x : ℕ}

variable (x) in
/-- The modulus stage's machine: the modulus search on the streams `tmapM`. -/
noncomputable def modDM := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tmapM x j)) Modulus.modM

theorem tmapM_12 : tmapM x 12 = sk x 82 := congrArg (sk x) (Fin.ext rfl)

theorem tmapM_0 : tmapM x 0 = sk x 91 := congrArg (sk x) (Fin.ext rfl)

theorem modStage (σ : WState (LNS x) LNR) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hin : σ.st (sk x 91) = List.replicate ℓ true)
    (hsc : ∀ j : Fin 17, j.val ≠ 0 → σ.st (tmapM x j) = []) (hh : ∀ j : Fin 17, σ.sh (tmapM x j) = 0) :
    ∃ To, Step (modDM x) (Modulus.modCost ℓ) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (updS (tmapM x) σ (fun _ => 0) To)).H (wenc cap (updS (tmapM x) σ (fun _ => 0) To)).A ∧
      (updS (tmapM x) σ (fun _ => 0) To).st (sk x 82) = frame (SignedSortKey.binary ℓ (GF.firstPrimitive ℓ)) ∧
      (updS (tmapM x) σ (fun _ => 0) To).sh (sk x 82) = 0 := by
  obtain ⟨To, hs, -, h12⟩ := Modulus.modulus_step ℓ hℓ
  have e1 : (fun _ : Fin 17 => (0 : ℕ)) = fun j => σ.sh (tmapM x j) := funext fun j => (hh j).symm
  have e2 : (fun i : Fin 17 => if i.val = 0 then List.replicate ℓ true else []) = fun j => σ.st (tmapM x j) := by
    funext j
    by_cases h0 : j.val = 0
    · have : j = 0 := Fin.ext h0
      subst this
      rw [if_pos h0, tmapM_0, hin]
    · rw [if_neg h0, hsc j h0]
  have hs' : Step Modulus.modM (Modulus.modCost ℓ) (fun j => σ.sh (tmapM x j)) (fun j => σ.st (tmapM x j))
      (fun _ => 0) To := by
    rw [← e1, ← e2]
    exact hs
  refine ⟨To, dockS cap (tmapM x) (tmapM_inj x) σ hs', ?_, ?_⟩
  · show install (tmapM x) σ.st To (sk x 82) = _
    rw [← tmapM_12, install_slot _ (tmapM_inj x), h12]
  · dsimp only [updS]
    rw [← tmapM_12, dockH_slot _ (tmapM_inj x)]

end Mod

/-! ## The table stage -/

section Build
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
variable (cap : ℕ) (x : ℕ)

/-- The FILTER table stage's machine: C5's stage-6 builder docked by `dockW`. -/
noncomputable def filtBuildM := RecoveryFocus.machine (wq (fsF x) frC (emF x)) builderM

/-- **The FILTER table stage**: C5's stage-6 builder docked on the cell layout. -/
theorem filtBuildStage (σ : WState (LNS x) LNR) (P : GapParams) (e : GapSeed P) (L R LW : ℕ) (hU : 1 ≤ P.cap)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1))
    (hvert : ∀ i, (sample.vertex i).1.val = (e.vertex i).1.val)
    (hR : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ R) (hLW : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ LW)
    (hcap : 2 * (wOf P.fieldBits P.labelBits * 128) + 4 * P.labelBits + 2 * P.fieldBits + L + 10 ≤ cap)
    (hO : (2 * (P.errExp / 4) + 1) * (128 * (2 * L + 2) + 2) + 12 < cap)
    (hsh : ∀ i, σ.sh (fsF x i) = (canon P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
      (WalkTimeLoop.A R LW sample [] 0 0) (owOf (GF.firstPrimitive P.fieldBits)
        (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits P.prefixBits L 128 sample 0)).w.sh i)
    (hst : ∀ i, σ.st (fsF x i) = (canon P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
      (WalkTimeLoop.A R LW sample [] 0 0) (owOf (GF.firstPrimitive P.fieldBits)
        (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits P.prefixBits L 128 sample 0)).w.st i)
    (hv : ∀ r, σ.val (frC r) = (canon P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
      (WalkTimeLoop.A R LW sample [] 0 0) (owOf (GF.firstPrimitive P.fieldBits)
        (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits P.prefixBits L 128 sample 0)).w.val r)
    (hc : σ.cell = false)
    (hqh : ∀ k, σ.sh (emF x k) = Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ)
      (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) 0 k.succ) (fun _ => 1) k)
    (hqt : ∀ k, σ.st (emF x k) = Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
      (fun k => WalkTimeLoop.A R LW sample [] 0 k.succ)
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4))) k) :
    Step (filtBuildM x) (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 R + 3) + 3 + 1 +
        lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4)))
      (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updW (fsF x) frC (emF x) σ
        (finalW P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
          (WalkTimeLoop.A R LW sample [] (2 * (P.errExp / 4)) 0) (tableWord (filterTable P e L)))
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ)
          (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) (2 * (P.errExp / 4)) k.succ) (fun _ => 1))
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample [] (2 * (P.errExp / 4)) k.succ)
          (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4)))))).H
      (wenc cap (updW (fsF x) frC (emF x) σ
        (finalW P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
          (WalkTimeLoop.A R LW sample [] (2 * (P.errExp / 4)) 0) (tableWord (filterTable P e L)))
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ)
          (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) (2 * (P.errExp / 4)) k.succ) (fun _ => 1))
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample [] (2 * (P.errExp / 4)) k.succ)
          (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4)))))).A := by
  have hb := stage6_step P e L cap R LW [] hU sample hvert hR hLW hcap hO
  have e1 : Fin.addCases (m := 11 + 2 + 19 + 7) (n := 1) (motive := fun _ => ℕ)
      (loopH cap P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P) (GF.firstPrimitive P.fieldBits)
        (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) 128 R LW sample [] 0) (fun _ : Fin 1 => 1) =
      Fin.addCases (m := 11 + 2 + 19) (n := 8) (motive := fun _ => ℕ)
        (wenc cap (canon P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
          (WalkTimeLoop.A R LW sample [] 0 0) (owOf (GF.firstPrimitive P.fieldBits)
            (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits P.prefixBits L 128 sample 0)).w).H
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) 0 k.succ)
          (fun _ => 1)) := by
    unfold loopH cH
    exact addCases_assoc _ _ _
  have e2 : Fin.addCases (m := 11 + 2 + 19 + 7) (n := 1) (motive := fun _ => List Bool)
      (loopA cap P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P) (GF.firstPrimitive P.fieldBits)
        (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) 128 R LW sample [] 0)
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4))) =
      Fin.addCases (m := 11 + 2 + 19) (n := 8) (motive := fun _ => List Bool)
        (wenc cap (canon P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
          (WalkTimeLoop.A R LW sample [] 0 0) (owOf (GF.firstPrimitive P.fieldBits)
            (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits P.prefixBits L 128 sample 0)).w).A
        (Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
          (fun k => WalkTimeLoop.A R LW sample [] 0 k.succ)
          (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4)))) := by
    unfold loopA cA
    exact addCases_assoc _ _ _
  rw [e1, e2] at hb
  exact dockW cap (fsF x) frC (emF x) (gsF_inj x) frC_inj σ _ _ _ _ _ _ hb hsh hst hv hc hqh hqt

end Build

/-! ## The FILTER row stage -/

section FiltRowS
open NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
variable (cap : ℕ) {x : ℕ}

theorem F28 : 1 + (1 + (14 + F37.t) + 1) = 28 := rfl

/-- The FILTER row machine's tapes: its input on the record stream `3`, its output tape `12` on the output stream
`1`, the others on `29 + j`. -/
def portR (j : Fin 28) : Fin 161 :=
  ⟨if j.val = 0 then 3 else if j.val = 12 then 1 else 29 + j.val, by split_ifs <;> omega⟩

theorem portR_val (j : Fin 28) : (portR j).val = if j.val = 0 then 3 else if j.val = 12 then 1 else 29 + j.val := rfl

variable (x) in
def tmapR (j : Fin (1 + (1 + (14 + F37.t) + 1))) : Fin (LNS x + 1) := sk x (portR (Fin.cast F28 j))

theorem tmapR_inj : Function.Injective (tmapR x) := by
  intro a b h
  have hv := congrArg Fin.val (sk_inj x h)
  rw [portR_val, portR_val, Fin.val_cast, Fin.val_cast] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem tmapR_in (j : Fin (1 + (1 + (14 + F37.t) + 1))) (h : j.val = 0) : tmapR x j = sk x 3 :=
  congrArg (sk x) (Fin.ext (by rw [portR_val, Fin.val_cast, if_pos h]; rfl))

theorem tmapR_out (j : Fin (1 + (1 + (14 + F37.t) + 1))) (h : j.val = 12) : tmapR x j = sk x 1 :=
  congrArg (sk x) (Fin.ext (by rw [portR_val, Fin.val_cast, if_neg (by omega), if_pos h]; rfl))

theorem filtEntryA (inp out B : List Bool) (j : Fin (1 + (1 + (14 + F37.t) + 1))) :
    rA F37.t inp (fA [] (entryBank out B) (fun _ => []) (List.replicate 0 false)) j =
      if j.val = 0 then inp else if j.val = 12 then overlay out B else [] := by
  rcases rcover F37.t j with rfl | ⟨i, rfl⟩
  · rw [rA_in]
    rfl
  · rw [rA_fl]
    rcases cover F37.t i with rfl | ⟨c, rfl⟩ | ⟨d, rfl⟩ | rfl
    · rw [fA_srcO]
      rfl
    · rw [fA_prSlot, Fin.addCases_left]
      fin_cases c <;> rfl
    · rw [fA_prSlot, Fin.addCases_right,
        if_neg (by simp only [flR, prSlot, Fin.val_natAdd, Fin.val_castAdd]; omega),
        if_neg (by simp only [flR, prSlot, Fin.val_natAdd, Fin.val_castAdd]; omega)]
    · rw [fA_logI]
      rfl

theorem filtEntryH (p o : ℕ) (j : Fin (1 + (1 + (14 + F37.t) + 1))) :
    rH F37.t p (fH F37.t 0 o) j = if j.val = 0 then p else if j.val = 12 then o else 0 := by
  rcases rcover F37.t j with rfl | ⟨i, rfl⟩
  · rw [rH_in]
    rfl
  · rw [rH_fl]
    rcases cover F37.t i with rfl | ⟨c, rfl⟩ | ⟨d, rfl⟩ | rfl
    · rw [fH_srcO]
      rfl
    · rw [fH_prSlot, Fin.addCases_left]
      fin_cases c <;> rfl
    · rw [fH_prSlot, Fin.addCases_right,
        if_neg (by simp only [flR, prSlot, Fin.val_natAdd, Fin.val_castAdd]; omega),
        if_neg (by simp only [flR, prSlot, Fin.val_natAdd, Fin.val_castAdd]; omega)]
    · rw [fH_logI]
      rfl

variable (x) in
/-- The FILTER row stage's machine: C2's FILTER row machine on the streams `tmapR`. -/
noncomputable def filtRowDM := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tmapR x j)) (filterRowM F37)

/-- **The FILTER row stage**: C2's FILTER row machine docked on the cell layout, the record on the record stream and
the output `out ++ [false]` at `|out|`: the output becomes `out ++ exprWord (filtRefC …)`, its head after it. -/
theorem filtRowStage (σ : WState (LNS x) LNR) (tbl : List (List (List Bool))) (thr L : ℕ)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ L) (labs : List ℕ) (hlabs : 4 * L ≤ labs.length) (out : List Bool)
    (hrec : σ.st (sk x 3) = frame (filtRecC tbl thr L true labs)) (hrec0 : σ.sh (sk x 3) = 0)
    (hout : σ.st (sk x 1) = out ++ [false]) (houth : σ.sh (sk x 1) = out.length)
    (hscr : ∀ j : Fin (1 + (1 + (14 + F37.t) + 1)), j.val ≠ 0 → j.val ≠ 12 →
      σ.st (tmapR x j) = [] ∧ σ.sh (tmapR x j) = 0) :
    ∃ n Ho To, n ≤ filtCostC tbl thr L true labs ∧
      Step (filtRowDM x) n (wenc cap σ).H (wenc cap σ).A (wenc cap (updS (tmapR x) σ Ho To)).H
        (wenc cap (updS (tmapR x) σ Ho To)).A ∧
      (updS (tmapR x) σ Ho To).st (sk x 1) = out ++ ListMachine.Rec.exprWord (filtRefC tbl thr L true labs) ∧
      (updS (tmapR x) σ Ho To).sh (sk x 1) = (out ++ ListMachine.Rec.exprWord (filtRefC tbl thr L true labs)).length := by
  obtain ⟨⟨n, A', hn, hs, -, hA'⟩, -⟩ := filtRow_run tbl thr L hlen true labs hlabs [] [] out (out ++ [false]) 0
  have e1 : rH F37.t ([] : List Bool).length (fH F37.t 0 out.length) = fun j => σ.sh (tmapR x j) := by
    funext j
    rw [filtEntryH]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, tmapR_in j h0, hrec0]
      rfl
    · by_cases h12 : j.val = 12
      · rw [if_neg h0, if_pos h12, tmapR_out j h12, houth]
      · rw [if_neg h0, if_neg h12]
        exact (hscr j h0 h12).2.symm
  have e2 : rA F37.t ([] ++ frame (filtRecC tbl thr L true labs) ++ [])
      (fA [] (entryBank out (out ++ [false])) (fun _ => []) (List.replicate 0 false)) = fun j => σ.st (tmapR x j) := by
    funext j
    rw [filtEntryA]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, tmapR_in j h0, hrec, List.nil_append, List.append_nil]
    · by_cases h12 : j.val = 12
      · rw [if_neg h0, if_pos h12, tmapR_out j h12, hout, overlay_self]
      · rw [if_neg h0, if_neg h12]
        exact (hscr j h0 h12).1.symm
  rw [e1, e2] at hs
  have jo : (flR F37.t (outI F37.t)).val = 12 := rfl
  refine ⟨n, _, A', hn, dockS cap (tmapR x) tmapR_inj σ hs, ?_, ?_⟩
  · show install (tmapR x) σ.st A' (sk x 1) = _
    rw [← tmapR_out (x := x) _ jo, install_slot _ tmapR_inj, hA', overlay_ext out _ (exprWord_len _)]
  · dsimp only [updS]
    rw [← tmapR_out (x := x) _ jo, dockH_slot _ tmapR_inj, rH_fl, outI_eq, fH_prSlot, Fin.addCases_left]
    rfl

end FiltRowS

/-! ## The FILTER record stage -/

section FCell
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
variable (cap : ℕ) {x : ℕ}

variable (x) in
/-- **The FILTER record stage's word program**: the record, then the record stream rewound. -/
def fcellW : WM (LNS x) LNR := .seq (filtRecW (sk x 3) (sk x 80) FR) (WM.rewind (sk x 3) (FR 0))

theorem FR_ne (i j : Fin 20) (h : i ≠ j) : FR i ≠ FR j := fun e => h (FR.injective e)

/-- **The FILTER record stage**: from the FILTER numbers in the registers `FR` and the table on stream `80`, the record
stream holds C2's FILTER row record `frame (filtRecC (filterTable P e L) thr L true labs)`, its head at `0`. -/
theorem fcellW_spec (σ : WState (LNS x) LNR) (P : GapParams) (e : GapSeed P) (L r4 G off Mlab : ℕ)
    (hlen : (sliceLabs r4 G off L).length = 4 * L)
    (hF0 : σ.val (FR 0) = 0) (hF1 : σ.val (FR 1) = r4) (hF2 : σ.val (FR 2) = G) (hF3 : σ.val (FR 3) = off)
    (hF4 : σ.val (FR 4) = L) (hFz : ∀ i : Fin 20, 5 ≤ i.val → i.val ≤ 12 → σ.val (FR i) = 0)
    (hF13 : σ.val (FR 13) = 4 * L) (hF14 : σ.val (FR 14) = filtDeg (filterTable P e L))
    (hF15 : σ.val (FR 15) = majorityThreshold P.walkLen)
    (hF16 : σ.val (FR 16) = cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1)
    (hF17 : σ.val (FR 17) = (tableWord (filterTable P e L)).length) (hF18 : σ.val (FR 18) = 0)
    (hF19 : σ.val (FR 19) = 0)
    (hO0 : σ.st (sk x 3) = []) (hO1 : σ.sh (sk x 3) = 0) (hS : σ.st (sk x 80) = tableWord (filterTable P e L))
    (hS0 : σ.sh (sk x 80) = 0) (hM : off + L + (r4 + 4) * G ≤ Mlab)
    (cA : 4 * (8 * (4 * L) + 6) + 30 + 4 * filtDeg (filterTable P e L) + 6 + 4 * L +
      filtDeg (filterTable P e L) + 10 ≤ cap)
    (cB : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6)) +
      ((sliceLabs r4 G off L).flatMap labE).length + 4 * labSum (sliceLabs r4 G off L) + 10 +
      L * (4 * (4 * Mlab + 4)) + L * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) + 4 * (2 * Mlab + 10) + 7 * Mlab +
      r4 + G + off + L + labSum (sliceLabs r4 G off L) + 40 ≤ cap)
    (cC : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) +
      (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4)) +
      4 * (tableWord (filterTable P e L)).length + 2 + (tableWord (filterTable P e L)).length + 5 ≤ cap)
    (cD : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) +
      (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4) +
      (4 * (tableWord (filterTable P e L)).length + 2)) + 4 * majorityThreshold P.walkLen + 6 +
      8 * (4 * (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1) + 2) + 7 +
      majorityThreshold P.walkLen + cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 10 ≤ cap)
    (crw : (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L))).length ≤ cap) :
    ∃ m τ, WExec cap (fcellW x) σ τ m ∧
      τ.st (sk x 3) = frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L)) ∧
      τ.sh (sk x 3) = 0 ∧ (∀ T, T ≠ sk x 3 → T ≠ sk x 80 → τ.st T = σ.st T ∧ τ.sh T = σ.sh T) ∧
      m ≤ filtBound (4 * L) (filtDeg (filterTable P e L)) (majorityThreshold P.walkLen)
        (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L) (tableWord (filterTable P e L)).length
        (labSum (sliceLabs r4 G off L)) r4 G off L + 1 +
        (5 * (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L))).length
          + 1) := by
  have hOS : sk x 3 ≠ sk x 80 := sk_ne _ _ (by decide)
  obtain ⟨u, hu⟩ : ∃ v, v = frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true
      (sliceLabs r4 G off L)) := ⟨_, rfl⟩
  have hlink : filtEmit (4 * L) (filtDeg (filterTable P e L)) (labSum (sliceLabs r4 G off L))
      (majorityThreshold P.walkLen) (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L)
      (tableWord (filterTable P e L)) (sliceLabs r4 G off L) = u := by
    rw [hu, filtEmit_eq, cap1C_eq L _ hlen]
  rw [← hu] at crw ⊢
  obtain ⟨m1, e1, b1⟩ := filtRecW_spec cap (sk x 3) (sk x 80) FR hOS σ (4 * L) (filtDeg (filterTable P e L))
    (majorityThreshold P.walkLen) (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L) r4 G off L
    (tableWord (filterTable P e L)) hF13 hF14 hF15 hF16 hF17 hF1 hF2 hF3 hF4
    (hFz 5 (by decide) (by decide)) (hFz 6 (by decide) (by decide)) (hFz 7 (by decide) (by decide))
    (hFz 8 (by decide) (by decide)) (hFz 9 (by decide) (by decide)) (hFz 10 (by decide) (by decide))
    (hFz 11 (by decide) (by decide)) (hFz 12 (by decide) (by decide)) hF19 (by rw [hO0, hO1]; rfl)
    (fun i hi => by rw [hS, hS0, Nat.zero_add]; rfl) Mlab hM _ _ rfl rfl
    (by rw [hF0, Nat.zero_add]; exact cA) (by rw [hF0, Nat.zero_add]; exact cB)
    (by rw [hF0, hF18, Nat.zero_add, Nat.add_zero]; exact cC) (by rw [hF0, Nat.zero_add]; exact cD)
  rw [hlink] at e1
  obtain ⟨ρ, hρ⟩ : ∃ τ, τ = fSt (sk x 3) (sk x 80) FR σ u (tableWord (filterTable P e L)).length := ⟨_, rfl⟩
  rw [← hρ] at e1
  have hρ0 : ρ.val (FR 0) = u.length := by
    rw [hρ, fSt_val, if_neg (FR_ne 0 18 (by decide)), if_pos rfl, hF0, Nat.zero_add]
  have hρO : ρ.sh (sk x 3) = u.length := by rw [hρ, fSt_shO hOS, hO1, Nat.zero_add]
  have e2 := wrewind_spec cap (sk x 3) (FR 0) u.length ρ hρ0 (by rw [hρ0]; exact crw)
  refine ⟨m1 + 1 + (5 * u.length + 1), _, WExec.seq e1 e2, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st, WState.setv_st]
    rw [hρ, fSt_stO, hO0, List.nil_append]
  · simp only [WState.seth_sh, Function.update_self]
    rw [hρO, Nat.sub_self]
  · intro T hT3 hT80
    refine ⟨?_, ?_⟩
    · simp only [WState.seth_st, WState.setv_st]
      rw [hρ]
      simp [fSt, Function.update_apply, hT3]
    · simp only [WState.seth_sh, WState.setv_sh, Function.update_apply, if_neg hT3]
      rw [hρ]
      simp [fSt, Function.update_apply, hT3, hT80]
  · exact Nat.add_le_add_right (Nat.add_le_add_right b1 1) _

end FCell

/-! ## Helpers for the FILTER pipeline -/

section FHelp
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
variable {x : ℕ}

/-- C5's stage-6 builder state before the first visit. -/
noncomputable def yFC (P : GapParams) (L R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)) : WState 11 19 :=
  (canon P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P) (WalkTimeLoop.A R LW sample [] 0 0)
    (owOf (GF.firstPrimitive P.fieldBits) (GF2.tau (GF.firstPrimitive P.fieldBits) P.fieldBits) P.fieldBits P.labelBits
      P.prefixBits L 128 sample 0)).w

theorem yFC_st1 (P : GapParams) (L R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)) :
    (yFC P L R LW sample).st 1 = [] := by
  simp [yFC, TSt.w, canon, owOf]

theorem yFC_sh (P : GapParams) (L R LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)) (i : Fin 12) :
    (yFC P L R LW sample).sh i = 0 := by
  fin_cases i <;> simp [yFC, TSt.w, canon, owOf]

theorem smv_val : ∀ j : Fin 7, (smv j).val = 82 ∨ (smv j).val = 81 ∨ (108 ≤ (smv j).val ∧ (smv j).val ≤ 112) := by
  decide

theorem fsF_ne (k : Fin 161) (i : Fin 12) (hk : k.val ≠ 5 ∧ (k.val < 80 ∨ 90 < k.val)) : fsF x i ≠ sk x k := by
  intro h
  have hv := congrArg Fin.val h
  rw [fsF_val, sk_val] at hv
  split_ifs at hv <;> omega

theorem outPorts_bank1 (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) (k : Fin 8) :
    PrimT.WalkBank.outPorts r n R LW sample ⟨k.val + 1, by omega⟩ =
      Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool) (fun k => WalkTimeLoop.A R LW sample [] 0 k.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n) k := by
  fin_cases k <;> rfl

theorem outHeads_bank1 (n : ℕ) (k : Fin 8) :
    PrimT.WalkBank.outHeads n ⟨k.val + 1, by omega⟩ =
      Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ) (fun k => WalkTimeLoop.H n 0 k.succ) (fun _ => 1) k := by
  fin_cases k <;> rfl

theorem updF_st_other (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 8 → ℕ) (tq : Fin 8 → List Bool)
    (k : Fin 161) (hk : k.val ≠ 5 ∧ k.val ≠ 7 ∧ (k.val < 17 ∨ 23 < k.val) ∧ (k.val < 80 ∨ 90 < k.val)) :
    (updW (fsF x) frC (emF x) σ y hq tq).st (sk x k) = σ.st (sk x k) :=
  install_other _ _ _ _ fun c h => by
    have hv := congrArg Fin.val h
    rw [gsF_val, sk_val] at hv
    have := c.isLt
    split_ifs at hv <;> omega

theorem updF_sh_other (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 8 → ℕ) (tq : Fin 8 → List Bool)
    (k : Fin 161) (hk : k.val ≠ 5 ∧ k.val ≠ 7 ∧ (k.val < 17 ∨ 23 < k.val) ∧ (k.val < 80 ∨ 90 < k.val)) :
    (updW (fsF x) frC (emF x) σ y hq tq).sh (sk x k) = σ.sh (sk x k) :=
  dockH_other _ _ _ _ fun c h => by
    have hv := congrArg Fin.val h
    rw [gsF_val, sk_val] at hv
    have := c.isLt
    split_ifs at hv <;> omega

theorem updF_st_fs (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 8 → ℕ) (tq : Fin 8 → List Bool)
    (i : Fin 12) : (updW (fsF x) frC (emF x) σ y hq tq).st (fsF x i) = y.st i := by
  show install (gs (fsF x) (emF x)) σ.st _ (fsF x i) = _
  have e : fsF x i = gs (fsF x) (emF x) (Fin.castAdd 8 i) := by simp only [gs, Fin.addCases_left]
  rw [e, install_slot _ (gsF_inj x), Fin.addCases_left]

theorem updF_sh_fs (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 8 → ℕ) (tq : Fin 8 → List Bool)
    (i : Fin 12) : (updW (fsF x) frC (emF x) σ y hq tq).sh (fsF x i) = y.sh i := by
  show dockH (gs (fsF x) (emF x)) σ.sh _ (fsF x i) = _
  have e : fsF x i = gs (fsF x) (emF x) (Fin.castAdd 8 i) := by simp only [gs, Fin.addCases_left]
  rw [e, dockH_slot _ (gsF_inj x), Fin.addCases_left]

theorem updF_val_other (σ : WState (LNS x) LNR) (y : WState 11 19) (hq : Fin 8 → ℕ) (tq : Fin 8 → List Bool)
    (r : Fin LNR) (hr : 19 ≤ r.val) : (updW (fsF x) frC (emF x) σ y hq tq).val r = σ.val r :=
  dockH_other _ _ _ _ fun r' h => by
    have hv := congrArg Fin.val h
    have e : (frC r').val = r'.val := rfl
    rw [e] at hv
    have := r'.isLt
    omega

theorem updM_other (σ : WState (LNS x) LNR) (hout : Fin 17 → ℕ) (tout : Fin 17 → List Bool) (k : Fin 161)
    (hk : k.val ≠ 82 ∧ (k.val < 91 ∨ 107 < k.val)) :
    (updS (tmapM x) σ hout tout).st (sk x k) = σ.st (sk x k) ∧
      (updS (tmapM x) σ hout tout).sh (sk x k) = σ.sh (sk x k) := by
  have hne : ∀ j : Fin 17, tmapM x j ≠ sk x k := fun j h => by
    have hv := congrArg Fin.val h
    rw [tmapM_val, sk_val] at hv
    have := j.isLt
    split_ifs at hv <;> omega
  exact ⟨install_other _ _ _ _ hne, dockH_other _ _ _ _ hne⟩

theorem updM_T (σ : WState (LNS x) LNR) (hout : Fin 17 → ℕ) (tout : Fin 17 → List Bool) (k : Fin x) :
    (updS (tmapM x) σ hout tout).st (sT x k) = σ.st (sT x k) ∧
      (updS (tmapM x) σ hout tout).sh (sT x k) = σ.sh (sT x k) := by
  have hne : ∀ j : Fin 17, tmapM x j ≠ sT x k := fun j h => by
    have hv := congrArg Fin.val h
    rw [tmapM_val, sT_val] at hv
    split_ifs at hv <;> omega
  exact ⟨install_other _ _ _ _ hne, dockH_other _ _ _ _ hne⟩

theorem SmT_ne (k : Fin 161) (hk : k.val ≠ 81 ∧ k.val ≠ 82 ∧ (k.val < 108 ∨ 112 < k.val)) (j : Fin 7) :
    SmT x j ≠ sk x k := by
  intro h
  have hv := congrArg Fin.val (sk_inj x h)
  rcases smv_val j with h1 | h1 | h1 <;> omega

theorem SmT_ne_T (k : Fin x) (j : Fin 7) : SmT x j ≠ sT x k := by
  intro h
  have hv := congrArg Fin.val h
  have e : (SmT x j).val = (smv j).val := rfl
  rw [e, sT_val] at hv
  rcases smv_val j with h1 | h1 | h1 <;> omega

theorem RgT_ne (r : Fin LNR) (hr : r.val < 219 ∨ 227 < r.val) (j : Fin 9) : RgT j ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  have e : (RgT j).val = 219 + j.val := rfl
  rw [e] at hv
  have := j.isLt
  omega

end FHelp

/-! ## The whole FILTER pipeline -/

section FPipe
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimT.WalkBank
variable (cap : ℕ) (W : WalkBankProducer)

variable (x : ℕ) in
/-- The trace-mask stage's machine. -/
noncomputable def tauM := (PrimT.tauW (SmT x) RgT).toProg.compile

variable (x : ℕ) in
/-- The FILTER record stage's machine. -/
noncomputable def fcellM := (fcellW x).toProg.compile

/-- **The FILTER cell's pipeline machine**: modulus, trace mask, walk, table, record, FILTER row, output head back. -/
noncomputable def filtPipeM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (modDM W.x) (tauM W.x)) (walkM W)) (filtBuildM W.x)) (fcellM W.x))
  (filtRowDM W.x)) (bwdM W.x)

/-- A bound on the FILTER pipeline's cost. -/
noncomputable def filtPipeBound (P : GapParams) (e : GapSeed P) (L r4 G off RW LW : ℕ) : ℕ :=
  Modulus.modCost P.fieldBits + 1 + PrimT.tauCost P.fieldBits + 1 +
    walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW + 1 +
    (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 RW + 3) + 3 + 1 +
      lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4))) + 1 +
    (filtBound (4 * L) (filtDeg (filterTable P e L)) (majorityThreshold P.walkLen)
        (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L) (tableWord (filterTable P e L)).length
        (labSum (sliceLabs r4 G off L)) r4 G off L + 1 +
      (5 * (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L))).length
        + 1)) + 1 +
    filtCostC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L) + 1 + 1

/-- **The FILTER cell's pipeline**: from a FILTER-ready state (the unary field degree, the trace mask's zero words,
the walk-bank producer's inputs, C5's stage-6 builder words and registers, the FILTER numbers, the record stream
empty, the output `out ++ [false]` at `|out|`), the output becomes `out ++ body ++ [false]` at `|out ++ body|`,
`body` the FILTER row's printed expression (`filtRefC` of C5's `filterTable P e L`, C2's reference of the regular
filter at the population point); the request and counter streams are kept. -/
theorem filtPipe (σ : WState (LNS W.x) LNR) (out : List Bool) (P : GapParams) (e : GapSeed P)
    (L r4 G off Mlab RW LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1))
    (hvert : ∀ i, (sample.vertex i).1.val = (e.vertex i).1.val) (hU : 1 ≤ P.cap)
    (hlen : (sliceLabs r4 G off L).length = 4 * L) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length)
    (hRW : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ RW) (hLW : 2 * (wOf P.fieldBits P.labelBits * 128) + 1 ≤ LW)
    (hcap6 : 2 * (wOf P.fieldBits P.labelBits * 128) + 4 * P.labelBits + 2 * P.fieldBits + L + 10 ≤ cap)
    (hO6 : (2 * (P.errExp / 4) + 1) * (128 * (2 * L + 2) + 2) + 12 < cap)
    (hcapT : 2 * P.fieldBits + 2 ≤ cap)
    (hout : σ.st (sk W.x 1) = out ++ [false]) (houth : σ.sh (sk W.x 1) = out.length)
    (hrec : σ.st (sk W.x 3) = []) (hrec0 : σ.sh (sk W.x 3) = 0)
    (hmod : σ.st (sk W.x 91) = List.replicate P.fieldBits true)
    (hmsc : ∀ j : Fin 17, j.val ≠ 0 → σ.st (tmapM W.x j) = []) (hmh : ∀ j : Fin 17, σ.sh (tmapM W.x j) = 0)
    (htau : ∀ j : Fin 7, 1 ≤ j.val →
      σ.st (SmT W.x j) = frame (SignedSortKey.binary P.fieldBits 0) ∧ σ.sh (SmT W.x j) = 0)
    (htauR : ∀ j : Fin 9, j ≠ 4 → σ.val (RgT j) = 0) (htauR4 : σ.val (RgT 4) = P.fieldBits)
    (hin : ∀ j : Fin 14, σ.st (sk W.x (portT j)) = inPorts (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4))
      RW LW (seedIndexWord (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) sample) j)
    (hh : ∀ j : Fin 14, σ.sh (sk W.x (portT j)) = 0)
    (hsc : ∀ k : Fin W.x, σ.st (sT W.x k) = []) (hsh : ∀ k : Fin W.x, σ.sh (sT W.x k) = 0)
    (hC5 : ∀ i : Fin 12, 4 ≤ i.val → σ.st (fsF W.x i) = (yFC P L RW LW sample).st i ∧ σ.sh (fsF W.x i) = 0)
    (hC51 : σ.st (sk W.x 80) = [] ∧ σ.sh (sk W.x 80) = 0)
    (hC5r : ∀ r, σ.val (frC r) = (yFC P L RW LW sample).val r) (hcell : σ.cell = false)
    (hF0 : σ.val (FR 0) = 0) (hF1 : σ.val (FR 1) = r4) (hF2 : σ.val (FR 2) = G) (hF3 : σ.val (FR 3) = off)
    (hF4 : σ.val (FR 4) = L) (hFz : ∀ i : Fin 20, 5 ≤ i.val → i.val ≤ 12 → σ.val (FR i) = 0)
    (hF13 : σ.val (FR 13) = 4 * L) (hF14 : σ.val (FR 14) = filtDeg (filterTable P e L))
    (hF15 : σ.val (FR 15) = majorityThreshold P.walkLen)
    (hF16 : σ.val (FR 16) = cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1)
    (hF17 : σ.val (FR 17) = (tableWord (filterTable P e L)).length) (hF18 : σ.val (FR 18) = 0)
    (hF19 : σ.val (FR 19) = 0) (hM : off + L + (r4 + 4) * G ≤ Mlab)
    (cA : 4 * (8 * (4 * L) + 6) + 30 + 4 * filtDeg (filterTable P e L) + 6 + 4 * L +
      filtDeg (filterTable P e L) + 10 ≤ cap)
    (cB : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6)) +
      ((sliceLabs r4 G off L).flatMap labE).length + 4 * labSum (sliceLabs r4 G off L) + 10 +
      L * (4 * (4 * Mlab + 4)) + L * (4 * (2 * Mlab + 10)) + 4 * (4 * Mlab + 4) + 4 * (2 * Mlab + 10) + 7 * Mlab +
      r4 + G + off + L + labSum (sliceLabs r4 G off L) + 40 ≤ cap)
    (cC : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) +
      (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4)) +
      4 * (tableWord (filterTable P e L)).length + 2 + (tableWord (filterTable P e L)).length + 5 ≤ cap)
    (cD : (4 * (8 * (4 * L) + 6) + 30 + (4 * filtDeg (filterTable P e L) + 6) +
      (((sliceLabs r4 G off L).flatMap labE).length + 6 + 4 * labSum (sliceLabs r4 G off L) + 4) +
      (4 * (tableWord (filterTable P e L)).length + 2)) + 4 * majorityThreshold P.walkLen + 6 +
      8 * (4 * (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 1) + 2) + 7 +
      majorityThreshold P.walkLen + cap37 (filterTable P e L) (majorityThreshold P.walkLen) L + 10 ≤ cap)
    (crw : (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true
      (sliceLabs r4 G off L))).length ≤ cap)
    (hscr : ∀ j : Fin (1 + (1 + (14 + F37.t) + 1)), j.val ≠ 0 → j.val ≠ 12 →
      σ.st (tmapR W.x j) = [] ∧ σ.sh (tmapR W.x j) = 0) :
    ∃ σF m, Step (filtPipeM W) m (wenc cap σ).H (wenc cap σ).A (wenc cap σF).H (wenc cap σF).A ∧
      σF.st (sk W.x 1) = out ++ (filtRefC (filterTable P e L) (majorityThreshold P.walkLen) L true
        (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t) ++ [false] ∧
      σF.sh (sk W.x 1) = (out ++ (filtRefC (filterTable P e L) (majorityThreshold P.walkLen) L true
        (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t)).length ∧
      (∀ k : Fin 161, (k.val = 0 ∨ k.val = 2) → σF.st (sk W.x k) = σ.st (sk W.x k) ∧ σF.sh (sk W.x k) = σ.sh (sk W.x k)) ∧
      m ≤ filtPipeBound P e L r4 G off RW LW := by
  have hm1 := one_le_fieldBits' P
  -- the modulus
  obtain ⟨To1, s1, m82, m82h⟩ := modStage cap σ P.fieldBits hm1 hmod hmsc hmh
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = updS (tmapM W.x) σ (fun _ => 0) To1 := ⟨_, rfl⟩
  rw [← hσ1] at s1 m82 m82h
  have h1o : ∀ k : Fin 161, (k.val ≠ 82 ∧ (k.val < 91 ∨ 107 < k.val)) →
      σ1.st (sk W.x k) = σ.st (sk W.x k) ∧ σ1.sh (sk W.x k) = σ.sh (sk W.x k) := fun k hk => by
    rw [hσ1]
    exact updM_other σ _ _ k hk
  have h1T : ∀ k : Fin W.x, σ1.st (sT W.x k) = σ.st (sT W.x k) ∧ σ1.sh (sT W.x k) = σ.sh (sT W.x k) := fun k => by
    rw [hσ1]
    exact updM_T σ _ _ k
  have h1v : σ1.val = σ.val := by rw [hσ1]; rfl
  have h1c : σ1.cell = σ.cell := by rw [hσ1]; rfl
  -- the trace mask
  have hsmv : ∀ j : Fin 7, 1 ≤ j.val → (smv j).val ≠ 82 ∧ ((smv j).val < 91 ∨ 107 < (smv j).val) := by decide
  obtain ⟨σ2, e2, t81, t81h, t82, tsh, -, -, hWF⟩ := PrimT.tauW_spec cap (SmT W.x) RgT P.fieldBits
    (GF.firstPrimitive P.fieldBits) (GF.firstPrimitive_cert _ hm1) hcapT σ1 m82 m82h
    (((h1o _ (hsmv 1 (by decide))).1).trans (htau 1 (by decide)).1)
    (((h1o _ (hsmv 1 (by decide))).2).trans (htau 1 (by decide)).2)
    (((h1o _ (hsmv 2 (by decide))).1).trans (htau 2 (by decide)).1)
    (((h1o _ (hsmv 2 (by decide))).2).trans (htau 2 (by decide)).2) 0 0 0 0
    (((h1o _ (hsmv 3 (by decide))).1).trans (htau 3 (by decide)).1)
    (((h1o _ (hsmv 3 (by decide))).2).trans (htau 3 (by decide)).2)
    (((h1o _ (hsmv 4 (by decide))).1).trans (htau 4 (by decide)).1)
    (((h1o _ (hsmv 4 (by decide))).2).trans (htau 4 (by decide)).2)
    (((h1o _ (hsmv 5 (by decide))).1).trans (htau 5 (by decide)).1)
    (((h1o _ (hsmv 5 (by decide))).2).trans (htau 5 (by decide)).2)
    (((h1o _ (hsmv 6 (by decide))).1).trans (htau 6 (by decide)).1)
    (((h1o _ (hsmv 6 (by decide))).2).trans (htau 6 (by decide)).2)
    (fun j hj => (congrFun h1v _).trans (htauR j hj)) ((congrFun h1v _).trans htauR4)
  obtain ⟨hWs, hWr, hWc⟩ := hWF
  have h2o : ∀ k : Fin 161, (k.val ≠ 81 ∧ k.val ≠ 82 ∧ (k.val < 108 ∨ 112 < k.val)) →
      σ2.st (sk W.x k) = σ1.st (sk W.x k) ∧ σ2.sh (sk W.x k) = σ1.sh (sk W.x k) :=
    fun k hk => hWs _ (fun ⟨j, hj⟩ => SmT_ne k hk j hj)
  have h2T : ∀ k : Fin W.x, σ2.st (sT W.x k) = σ1.st (sT W.x k) ∧ σ2.sh (sT W.x k) = σ1.sh (sT W.x k) :=
    fun k => hWs _ (fun ⟨j, hj⟩ => SmT_ne_T k j hj)
  have h2v : ∀ r : Fin LNR, (r.val < 219 ∨ 227 < r.val) → σ2.val r = σ1.val r :=
    fun r hr => hWr r (fun ⟨j, hj⟩ => RgT_ne r hr j hj)
  have e2s := (WExec.exec cap e2).step
  -- the walk
  have hpT : ∀ j : Fin 14, (portT j).val ≠ 82 ∧ ((portT j).val < 91 ∨ 107 < (portT j).val) ∧ (portT j).val ≠ 81 ∧
      ((portT j).val < 108 ∨ 112 < (portT j).val) := by decide
  have h12 : ∀ j : Fin 14, σ2.st (sk W.x (portT j)) = σ.st (sk W.x (portT j)) ∧
      σ2.sh (sk W.x (portT j)) = σ.sh (sk W.x (portT j)) := fun j => by
    obtain ⟨a1, a2, a3, a4⟩ := hpT j
    obtain ⟨b1, b2⟩ := h2o _ ⟨a3, a1, a4⟩
    obtain ⟨c1, c2⟩ := h1o _ ⟨a1, a2⟩
    exact ⟨b1.trans c1, b2.trans c2⟩
  obtain ⟨J, -, s3⟩ := walkStage cap W σ2 (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW sample hRW
    hLW (fun j => (h12 j).1.trans (hin j)) (fun j => (h12 j).2.trans (hh j))
    (fun k => ((h2T k).1.trans (h1T k).1).trans (hsc k)) (fun k => ((h2T k).2.trans (h1T k).2).trans (hsh k))
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = updS (tmapT W.x) σ2 (Fin.addCases (motive := fun _ => ℕ)
      (outHeads (2 * (P.errExp / 4))) (fun _ => 0)) (Fin.addCases (motive := fun _ => List Bool)
      (outPorts (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW sample) J) := ⟨_, rfl⟩
  have s3' : Step (walkM W) (walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW)
      (wenc cap σ2).H (wenc cap σ2).A (wenc cap σ3).H (wenc cap σ3).A := by
    rw [hσ3]
    exact s3
  have h3o : ∀ k : Fin 161, (∀ j : Fin 14, portT j ≠ k) →
      σ3.st (sk W.x k) = σ2.st (sk W.x k) ∧ σ3.sh (sk W.x k) = σ2.sh (sk W.x k) := fun k hk => by
    rw [hσ3]
    exact ⟨updT_st_other σ2 _ _ k hk, updT_sh_other σ2 _ _ k hk⟩
  have h3pst : ∀ j : Fin 14, σ3.st (sk W.x (portT j)) =
      outPorts (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW sample j :=
    fun j => by rw [hσ3, updT_st_port, Fin.addCases_left]
  have h3psh : ∀ j : Fin 14, σ3.sh (sk W.x (portT j)) = outHeads (2 * (P.errExp / 4)) j :=
    fun j => by rw [hσ3, updT_sh_port, Fin.addCases_left]
  have h3v : σ3.val = σ2.val := by rw [hσ3]; rfl
  have h3c : σ3.cell = σ2.cell := by rw [hσ3]; rfl
  -- a stream no stage before the table touches
  have hkeep : ∀ k : Fin 161, (k.val ≠ 5 ∧ k.val ≠ 7 ∧ (k.val < 17 ∨ 28 < k.val) ∧ k.val ≠ 81 ∧ k.val ≠ 82 ∧
      (k.val < 91 ∨ 112 < k.val)) → σ3.st (sk W.x k) = σ.st (sk W.x k) ∧ σ3.sh (sk W.x k) = σ.sh (sk W.x k) :=
    fun k hk => by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hk
      obtain ⟨b1, b2⟩ := h3o k (fun j h => by
        have := portT_le j
        have := portT_ge j
        have hj := congrArg Fin.val h
        have hT : ∀ j : Fin 14, (portT j).val = 5 ∨ (portT j).val = 7 ∨ (17 ≤ (portT j).val ∧ (portT j).val ≤ 28) := by
          decide
        rcases hT j with h' | h' | h' <;> omega)
      obtain ⟨c1, c2⟩ := h2o k ⟨a4, a5, by omega⟩
      obtain ⟨d1, d2⟩ := h1o k ⟨a5, by omega⟩
      exact ⟨b1.trans (c1.trans d1), b2.trans (c2.trans d2)⟩
  -- the table
  have hst4 : ∀ i, σ3.st (fsF W.x i) = (yFC P L RW LW sample).st i := by
    intro i
    by_cases i0 : i.val = 0
    · have : i = 0 := Fin.ext i0
      subst this
      rw [show fsF W.x 0 = sk W.x (portT 0) from congrArg (sk W.x) (Fin.ext rfl), h3pst]
      rfl
    · by_cases i1 : i.val = 1
      · have : i = 1 := Fin.ext i1
        subst this
        rw [show fsF W.x 1 = sk W.x 80 from congrArg (sk W.x) (Fin.ext rfl),
          (hkeep 80 (by decide)).1, hC51.1, yFC_st1]
      · by_cases i2 : i.val = 2
        · have : i = 2 := Fin.ext i2
          subst this
          rw [show fsF W.x 2 = sk W.x 81 from congrArg (sk W.x) (Fin.ext rfl),
            (h3o 81 (by decide)).1, show sk W.x 81 = SmT W.x 1 from rfl, t81]
          rfl
        · by_cases i3 : i.val = 3
          · have : i = 3 := Fin.ext i3
            subst this
            rw [show fsF W.x 3 = sk W.x 82 from congrArg (sk W.x) (Fin.ext rfl),
              (h3o 82 (by decide)).1, show sk W.x 82 = SmT W.x 0 from rfl, t82, show SmT W.x 0 = sk W.x 82 from rfl, m82]
            rfl
          · have hi4 : 4 ≤ i.val := by omega
            have ev : fsF W.x i = sk W.x ⟨79 + i.val, by omega⟩ :=
              congrArg (sk W.x) (Fin.ext (by show (if i.val = 0 then 5 else 79 + i.val) = 79 + i.val; rw [if_neg i0]))
            rw [ev, (hkeep _ ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega, by simp; omega,
              by simp; omega⟩).1, ← ev]
            exact (hC5 i hi4).1
  have hsh4 : ∀ i, σ3.sh (fsF W.x i) = (yFC P L RW LW sample).sh i := by
    intro i
    rw [yFC_sh]
    by_cases i0 : i.val = 0
    · have : i = 0 := Fin.ext i0
      subst this
      rw [show fsF W.x 0 = sk W.x (portT 0) from congrArg (sk W.x) (Fin.ext rfl), h3psh]
      rfl
    · by_cases i1 : i.val = 1
      · have : i = 1 := Fin.ext i1
        subst this
        rw [show fsF W.x 1 = sk W.x 80 from congrArg (sk W.x) (Fin.ext rfl), (hkeep 80 (by decide)).2, hC51.2]
      · by_cases i2 : i.val = 2
        · have : i = 2 := Fin.ext i2
          subst this
          rw [show fsF W.x 2 = sk W.x 81 from congrArg (sk W.x) (Fin.ext rfl), (h3o 81 (by decide)).2]
          exact tsh 1
        · by_cases i3 : i.val = 3
          · have : i = 3 := Fin.ext i3
            subst this
            rw [show fsF W.x 3 = sk W.x 82 from congrArg (sk W.x) (Fin.ext rfl), (h3o 82 (by decide)).2]
            exact tsh 0
          · have hi4 : 4 ≤ i.val := by omega
            have ev : fsF W.x i = sk W.x ⟨79 + i.val, by omega⟩ :=
              congrArg (sk W.x) (Fin.ext (by show (if i.val = 0 then 5 else 79 + i.val) = 79 + i.val; rw [if_neg i0]))
            rw [ev, (hkeep _ ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega, by simp; omega,
              by simp; omega⟩).2, ← ev]
            exact (hC5 i hi4).2
  have hv4 : ∀ r, σ3.val (frC r) = (yFC P L RW LW sample).val r := fun r => by
    rw [h3v, h2v _ (Or.inl (by have := r.isLt; show r.val < 219; omega)), h1v]
    exact hC5r r
  have s4 := filtBuildStage cap W.x σ3 P e L RW LW hU sample hvert hRW hLW hcap6 hO6 hsh4 hst4 hv4
    (by rw [h3c, hWc, h1c, hcell])
    (fun k => by rw [show emF W.x k = sk W.x (portT ⟨k.val + 1, by omega⟩) from rfl, h3psh, outHeads_bank1])
    (fun k => by rw [show emF W.x k = sk W.x (portT ⟨k.val + 1, by omega⟩) from rfl, h3pst, outPorts_bank1])
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = updW (fsF W.x) frC (emF W.x) σ3
      (finalW P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
        (WalkTimeLoop.A RW LW sample [] (2 * (P.errExp / 4)) 0) (tableWord (filterTable P e L)))
      (Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ)
        (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) (2 * (P.errExp / 4)) k.succ) (fun _ => 1))
      (Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
        (fun k => WalkTimeLoop.A RW LW sample [] (2 * (P.errExp / 4)) k.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4)))) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have h4o : ∀ k : Fin 161, (k.val ≠ 5 ∧ k.val ≠ 7 ∧ (k.val < 17 ∨ 23 < k.val) ∧ (k.val < 80 ∨ 90 < k.val)) →
      σ4.st (sk W.x k) = σ3.st (sk W.x k) ∧ σ4.sh (sk W.x k) = σ3.sh (sk W.x k) := fun k hk => by
    rw [hσ4]
    exact ⟨updF_st_other σ3 _ _ _ k hk, updF_sh_other σ3 _ _ _ k hk⟩
  have h4tab : σ4.st (sk W.x 80) = tableWord (filterTable P e L) ∧ σ4.sh (sk W.x 80) = 0 := by
    rw [hσ4, show sk W.x 80 = fsF W.x 1 from congrArg (sk W.x) (Fin.ext rfl), updF_st_fs, updF_sh_fs]
    exact ⟨rfl, by simp [finalW]⟩
  have hFR : ∀ i : Fin 20, σ4.val (FR i) = σ.val (FR i) := fun i => by
    have hv : (FR i).val = 230 + i.val := rfl
    rw [hσ4, updF_val_other σ3 _ _ _ _ (by rw [hv]; omega), h3v, h2v _ (Or.inr (by rw [hv]; omega)), h1v]
  -- the record
  have hK : ∀ k : Fin 161, (k.val = 1 ∨ k.val = 3 ∨ (30 ≤ k.val ∧ k.val ≤ 56)) →
      σ4.st (sk W.x k) = σ.st (sk W.x k) ∧ σ4.sh (sk W.x k) = σ.sh (sk W.x k) := fun k hk => by
    obtain ⟨b1, b2⟩ := h4o k ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨c1, c2⟩ := hkeep k ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact ⟨b1.trans c1, b2.trans c2⟩
  obtain ⟨m5, τ5, e5, r5, r5h, k5, b5⟩ := fcellW_spec cap σ4 P e L r4 G off Mlab hlen
    ((hFR 0).trans hF0) ((hFR 1).trans hF1) ((hFR 2).trans hF2) ((hFR 3).trans hF3) ((hFR 4).trans hF4)
    (fun i a b => (hFR i).trans (hFz i a b)) ((hFR 13).trans hF13) ((hFR 14).trans hF14) ((hFR 15).trans hF15)
    ((hFR 16).trans hF16) ((hFR 17).trans hF17) ((hFR 18).trans hF18) ((hFR 19).trans hF19)
    ((hK 3 (by decide)).1.trans hrec) ((hK 3 (by decide)).2.trans hrec0) h4tab.1 h4tab.2 hM cA cB cC cD crw
  have s5 := (WExec.exec cap e5).step
  -- the FILTER row
  have hscr5 : ∀ j : Fin (1 + (1 + (14 + F37.t) + 1)), j.val ≠ 0 → j.val ≠ 12 →
      τ5.st (tmapR W.x j) = [] ∧ τ5.sh (tmapR W.x j) = 0 := by
    intro j j0 j12
    have hv : (portR (Fin.cast F28 j)).val = 29 + j.val := by
      rw [portR_val, Fin.val_cast, if_neg j0, if_neg j12]
    have hj28 : j.val < 28 := j.isLt
    have n3 : portR (Fin.cast F28 j) ≠ 3 := fun h => by
      have h' := congrArg Fin.val h
      have e3 : (3 : Fin 161).val = 3 := rfl
      rw [hv, e3] at h'
      omega
    have n80 : portR (Fin.cast F28 j) ≠ 80 := fun h => by
      have h' := congrArg Fin.val h
      have e80 : (80 : Fin 161).val = 80 := rfl
      rw [hv, e80] at h'
      omega
    obtain ⟨k1, k2⟩ := k5 (tmapR W.x j) (sk_ne _ _ n3) (sk_ne _ _ n80)
    obtain ⟨c1, c2⟩ := hK (portR (Fin.cast F28 j)) (Or.inr (Or.inr ⟨by omega, by omega⟩))
    obtain ⟨s1', s2'⟩ := hscr j j0 j12
    exact ⟨k1.trans (c1.trans s1'), k2.trans (c2.trans s2')⟩
  have n13 : sk W.x 1 ≠ sk W.x 3 := sk_ne _ _ (by decide)
  have n180 : sk W.x 1 ≠ sk W.x 80 := sk_ne _ _ (by decide)
  obtain ⟨n6, Ho, To, hn6, s6, o6, o6h⟩ := filtRowStage cap τ5 (filterTable P e L) (majorityThreshold P.walkLen) L
    (fun vs hvs cs hcs => (filterTable_lengths P e L vs hvs cs hcs).le) (sliceLabs r4 G off L) hlabs out r5 r5h
    (((k5 _ n13 n180).1.trans (hK 1 (by decide)).1).trans hout)
    (((k5 _ n13 n180).2.trans (hK 1 (by decide)).2).trans houth) hscr5
  -- the output head back
  have eF := WExec.bwd (cap := cap) (sk W.x 1) (updS (tmapR W.x) τ5 Ho To)
  have sF := (WExec.exec cap eF).step
  refine ⟨_, _, Step.seq (Step.seq (Step.seq (Step.seq (Step.seq (Step.seq s1 e2s) s3') s4) s5)
    (Step.enlarge s6 hn6)) sF, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]
    rw [o6, exprWord_eq, List.append_assoc]
  · simp only [WState.seth_sh, Function.update_self]
    rw [o6h, exprWord_eq]
    simp
  · intro k hk
    have n1 : sk W.x k ≠ sk W.x 1 := sk_ne _ _ (fun h => by rw [h] at hk; revert hk; decide)
    have nk3 : sk W.x k ≠ sk W.x 3 := sk_ne _ _ (fun h => by rw [h] at hk; revert hk; decide)
    have nk80 : sk W.x k ≠ sk W.x 80 := sk_ne _ _ (fun h => by rw [h] at hk; revert hk; decide)
    obtain ⟨k1, k2⟩ := k5 (sk W.x k) nk3 nk80
    obtain ⟨b1, b2⟩ := h4o k ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨c1, c2⟩ := hkeep k ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hRne : ∀ j, tmapR W.x j ≠ sk W.x k := fun j h => by
      have hv := congrArg Fin.val (sk_inj W.x h)
      rw [portR_val, Fin.val_cast] at hv
      split_ifs at hv <;> omega
    refine ⟨?_, ?_⟩
    · simp only [WState.seth_st]
      show install (tmapR W.x) τ5.st To (sk W.x k) = _
      rw [install_other _ _ _ _ hRne]
      exact k1.trans (b1.trans c1)
    · simp only [WState.seth_sh, Function.update_apply, if_neg n1]
      show dockH (tmapR W.x) τ5.sh Ho (sk W.x k) = _
      rw [dockH_other _ _ _ _ hRne]
      exact k2.trans (b2.trans c2)
  · unfold filtPipeBound
    have hb : Modulus.modCost P.fieldBits + 1 + PrimT.tauCost P.fieldBits + 1 +
        walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW + 1 +
        (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 RW + 3) + 3 + 1 +
          lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4))) + 1 + m5 + 1 +
        filtCostC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L) + 1 + 1 ≤
        Modulus.modCost P.fieldBits + 1 + PrimT.tauCost P.fieldBits + 1 +
        walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW + 1 +
        (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 RW + 3) + 3 + 1 +
          lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4))) + 1 +
        (filtBound (4 * L) (filtDeg (filterTable P e L)) (majorityThreshold P.walkLen)
            (cap37 (filterTable P e L) (majorityThreshold P.walkLen) L) (tableWord (filterTable P e L)).length
            (labSum (sliceLabs r4 G off L)) r4 G off L + 1 +
          (5 * (frame (filtRecC (filterTable P e L) (majorityThreshold P.walkLen) L true
            (sliceLabs r4 G off L))).length + 1)) + 1 +
        filtCostC (filterTable P e L) (majorityThreshold P.walkLen) L true (sliceLabs r4 G off L) + 1 + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_left b5 _) _) _) _) _
    exact hb

end FPipe

end NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
