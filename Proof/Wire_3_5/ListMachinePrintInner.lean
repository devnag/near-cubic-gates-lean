import Proof.Wire_3_5.ListMachinePrintBank

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

structure PointEval (L : ℕ) (f : List Bool → Bool) where
  t : ℕ
  s : ℕ
  machine : Machine (2 + t) s
  data : Fin t → List Bool
  cost : ℕ
  step : ∀ (Z : List Bool) (b : Bool), Z.length = L →
    Step machine cost (fun _ => 0) (Fin.addCases ![frame Z, [b]] data) (fun _ => 0)
      (Fin.addCases ![frame Z, [f Z]] data)

/-! ## Lifting the bank -/

theorem castAdd_inj (N t : ℕ) : Function.Injective (Fin.castAdd t : Fin N → Fin (N + t)) :=
  fun _ _ h => Fin.castAdd_inj.mp h

theorem castAdd_ne_natAdd' {N t : ℕ} (j : Fin N) (b : Fin t) : Fin.castAdd t j ≠ Fin.natAdd N b := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem install_castAdd {N t : ℕ} (A : Fin N → List Bool) (d : Fin t → List Bool) (v : Fin N → List Bool) :
    RecoveryRootRound.install (Fin.castAdd t) (Fin.addCases A d) v = Fin.addCases v d := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [RecoveryRootRound.install_slot _ (castAdd_inj N t), Fin.addCases_left]
  · rw [RecoveryRootRound.install_other _ _ _ _ (fun j h => castAdd_ne_natAdd' j b h), Fin.addCases_right,
      Fin.addCases_right]

theorem dockH_castAdd {N t : ℕ} (H : Fin N → ℕ) (hd : Fin t → ℕ) (v : Fin N → ℕ) :
    dockH (Fin.castAdd t) (Fin.addCases H hd) v = Fin.addCases v hd := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [dockH_slot _ (castAdd_inj N t), Fin.addCases_left]
  · rw [dockH_other _ _ _ _ (fun j h => castAdd_ne_natAdd' j b h), Fin.addCases_right, Fin.addCases_right]

/-- **A bank stage lifted over the evaluator's tapes.** -/
theorem lift_stage {t s n : ℕ} {p : Machine 14 s} {H H' : Fin 14 → ℕ} {A A' : Fin 14 → List Bool}
    (h : Step p n H A H' A') (d : Fin t → List Bool) :
    Step (RecoveryFocus.machine (Fin.castAdd t) p) n (Fin.addCases H (fun _ => 0)) (Fin.addCases A d)
      (Fin.addCases H' (fun _ => 0)) (Fin.addCases A' d) := by
  have hd := dockRun h (Fin.castAdd t) (castAdd_inj 14 t) (Fin.addCases H (fun _ => 0)) (Fin.addCases A d)
    (fun j => Fin.addCases_left j) (fun j => Fin.addCases_left j)
  rwa [dockH_castAdd, install_castAdd] at hd

/-! ## The evaluator on the sub-bitmap and the result cell -/

/-- The evaluator's slots: the sub-bitmap (1), the result cell (2), then its own tapes. -/
def evS (t : ℕ) : Fin (2 + t) → Fin (14 + t) :=
  Fin.addCases (fun j : Fin 2 => Fin.castAdd t (![1, 2] j)) (fun j => Fin.natAdd 14 j)

theorem evS_inj (t : ℕ) : Function.Injective (evS t) := by
  intro i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    intro h
  · simp only [evS, Fin.addCases_left] at h
    have := Fin.castAdd_inj.mp h
    congr 1
    fin_cases a <;> fin_cases b <;> simp_all
  · simp only [evS, Fin.addCases_left, Fin.addCases_right] at h
    exact absurd h (castAdd_ne_natAdd' _ _)
  · simp only [evS, Fin.addCases_left, Fin.addCases_right] at h
    exact absurd h.symm (castAdd_ne_natAdd' _ _)
  · simp only [evS, Fin.addCases_right] at h
    congr 1
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    exact this

theorem evS_left (t : ℕ) (j : Fin 2) : evS t (Fin.castAdd t j) = Fin.castAdd t (![1, 2] j) := by
  simp [evS]

theorem evS_right (t : ℕ) (j : Fin t) : evS t (Fin.natAdd 2 j) = Fin.natAdd 14 j := by
  simp [evS]

theorem install_evS {t : ℕ} (A : Fin 14 → List Bool) (d d' : Fin t → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install (evS t) (Fin.addCases A d) (Fin.addCases v d') =
      Fin.addCases (fun i => if i = 1 then v 0 else if i = 2 then v 1 else A i) d' := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [Fin.addCases_left]
    by_cases h1 : a = 1
    · subst h1
      have e : (Fin.castAdd t (1 : Fin 14) : Fin (14 + t)) = evS t (Fin.castAdd t 0) := by rw [evS_left]; rfl
      rw [e, RecoveryRootRound.install_slot _ (evS_inj t), Fin.addCases_left]
      simp
    · by_cases h2 : a = 2
      · subst h2
        have e : (Fin.castAdd t (2 : Fin 14) : Fin (14 + t)) = evS t (Fin.castAdd t 1) := by rw [evS_left]; rfl
        rw [e, RecoveryRootRound.install_slot _ (evS_inj t), Fin.addCases_left]
        simp
      · rw [RecoveryRootRound.install_other, Fin.addCases_left, if_neg h1, if_neg h2]
        intro j
        refine Fin.addCases (fun c => ?_) (fun c => ?_) j
        · rw [evS_left]
          intro h
          have := Fin.castAdd_inj.mp h
          fin_cases c <;> simp_all
        · rw [evS_right]
          exact fun h => castAdd_ne_natAdd' a c h.symm
  · rw [Fin.addCases_right]
    rw [← evS_right, RecoveryRootRound.install_slot _ (evS_inj t), Fin.addCases_right]

/-- **The evaluator stage**: the result cell becomes `[f Z]` for the sub-bitmap `frame Z`. -/
theorem ev_stage {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (b : Bank) (o : ℕ) (Z : List Bool) (c : Bool)
    (hZ : Z.length = L) (ht : b.t = frame Z) (hr : b.r = [c]) :
    Step (RecoveryFocus.machine (evS E.t) E.machine) E.cost
      (Fin.addCases (bh o) (fun _ => 0)) (Fin.addCases b.tapes E.data)
      (Fin.addCases (bh o) (fun _ => 0)) (Fin.addCases { b with r := [f Z] }.tapes E.data) := by
  have h := Block.dockKeep (E.step Z c hZ) (evS E.t) (evS_inj E.t) (Fin.addCases (bh o) (fun _ => 0))
    (Fin.addCases b.tapes E.data)
    (by intro j; refine Fin.addCases (fun a => ?_) (fun a => ?_) j
        · rw [evS_left, Fin.addCases_left]; fin_cases a <;> rfl
        · rw [evS_right, Fin.addCases_right])
    (by intro j; refine Fin.addCases (fun a => ?_) (fun a => ?_) j
        · rw [evS_left, Fin.addCases_left, Fin.addCases_left]
          fin_cases a
          · exact ht
          · exact hr
        · rw [evS_right, Fin.addCases_right, Fin.addCases_right])
  rw [install_evS] at h
  have e : (fun i : Fin 14 => if i = 1 then ![frame Z, [f Z]] 0 else if i = 2 then ![frame Z, [f Z]] 1 else b.tapes i) =
      { b with r := [f Z] }.tapes := by
    funext i; fin_cases i <;> simp [Bank.tapes, ht]
  rw [e] at h
  exact h

/-! ## The rest of one pass, on the bank: accumulate, step the sub-bitmap, test it -/

def xorOp (t a _ : Bool) : Bool := xor t a
def orFold (a _ s : Bool) : Bool := s || a

theorem foldBits_orFold (u v : List Bool) (hl : u.length = v.length) (s : Bool) :
    Block.foldBits orFold s u v = (s || u.any id) := by
  induction u generalizing v s with
  | nil => cases v <;> simp [Block.foldBits]
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v =>
      rw [Block.foldBits, ih v (by simpa using hl)]
      simp [orFold, Bool.or_assoc]

def sAR : Fin 3 → Fin 14 := ![3, 2, 4]
theorem sAR_inj : Function.Injective sAR := by decide
def pAR : Fin 14 → Option (Fin 3) :=
  ![none, none, some 1, some 0, some 2, none, none, none, none, none, none, none, none, none]
theorem pick_sAR : ∀ i, RecoveryFocus.pick sAR i = pAR i := by pick_table sAR_inj

def sTXL : Fin 3 → Fin 14 := ![1, 0, 12]
theorem sTXL_inj : Function.Injective sTXL := by decide
def pTXL : Fin 14 → Option (Fin 3) :=
  ![some 1, some 0, none, none, none, none, none, none, none, none, none, none, some 2, none]
theorem pick_sTXL : ∀ i, RecoveryFocus.pick sTXL i = pTXL i := by pick_table sTXL_inj

def sTXFL : Fin 4 → Fin 14 := ![1, 0, 4, 12]
theorem sTXFL_inj : Function.Injective sTXFL := by decide
def pTXFL : Fin 14 → Option (Fin 4) :=
  ![some 1, some 0, none, none, some 2, none, none, none, none, none, none, none, some 3, none]
theorem pick_sTXFL : ∀ i, RecoveryFocus.pick sTXFL i = pTXFL i := by pick_table sTXFL_inj

/-- The rest of one pass: `A := A ⊕ R`, `T := T + 1` over the ones of `X`, `FI := [T ≠ 0]`. -/
noncomputable def innerRest := Composition.machine
  (Composition.machine (RecoveryFocus.machine sAR (GF2.CellOp.machine xorOp))
    (RecoveryFocus.machine sTXL (MaskedReset.machine (Block.RippleIn.machine Interp.gS Interp.hS true) selTT)))
  (RecoveryFocus.machine sTXFL (MaskedReset.machine (Block.FoldCell.machine orFold false) selTTF))

def innerRestCost (L : ℕ) : ℕ := 1 + 1 + (2 * (2 * L + 1) + 2) + 1 + (2 * (2 * L + 1) + 2)

theorem innerRest_step (b : Bank) (o : ℕ) (xs : List Bool) (j : ℕ) (acc fz fi0 : Bool) (cap : ℕ)
    (hx : b.x = frame xs) (ht : b.t = frame (Interp.spread xs j)) (hr : b.r = [fz]) (ha : b.a = [acc])
    (hfi : b.fi = [fi0]) (hl : b.l1 = List.replicate cap false) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step innerRest (innerRestCost xs.length) (bh o) b.tapes (bh o)
      { b with a := [xor acc fz], t := frame (Interp.spread xs (j + 1)),
               fi := [(Interp.spread xs (j + 1)).any id] }.tapes := by
  -- accumulate
  have s1 := cell_step xorOp sAR sAR_inj o b { b with a := [xor acc fz] } acc fz fi0
    (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k
        · exact ha
        · exact hr
        · exact hfi)
    (by rw [install_of_pick sAR pAR pick_sAR]; funext i; fin_cases i <;> simp [pAR, Bank.tapes, hr, hfi, xorOp])
  -- step the sub-bitmap
  set b1 := { b with a := [xor acc fz] } with hb1
  have hl1 : (Interp.spread xs j).length = xs.length := Interp.spread_length xs j
  have s2 := ripple_stage Interp.gS Interp.hS true sTXL sTXL_inj o b1
    { b1 with t := frame (Interp.spread xs (j + 1)) } (Interp.spread xs j) xs hl1 cap (by rw [hl1]; exact hcap)
    (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k
        · exact ht
        · exact hx
        · exact hl)
    (by rw [install_of_pick sTXL pTXL pick_sTXL, Interp.ripple_spread]
        funext i; fin_cases i <;> simp [pTXL, Bank.tapes, hx, hl, hb1])
  -- test it
  set b2 := { b1 with t := frame (Interp.spread xs (j + 1)) } with hb2
  have hl2 : (Interp.spread xs (j + 1)).length = xs.length := Interp.spread_length xs (j + 1)
  have s3 := fold_stage orFold false sTXFL sTXFL_inj o b2
    { b2 with fi := [(Interp.spread xs (j + 1)).any id] } (Interp.spread xs (j + 1)) xs fi0 hl2 cap
    (by rw [hl2]; exact hcap)
    (by intro k; fin_cases k <;> rfl)
    (by intro k; fin_cases k
        · rfl
        · exact hx
        · exact hfi
        · exact hl)
    (by rw [install_of_pick sTXFL pTXFL pick_sTXFL, foldBits_orFold _ _ hl2]
        funext i; fin_cases i <;> simp [pTXFL, Bank.tapes, hx, hl, hb2, hb1])
  have t := Step.seq (Step.seq s1 s2) s3
  refine t.enlarge (le_of_eq ?_)
  simp [innerRestCost, hl1]

/-! ## One pass and the loop -/

/-- One pass: evaluate `f` at the sub-bitmap, accumulate, step, test. -/
noncomputable def innerBody {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) :=
  Composition.machine (RecoveryFocus.machine (evS E.t) E.machine) (RecoveryFocus.machine (Fin.castAdd E.t) innerRest)

/-- The result cell before pass `j`: the value at the previous sub-bitmap. -/
def rAt (f : List Bool → Bool) (xs : List Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => f (Interp.spread xs k)

/-- The coefficient cell before pass `j`. -/
def accAt (f : List Bool → Bool) (xs : List Bool) (j : ℕ) : Bool :=
  (List.range j).foldl (fun acc i => xor acc (f (Interp.spread xs i))) false

theorem accAt_succ (f : List Bool → Bool) (xs : List Bool) (j : ℕ) :
    accAt f xs (j + 1) = xor (accAt f xs j) (f (Interp.spread xs j)) := by
  simp [accAt, List.range_succ, List.foldl_append]

theorem spread_any_succ (xs : List Bool) (j : ℕ) (hj : j < 2 ^ Interp.pop xs) :
    (Interp.spread xs (j + 1)).any id = decide (j + 1 < 2 ^ Interp.pop xs) := by
  rcases Nat.lt_or_eq_of_le (show j + 1 ≤ 2 ^ Interp.pop xs by omega) with h | h
  · rw [Interp.spread_any xs (j + 1) h]; simp [h]
  · rw [h, Interp.spread_pow]; simp

/-- The bank before pass `j` of the inner loop over the sub-bitmaps of `xs`. -/
def innerBank (f : List Bool → Bool) (b0 : Bank) (xs : List Bool) (j : ℕ) : Bank :=
  { b0 with t := frame (Interp.spread xs j), r := [rAt f xs j], a := [accAt f xs j],
            fi := [decide (j < 2 ^ Interp.pop xs)] }

theorem innerBody_step {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (b0 : Bank) (o : ℕ) (xs : List Bool)
    (hL : xs.length = L) (cap : ℕ) (hx : b0.x = frame xs) (hl : b0.l1 = List.replicate cap false)
    (hcap : 2 * xs.length + 1 ≤ cap) (j : ℕ) (hj : j < 2 ^ Interp.pop xs) :
    Step (innerBody E) (E.cost + 1 + innerRestCost xs.length)
      (Fin.addCases (bh o) (fun _ => 0)) (Fin.addCases (innerBank f b0 xs j).tapes E.data)
      (Fin.addCases (bh o) (fun _ => 0)) (Fin.addCases (innerBank f b0 xs (j + 1)).tapes E.data) := by
  have h1 := ev_stage E (innerBank f b0 xs j) o (Interp.spread xs j) (rAt f xs j)
    (by rw [Interp.spread_length, hL]) rfl rfl
  have h2 := lift_stage (innerRest_step { innerBank f b0 xs j with r := [f (Interp.spread xs j)] } o xs j
    (accAt f xs j) (f (Interp.spread xs j)) (decide (j < 2 ^ Interp.pop xs)) cap hx rfl rfl rfl rfl hl hcap) E.data
  have t := Step.seq h1 h2
  have e : ({ { innerBank f b0 xs j with r := [f (Interp.spread xs j)] } with
      a := [xor (accAt f xs j) (f (Interp.spread xs j))], t := frame (Interp.spread xs (j + 1)),
      fi := [(Interp.spread xs (j + 1)).any id] } : Bank).tapes = (innerBank f b0 xs (j + 1)).tapes := by
    funext i; fin_cases i <;> simp [Bank.tapes, innerBank, accAt_succ, spread_any_succ xs j hj, rAt]
  rw [e] at t
  exact t

/-- The inner loop's pass cost. -/
def innerPassCost {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (len : ℕ) : ℕ :=
  E.cost + 1 + innerRestCost len

/-- **The inner loop** over the sub-bitmaps of `xs`. -/
noncomputable def innerLoop {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (b0 : Bank) (o : ℕ)
    (xs : List Bool) (hL : xs.length = L) (cap : ℕ) (hx : b0.x = frame xs) (hl : b0.l1 = List.replicate cap false)
    (hcap : 2 * xs.length + 1 ≤ cap) :
    Block.WhileBody (14 + E.t) (E.s + (2 + (5 + 2) + (5 + 2))) where
  body := innerBody E
  tape := Fin.castAdd E.t 4
  bound := 2 ^ Interp.pop xs
  H := fun _ => Fin.addCases (bh o) (fun _ => 0)
  A := fun j => Fin.addCases (innerBank f b0 xs j).tapes E.data
  cost := fun _ => innerPassCost E xs.length
  step := by intro j hj; exact innerBody_step E b0 o xs hL cap hx hl hcap j hj
  cont := by
    intro j hj
    simp [Fin.addCases_left, innerBank, Bank.tapes, bh, readTapeBit, hj]
  halt := by
    simp [Fin.addCases_left, innerBank, Bank.tapes, bh, readTapeBit]

theorem inner_run {L : ℕ} {f : List Bool → Bool} (E : PointEval L f) (b0 : Bank) (o : ℕ) (xs : List Bool)
    (hL : xs.length = L) (cap : ℕ) (hx : b0.x = frame xs) (hl : b0.l1 = List.replicate cap false)
    (hcap : 2 * xs.length + 1 ≤ cap) :
    Step (StreamController.machine (innerBody E) (Fin.castAdd E.t 4))
      (2 ^ Interp.pop xs * (innerPassCost E xs.length + 2) + 1)
      (Fin.addCases (bh o) (fun _ => 0))
      (Fin.addCases { b0 with t := frame (List.replicate xs.length false), r := [false], a := [false],
                              fi := [true] }.tapes E.data)
      (Fin.addCases (bh o) (fun _ => 0))
      (Fin.addCases { b0 with t := frame (List.replicate xs.length false),
                              r := [rAt f xs (2 ^ Interp.pop xs)], a := [Interp.subsetX f L (Interp.supp xs)],
                              fi := [false] }.tapes E.data) := by
  have h := (innerLoop E b0 o xs hL cap hx hl hcap).run
  rw [Block.WhileBody.rest_const _ (innerPassCost E xs.length) (fun _ => rfl)] at h
  have h' : Step (StreamController.machine (innerBody E) (Fin.castAdd E.t 4))
      (2 ^ Interp.pop xs * (innerPassCost E xs.length + 2) + 1)
      (Fin.addCases (bh o) (fun _ => 0)) (Fin.addCases (innerBank f b0 xs 0).tapes E.data)
      (Fin.addCases (bh o) (fun _ => 0)) (Fin.addCases (innerBank f b0 xs (2 ^ Interp.pop xs)).tapes E.data) := h
  have e0 : (innerBank f b0 xs 0).tapes =
      { b0 with t := frame (List.replicate xs.length false), r := [false], a := [false], fi := [true] }.tapes := by
    funext i; fin_cases i <;> simp [Bank.tapes, innerBank, Interp.spread_zero, rAt, accAt]
  have hs := Interp.subsetX_eq_spread f xs
  rw [hL] at hs
  have e1 : (innerBank f b0 xs (2 ^ Interp.pop xs)).tapes =
      { b0 with t := frame (List.replicate xs.length false), r := [rAt f xs (2 ^ Interp.pop xs)],
                 a := [Interp.subsetX f L (Interp.supp xs)], fi := [false] }.tapes := by
    funext i; fin_cases i <;> simp [Bank.tapes, innerBank, Interp.spread_pow, accAt, hs]
  rw [e0, e1] at h'
  exact h'

end NearCubicWires.WireExponent3_5.ListMachine.Print
