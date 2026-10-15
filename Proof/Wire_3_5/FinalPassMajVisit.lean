import Proof.Wire_3_5.FinalPassMajCopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Maj
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ListEval

variable (cap : ℕ)

/-! ## Stage 5 in the layout -/

/-- Stage 5's streams are the layout's first three. -/
def fsM : Fin 3 → Fin 4 := Fin.castSucc
/-- Stage 5's registers are the layout's first fifteen. -/
def frM : Fin 15 → Fin 26 := Fin.castAdd 11

theorem fsM_inj : Function.Injective fsM := Fin.castSucc_injective 3
theorem frM_inj : Function.Injective frM := Fin.castAdd_injective 15 11

/-- Stage 5's indicator program in the layout. -/
def mainM : MProg := RM.liftR fsM frM mainI

theorem frM_ne (k : ℕ) (hk : 15 ≤ k) (hk' : k < 26) : ∀ r : Fin 15, frM r ≠ ⟨k, hk'⟩ := by
  intro r h
  have := congrArg Fin.val h
  simp [frM] at this
  omega

theorem fsM_ne3 : ∀ i : Fin 3, fsM i ≠ 3 := by
  intro i h
  have := congrArg Fin.val h
  simp [fsM] at this
  omega

/-- **Stage 5 at a phase record**: with the point, the table word and `unary s` on the first three streams (heads at
`0`) and stage 5's registers blank, the indicator `[reportRef … = s]` lands in `C`; nothing else changes. -/
theorem mainM_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (x : MSt)
    (hpt : x.pt = frame Z) (ht5 : x.t5 = levelWord M J W row) (ht5h : x.t5h = 0)
    (hss : ∀ p, readTapeBit x.ss p = readTapeBit (unary s) p) (hssh : x.ssh = 0) (hc : x.c = 0)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hs : s ≤ M) (hcap : capOf M J W row Z.length ≤ cap) :
    WExec cap mainM x.w { x with c := if reportRef M J W row Z = s then 1 else 0, cell := false }.w
      (mainCost (capOf M J W row Z.length)) := by
  have h := mainI_spec M J W row Z s x.cell hrows hs
  have hrel : LiftRelR fsM frM (streams M J W row Z s) x.w (blank x.cell) := by
    refine ⟨fun i => ?_, fun i p => ?_, fun r => ?_, rfl⟩
    · fin_cases i
      · rfl
      · show x.t5h = 0; exact ht5h
      · show x.ssh = 0; exact hssh
    · fin_cases i
      · show readTapeBit x.pt p = readTapeBit (frame Z) p; rw [hpt]
      · show readTapeBit x.t5 p = readTapeBit (levelWord M J W row) p; rw [ht5]
      · exact hss p
    · fin_cases r <;> first | rfl | (show x.c = 0; exact hc)
  obtain ⟨ω, hω, hrel', hout⟩ := RExec.liftR _ _ cap hcap fsM fsM_inj frM frM_inj h x.w hrel
  refine WExec.cast cap hω ?_ (le_refl _)
  apply WState.eq
  · funext i
    fin_cases i
    · exact hrel'.sh 0
    · exact (hrel'.sh 1).trans ht5h.symm
    · exact (hrel'.sh 2).trans hssh.symm
    · exact hout.2.1 3 fsM_ne3
  · exact hout.1
  · funext r
    fin_cases r
    all_goals first
      | exact hrel'.val 0
      | exact hrel'.val 1
      | exact hrel'.val 2
      | exact hrel'.val 3
      | exact hrel'.val 4
      | exact hrel'.val 5
      | exact hrel'.val 6
      | exact hrel'.val 7
      | exact hrel'.val 8
      | exact hrel'.val 9
      | exact hrel'.val 10
      | exact hrel'.val 11
      | exact hrel'.val 12
      | exact hrel'.val 13
      | exact hrel'.val 14
      | exact hout.2.2 _ (frM_ne _ (by decide) _)
  · exact hrel'.cell

/-! ## One visit -/

/-- **One visit**: the rows copied, stage 5, the indicator added to `A`, the visit counted. -/
def visitM : MProg := .seq copyRows (.seq mainM (.seq (WM.move mC mA) (.inc mV)))

def visitCost (M J : ℕ) (W : ℕ → ℕ) (L T c5 : ℕ) : ℕ := copyCost M J W L T + 1 + (c5 + 1 + ((7 * 1 + 1) + 1 + 3))

theorem visit_spec (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) (rowOld rowNew : ℕ → List Bool) (Z : List Bool) (s : ℕ)
    (preF postF : List Bool) (x : MSt) (hZ : Z.length = L) (hO : ∀ j ≤ J, (rowOld j).length = L)
    (hN : ∀ j ≤ J, (rowNew j).length = L) (hpt : x.pt = frame Z) (ht : x.t5 = levelWord M J W rowOld)
    (hth : x.t5h = 0) (hss : ∀ p, readTapeBit x.ss p = readTapeBit (unary s) p) (hssh : x.ssh = 0) (hc : x.c = 0)
    (hf : x.ft = preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j))) ++ postF) (hfh : x.fth = preF.length)
    (hs : s ≤ M) (hcT : (levelWord M J W rowNew).length < cap)
    (hcF : (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length < cap)
    (hc5 : capOf M J W rowNew Z.length ≤ cap) (hA : x.a + 1 ≤ cap) (hV : x.v < cap) :
    WExec cap visitM x.w
      { x with t5 := levelWord M J W rowNew,
               fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length,
               a := x.a + (if reportRef M J W rowNew Z = s then 1 else 0), v := x.v + 1, cell := false }.w
      (visitCost M J W L (levelWord M J W rowNew).length (mainCost (capOf M J W rowNew Z.length))) := by
  have s1 := copyRows_spec cap M J W L rowOld rowNew preF postF x hO hN ht hth hf hfh hcT hcF
  have s2 := mainM_spec cap M J W rowNew Z s
    { x with t5 := levelWord M J W rowNew,
             fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length }
    hpt rfl hth hss hssh hc (fun j hj => by rw [hN j hj, hZ]) hs hc5
  have hind : (if reportRef M J W rowNew Z = s then 1 else 0) ≤ 1 := by split <;> omega
  have s3 := wmove_spec cap mC mA (by decide) (if reportRef M J W rowNew Z = s then 1 else 0)
    ({ x with t5 := levelWord M J W rowNew,
              fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length,
              c := if reportRef M J W rowNew Z = s then 1 else 0, cell := false } : MSt).w rfl
    (by show (if reportRef M J W rowNew Z = s then 1 else 0) ≤ cap; omega)
    (by show x.a + (if reportRef M J W rowNew Z = s then 1 else 0) ≤ cap; omega)
  rw [m_c, m_a] at s3
  have s3' : WExec cap (WM.move mC mA)
      ({ x with t5 := levelWord M J W rowNew,
                fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length,
                c := if reportRef M J W rowNew Z = s then 1 else 0, cell := false } : MSt).w
      ({ x with t5 := levelWord M J W rowNew,
                fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length,
                c := 0, a := x.a + (if reportRef M J W rowNew Z = s then 1 else 0), cell := false } : MSt).w
      (7 * 1 + 1) := WExec.mono s3 (by omega)
  have s4 := WExec.inc (cap := cap) mV
    ({ x with t5 := levelWord M J W rowNew,
              fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (rowNew j)))).length,
              c := 0, a := x.a + (if reportRef M J W rowNew Z = s then 1 else 0), cell := false } : MSt).w hV
  rw [m_v] at s4
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3' s4))) ?_ (le_refl _)
  cases x
  simp only at hc ⊢
  rw [hc]
  rfl

/-! ## The visits -/

/-- The visits, while the flat table reads a visit marker. -/
def visitsM : MProg := .whs sFT visitM

/-- The rows the template holds after the visits `ks` (the last visit's). -/
def lastRows {κ : Type} (R : κ → ℕ → List Bool) : List κ → (ℕ → List Bool) → ℕ → List Bool
  | [], r => r
  | k :: ks, _ => lastRows R ks (R k)

/-- The visit words of `ks`. -/
def visitWords {κ : Type} (J : ℕ) (R : κ → ℕ → List Bool) (ks : List κ) : List Bool :=
  ks.flatMap fun k => true :: (levels J).flatMap (fun j => frame (R k j))

/-- The visits reporting `s` among `ks`. -/
def hitsOf {κ : Type} (M J : ℕ) (W : ℕ → ℕ) (R : κ → ℕ → List Bool) (Z : List Bool) (s : ℕ) (ks : List κ) : ℕ :=
  (ks.map fun k => if reportRef M J W (R k) Z = s then 1 else 0).sum

/-- The visits' cost. -/
def visitsCost {κ : Type} (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) (R : κ → ℕ → List Bool) (Z : List Bool) (ks : List κ) : ℕ :=
  (ks.map fun k => visitCost M J W L (levelWord M J W (R k)).length (mainCost (capOf M J W (R k) Z.length)) + 2).sum + 1

/-- **The count after the visits**: from a flat table at the visit words `ks` (then its end marker), the count grows by
the number of visits whose stage-5 report is `s`, the visit count by `|ks|`. -/
theorem visits_spec {κ : Type} (M J : ℕ) (W : ℕ → ℕ) (L : ℕ) (R : κ → ℕ → List Bool) (Z : List Bool) (s : ℕ)
    (postF : List Bool) (hZ : Z.length = L) (hR : ∀ k j, j ≤ J → (R k j).length = L) (hs : s ≤ M) :
    ∀ (ks : List κ) (rowOld : ℕ → List Bool) (preF : List Bool) (x : MSt),
    (∀ j ≤ J, (rowOld j).length = L) → x.pt = frame Z → x.t5 = levelWord M J W rowOld → x.t5h = 0 →
    (∀ p, readTapeBit x.ss p = readTapeBit (unary s) p) → x.ssh = 0 → x.c = 0 →
    x.ft = preF ++ visitWords J R ks ++ false :: postF → x.fth = preF.length →
    (∀ k ∈ ks, (levelWord M J W (R k)).length < cap) → (preF ++ visitWords J R ks).length < cap →
    (∀ k ∈ ks, capOf M J W (R k) Z.length ≤ cap) → x.a + ks.length ≤ cap → x.v + ks.length < cap →
    ∃ b, WExec cap visitsM x.w
      { x with t5 := levelWord M J W (lastRows R ks rowOld), fth := (preF ++ visitWords J R ks).length,
               a := x.a + hitsOf M J W R Z s ks, v := x.v + ks.length, cell := b }.w
      (visitsCost M J W L R Z ks)
  | [], rowOld, preF, x, _, _, ht, _, _, _, _, hf, hfh, _, _, _, _, _ => by
    refine ⟨x.cell, ?_⟩
    have hb : wbit x.w sFT = false := by
      rw [wbit_ft, hf, hfh]; simpa [visitWords] using readTapeBit_mid preF postF false
    refine WExec.cast cap (WExec.whsF hb) ?_ (by simp [visitsCost])
    cases x
    simp only at ht hfh ⊢
    subst ht hfh
    simp [lastRows, visitWords, hitsOf]
  | k :: ks, rowOld, preF, x, hO, hpt, ht, hth, hss, hssh, hc, hf, hfh, hcT, hcF, hc5, hA, hV => by
    have hwk : visitWords J R (k :: ks) = (true :: (levels J).flatMap (fun j => frame (R k j))) ++
        visitWords J R ks := by simp [visitWords]
    have hb : wbit x.w sFT = true := by
      rw [wbit_ft, hf, hfh, hwk]; simpa using readTapeBit_mid preF _ true
    have s1 := visit_spec cap M J W L rowOld (R k) Z s preF (visitWords J R ks ++ false :: postF) x hZ hO
      (fun j hj => hR k j hj) hpt ht hth hss hssh hc (by rw [hf, hwk]; simp) hfh hs (hcT k List.mem_cons_self)
      (by rw [hwk, ← List.append_assoc, List.length_append] at hcF; omega) (hc5 k List.mem_cons_self)
      (by simp only [List.length_cons] at hA; omega) (by simp only [List.length_cons] at hV; omega)
    obtain ⟨b, ih⟩ := visits_spec M J W L R Z s postF hZ hR hs ks (R k)
      (preF ++ (true :: (levels J).flatMap (fun j => frame (R k j))))
      { x with t5 := levelWord M J W (R k),
               fth := (preF ++ (true :: (levels J).flatMap (fun j => frame (R k j)))).length,
               a := x.a + (if reportRef M J W (R k) Z = s then 1 else 0), v := x.v + 1, cell := false }
      (fun j hj => hR k j hj) hpt rfl hth hss hssh hc (by show x.ft = _; rw [hf, hwk]; simp) rfl
      (fun k' hk' => hcT k' (List.mem_cons_of_mem _ hk')) (by rw [hwk, ← List.append_assoc] at hcF; exact hcF)
      (fun k' hk' => hc5 k' (List.mem_cons_of_mem _ hk'))
      (by show x.a + (if reportRef M J W (R k) Z = s then 1 else 0) + ks.length ≤ cap
          simp only [List.length_cons] at hA; split <;> omega)
      (by show x.v + 1 + ks.length < cap; simp only [List.length_cons] at hV; omega)
    refine ⟨b, WExec.cast cap (WExec.whsT hb s1 ih) ?_ (by simp [visitsCost]; omega)⟩
    cases x
    simp only
    congr 1
    simp [lastRows, hwk, hitsOf, frame_eq_frameP, frameP]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.Maj
