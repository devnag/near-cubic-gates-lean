import Proof.Gates.Succinct.EvalW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- **The evaluator** (paper lem:succinct-verifier, stage (3)): skip the arity, read the gate count, the gates, the
output; fetch the output gate's value into `rv`; clear the value tape; return the description head. -/
def evalW (D P V : Fin (ns + 1)) (E : EReg → Fin nr) : WM ns nr :=
  .seq (fieldTo D (fE E) (E .lb) (E .a))
  (.seq (WM.clear (E .a))
  (.seq (fieldTo D (fE E) (E .lb) (E .s))
  (.seq (.whr (E .s) (.seq (.dec (E .s)) (nodeW D P V E)))
  (.seq (fieldTo D (fE E) (E .lb) (E .a))
  (.seq (seekRead V (E .a) (E .y) (E .rv))
  (.seq (clearV V (E .j) (E .y))
  (WM.rewind D (E (.f .cd)))))))))

/-- The cost class of one evaluation (paper lem:succinct-verifier, stage (3)). -/
def evalCost (dl lb lp : ℕ) : ℕ :=
  (2 ^ lb + 4) * (nodeCost dl lb lp (2 ^ lb) + 100) + 3 * fieldCost dl lb + 20 * dl + 100 * 2 ^ lb + 100

/-! ## The model's positions and values -/

theorem evFinal_iter_length (d : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) :
    ∀ k, ((nodeStep d lb lp pt)^[k] (evStart d)).vals.length = k := by
  intro k
  induction k with
  | zero => simp [evStart]
  | succ k ih => rw [Function.iterate_succ_apply']; simp [nodeStep, ih]

theorem fieldEnd_le_of (d : List Bool) (p c : ℕ) (h : p ≤ 2 * d.length + c) :
    fieldEnd d p ≤ 2 * d.length + c + 1 := by
  have := fieldEnd_le d p; omega

theorem evStart_pos_le (d : List Bool) : (evStart d).pos ≤ 2 * d.length + 2 := by
  unfold evStart
  have h1 := fieldEnd_le_of d 0 0 (by omega)
  have h2 := fieldEnd_le_of d (fieldEnd d 0) 1 (by omega)
  simpa using h2

theorem iter_pos_le (d : List Bool) (lb lp : ℕ) (pt : ℕ → Bool) :
    ∀ k, ((nodeStep d lb lp pt)^[k] (evStart d)).pos ≤ 2 * d.length + 2 + 3 * k := by
  intro k
  induction k with
  | zero => simpa using evStart_pos_le d
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [nodeStep]
    generalize ((nodeStep d lb lp pt)^[k] (evStart d)).pos = q at ih ⊢
    have h1 := fieldEnd_le_of d q (2 + 3 * k) (by omega)
    have h2 := fieldEnd_le_of d (fieldEnd d q) (2 + 3 * k + 1) (by omega)
    have h3 := fieldEnd_le_of d (fieldEnd d (fieldEnd d q)) (2 + 3 * k + 2) (by omega)
    omega

theorem nodeCost_mono (dl lb lp : ℕ) {J J' : ℕ} (h : J ≤ J') : nodeCost dl lb lp J ≤ nodeCost dl lb lp J' := by
  unfold nodeCost; omega

/-- **The evaluator** (paper lem:succinct-verifier, stage (3) and item (ii)), on every description stream. -/
theorem evalW_spec (cap : ℕ) (D P V : Fin (ns + 1)) (hDP : D ≠ P) (hDV : D ≠ V) (hPV : P ≠ V)
    (E : EReg → Fin nr) (hE : Function.Injective E) (σ : WState ns nr) (m : ℕ) (d : List Bool) (lb lp : ℕ)
    (hd : σ.st D = d) (hDh : σ.sh D = 0) (hV : σ.st V = List.replicate m false) (hVh : σ.sh V = 0)
    (hPh : σ.sh P = 0) (hlb : σ.val (E .lb) = lb) (hlp : σ.val (E .lp) = lp)
    (hz : ∀ r ∈ scratchE, σ.val (E r) = 0) (hs : σ.val (E .s) = 0) (hj : σ.val (E .j) = 0)
    (hcd : σ.val (E (.f .cd)) = 0)
    (hcap : 10 * d.length + 8 * (lb + lp) + 16 * 2 ^ (lb + lp + 1) + 200 ≤ cap) :
    ∃ τ, WExec cap (evalW D P V E) σ τ (evalCost d.length lb lp) ∧
      τ.val (E .rv) = (evalModel d lb lp (readTapeBit (σ.st P))).toNat ∧
      (∃ m', τ.st V = List.replicate m' false) ∧ τ.sh V = 0 ∧ SameExcept σ τ [V] [E .rv] := by
  have hR := fE_inj E hE
  have fne : ∀ (k : FReg) (r : EReg), (∀ k', r ≠ .f k') → fE E k ≠ E r := fun k r h => fE_ne E hE k r h
  have z : ∀ k : FReg, k ≠ .cd → σ.val (fE E k) = 0 := by
    intro k hk; cases k <;> first | exact absurd rfl hk | exact hz _ (by simp [scratchE])
  have hpowlb : 2 ^ lb ≤ 2 ^ (lb + lp) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpowS : 2 ^ (lb + lp + 1) = 2 * 2 ^ (lb + lp) := by rw [pow_succ]; ring
  have hpowS' : 2 ^ (lb + 1) = 2 * 2 ^ lb := by rw [pow_succ]; ring
  set pt := readTapeBit (σ.st P) with hpt
  -- 1. the arity field (discarded)
  have hd0 := ones_le d 0
  have e1 := fieldTo_spec cap D (fE E) hR (E .lb) (E .a) (fun k => fne k _ (by intro k'; simp))
    (fun k => fne k _ (by intro k'; simp)) σ z (hz .a (by simp [scratchE]))
    (by rw [show σ.val (fE E .cd) = 0 from hcd, hd, hDh, hlb]; omega)
  rw [show σ.val (fE E .cd) = 0 from hcd, hd, hDh, hlb] at e1
  generalize hσ1 : ((σ.seth D (fieldEnd d 0)).setv (fE E .cd) (0 + 2 * ones d 0 + 1)).setv (E .a)
    (fieldVal d 0 lb) = σ1 at e1
  have ha1 : σ1.val (E .a) = fieldVal d 0 lb := by rw [← hσ1]; simp
  have hal : fieldVal d 0 lb < 2 ^ lb := fieldVal_lt _ _ _
  have e2 := wclear_spec cap (E .a) _ σ1 ha1 (by omega)
  generalize hσ2 : σ1.setv (E .a) 0 = σ2 at e2
  have s2 : ∀ r, r ≠ E (.f .cd) → σ2.val r = σ.val r := by
    intro r h1; rw [← hσ2, ← hσ1]
    by_cases ha : r = E .a
    · subst ha; simp; exact (hz .a (by simp [scratchE])).symm
    · simp only [WState.setv_val, WState.seth_val, Function.update_apply, fE, if_neg h1, if_neg ha]
  have h2st : ∀ x, σ2.st x = σ.st x := by intro x; rw [← hσ2, ← hσ1]; simp
  have h2sh : ∀ x, x ≠ D → σ2.sh x = σ.sh x := by
    intro x hx; rw [← hσ2, ← hσ1]; simp [Function.update_apply, hx]
  have h2D : σ2.sh D = fieldEnd d 0 := by rw [← hσ2, ← hσ1]; simp
  have h2cd : σ2.val (fE E .cd) = fieldEnd d 0 := by
    rw [← hσ2, ← hσ1]; simp [fE, Function.update_apply, hE.eq_iff, fieldEnd]
  -- 2. the gate count
  have z2 : ∀ k : FReg, k ≠ .cd → σ2.val (fE E k) = 0 := by
    intro k hk; rw [s2 _ (fun h => hk (by have := hE h; injection this))]; exact z k hk
  have hd1 := ones_le d (fieldEnd d 0)
  have hp1 := fieldEnd_le_of d 0 0 (by omega)
  have e3 := fieldTo_spec cap D (fE E) hR (E .lb) (E .s) (fun k => fne k _ (by intro k'; simp))
    (fun k => fne k _ (by intro k'; simp)) σ2 z2 (by rw [s2 _ (hE.ne (by simp)), hs])
    (by rw [h2cd, h2st, hd, h2D, s2 _ (hE.ne (by simp)), hlb]; omega)
  rw [h2cd, h2st, hd, h2D, s2 (E .lb) (hE.ne (by simp)), hlb] at e3
  generalize hσ3 : ((σ2.seth D (fieldEnd d (fieldEnd d 0))).setv (fE E .cd)
    (fieldEnd d 0 + 2 * ones d (fieldEnd d 0) + 1)).setv (E .s) (fieldVal d (fieldEnd d 0) lb) = σ3 at e3
  set n := evCount d lb with hn
  have hnl : n < 2 ^ lb := fieldVal_lt _ _ _
  set it : ℕ → EvSt := fun k => (nodeStep d lb lp pt)^[k] (evStart d) with hit
  have hitlen : ∀ k, (it k).vals.length = k := evFinal_iter_length d lb lp pt
  have hitpos : ∀ k, (it k).pos ≤ 2 * d.length + 2 + 3 * k := iter_pos_le d lb lp pt
  -- 3. the gate loop
  let Inv : ℕ → WState ns nr → Prop := fun k τ =>
    τ.st D = d ∧ τ.sh D = (it k).pos ∧ τ.st V = vtape m (it k).vals ∧ τ.sh V = 0 ∧ τ.val (E .j) = k ∧
      τ.val (E (.f .cd)) = τ.sh D ∧ (∀ r ∈ scratchE, τ.val (E r) = 0) ∧ τ.val (E .lb) = lb ∧
      τ.val (E .lp) = lp ∧ τ.sh P = 0 ∧ τ.st P = σ.st P ∧ SameExcept σ3 τ [D, V] [E (.f .cd), E .j, E .s]
  have hInv0 : Inv 0 σ3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, SameExcept.refl _ _ _⟩
    · rw [← hσ3]; simpa [h2st] using hd
    · rw [← hσ3]; simp [it, evStart]
    · rw [← hσ3]; simp [it, evStart, vtape, h2st, hV]
    · rw [← hσ3]; simp [Function.update_of_ne (Ne.symm hDV), h2sh V (Ne.symm hDV), hVh]
    · rw [← hσ3]; simp [Function.update_apply, hE.eq_iff, fE]; rw [s2 _ (hE.ne (by simp)), hj]
    · rw [← hσ3]; simp [fE, Function.update_apply, hE.eq_iff, fieldEnd]
    · intro r hr; rw [← hσ3]
      have : r ≠ .s := by intro h; subst h; simp [scratchE] at hr
      have h2 : r ≠ .f .cd := by intro h; subst h; simp [scratchE] at hr
      simp [Function.update_apply, hE.eq_iff, fE, this, h2]
      rw [s2 _ (fun h => h2 (hE h))]; exact hz r hr
    · rw [← hσ3]; simp [Function.update_apply, hE.eq_iff, fE]; rw [s2 _ (hE.ne (by simp)), hlb]
    · rw [← hσ3]; simp [Function.update_apply, hE.eq_iff, fE]; rw [s2 _ (hE.ne (by simp)), hlp]
    · rw [← hσ3]; simp [Function.update_apply, Ne.symm hDP, h2sh P (Ne.symm hDP), hPh]
    · rw [← hσ3]; simp [h2st]
  have hσ3s : σ3.val (E .s) = n := by rw [← hσ3]; simp; rfl
  have hloop := UnionMachine.Round.wloopE cap (E .s) (nodeW D P V E) (nodeCost d.length lb lp n) n Inv
    (by omega)
    (by
      intro k hk τ hI hsk
      obtain ⟨hId, hIDh, hIV, hIVh, hIj, hIcd, hIz, hIlb, hIlp, hIPh, hIP, hIse⟩ := hI
      have hlenk := hitlen k
      have hposk := hitpos k
      have hcapk : (it k).pos + 4 * d.length + 4 * (lb + lp) + 4 * 2 ^ (lb + lp + 1) + (it k).vals.length + 40 ≤
          cap := by rw [hlenk]; omega
      obtain ⟨τ', e, h1, h2, h3, h4, h5, h6, hse⟩ := nodeW_spec cap D P V hDP hDV E hE (τ.setv (E .s) (n - k - 1))
        m (it k).vals d (it k).pos lb lp (by simpa using hId) (by simpa using hIDh)
        (by simp [Function.update_apply, hE.eq_iff, hIlb]) (by simp [Function.update_apply, hE.eq_iff, hIlp])
        (by intro r hr; have : r ≠ .s := by intro h; subst h; simp [scratchE] at hr
            simp [Function.update_apply, hE.eq_iff, this]; exact hIz r hr)
        (by simp [Function.update_apply, hE.eq_iff]; rw [hIcd, hIDh])
        (by simp [Function.update_apply, hE.eq_iff, hIj, hlenk]) (by simpa using hIV) (by simpa using hIVh)
        (by simpa using hIPh) hcapk
      have hP' : (τ.setv (E .s) (n - k - 1)).st P = σ.st P := by simpa using hIP
      rw [hP'] at h1 h2
      refine ⟨τ', WExec.mono e (nodeCost_mono _ _ _ (by rw [hlenk]; omega)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact h5
      · have hs : it (k + 1) = nodeStep d lb lp pt (it k) := by
          simp only [hit]; exact Function.iterate_succ_apply' _ _ _
        rw [h1, hs]
      · have hs : it (k + 1) = nodeStep d lb lp pt (it k) := by
          simp only [hit]; exact Function.iterate_succ_apply' _ _ _
        rw [h2, hs]
      · exact h6
      · rw [h3, hlenk]
      · exact h4
      · intro r hr
        have h1' : E r ∉ [E (.f .cd), E .j] := by
          have : r ≠ .j := by intro h; subst h; simp [scratchE] at hr
          have h2' : r ≠ .f .cd := by intro h; subst h; simp [scratchE] at hr
          simp [hE.eq_iff, this, h2']
        rw [hse.val h1']
        have : r ≠ .s := by intro h; subst h; simp [scratchE] at hr
        simp [Function.update_apply, hE.eq_iff, this]; exact hIz r hr
      · rw [hse.val (by simp [hE.eq_iff])]; simp [Function.update_apply, hE.eq_iff, hIlb]
      · rw [hse.val (by simp [hE.eq_iff])]; simp [Function.update_apply, hE.eq_iff, hIlp]
      · rw [hse.sh (by simp [Ne.symm hDP, hPV])]; simpa using hIPh
      · rw [hse.st (by simp [Ne.symm hDP, hPV])]; simpa using hIP
      · exact hIse.trans ((sameExcept_setv τ (by simp) _).trans
          (hse.weaken (fun _ h => h) (fun r hr => by simp at hr ⊢; tauto)))
      · rw [hse.val (by simp [hE.eq_iff])]; simp)
    σ3 hInv0 hσ3s
  obtain ⟨τ4, e4, hI4, h4s⟩ := hloop
  obtain ⟨h4d, h4D, h4V, h4Vh, h4j, h4cd, h4z, h4lb, h4lp, h4Ph, h4P, h4se⟩ := hI4
  -- 4. the output field
  have hposn := hitpos n
  have hdn := ones_le d (it n).pos
  have z4 : ∀ k : FReg, k ≠ .cd → τ4.val (fE E k) = 0 := by
    intro k hk; cases k <;> first | exact absurd rfl hk | exact h4z _ (by simp [scratchE])
  have e5 := fieldTo_spec cap D (fE E) hR (E .lb) (E .a) (fun k => fne k _ (by intro k'; simp))
    (fun k => fne k _ (by intro k'; simp)) τ4 z4 (h4z .a (by simp [scratchE]))
    (by rw [show τ4.val (fE E .cd) = τ4.sh D from h4cd, h4D, h4d, h4lb]; omega)
  rw [show τ4.val (fE E .cd) = τ4.sh D from h4cd, h4D, h4d, h4lb] at e5
  generalize hσ5 : ((τ4.seth D (fieldEnd d (it n).pos)).setv (fE E .cd)
    ((it n).pos + 2 * ones d (it n).pos + 1)).setv (E .a) (fieldVal d (it n).pos lb) = σ5 at e5
  have houtl : fieldVal d (it n).pos lb < 2 ^ lb := fieldVal_lt _ _ _
  -- 5. the output gate's value
  have e6 := seekRead_spec cap V (E .a) (E .y) (E .rv) (hE.ne (by simp)) (hE.ne (by simp)) (hE.ne (by simp)) σ5
    (by rw [← hσ5]; simp [Function.update_apply, hE.eq_iff, fE]; exact h4z .y (by simp [scratchE]))
    (by rw [← hσ5]; simp [Function.update_apply, hE.eq_iff, fE, h4z .rv (by simp [scratchE])]; omega)
  have h5V : σ5.st V = vtape m (it n).vals := by rw [← hσ5]; simpa using h4V
  have h5Vh : σ5.sh V = 0 := by rw [← hσ5]; simp [Function.update_apply, Ne.symm hDV, h4Vh]
  have h5a : σ5.val (E .a) = fieldVal d (it n).pos lb := by rw [← hσ5]; simp
  have h5rv : σ5.val (E .rv) = 0 := by
    rw [← hσ5]; simp [Function.update_apply, hE.eq_iff, fE]; exact h4z .rv (by simp [scratchE])
  replace e6 : WExec cap (seekRead V (E .a) (E .y) (E .rv)) σ5
      ((σ5.setv (E .a) 0).setv (E .rv) (evalModel d lb lp pt).toNat) (σ5.val (E .a) * 14 + 10) :=
    WExec.cast cap e6 (by rw [h5V, h5Vh, h5a, h5rv]; simp only [Nat.zero_add, read_vtape]; rfl) le_rfl
  rw [h5a] at e6
  generalize hσ6 : (σ5.setv (E .a) 0).setv (E .rv) (evalModel d lb lp pt).toNat = σ6 at e6
  -- 6. clear the value tape
  have e7 := clearV_spec cap V (E .j) (E .y) (hE.ne (by simp)) σ6 m (it n).vals
    (by rw [← hσ6]; simpa using h5V) (by rw [← hσ6]; simpa using h5Vh)
    (by rw [← hσ6, ← hσ5]; simp [Function.update_apply, hE.eq_iff, fE, h4j, hitlen])
    (by rw [← hσ6, ← hσ5]; simp [Function.update_apply, hE.eq_iff, fE]; exact h4z .y (by simp [scratchE]))
    (by rw [hitlen]; omega)
  generalize hσ7 : (σ6.setv (E .j) 0).sets V (List.replicate (max m (it n).vals.length) false) = σ7 at e7
  -- 7. return the description head
  have h7cd : σ7.val (E (.f .cd)) = fieldEnd d (it n).pos := by
    rw [← hσ7, ← hσ6, ← hσ5]; simp [Function.update_apply, hE.eq_iff, fE, fieldEnd]
  have h7D : σ7.sh D = fieldEnd d (it n).pos := by
    rw [← hσ7, ← hσ6, ← hσ5]; simp [Function.update_apply, hDV]
  have hpe := fieldEnd_le_of d (it n).pos (2 + 3 * n) (by omega)
  have e8 := wrewind_spec cap D (E (.f .cd)) _ σ7 h7cd (by rw [h7cd]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have c0 : fieldCost (ones d 0) lb ≤ fieldCost d.length lb := fieldCost_mono hd0 le_rfl
    have c1 : fieldCost (ones d (fieldEnd d 0)) lb ≤ fieldCost d.length lb := fieldCost_mono hd1 le_rfl
    have c2 : fieldCost (ones d (it n).pos) lb ≤ fieldCost d.length lb := fieldCost_mono hdn le_rfl
    have cn : nodeCost d.length lb lp n ≤ nodeCost d.length lb lp (2 ^ lb) := nodeCost_mono _ _ _ (by omega)
    have cnm : n * (nodeCost d.length lb lp n + 4) ≤ 2 ^ lb * (nodeCost d.length lb lp (2 ^ lb) + 100) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [hitlen]
    unfold evalCost
    have : (2 ^ lb + 4) * (nodeCost d.length lb lp (2 ^ lb) + 100) =
        2 ^ lb * (nodeCost d.length lb lp (2 ^ lb) + 100) + 4 * (nodeCost d.length lb lp (2 ^ lb) + 100) := by ring
    rw [this]
    omega
  · rw [← hσ7, ← hσ6]; simp [Function.update_apply, hE.eq_iff]
  · exact ⟨max m (it n).vals.length, by rw [← hσ7]; simp [Function.update_apply, hDV]⟩
  · rw [← hσ7, ← hσ6]; simp [Function.update_apply, Ne.symm hDV, h5Vh]
  · -- the frame
    refine ⟨fun x hx => ?_, fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      by_cases hxD : x = D
      · subst hxD
        refine ⟨?_, ?_⟩
        · rw [← hσ7, ← hσ6, ← hσ5]; simp [Function.update_apply, hDV, h4d, hd]
        · simp [h7D, hDh]
      · have hx' : x ∉ [D, V] := by simp [hxD, hx]
        refine ⟨?_, ?_⟩
        · rw [← hσ7, ← hσ6, ← hσ5]
          simp [Function.update_apply, hx, hxD, h4se.st hx']
          rw [← hσ3]; simp [h2st]
        · rw [← hσ7, ← hσ6, ← hσ5]
          simp [Function.update_apply, hx, hxD, h4se.sh hx']
          rw [← hσ3]; simp [Function.update_apply, hxD, h2sh x hxD]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      by_cases hcd' : r = E (.f .cd)
      · rw [if_pos hcd', hcd', hcd]
      · rw [if_neg hcd']
        rw [← hσ7, ← hσ6, ← hσ5]
        simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply, fE, if_neg hcd', if_neg hr]
        by_cases hrj : r = E .j
        · rw [if_pos hrj, hrj, hj]
        · rw [if_neg hrj]
          by_cases hra : r = E .a
          · rw [if_pos hra, hra]; exact (hz .a (by simp [scratchE])).symm
          · rw [if_neg hra, if_neg hra]
            by_cases hrs : r = E .s
            · rw [hrs, h4s, hs]
            · rw [h4se.val (by simp [hcd', hrj, hrs])]
              rw [← hσ3]
              simp only [WState.setv_val, WState.seth_val, Function.update_apply, fE, if_neg hcd', if_neg hrs]
              exact s2 r hcd'
    · rw [← hσ7, ← hσ6, ← hσ5]
      simp [h4se.cell]
      rw [← hσ3, ← hσ2, ← hσ1]; simp

end NearCubicGates.Close.Succinct
