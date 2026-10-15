import Proof.Gates.Codec.FieldGate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Table bits -/

/-- Append `marks (bitWord b)` for the scanned bit `b`, then step. -/
def bitW (W o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.ifs W (emitMarks o OP (natWord 1)) (emitMarks o OP (natWord 0))) (.fwd W)

theorem bitW_spec (W o : Fin (ns + 1)) (OP : Fin nr) (hWo : W ≠ o) (σ : WState ns nr)
    (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 6 ≤ cap) :
    WExec cap (bitW W o OP) σ
      (appendO (σ.seth W (σ.sh W + 1)) o OP (marks (Interfaces.bitWord ((σ.st W).getD (σ.sh W) false)))) 51 := by
  have hb : wbit σ W = (σ.st W).getD (σ.sh W) false := rfl
  rcases hc' : (σ.st W).getD (σ.sh W) false with _ | _
  · have e := emitMarks_spec cap o OP (natWord 0) σ ho (by simp [natWord_zero]; omega)
    have e1 := WExec.ifsF (P := emitMarks o OP (natWord 1)) (by rw [hb, hc']) e
    refine WExec.cast cap (WExec.seq e1 (WExec.fwd W _)) ?_ (by simp [natWord_zero])
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [appendO, hWo]
      · by_cases hjo : j = o
        · subst hjo; simp [appendO, hj, Interfaces.bitWord, natWord_zero, natWord_one]
        · simp [appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · simp [appendO, Interfaces.bitWord]
    · simp [appendO, Interfaces.bitWord]
    · simp
  · have e := emitMarks_spec cap o OP (natWord 1) σ ho (by simp [natWord_one]; omega)
    have e1 := WExec.ifsT (Q := emitMarks o OP (natWord 0)) (by rw [hb, hc']) e
    refine WExec.cast cap (WExec.seq e1 (WExec.fwd W _)) ?_ (by simp [natWord_one])
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [appendO, hWo]
      · by_cases hjo : j = o
        · subst hjo; simp [appendO, hj, Interfaces.bitWord, natWord_zero, natWord_one]
        · simp [appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · simp [appendO, Interfaces.bitWord]
    · simp [appendO, Interfaces.bitWord]
    · simp

/-! ## A counted emitting loop -/

/-- The output after `i` elements. -/
def emitted {α : Type} (val : ℕ → α) (enc : α → List Bool) (nxt : ℕ → ℕ) (p i : ℕ) : List Bool :=
  ((List.range i).map fun j => val (iter nxt p j)).flatMap enc

theorem emitted_succ {α : Type} (val : ℕ → α) (enc : α → List Bool) (nxt : ℕ → ℕ) (p i : ℕ) :
    emitted val enc nxt p (i + 1) = emitted val enc nxt p i ++ enc (val (iter nxt p i)) := by
  simp [emitted, List.range_succ, List.flatMap_append]

theorem emitted_mono {α : Type} (val : ℕ → α) (enc : α → List Bool) (nxt : ℕ → ℕ) (p i m : ℕ) (h : i ≤ m) :
    (emitted val enc nxt p i).length ≤ (emitted val enc nxt p m).length := by
  induction m with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hi | hi
    · rw [emitted_succ, List.length_append]; have := ih (by omega); omega
    · have : i = m + 1 := by omega
      subst this; exact le_rfl

/-- **The counted emitting loop.** `C` starts at `m`; each pass appends `marks (enc (val pos))` and moves the head
of `W` from `pos` to `nxt pos`, leaving every other register as it was. -/
theorem repEmit_spec {α : Type} (W o : Fin (ns + 1)) (OP C : Fin nr) (body : WM ns nr) (val : ℕ → α)
    (enc : α → List Bool) (nxt : ℕ → ℕ) (c m : ℕ) (σ : WState ns nr) (hWo : W ≠ o) (hCO : C ≠ OP)
    (hC0 : σ.val C = m) (hcap : m ≤ cap) (ho : σ.sh o = (σ.st o).length)
    (hbody : ∀ i < m, ∀ τ : WState ns nr, (∀ r, r ≠ OP → r ≠ C → τ.val r = σ.val r) → τ.val C = m - i - 1 →
      τ.st W = σ.st W → τ.sh W = iter nxt (σ.sh W) i → τ.sh o = (τ.st o).length →
      τ.val OP = σ.val OP + 2 * (emitted val enc nxt (σ.sh W) i).length →
      WExec cap body τ (appendO (τ.seth W (nxt (τ.sh W))) o OP (marks (enc (val (τ.sh W))))) c) :
    WExec cap (repLoop C body) σ
      ((appendO (σ.seth W (iter nxt (σ.sh W) m)) o OP (marks (emitted val enc nxt (σ.sh W) m))).setv C 0)
      (m * (c + 4) + 1) := by
  set p := σ.sh W with hp
  set g : ℕ → WState ns nr := fun i =>
    (appendO (σ.seth W (iter nxt p i)) o OP (marks (emitted val enc nxt p i))).setv C (m - i) with hg
  have hg0 : g 0 = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hg, iter, emitted, appendO, hWo, hp]
      · simp [hg, iter, emitted, appendO, Function.update_of_ne hj]
    · funext j; by_cases hj : j = o
      · subst hj; simp [hg, emitted, appendO, marks]
      · simp [hg, emitted, appendO, Function.update_of_ne hj]
    · funext r; by_cases hr : r = C
      · subst hr; simp [hg, hC0]
      · by_cases hr' : r = OP
        · subst hr'; simp [hg, emitted, appendO, hr]
        · simp [hg, emitted, appendO, hr, hr']
    · simp [hg]
  have hgm : g m = (appendO (σ.seth W (iter nxt p m)) o OP (marks (emitted val enc nxt p m))).setv C 0 := by
    simp [hg]
  have hgC : ∀ i ≤ m, (g i).val C = m - i := fun i _ => by simp [hg]
  have hstep : ∀ i < m, WExec cap body ((g i).setv C (m - i - 1)) (g (i + 1)) c := by
    intro i hi
    set τ := (g i).setv C (m - i - 1) with hτ
    have hτsh : τ.sh W = iter nxt p i := by simp [hτ, hg, appendO, Function.update_of_ne hWo]
    have e := hbody i hi τ
      (fun r hr hrC => by simp [hτ, hg, appendO, Function.update_of_ne hr, Function.update_of_ne hrC])
      (by simp [hτ, hg])
      (by simp [hτ, hg, appendO, Function.update_of_ne hWo])
      hτsh
      (by simp [hτ, hg, appendO, Function.update_apply, Ne.symm hWo, ho])
      (by simp [hτ, hg, appendO, Function.update_of_ne (Ne.symm hCO), marks_length])
    rw [hτsh] at e
    refine WExec.cast cap e ?_ le_rfl
    apply WState.eq
    · funext j; by_cases hj : j = W
      · subst hj; simp [hτ, hg, appendO, hWo, iter_succ']
      · by_cases hjo : j = o
        · subst hjo; simp [hτ, hg, appendO, hj, Ne.symm hWo, emitted_succ, marksApp, marks_length]; omega
        · simp [hτ, hg, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [hτ, hg, appendO, emitted_succ, marksApp]
      · simp [hτ, hg, appendO, Function.update_of_ne hjo]
    · funext r
      simp only [hτ, hg, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases hr : r = OP
      · subst hr; simp [hCO, Ne.symm hCO, emitted_succ, marksApp, marks_length]; omega
      by_cases hrC : r = C
      · subst hrC; simp [hr]; omega
      · simp [hr, hrC]
    · simp [hτ, hg]
  have e := repLoop_spec cap C body m c g hgC hcap hstep
  rw [hg0, hgm] at e
  exact e

/-! ## The circuit field, read at a position -/

theorem readField_drop (w : List Bool) (p : ℕ) :
    readField (w.drop p) = (fieldBits w (p + fieldLen w p + 1) (fieldLen w p),
      w.drop (p + fieldLen w p + 1 + fieldLen w p)) := by
  unfold readField readBits fieldLen
  rw [readCount_drop]
  simp only [List.drop_drop, getD_drop, fieldBits]

theorem iter_succ_eq (p j : ℕ) : iter (· + 1) p j = p + j := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih => show iter (· + 1) (p + 1) j = p + (j + 1); rw [ih]; omega

theorem readGate_pair (w : List Bool) (q p : ℕ) :
    readGate q (w.drop p) = ((readGate q (w.drop p)).1, w.drop (gateEnd w p q)) :=
  Prod.ext rfl (readGate_drop w p q).1

/-- Positions inside a circuit field at `p` on native width `q`. -/
def cK (w : List Bool) (p : ℕ) : ℕ := fieldLen w p
def cP1 (w : List Bool) (p : ℕ) : ℕ := p + cK w p + 1
def cPg (w : List Bool) (p q : ℕ) : ℕ := iter (fun r => gateEnd w r q) (cP1 w p) (cK w p)
def cPc (w : List Bool) (p q : ℕ) : ℕ := iter (intEnd w) (cPg w p q) (cK w p)
def cL (w : List Bool) (p q : ℕ) : ℕ := fieldLen w (cPc w p q)
def cP2 (w : List Bool) (p q : ℕ) : ℕ := cPc w p q + cL w p q + 1
def circuitEnd (w : List Bool) (p q : ℕ) : ℕ := cP2 w p q + cL w p q

theorem readCircuit_drop (w : List Bool) (p q : ℕ) :
    (readCircuit q (w.drop p)).2 = w.drop (circuitEnd w p q) ∧
      Interfaces.circuitWord (readCircuit q (w.drop p)).1 =
        natWord (cK w p) ++ emitted (fun r => (readGate q (w.drop r)).1) Interfaces.gateWord (fun r => gateEnd w r q)
          (cP1 w p) (cK w p) ++
        (natWord (cK w p) ++ emitted (ival w) Interfaces.intWord (intEnd w) (cPg w p q) (cK w p)) ++
        (natWord (cL w p q) ++ emitted (fun r => w.getD r false) Interfaces.bitWord (· + 1) (cP2 w p q) (cL w p q)) := by
  have hc := readCount_drop w p
  have hg := readMany_iter (readGate q) w (fun r => (readGate q (w.drop r)).1) (fun r => gateEnd w r q)
    (readGate_pair w q) (cK w p) (cP1 w p)
  have hi := readMany_iter readInt w (ival w) (intEnd w) (readInt_pos w) (cK w p) (cPg w p q)
  have hf := readField_drop w (cPc w p q)
  unfold readCircuit
  simp only
  rw [hc]
  simp only [show (readCount (w.drop p)).1 = cK w p from rfl, show p + cK w p + 1 = cP1 w p from rfl]
  rw [hg]
  simp only [show iter (fun r => gateEnd w r q) (cP1 w p) (cK w p) = cPg w p q from rfl]
  rw [hi]
  simp only [show iter (intEnd w) (cPg w p q) (cK w p) = cPc w p q from rfl]
  rw [hf]
  refine ⟨rfl, ?_⟩
  unfold Interfaces.circuitWord Interfaces.listWord emitted
  have hbits : fieldBits w (cPc w p q + fieldLen w (cPc w p q) + 1) (fieldLen w (cPc w p q)) =
      (List.range (cL w p q)).map fun j => w.getD (iter (· + 1) (cP2 w p q) j) false := by
    apply List.ext_getElem (by simp [fieldBits_length, cL])
    intro i h1 h2
    simp [fieldBits, iter_succ_eq, cP2, cL]
  simp only [List.length_map, List.length_range, hbits]

def AX (A : Fin 18 ↪ Fin nr) : Fin 5 ↪ Fin nr :=
  ⟨fun i => A ⟨i.val, by omega⟩, fun i j h => by
    have := A.injective h; ext; simpa using congrArg Fin.val this⟩

def qIdx (z : Fin 18) (i : Fin 8) : Fin 18 := if i.val = 0 then z else if i.val = 7 then 13 else ⟨6 + i.val, by omega⟩

/-- `writeNatM` registers printing register `A z` (`z ∈ {6, 14}`). -/
def AR (A : Fin 18 ↪ Fin nr) (z : Fin 18) (hz : z = 6 ∨ z = 14) : Fin 8 ↪ Fin nr :=
  ⟨fun i => A (qIdx z i), fun i j h => by
    have h' := A.injective h
    unfold qIdx at h'
    rcases hz with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all⟩

theorem AR_val (A : Fin 18 ↪ Fin nr) (z : Fin 18) (hz : z = 6 ∨ z = 14) (i : Fin 8) :
    AR A z hz i = A (qIdx z i) := rfl

theorem Ane (A : Fin 18 ↪ Fin nr) {i j : Fin 18} (h : i ≠ j) : A i ≠ A j := A.injective.ne h

/-- The circuit transcoder. -/
def circuitW (W o : Fin (ns + 1)) (A : Fin 18 ↪ Fin nr) : WM ns nr :=
  let RK := AR A 14 (Or.inr rfl)
  .seq (countW W (A 14)) (.seq (writeNatM o RK) (.seq (dupR (A 14) (A 17) (A 16))
  (.seq (repLoop (A 17) (gateW W o (AX A) (A 5) (AR A 6 (Or.inl rfl)) (A 15) (A 16)))
  (.seq (writeNatM o RK) (.seq (dupR (A 14) (A 17) (A 16)) (.seq (repLoop (A 17) (intW W o (AX A) (A 5) (A 13)))
  (.seq (WM.clear (A 14)) (.seq (countW W (A 14)) (.seq (writeNatM o RK) (.seq (dupR (A 14) (A 17) (A 16))
  (.seq (repLoop (A 17) (bitW W o (A 13))) (WM.clear (A 14)))))))))))))

theorem natBitLength_le_succ (v : ℕ) : natBitLength v ≤ v + 1 := by
  have h1 := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
  have h2 := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
  unfold natBitLength; omega

/-! ## States of the circuit transcoder -/

section Shape
variable (W o : Fin (ns + 1)) (A : Fin 18 ↪ Fin nr) (σ : WState ns nr)

def shp (pos : ℕ) (out : List Bool) (kv c2 : ℕ) : WState ns nr :=
  ((appendO (σ.seth W pos) o (A 13) (marks out)).setv (A 14) kv).setv (A 17) c2

variable {W o A σ}

theorem shp_stW (hWo : W ≠ o) (pos : ℕ) (out : List Bool) (kv c2 : ℕ) : (shp W o A σ pos out kv c2).st W = σ.st W := by
  simp [shp, appendO, Function.update_of_ne hWo]
theorem shp_shW (hWo : W ≠ o) (pos : ℕ) (out : List Bool) (kv c2 : ℕ) : (shp W o A σ pos out kv c2).sh W = pos := by
  simp [shp, appendO, Function.update_of_ne hWo]
theorem shp_ho (hWo : W ≠ o) (ho : σ.sh o = (σ.st o).length) (pos : ℕ) (out : List Bool) (kv c2 : ℕ) :
    (shp W o A σ pos out kv c2).sh o = ((shp W o A σ pos out kv c2).st o).length := by
  simp [shp, appendO, Function.update_apply, Ne.symm hWo, ho]
theorem shp_K (pos : ℕ) (out : List Bool) (kv c2 : ℕ) : (shp W o A σ pos out kv c2).val (A 14) = kv := by
  simp [shp, Function.update_of_ne (Ane A (show (14 : Fin 18) ≠ 17 by decide))]
theorem shp_C (pos : ℕ) (out : List Bool) (kv c2 : ℕ) : (shp W o A σ pos out kv c2).val (A 17) = c2 := by simp [shp]
theorem shp_OP (pos : ℕ) (out : List Bool) (kv c2 : ℕ) :
    (shp W o A σ pos out kv c2).val (A 13) = σ.val (A 13) + 2 * out.length := by
  simp [shp, appendO, Function.update_of_ne (Ane A (show (13 : Fin 18) ≠ 17 by decide)),
    Function.update_of_ne (Ane A (show (13 : Fin 18) ≠ 14 by decide)), marks_length]
theorem shp_other (pos : ℕ) (out : List Bool) (kv c2 : ℕ) (r : Fin nr) (h13 : r ≠ A 13) (h14 : r ≠ A 14)
    (h17 : r ≠ A 17) : (shp W o A σ pos out kv c2).val r = σ.val r := by
  simp [shp, appendO, Function.update_of_ne h13, Function.update_of_ne h14, Function.update_of_ne h17]

theorem shp_app (hWo : W ≠ o) (pos pos' : ℕ) (out u : List Bool) (kv c2 : ℕ) :
    appendO ((shp W o A σ pos out kv c2).seth W pos') o (A 13) (marks u) = shp W o A σ pos' (out ++ u) kv c2 := by
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp [shp, appendO, hWo]
    · by_cases hjo : j = o
      · subst hjo; simp [shp, appendO, hj, marksApp, marks_length]; omega
      · simp [shp, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [shp, appendO, marksApp]
    · simp [shp, appendO, Function.update_of_ne hjo]
  · funext r
    simp only [shp, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
    have h1 := Ane A (show (13 : Fin 18) ≠ 14 by decide); have h2 := Ane A (show (13 : Fin 18) ≠ 17 by decide)
    by_cases hr : r = A 13
    · subst hr; simp [h1, h2, Ne.symm h1, Ne.symm h2, marksApp, marks_length]; omega
    · simp [hr]
  · simp [shp]

theorem shp_app0 (hWo : W ≠ o) (pos : ℕ) (out u : List Bool) (kv c2 : ℕ) :
    appendO (shp W o A σ pos out kv c2) o (A 13) (marks u) = shp W o A σ pos (out ++ u) kv c2 := by
  rw [← shp_app hWo pos pos out u kv c2]
  congr 1
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp [shp_shW hWo]
    · simp [Function.update_of_ne hj]
  · rfl
  · rfl
  · rfl

theorem shp_setK (pos : ℕ) (out : List Bool) (kv c2 kv' : ℕ) :
    (shp W o A σ pos out kv c2).setv (A 14) kv' = shp W o A σ pos out kv' c2 := by
  apply WState.eq <;> try rfl
  funext r; simp only [shp, WState.setv_val, Function.update_apply]
  have h := Ane A (show (14 : Fin 18) ≠ 17 by decide)
  by_cases hr : r = A 14
  · subst hr; simp [h]
  · simp [hr]

theorem shp_setC (pos : ℕ) (out : List Bool) (kv c2 c' : ℕ) :
    (shp W o A σ pos out kv c2).setv (A 17) c' = shp W o A σ pos out kv c' := by
  apply WState.eq <;> try rfl
  funext r; simp only [shp, WState.setv_val, Function.update_apply]
  by_cases hr : r = A 17
  · subst hr; simp
  · simp [hr]

theorem shp_count (hWo : W ≠ o) (pos pos' : ℕ) (out : List Bool) (kv c2 kv' : ℕ) :
    ((shp W o A σ pos out kv c2).seth W pos').setv (A 14) kv' = shp W o A σ pos' out kv' c2 := by
  rw [← shp_setK pos' out kv c2 kv']
  congr 1
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp [shp, appendO, hWo]
    · simp [shp, appendO, Function.update_apply, hj, Ne.symm hWo]
  · simp [shp, appendO, Function.update_of_ne hWo]
  · rfl
  · rfl

theorem shp_final (_hWo : W ≠ o) (pos : ℕ) (out : List Bool) (hK : σ.val (A 14) = 0) (hC : σ.val (A 17) = 0) :
    shp W o A σ pos out 0 0 = appendO (σ.seth W pos) o (A 13) (marks out) := by
  apply WState.eq <;> try rfl
  funext r; simp only [shp, WState.setv_val, appendO_val, WState.seth_val, Function.update_apply]
  have h1 := Ane A (show (13 : Fin 18) ≠ 14 by decide); have h2 := Ane A (show (13 : Fin 18) ≠ 17 by decide)
  by_cases hr : r = A 17
  · subst hr; simp [Ne.symm h2, hC]
  by_cases hr' : r = A 14
  · subst hr'; simp [Ane A (show (14 : Fin 18) ≠ 17 by decide), Ne.symm h1, hK]
  · simp [hr, hr']

theorem shp_init (hWo : W ≠ o) (hK : σ.val (A 14) = 0) (hC : σ.val (A 17) = 0) :
    shp W o A σ (σ.sh W) [] 0 0 = σ := by
  rw [shp_final hWo _ _ hK hC]
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp [appendO, hWo]
    · by_cases hjo : j = o
      · subst hjo; simp [appendO, hj, marks]
      · simp [appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [appendO, marks]
    · simp [appendO, Function.update_of_ne hjo]
  · funext r; by_cases hr : r = A 13
    · subst hr; simp [appendO, marks]
    · simp [appendO, Function.update_of_ne hr]
  · simp

end Shape

end NearCubicGates.Close.Codec
