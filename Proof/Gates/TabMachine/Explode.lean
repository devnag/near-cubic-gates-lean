import Proof.Gates.TabMachine.CompileM14
import Proof.Gates.WordPrograms.CopyN
import Proof.Gates.WordPrograms.ToReg
import Proof.Gates.WordPrograms.RecLoopJ

/-! # The children's fields as single-number records

The compiler writes one record per child (`recBits W c`, the `s + 1` fields side by side). A child record is the
number `packV W c` (base `2^{W+1}`, `recBits_pack`); **`explode_spec`** splits every child record of a stream into
its fields by `s + 1` divisions by `2^{W+1}` (at the record width `Lc = (s+1)(W+1)`), appending each field
`binary Lc (encS z)` to an output stream, and counts the children. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-! ## Records as numbers -/

/-- A list of signed fields as one number in base `2^{W+1}` (first field lowest). -/
def packV (W : ℕ) : List ℤ → ℕ
  | [] => 0
  | z :: zs => encS z + 2 ^ (W + 1) * packV W zs

theorem binary_split (a b x t : ℕ) (hx : x < 2 ^ a) : binary (a + b) (x + 2 ^ a * t) = binary a x ++ binary b t := by
  induction a generalizing x with
  | zero => simp at hx; subst hx; simp [binary]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [binary, List.cons_append]
    have e : 2 ^ (a + 1) * t = 2 * (2 ^ a * t) := by ring
    have h1 : (x + 2 ^ (a + 1) * t) % 2 = x % 2 := by rw [e, Nat.add_mul_mod_self_left]
    have h2 : (x + 2 ^ (a + 1) * t) / 2 = x / 2 + 2 ^ a * t := by rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
    rw [h1, h2, ih (x / 2) (by rw [pow_succ] at hx; omega)]

theorem packV_lt (W : ℕ) (zs : List ℤ) (h : ∀ z ∈ zs, z.natAbs < 2 ^ W) :
    packV W zs < 2 ^ (zs.length * (W + 1)) := by
  induction zs with
  | nil => simp [packV]
  | cons z zs ih =>
    have hz := SInt.encS_lt (h z (by simp))
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [packV, List.length_cons]
    rw [show (zs.length + 1) * (W + 1) = (W + 1) + zs.length * (W + 1) by ring, pow_add 2 (W + 1)]
    have : 2 ^ (W + 1) * (packV W zs + 1) ≤ 2 ^ (W + 1) * 2 ^ (zs.length * (W + 1)) :=
      Nat.mul_le_mul_left _ ht
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

theorem recBits_pack (W : ℕ) (zs : List ℤ) (h : ∀ z ∈ zs, z.natAbs < 2 ^ W) :
    recBits W zs = binary (zs.length * (W + 1)) (packV W zs) := by
  induction zs with
  | nil => simp [recBits, packV, binary]
  | cons z zs ih =>
    have hz := SInt.encS_lt (h z (by simp))
    simp only [List.length_cons, packV]
    rw [show (zs.length + 1) * (W + 1) = (W + 1) + zs.length * (W + 1) by ring, binary_split _ _ _ _ hz,
      ← ih (fun y hy => h y (by simp [hy]))]
    simp [recBits]

theorem packV_div (W : ℕ) (z : ℤ) (zs : List ℤ) (hz : z.natAbs < 2 ^ W) :
    packV W (z :: zs) / 2 ^ (W + 1) = packV W zs ∧ packV W (z :: zs) % 2 ^ (W + 1) = encS z := by
  have h := SInt.encS_lt hz
  simp only [packV]
  constructor
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem flatMap_take_succ {α β : Type} (l : List α) (f : α → List β) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).flatMap f = (l.take j).flatMap f ++ f l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.flatMap_append]; simp

theorem flatten_take_succ {α : Type} (l : List (List α)) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).flatten = (l.take j).flatten ++ l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.flatten_append]; simp

theorem flatten_take_length {α : Type} (N : ℕ) : ∀ (l : List (List α)) (m : ℕ), (∀ c ∈ l, c.length = N) →
    m ≤ l.length → ((l.take m).flatten).length = m * N
  | [], m, _, hm => by simp at hm; subst hm; simp
  | _ :: _, 0, _, _ => by simp
  | c :: cs, m + 1, h, hm => by
    simp only [List.take_succ_cons, List.flatten_cons, List.length_append]
    rw [h c (by simp), flatten_take_length N cs m (fun d hd => h d (by simp [hd])) (by simp at hm; omega)]; ring

/-- One field as a record of width `L`. -/
def fieldRec (L : ℕ) (z : ℤ) : List Bool := frame (binary L (encS z))

end NearCubicGates.Close.TabMachine

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

section Explode
/- Streams: `0` the child records, `1` the loop's work stream, `2` the value `V`, `3` the radix `2^{W+1}`,
`4` quotient, `5` remainder, `6` scratch, `7` the output. Registers: `0, 1` loop counters, `2, 3, 4, 5` arithmetic
scratch, `6, 7` output counters, `8, 9` the field loop (`8` holds `s + 1`), `10` the child count. -/
variable (E : Fin 8 ↪ Fin (ns + 1)) (G : Fin 11 ↪ Fin nr)

/-- One field: `Q, M := V / 2^{W+1}, V % 2^{W+1}`; append `M`; `V := Q`. -/
def exInner : WMX ns nr :=
  .seq (BinW.divmod (E 2) (E 3) (E 4) (E 5) (E 6) (G 2) (G 3) (G 4) (G 5))
    (.seq (appendRecX (E 5) (E 7) (G 6) (G 7)) (BinW.copy (E 2) (E 4) (G 2) (G 3)))

def exInnerCost (L : ℕ) : ℕ := BinW.divCost L + 1 + (40 * L + 11 + 1 + (41 * L + 3))

/-- The words of the field loop. -/
structure ExWords (L : ℕ) (σ : WState ns nr) : Prop where
  q : ∃ v, NumOn σ (E 4) L v
  m : ∃ v, NumOn σ (E 5) L v
  x : ∃ v, NumOn σ (E 6) L v

theorem exWords_frame {L : ℕ} {σ τ : WState ns nr} {Ls : List (Fin (ns + 1))} {Rs : List (Fin nr)}
    (h : ExWords E L σ) (hfr : SameExcept σ τ Ls Rs) (h4 : E 4 ∉ Ls) (h5 : E 5 ∉ Ls) (h6 : E 6 ∉ Ls) :
    ExWords E L τ :=
  ⟨h.q.elim fun v h => ⟨v, hfr.numOn h4 h⟩, h.m.elim fun v h => ⟨v, hfr.numOn h5 h⟩,
    h.x.elim fun v h => ⟨v, hfr.numOn h6 h⟩⟩

theorem exInner_spec (cap W L : ℕ) (hL : W + 2 ≤ L) (σ : WState ns nr) (z : ℤ) (zs : List ℤ) (out L0 : List Bool)
    (hz : z.natAbs < 2 ^ W) (hzs : (z :: zs).length * (W + 1) ≤ L) (hfit : ∀ y ∈ z :: zs, y.natAbs < 2 ^ W)
    (hV : NumOn σ (E 2) L (packV W (z :: zs))) (hMP : NumOn σ (E 3) L (2 ^ (W + 1))) (hw : ExWords E L σ)
    (h2 : σ.val (G 2) = 0) (h3 : σ.val (G 3) = 0) (h4 : σ.val (G 4) = 0) (h5 : σ.val (G 5) = 0)
    (h6 : σ.val (G 6) = 0) (hO : OutOn σ (E 7) (G 7) out L0) (hcap : 2 * L + 1 ≤ cap)
    (hcapO : out.length + 2 * L + 2 ≤ cap) :
    Runs cap (exInner E G) σ (exInnerCost L) (fun τ =>
      NumOn τ (E 2) L (packV W zs) ∧ OutOn τ (E 7) (G 7) (out ++ fieldRec L z) L0 ∧ ExWords E L τ ∧
        SameExcept σ τ [E 2, E 4, E 5, E 6, E 7] [G 7]) := by
  have hne : ∀ {a b : Fin 8}, a ≠ b → E a ≠ E b := fun h => emb_ne E h
  have hner : ∀ {a b : Fin 11}, a ≠ b → G a ≠ G b := fun h => emb_ne G h
  obtain ⟨⟨q0, hq0⟩, ⟨m0, hm0⟩, ⟨x0, hx0⟩⟩ := hw
  have hpl := packV_lt W (z :: zs) hfit
  have hpL : 2 ^ ((z :: zs).length * (W + 1)) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hzs
  have hbL : 2 * 2 ^ (W + 1) ≤ 2 ^ L := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd := BinW.divmod_spec cap L (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hner (by decide))
    (hner (by decide)) (hner (by decide)) (hner (by decide)) σ _ _ q0 m0 x0 hV hMP hq0 hm0 hx0 h2 h3 h4 h5
    (by omega) (by positivity) hbL hcap
  obtain ⟨hq, hm⟩ := packV_div W z zs hz
  rw [hq, hm] at hd
  set σ1 := ((σ.sets (E 4) (frame (binary L (packV W zs)))).sets (E 5) (frame (binary L (encS z)))).sets (E 6)
    (frame (binary L 0)) with hσ1
  have hO1 : OutOn σ1 (E 7) (G 7) out L0 :=
    ⟨by simp [hσ1, emb_eq_iff, hO.1], by simp [hσ1, emb_eq_iff, hO.2.1], by simp [hσ1, hO.2.2]⟩
  have ha := appendRec_spec cap (Src := E 5) (O := E 7) (CS := G 6) (CO := G 7) (hne (by decide)) (hner (by decide))
    σ1 (binary L (encS z)) [] out L0 (by simp [hσ1, emb_eq_iff, BinW.frame_frameP])
    (by simp [hσ1, emb_eq_iff, hm0.2]) (by simp [hσ1, h6]) hO1 (by rw [binary_length]; omega)
  rw [binary_length] at ha
  set σ2 := ((σ1.sets (E 7) (overlay (out ++ frame (binary L (encS z))) L0)).seth (E 7)
    (out ++ frame (binary L (encS z))).length).setv (G 7) (out ++ frame (binary L (encS z))).length with hσ2
  have hc := BinW.copy_spec (A := E 2) (B := E 4) (F := G 2) (R := G 3) cap L (hne (by decide)) (hner (by decide))
    σ2 (packV W (z :: zs)) (packV W zs) ⟨by simp [hσ2, hσ1, emb_eq_iff, hV.1], by simp [hσ2, hσ1, emb_eq_iff, hV.2]⟩
    ⟨by simp [hσ2, hσ1, emb_eq_iff], by simp [hσ2, hσ1, emb_eq_iff, hq0.2]⟩ (by simp [hσ2, hσ1, emb_eq_iff, h2])
    (by simp [hσ2, hσ1, emb_eq_iff, h3]) hcap
  refine Runs.of (WXExec.seq hd (WXExec.seq (WXExec.wm ha) hc)) ⟨?_, ?_, ?_, ?_⟩
  · exact BinW.numOn_sets_self _ _ _ _ (by simp [hσ2, hσ1, emb_eq_iff, hV.2])
  · exact ⟨by simp [hσ2, emb_eq_iff, fieldRec], by simp [hσ2, emb_eq_iff, fieldRec],
      by simp [hσ2, fieldRec]⟩
  · exact ⟨⟨packV W zs, ⟨by simp [hσ2, hσ1, emb_eq_iff], by simp [hσ2, hσ1, emb_eq_iff, hq0.2]⟩⟩,
      ⟨encS z, ⟨by simp [hσ2, hσ1, emb_eq_iff], by simp [hσ2, hσ1, emb_eq_iff, hm0.2]⟩⟩,
      ⟨0, ⟨by simp [hσ2, hσ1, emb_eq_iff], by simp [hσ2, hσ1, emb_eq_iff, hx0.2]⟩⟩⟩
  · refine ⟨fun y hy => ?_, fun r hr => ?_, by simp [hσ2, hσ1]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1,
        Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hσ2, hσ1, Function.update_of_ne hr]

theorem fieldRecs_length (L : ℕ) (l : List ℤ) : (l.flatMap (fieldRec L)).length = l.length * (2 * L + 1) := by
  induction l with
  | nil => simp
  | cons z l ih => simp [List.flatMap_cons, ih, fieldRec, frame_length]; ring

theorem exFields_spec (cap W L : ℕ) (hL : W + 2 ≤ L) (σ : WState ns nr) (cs : List ℤ) (out L0 : List Bool)
    (hlen : cs.length * (W + 1) ≤ L) (hfit : ∀ y ∈ cs, y.natAbs < 2 ^ W)
    (hV : NumOn σ (E 2) L (packV W cs)) (hMP : NumOn σ (E 3) L (2 ^ (W + 1))) (hw : ExWords E L σ)
    (h2 : σ.val (G 2) = 0) (h3 : σ.val (G 3) = 0) (h4 : σ.val (G 4) = 0) (h5 : σ.val (G 5) = 0)
    (h6 : σ.val (G 6) = 0) (hO : OutOn σ (E 7) (G 7) out L0) (hKS : σ.val (G 8) = cs.length)
    (hKS2 : σ.val (G 9) = 0) (hcap : 2 * L + 1 ≤ cap) (hcapN : 2 * cs.length ≤ cap)
    (hcapO : out.length + cs.length * (2 * L + 1) + 1 ≤ cap) :
    Runs cap (repK (G 8) (G 9) (exInner E G)) σ (cs.length * (exInnerCost L + 8) + 7 * cs.length + 3) (fun τ =>
      NumOn τ (E 2) L 0 ∧ OutOn τ (E 7) (G 7) (out ++ cs.flatMap (fieldRec L)) L0 ∧ ExWords E L τ ∧
        τ.val (G 8) = cs.length ∧ τ.val (G 9) = 0 ∧ SameExcept σ τ [E 2, E 4, E 5, E 6, E 7] [G 7]) := by
  have hne : ∀ {a b : Fin 8}, a ≠ b → E a ≠ E b := fun h => emb_ne E h
  have hner : ∀ {a b : Fin 11}, a ≠ b → G a ≠ G b := fun h => emb_ne G h
  let Inv : ℕ → WState ns nr → Prop := fun j ρ =>
    NumOn ρ (E 2) L (packV W (cs.drop j)) ∧ OutOn ρ (E 7) (G 7) (out ++ (cs.take j).flatMap (fieldRec L)) L0 ∧
      ExWords E L ρ ∧ SameExcept σ ρ [E 2, E 4, E 5, E 6, E 7] [G 7, G 8, G 9]
  have hInv : ∀ j ρ (k : Fin 11), k = 8 ∨ k = 9 → ∀ v, Inv j ρ → Inv j (ρ.setv (G k) v) := by
    rintro j ρ k hk v ⟨a1, a2, a3, a4⟩
    have h7 : G 7 ≠ G k := hner (by rcases hk with rfl | rfl <;> decide)
    exact ⟨BinW.numOn_setv a1 _ _, ⟨by simpa using a2.1, by simpa using a2.2.1, by
      rw [WState.setv_val, Function.update_of_ne h7]; exact a2.2.2⟩,
      exWords_frame E a3 (sameExcept_setv ρ (S := []) (Rg := [G k]) (by simp) v) (by simp) (by simp) (by simp),
      a4.trans (sameExcept_setv ρ (by rcases hk with rfl | rfl <;> simp) v)⟩
  have h := Runs.rep (cap := cap) (K := G 8) (K2 := G 9) (body := exInner E G) (hner (by decide))
    (exInnerCost L) cs.length Inv hcapN (fun j ρ v hI => hInv j ρ 8 (Or.inl rfl) v hI)
    (fun j ρ v hI => hInv j ρ 9 (Or.inr rfl) v hI) ?_ σ ⟨by simpa using hV, by simpa using hO, hw,
      SameExcept.refl _ _ _⟩ hKS hKS2
  · refine h.post fun τ hτ => ?_
    obtain ⟨⟨a1, a2, a3, a4⟩, a5, a6⟩ := hτ
    simp only [List.drop_length, List.take_length] at a1 a2
    refine ⟨by simpa [packV] using a1, a2, a3, a5, a6, ⟨a4.1, fun r hr => ?_, a4.2.2⟩⟩
    by_cases r8 : r = G 8
    · rw [r8, a5, hKS]
    · by_cases r9 : r = G 9
      · rw [r9, a6, hKS2]
      · exact a4.2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  · intro j hj ρ hI
    obtain ⟨a1, a2, a3, a4⟩ := hI
    have hval : ∀ k : Fin 11, k ≠ 7 → k ≠ 8 → k ≠ 9 → ρ.val (G k) = σ.val (G k) := fun k h7 h8 h9 =>
      a4.val (by simp [emb_eq_iff, h7, h8, h9])
    have hdrop : cs.drop j = cs[j] :: cs.drop (j + 1) := List.drop_eq_getElem_cons hj
    have hlj : (cs.take j).length = j := by simp; omega
    have hx := exInner_spec E G cap W L hL ρ cs[j] (cs.drop (j + 1)) (out ++ (cs.take j).flatMap (fieldRec L)) L0
      (hfit _ (List.getElem_mem hj))
      (by rw [← hdrop, List.length_drop]; exact le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) hlen)
      (by rw [← hdrop]; exact fun y hy => hfit y (List.mem_of_mem_drop hy)) (by rw [← hdrop]; exact a1)
      (a4.numOn (by simp [emb_eq_iff]) hMP) a3 (by rw [hval 2 (by decide) (by decide) (by decide)]; exact h2)
      (by rw [hval 3 (by decide) (by decide) (by decide)]; exact h3)
      (by rw [hval 4 (by decide) (by decide) (by decide)]; exact h4)
      (by rw [hval 5 (by decide) (by decide) (by decide)]; exact h5)
      (by rw [hval 6 (by decide) (by decide) (by decide)]; exact h6) a2 hcap
      (by
        rw [List.length_append, fieldRecs_length, hlj]
        have : (j + 1) * (2 * L + 1) ≤ cs.length * (2 * L + 1) := Nat.mul_le_mul_right _ (by omega)
        nlinarith)
    refine hx.post fun τ ⟨b1, b2, b3, b4⟩ => ⟨⟨b1, ?_, b3, a4.trans (b4.weaken (by simp) (by simp))⟩, ?_, ?_⟩
    · have e : (cs.take (j + 1)).flatMap (fieldRec L) = (cs.take j).flatMap (fieldRec L) ++ fieldRec L cs[j] := by
        exact flatMap_take_succ cs (fieldRec L) j hj
      show OutOn τ (E 7) (G 7) (out ++ (cs.take (j + 1)).flatMap (fieldRec L)) L0
      rw [e, ← List.append_assoc]; exact b2
    · exact b4.val (by simp [emb_eq_iff])
    · exact b4.val (by simp [emb_eq_iff])

/-- One child record: `V := Wk`, its `s + 1` fields, count it. -/
def exBody : WMX ns nr :=
  .seq (BinW.copy (E 2) (E 1) (G 2) (G 3)) (.seq (repK (G 8) (G 9) (exInner E G)) (WMX.inc (G 10)))

/-- **Explode**: every child record of stream `0` into its fields on the output stream `7`. -/
def explode : WMX ns nr := recLoop (E 0) (E 1) (G 0) (G 1) (exBody E G)

def exBodyCost (L N : ℕ) : ℕ := 41 * L + 3 + 1 + (N * (exInnerCost L + 8) + 7 * N + 3) + 1 + 3

/-- The explode loop's invariant. -/
def XInv (L : ℕ) (σ0 : WState ns nr) (css : List (List ℤ)) (out L0 : List Bool) (nk0 : ℕ) (i : ℕ)
    (ρ : WState ns nr) : Prop :=
  OutOn ρ (E 7) (G 7) (out ++ ((css.take i).flatten).flatMap (fieldRec L)) L0 ∧ ρ.val (G 10) = nk0 + i ∧
    (∃ v, NumOn ρ (E 2) L v) ∧ ExWords E L ρ ∧
    SameExcept σ0 ρ [E 0, E 1, E 2, E 4, E 5, E 6, E 7] [G 0, G 1, G 7, G 10] ∧ ρ.sh (E 1) = 0 ∧
    (ρ.st (E 1)).length ≤ 2 * L + 1

theorem exBody_spec (cap W N : ℕ) (hN : 2 ≤ N) (σ0 ρ : WState ns nr) (css : List (List ℤ)) (out L0 : List Bool)
    (nk0 i p : ℕ) (hi : i < css.length) (hlen : ∀ c ∈ css, c.length = N)
    (hfit : ∀ c ∈ css, ∀ y ∈ c, y.natAbs < 2 ^ W) (hMP : NumOn σ0 (E 3) (N * (W + 1)) (2 ^ (W + 1)))
    (h2 : σ0.val (G 2) = 0) (h3 : σ0.val (G 3) = 0) (h4 : σ0.val (G 4) = 0) (h5 : σ0.val (G 5) = 0)
    (h6 : σ0.val (G 6) = 0) (hKS : σ0.val (G 8) = N) (hKS2 : σ0.val (G 9) = 0)
    (hInv : XInv E G (N * (W + 1)) σ0 css out L0 nk0 i ρ)
    (hcap : 2 * (N * (W + 1)) + 1 + 2 * N + nk0 + css.length ≤ cap)
    (hcapO : out.length + css.length * N * (2 * (N * (W + 1)) + 1) + 1 ≤ cap) :
    ∃ τ, WXExec cap (exBody E G) (atRec (E 0) (E 1) (G 0) ρ (binary (N * (W + 1)) (packV W css[i])) p) τ
      (exBodyCost (N * (W + 1)) N) ∧ XInv E G (N * (W + 1)) σ0 css out L0 nk0 (i + 1) τ ∧
      BodyFrame (E 0) (E 1) (G 0) (G 1) (N * (W + 1))
        (atRec (E 0) (E 1) (G 0) ρ (binary (N * (W + 1)) (packV W css[i])) p) τ := by
  have hne : ∀ {a b : Fin 8}, a ≠ b → E a ≠ E b := fun h => emb_ne E h
  have hner : ∀ {a b : Fin 11}, a ≠ b → G a ≠ G b := fun h => emb_ne G h
  set L := N * (W + 1) with hLdef
  have hL : W + 2 ≤ L := by rw [hLdef]; nlinarith
  obtain ⟨a1, a2, ⟨v0, hv0⟩, a4, a5, hwh, -⟩ := hInv
  have hval : ∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 7 → k ≠ 10 → ρ.val (G k) = σ0.val (G k) :=
    fun k b0 b1 b7 b10 => a5.val (by simp [emb_eq_iff, b0, b1, b7, b10])
  set τ1 := atRec (E 0) (E 1) (G 0) ρ (binary L (packV W css[i])) p with hτ1
  have hfr1 : SameExcept ρ τ1 [E 0, E 1] [G 0] := ⟨fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hτ1, atRec, Function.update_of_ne hy.1, Function.update_of_ne hy.2], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [hτ1, atRec, Function.update_of_ne hr], rfl⟩
  have hWk1 : NumOn τ1 (E 1) L (packV W css[i]) := ⟨by simp [hτ1, atRec], by
    simp [hτ1, atRec, emb_eq_iff, hwh]⟩
  have hc := BinW.copy_spec (A := E 2) (B := E 1) (F := G 2) (R := G 3) cap L (hne (by decide)) (hner (by decide))
    τ1 v0 (packV W css[i]) (hfr1.numOn (by simp [emb_eq_iff]) hv0) hWk1
    (by rw [hfr1.val (by simp [emb_eq_iff]), hval 2 (by decide) (by decide) (by decide) (by decide)]; exact h2)
    (by rw [hfr1.val (by simp [emb_eq_iff]), hval 3 (by decide) (by decide) (by decide) (by decide)]; exact h3)
    (by omega)
  set τ2 := τ1.sets (E 2) (frame (binary L (packV W css[i]))) with hτ2
  have hfr12 : SameExcept τ1 τ2 [E 2] [] := sameExcept_sets τ1 (by simp) _
  have hfr2 : SameExcept ρ τ2 [E 0, E 1, E 2] [G 0] := (hfr1.comp' hfr12).weaken (by simp) (by simp)
  have hvτ2 : ∀ k : Fin 11, k ≠ 0 → k ≠ 1 → k ≠ 7 → k ≠ 10 → τ2.val (G k) = σ0.val (G k) :=
    fun k b0 b1 b7 b10 => by rw [hfr2.val (by simp [emb_eq_iff, b0])]; exact hval k b0 b1 b7 b10
  have hci_len : css[i].length = N := hlen _ (List.getElem_mem hi)
  have htl : ((css.take i).flatten).length = i * N := flatten_take_length N css i hlen hi.le
  have hf := exFields_spec E G cap W L hL τ2 css[i] (out ++ ((css.take i).flatten).flatMap (fieldRec L)) L0
    (by rw [hci_len]) (hfit _ (List.getElem_mem hi))
    (BinW.numOn_sets_self _ _ _ _ (by rw [hfr1.sh (by simp [emb_eq_iff])]; exact hv0.2))
    (hfr2.numOn (by simp [emb_eq_iff]) (a5.numOn (by simp [emb_eq_iff]) hMP))
    (exWords_frame E a4 hfr2 (by simp [emb_eq_iff]) (by simp [emb_eq_iff]) (by simp [emb_eq_iff]))
    (by rw [hvτ2 2 (by decide) (by decide) (by decide) (by decide)]; exact h2)
    (by rw [hvτ2 3 (by decide) (by decide) (by decide) (by decide)]; exact h3)
    (by rw [hvτ2 4 (by decide) (by decide) (by decide) (by decide)]; exact h4)
    (by rw [hvτ2 5 (by decide) (by decide) (by decide) (by decide)]; exact h5)
    (by rw [hvτ2 6 (by decide) (by decide) (by decide) (by decide)]; exact h6)
    ⟨by rw [hfr2.st (by simp [emb_eq_iff])]; exact a1.1, by rw [hfr2.sh (by simp [emb_eq_iff])]; exact a1.2.1,
      by rw [hfr2.val (by simp [emb_eq_iff])]; exact a1.2.2⟩
    (by rw [hci_len, hvτ2 8 (by decide) (by decide) (by decide) (by decide)]; exact hKS)
    (by rw [hvτ2 9 (by decide) (by decide) (by decide) (by decide)]; exact hKS2) (by omega) (by omega)
    (by
      rw [List.length_append, fieldRecs_length, htl, hci_len]
      have : (i + 1) * N * (2 * L + 1) ≤ css.length * N * (2 * L + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      nlinarith)
  obtain ⟨τ3, e3, b1, b2, b3, b4, b5, b6⟩ := hf
  have h10 : τ3.val (G 10) = nk0 + i := by
    rw [b6.val (by simp [emb_eq_iff]), hfr2.val (by simp [emb_eq_iff])]; exact a2
  have hi10 := WXExec.inc cap (G 10) τ3 (by rw [h10]; omega)
  rw [hci_len] at e3
  have hex : WXExec cap (exBody E G) τ1 (τ3.setv (G 10) (τ3.val (G 10) + 1)) (exBodyCost L N) :=
    (WXExec.seq hc (WXExec.seq e3 hi10)).mono (by unfold exBodyCost; omega)
  have f1 : ∀ x, x ∉ [E 2, E 4, E 5, E 6, E 7] → (τ3.setv (G 10) (τ3.val (G 10) + 1)).st x = τ1.st x ∧
      (τ3.setv (G 10) (τ3.val (G 10) + 1)).sh x = τ1.sh x := by
    intro x hx
    have hx2 : x ∉ [E 2] := fun e => hx (by simp at e; simp [e])
    have e1 := b6.1 x hx
    have e2 := hfr12.1 x hx2
    exact ⟨by simp only [WState.setv_st]; rw [e1.1, e2.1], by simp only [WState.setv_sh]; rw [e1.2, e2.2]⟩
  have wh4 : (τ3.setv (G 10) (τ3.val (G 10) + 1)).sh (E 1) = 0 := by
    rw [(f1 (E 1) (by simp [emb_eq_iff])).2]; simp [hτ1, atRec, emb_eq_iff, hwh]
  have wl4 : ((τ3.setv (G 10) (τ3.val (G 10) + 1)).st (E 1)).length ≤ 2 * L + 1 := by
    rw [(f1 (E 1) (by simp [emb_eq_iff])).1]; simp [hτ1, atRec, frame_length]
  refine ⟨_, hex, ⟨?_, ?_, ?_, ?_, ?_, wh4, wl4⟩, ?_⟩
  · have e : ((css.take (i + 1)).flatten).flatMap (fieldRec L) =
        ((css.take i).flatten).flatMap (fieldRec L) ++ css[i].flatMap (fieldRec L) := by
      rw [flatten_take_succ css i hi, List.flatMap_append]
    show OutOn _ (E 7) (G 7) (out ++ ((css.take (i + 1)).flatten).flatMap (fieldRec L)) L0
    rw [e, ← List.append_assoc]
    exact ⟨by simpa using b2.1, by simpa using b2.2.1, by
      rw [WState.setv_val, Function.update_of_ne (hner (by decide))]; exact b2.2.2⟩
  · rw [WState.setv_val, Function.update_self, h10]; omega
  · exact ⟨0, BinW.numOn_setv b1 _ _⟩
  · exact exWords_frame E b3 (sameExcept_setv τ3 (S := []) (Rg := [G 10]) (by simp) _) (by simp) (by simp)
      (by simp)
  · have h34 : SameExcept τ3 (τ3.setv (G 10) (τ3.val (G 10) + 1)) [] [G 10] := sameExcept_setv τ3 (by simp) _
    refine (((a5.comp' hfr2).comp' b6).comp' h34).weaken ?_ ?_
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with ((h | h | h | h | h | h | h) | (h | h | h)) | (h | h | h | h | h) <;> simp [h]
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with (((h | h | h | h) | h) | h) | h <;> simp [h]
  · have f2 : ∀ k : Fin 11, k ≠ 7 → k ≠ 10 → (τ3.setv (G 10) (τ3.val (G 10) + 1)).val (G k) = τ1.val (G k) := by
      intro k h7 h10'
      rw [WState.setv_val, Function.update_of_ne (hner h10'), b6.val (by simp [emb_eq_iff, h7]), hfr12.val (by simp)]
    exact ⟨(f1 (E 0) (by simp [emb_eq_iff])).1, (f1 (E 0) (by simp [emb_eq_iff])).2,
      f2 0 (by decide) (by decide), f2 1 (by decide) (by decide), wh4, wl4⟩

theorem explode_spec (cap W N : ℕ) (hN : 2 ≤ N) (σ : WState ns nr) (css : List (List ℤ)) (junk out L0 : List Bool)
    (nk0 : ℕ) (hlen : ∀ c ∈ css, c.length = N) (hfit : ∀ c ∈ css, ∀ y ∈ c, y.natAbs < 2 ^ W)
    (hI : σ.st (E 0) = recStream (css.map (recBits W)) ++ junk) (hIh : σ.sh (E 0) = 0)
    (hWh : σ.sh (E 1) = 0) (hWl : (σ.st (E 1)).length ≤ 2 * (N * (W + 1)) + 1)
    (hV : ∃ v, NumOn σ (E 2) (N * (W + 1)) v) (hMP : NumOn σ (E 3) (N * (W + 1)) (2 ^ (W + 1)))
    (hw : ExWords E (N * (W + 1)) σ) (h0 : σ.val (G 0) = 0) (h1 : σ.val (G 1) = 0)
    (h2 : σ.val (G 2) = 0) (h3 : σ.val (G 3) = 0) (h4 : σ.val (G 4) = 0) (h5 : σ.val (G 5) = 0)
    (h6 : σ.val (G 6) = 0) (hO : OutOn σ (E 7) (G 7) out L0) (hKS : σ.val (G 8) = N) (hKS2 : σ.val (G 9) = 0)
    (hNK : σ.val (G 10) = nk0)
    (hcap : css.length * (2 * (N * (W + 1)) + 1) + 2 * (N * (W + 1)) + 2 + 2 * N + nk0 ≤ cap)
    (hcapO : out.length + css.length * N * (2 * (N * (W + 1)) + 1) + 1 ≤ cap) :
    Runs cap (explode E G) σ (css.length * (exBodyCost (N * (W + 1)) N + (50 * (N * (W + 1)) + 30)) + 3)
      (fun τ => OutOn τ (E 7) (G 7) (out ++ css.flatten.flatMap (fieldRec (N * (W + 1)))) L0 ∧
        τ.val (G 10) = nk0 + css.length ∧ (∃ v, NumOn τ (E 2) (N * (W + 1)) v) ∧ ExWords E (N * (W + 1)) τ ∧
        τ.sh (E 1) = 0 ∧ (τ.st (E 1)).length ≤ 2 * (N * (W + 1)) + 1 ∧
        SameExcept σ τ [E 1, E 2, E 4, E 5, E 6, E 7] [G 7, G 10]) := by
  have hne : ∀ {a b : Fin 8}, a ≠ b → E a ≠ E b := fun h => emb_ne E h
  have hner : ∀ {a b : Fin 11}, a ≠ b → G a ≠ G b := fun h => emb_ne G h
  set L := N * (W + 1) with hLdef
  have hwl : ∀ w ∈ css.map (recBits W), w.length = L := by
    intro w hw'; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw'
    simp [recBits, hlen c hc, hLdef]
  have hb : BodySpecJ cap L (I := E 0) (Wk := E 1) (CI := G 0) (CW := G 1) (exBody E G) (css.map (recBits W))
      (XInv E G L σ css out L0 nk0) (fun _ => exBodyCost L N) junk := by
    intro i hi ρ hInv _ _ _ _ _ _
    simp only [List.length_map] at hi
    have hrec : (css.map (recBits W))[i] = binary L (packV W css[i]) := by
      rw [List.getElem_map, recBits_pack W _ (hfit _ (List.getElem_mem hi)), hlen _ (List.getElem_mem hi)]
    rw [hrec]
    exact exBody_spec E G cap W N hN σ ρ css out L0 nk0 i _ hi hlen hfit hMP h2 h3 h4 h5 h6 hKS hKS2 hInv
      (by have : i < css.length := hi; nlinarith) hcapO
  obtain ⟨τ, hInv, hτI, hτCW, hloop⟩ := recLoopJ_spec (cap := cap) (L := L) (I := E 0) (Wk := E 1) (CI := G 0)
    (CW := G 1) (body := exBody E G) (hne (by decide)) (hner (by decide)) hwl (by rw [hLdef]; nlinarith)
    (by simp only [List.length_map]; omega) hb σ
    ⟨by simpa using hO, by simpa using hNK, hV, hw, SameExcept.refl _ _ _, hWh, hWl⟩ hI hIh h0 h1 hWh hWl
  simp only [List.length_map, List.take_length] at hInv hloop
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hInv
  rw [List.take_of_length_le (le_refl _)] at c1
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
  have hne0 : ∀ x, x ≠ E 0 → ((τ.setv (G 0) 0).seth (E 0) 0).st x = τ.st x ∧
      ((τ.setv (G 0) 0).seth (E 0) 0).sh x = τ.sh x := fun x hx => by simp [Function.update_of_ne hx]
  have hv0 : ∀ r, r ≠ G 0 → ((τ.setv (G 0) 0).seth (E 0) 0).val r = τ.val r := fun r hr => by
    simp [Function.update_of_ne hr]
  refine ⟨_, hloop, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hne0 (E 7) (hne (by decide))).1]; exact c1.1
  · rw [(hne0 (E 7) (hne (by decide))).2]; exact c1.2.1
  · rw [hv0 _ (hner (by decide))]; exact c1.2.2
  · rw [hv0 _ (hner (by decide))]; exact c2
  · obtain ⟨v, hv⟩ := c3
    exact ⟨v, by rw [(hne0 (E 2) (hne (by decide))).1]; exact hv.1, by
      rw [(hne0 (E 2) (hne (by decide))).2]; exact hv.2⟩
  · obtain ⟨⟨q, hq⟩, ⟨m, hm⟩, ⟨x, hx⟩⟩ := c4
    exact ⟨⟨q, by rw [(hne0 (E 4) (hne (by decide))).1]; exact hq.1, by
        rw [(hne0 (E 4) (hne (by decide))).2]; exact hq.2⟩,
      ⟨m, by rw [(hne0 (E 5) (hne (by decide))).1]; exact hm.1, by rw [(hne0 (E 5) (hne (by decide))).2]; exact hm.2⟩,
      ⟨x, by rw [(hne0 (E 6) (hne (by decide))).1]; exact hx.1, by rw [(hne0 (E 6) (hne (by decide))).2]; exact hx.2⟩⟩
  · rw [(hne0 (E 1) (hne (by decide))).2]; exact c6
  · rw [(hne0 (E 1) (hne (by decide))).1]; exact c7
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by simp [c5.cell]⟩
    · by_cases hx0 : x = E 0
      · subst hx0; simp [hτI, hI, hIh]
      · rw [(hne0 x hx0).1, (hne0 x hx0).2]
        exact c5.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
    · by_cases r0 : r = G 0
      · subst r0; simp [h0]
      · rw [hv0 r r0]
        by_cases r1 : r = G 1
        · subst r1; rw [hτCW, h1]
        · exact c5.2.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)

end Explode

end NearCubicGates.Close.TabMachine
