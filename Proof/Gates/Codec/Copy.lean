import Proof.Gates.Codec.Circuit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

theorem marksApp (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by
  induction u with
  | nil => simp [marks]
  | cons b w ih => simp [marks] at ih ⊢

theorem marks_length (w : List Bool) : (marks w).length = 2 * w.length := by
  induction w with
  | nil => simp [marks]
  | cons b w ih => simp [marks] at ih ⊢; omega

theorem marks_flatMap {α : Type*} (u : α → List Bool) (xs : List α) :
    marks (xs.flatMap u) = xs.flatMap fun x => marks (u x) := by
  induction xs with
  | nil => simp [marks]
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- **The copy loop.** If `body` copies one element of `xs` (reads `g x` on `s`, appends `marks (u x)` to `o`), the
loop copies them all and clears `k`. -/
theorem copyLoop_spec {α : Type*} (s o : Fin (ns + 1)) (hso : s ≠ o) (k OP : Fin nr) (hkO : k ≠ OP) (body : WM ns nr)
    (g u : α → List Bool) (cost : α → ℕ) (ok : WState ns nr → Prop) (V : ℕ)
    (hok_h : ∀ σ x, ok σ → ok (σ.seth s x)) (hok_v : ∀ σ x, ok σ → ok (σ.setv k x))
    (hok_o : ∀ σ w, ok σ → ok (appendO σ o OP w)) (xs : List α)
    (hbody : ∀ x ∈ xs, ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st s = pre ++ g x ++ rest →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val OP + (marks (u x)).length ≤ V →
      WExec cap body σ ((appendO σ o OP (marks (u x))).seth s (pre.length + (g x).length)) (cost x)) :
    ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st s = pre ++ xs.flatMap g ++ rest →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val k = xs.length → xs.length ≤ cap →
      σ.val OP + (marks (xs.flatMap u)).length ≤ V →
      WExec cap (listLoop k body) σ
        (((appendO σ o OP (marks (xs.flatMap u))).setv k 0).seth s (pre.length + (xs.flatMap g).length))
        ((xs.map fun x => cost x + 4).sum + 1) := by
  induction xs with
  | nil =>
    intro pre rest σ _ _ hsh _ hk _ _
    have e : ((appendO σ o OP (marks (([] : List α).flatMap u))).setv k 0).seth s
        (pre.length + (([] : List α).flatMap g).length) = σ := by
      refine WState.eq ?_ ?_ ?_ rfl
      · funext j; by_cases hj : j = s
        · subst hj; simp [appendO, marks, hsh]
        · by_cases hjo : j = o
          · subst hjo; simp [appendO, marks, Function.update_of_ne hj]
          · simp [appendO, Function.update_of_ne hj]
      · funext j; by_cases hjo : j = o
        · subst hjo; simp [appendO, marks]
        · simp [appendO, Function.update_of_ne hjo]
      · funext r; by_cases hr : r = k
        · subst hr; simp [appendO, hk]
        · by_cases hrO : r = OP
          · subst hrO; simp [appendO, marks, Function.update_of_ne hr]
          · simp [appendO, Function.update_of_ne hr]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hk)) (by simp)
  | cons x xs ih =>
    intro pre rest σ hσ hst hsh ho hk hcap hV
    have h1 := WExec.dec (cap := cap) k σ (by rw [hk]; simpa using hcap)
    set σ1 := σ.setv k (σ.val k - 1) with hσ1
    have hok1 : ok σ1 := hok_v σ _ hσ
    have hst1 : σ1.st s = pre ++ g x ++ (xs.flatMap g ++ rest) := by
      simp only [hσ1, WState.setv_st]; rw [hst]; simp [List.flatMap_cons, List.append_assoc]
    have hmx : (marks ((x :: xs).flatMap u)).length = (marks (u x)).length + (marks (xs.flatMap u)).length := by
      simp [List.flatMap_cons]
    have h2 := hbody x (by simp) pre (xs.flatMap g ++ rest) σ1 hok1 hst1 (by simp [hσ1, hsh]) (by simp [hσ1, ho])
      (by simp only [hσ1, WState.setv_val]; rw [Function.update_of_ne (Ne.symm hkO)]; omega)
    set σ2 := (appendO σ1 o OP (marks (u x))).seth s (pre.length + (g x).length) with hσ2
    have hok2 : ok σ2 := hok_h _ _ (hok_o _ _ hok1)
    have hst2 : σ2.st s = (pre ++ g x) ++ xs.flatMap g ++ rest := by
      simp only [hσ2, WState.seth_st, appendO_st]; rw [Function.update_of_ne hso]
      simp only [hσ1, WState.setv_st]; rw [hst]; simp [List.flatMap_cons, List.append_assoc]
    have hsh2 : σ2.sh s = (pre ++ g x).length := by simp [hσ2]
    have ho2 : σ2.sh o = (σ2.st o).length := by
      simp only [hσ2, WState.seth_sh, WState.seth_st, appendO_st, appendO_sh]
      rw [Function.update_of_ne (Ne.symm hso), Function.update_self, Function.update_self]
      simp [hσ1, ho]
    have hk2 : σ2.val k = xs.length := by
      simp only [hσ2, WState.seth_val, appendO_val]
      rw [Function.update_of_ne hkO]; simp [hσ1, hk]
    have hV2 : σ2.val OP + (marks (xs.flatMap u)).length ≤ V := by
      simp only [hσ2, WState.seth_val, appendO_val, Function.update_self]
      simp only [hσ1, WState.setv_val]; rw [Function.update_of_ne (Ne.symm hkO)]; omega
    have h3 := ih (fun y hy => hbody y (List.mem_cons_of_mem x hy)) (pre ++ g x) rest σ2 hok2 hst2 hsh2 ho2 hk2
      (by simp at hcap; omega) hV2
    have hne : σ.val k ≠ 0 := by rw [hk]; simp
    refine WExec.cast cap (WExec.whrT hne (WExec.seq h1 h2) h3) ?_ (by simp; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; by_cases hj : j = s
      · subst hj; simp [hσ2, List.flatMap_cons, Nat.add_assoc]
      · by_cases hjo : j = o
        · subst hjo
          simp [hσ2, hσ1, appendO, Function.update_of_ne hj, ho,
            List.flatMap_cons, Nat.add_assoc]
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo
        simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hso), List.flatMap_cons, List.append_assoc]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hjo]
    · funext r; by_cases hr : r = k
      · subst hr; simp [hσ2, hσ1, appendO]
      · by_cases hrO : r = OP
        · subst hrO
          simp [hσ2, hσ1, appendO, Function.update_of_ne hr,
            List.flatMap_cons, Nat.add_assoc]
        · simp [hσ2, hσ1, appendO, Function.update_of_ne hr, Function.update_of_ne hrO]

/-- Copy `listWord g xs`: read the count into `R 0`, write it canonically, then copy the elements (`R 1 … R 6`
scratch, `R 7` the output position). -/
def copyList (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (body : WM ns nr) : WM ns nr :=
  .seq (readNatM ε s (R 1) (R 2) (R 0) (R 3) (R 6)) (.seq (writeNatM o R) (listLoop (R 0) body))

theorem Rne (R : Fin 8 ↪ Fin nr) {i j : Fin 8} (h : i ≠ j) : R i ≠ R j := R.injective.ne h

/-- The cost of `copyList`. -/
def copyListCost (m : ℕ) (cs : List ℕ) : ℕ :=
  (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) + 1 +
    ((natBitLength m + 10) * (100 * m + 200) + 1 + ((cs.map fun c => c + 4).sum + 1))

theorem copyList_spec {α : Type} (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr)
    (body : WM ns nr) (g : α → List Bool) (cost : α → ℕ) (ok : WState ns nr → Prop) (V : ℕ)
    (hok_h : ∀ σ x, ok σ → ok (σ.seth s x)) (hok_v : ∀ σ x, ok σ → ok (σ.setv (R 0) x))
    (hok_o : ∀ σ w, ok σ → ok (appendO σ o (R 7) w)) (xs : List α)
    (hbody : ∀ x ∈ xs, ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st s = pre ++ enc ε (g x) ++ rest →
      σ.sh s = pre.length → σ.sh o = (σ.st o).length → σ.val (R 7) + (marks (g x)).length ≤ V →
      WExec cap body σ ((appendO σ o (R 7) (marks (g x))).seth s (pre.length + stp ε * (g x).length)) (cost x))
    (pre rest : List Bool) (σ : WState ns nr) (hok : ok σ)
    (hst : σ.st s = pre ++ enc ε (listWord g xs) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength xs.length + 1) ≤ cap) (hlen : xs.length ≤ cap)
    (hcapw : xs.length + σ.val (R 7) + 6 * natBitLength xs.length + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (listWord g xs)).length ≤ V) :
    WExec cap (copyList ε s o R body) σ
      ((appendO σ o (R 7) (marks (listWord g xs))).seth s (pre.length + stp ε * (listWord g xs).length))
      (copyListCost xs.length (xs.map cost)) := by
  have hsplit : enc ε (listWord g xs) = enc ε (natWord xs.length) ++ xs.flatMap fun x => enc ε (g x) := by
    unfold listWord; rw [NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, enc_flatMap]
  have h1 := readNatM_spec cap ε s (R 1) (R 2) (R 0) (R 3) (R 6) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
    (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide)) xs.length pre
    ((xs.flatMap fun x => enc ε (g x)) ++ rest) σ (by rw [hst, hsplit]; simp [List.append_assoc]) hsh
    (hz 1 (by decide)) (hz 2 (by decide)) (hz 3 (by decide)) (hz 6 (by decide)) (by rw [hz 0 (by decide)]; simpa using hcap)
  set σ1 := (σ.seth s (pre.length + stp ε * (natWord xs.length).length)).setv (R 0) (σ.val (R 0) + xs.length)
    with hσ1
  have hR : ∀ i : Fin 8, i ≠ 0 → σ1.val (R i) = σ.val (R i) := by
    intro i hi; simp [hσ1, Function.update_of_ne (Rne R hi)]
  have h2 := writeNatM_spec cap o R σ1 (by rw [hR 1 (by decide)]; exact hz 1 (by decide))
    (by rw [hR 2 (by decide)]; exact hz 2 (by decide)) (by rw [hR 3 (by decide)]; exact hz 3 (by decide))
    (by rw [hR 4 (by decide)]; exact hz 4 (by decide)) (by rw [hR 5 (by decide)]; exact hz 5 (by decide))
    (by rw [hR 6 (by decide)]; exact hz 6 (by decide)) (by simp [hσ1, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ1, hz 0 (by decide)]; omega)
  have hv0 : σ1.val (R 0) = xs.length := by simp [hσ1, hz 0 (by decide)]
  rw [hv0] at h2
  set σ2 := appendO σ1 o (R 7) (marks (natWord xs.length)) with hσ2
  have hok2 : ok σ2 := hok_o _ _ (hok_v _ _ (hok_h _ _ hok))
  have hbody' : ∀ x ∈ xs, ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ →
      σ.st s = pre ++ enc ε (g x) ++ rest → σ.sh s = pre.length → σ.sh o = (σ.st o).length →
      σ.val (R 7) + (marks (g x)).length ≤ V →
      WExec cap body σ ((appendO σ o (R 7) (marks (g x))).seth s (pre.length + (enc ε (g x)).length)) (cost x) := by
    intro x hx pre rest σ hσ h1 h2 h3 h4
    rw [WireExponent3_5.PrimAsm.ParseNat.enc_length]; exact hbody x hx pre rest σ hσ h1 h2 h3 h4
  have hml : (marks (listWord g xs)).length = (marks (natWord xs.length)).length + (marks (xs.flatMap g)).length := by
    unfold listWord; rw [marksApp, List.length_append]
  have hv2 : σ2.val (R 7) = σ.val (R 7) + (marks (natWord xs.length)).length := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne (Rne R (show (7 : Fin 8) ≠ 0 by decide))]
  have h3 := copyLoop_spec cap s o hso (R 0) (R 7) (Rne R (by decide)) body (fun x => enc ε (g x)) g cost ok V
    hok_h hok_v hok_o xs hbody' (pre ++ enc ε (natWord xs.length)) rest σ2 hok2
    (by simp only [hσ2, appendO_st, hσ1]; rw [Function.update_of_ne hso]; simp only [WState.setv_st, WState.seth_st];
        rw [hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ2, hσ1, Function.update_of_ne hso, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ2, hσ1, appendO, Function.update_of_ne (Rne R (show (0 : Fin 8) ≠ 7 by decide)), hz 0 (by decide)])
    hlen (by rw [hv2]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by unfold copyListCost; rw [List.map_map]; exact le_refl _)
  have hfl : (xs.flatMap fun x => enc ε (g x)).length = stp ε * (xs.flatMap g).length := by
    rw [← enc_flatMap, WireExponent3_5.PrimAsm.ParseNat.enc_length]
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ2, hσ1, appendO, Function.update_of_ne hso, listWord, hfl,
        WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
    · by_cases hjo : j = o
      · subst hjo; simp [hσ2, hσ1, appendO, Function.update_of_ne hj, ho, listWord, marksApp]; ring
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hso), listWord, marksApp]
    · by_cases hj : j = s
      · subst hj; simp [hσ2, hσ1, appendO, Function.update_of_ne hjo]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hjo, Function.update_of_ne hj]
  · funext r; by_cases hr0 : r = R 0
    · subst hr0
      simp [hσ2, hσ1, appendO, Function.update_of_ne (Rne R (show (0 : Fin 8) ≠ 7 by decide)), hz 0 (by decide)]
    · by_cases hr7 : r = R 7
      · subst hr7
        simp [hσ2, hσ1, appendO, Function.update_of_ne hr0, listWord, marksApp]; ring
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hr0, Function.update_of_ne hr7]

/-- Copy one `natWord` (the shared `copyNatM`, scratch `R 1, R 2`, position `R 7`). -/
abbrev copyNat (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM ε s o (R 1) (R 2) (R 7)

theorem copyNat_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (x : ℕ)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (natWord x) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * (natWord x).length + 2 ≤ cap) :
    WExec cap (copyNat ε s o R) σ ((appendO σ o (R 7) (marks (natWord x))).seth s (pre.length + stp ε * (natWord x).length))
      (60 * (natWord x).length + 60) :=
  NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM_spec cap ε s o hso (R 1) (R 2) (R 7) (Rne R (by decide)) (Rne R (by decide)) (Rne R (by decide))
    x pre rest σ hst hsh ho h1 h2 hcap

def copyInt (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr := .seq (copyNat ε s o R) (copyNat ε s o R)

theorem copyInt_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (z : ℤ)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (Interfaces.intWord z) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * (Interfaces.intWord z).length + 4 ≤ cap) :
    WExec cap (copyInt ε s o R) σ
      ((appendO σ o (R 7) (marks (Interfaces.intWord z))).seth s (pre.length + stp ε * (Interfaces.intWord z).length))
      (60 * (Interfaces.intWord z).length + 121) := by
  have hsplit : enc ε (Interfaces.intWord z) = enc ε (natWord (if z < 0 then 1 else 0)) ++ enc ε (natWord z.natAbs) := by
    unfold Interfaces.intWord; exact NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append ε _ _
  have hl : (Interfaces.intWord z).length = (natWord (if z < 0 then 1 else 0)).length + (natWord z.natAbs).length := by
    simp [Interfaces.intWord]
  have hA := copyNat_spec cap ε s o hso R (if z < 0 then 1 else 0) pre (enc ε (natWord z.natAbs) ++ rest) σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) hsh ho h1 h2 (by omega)
  set σ1 := (appendO σ o (R 7) (marks (natWord (if z < 0 then 1 else 0)))).seth s
    (pre.length + stp ε * (natWord (if z < 0 then 1 else 0)).length) with hσ1
  have hB := copyNat_spec cap ε s o hso R z.natAbs (pre ++ enc ε (natWord (if z < 0 then 1 else 0))) rest σ1
    (by simp only [hσ1, WState.seth_st, appendO_st]; rw [Function.update_of_ne hso, hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)), h1])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), h2])
    (by simp only [hσ1, WState.seth_val, appendO_val, Function.update_self]; rw [marks_length]; omega)
  refine WExec.cast cap (WExec.seq hA hB) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hso, Interfaces.intWord,
        WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
    · by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, ho, Interfaces.intWord, marksApp]; ring
      · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), Interfaces.intWord, marksApp]
    · by_cases hj : j = s
      · subst hj; simp [hσ1, appendO, Function.update_of_ne hjo]
      · simp [hσ1, appendO, Function.update_of_ne hjo, Function.update_of_ne hj]
  · funext r; by_cases hr7 : r = R 7
    · subst hr7; simp [hσ1, appendO, Interfaces.intWord, marksApp]; ring
    · simp [hσ1, appendO, Function.update_of_ne hr7]

/-- Copy `listWord intWord zs`. -/
def copyIntList (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr := copyList ε s o R (copyInt ε s o R)

theorem copyIntList_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (V : ℕ) (hVcap : V + 4 ≤ cap)
    (zs : List ℤ) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ enc ε (listWord Interfaces.intWord zs) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength zs.length + 1) ≤ cap) (hlen : zs.length ≤ cap)
    (hcapw : zs.length + σ.val (R 7) + 6 * natBitLength zs.length + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (listWord Interfaces.intWord zs)).length ≤ V) :
    WExec cap (copyIntList ε s o R) σ
      ((appendO σ o (R 7) (marks (listWord Interfaces.intWord zs))).seth s
        (pre.length + stp ε * (listWord Interfaces.intWord zs).length))
      (copyListCost zs.length (zs.map fun z => 60 * (Interfaces.intWord z).length + 121)) := by
  refine copyList_spec cap ε s o hso R (copyInt ε s o R) Interfaces.intWord (fun z => 60 * (Interfaces.intWord z).length + 121)
    (fun σ => σ.val (R 1) = 0 ∧ σ.val (R 2) = 0) V (fun σ x h => by simpa using h)
    (fun σ x h => by
      simp [Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 0 by decide)),
        Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 0 by decide)), h.1, h.2])
    (fun σ w h => by
      simp [appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)),
        Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), h.1, h.2])
    zs ?_ pre rest σ ⟨hz 1 (by decide), hz 2 (by decide)⟩ hst hsh ho hz hcap hlen hcapw hV
  intro z _ pre' rest' σ' hok hst' hsh' ho' hV'
  exact copyInt_spec cap ε s o hso R z pre' rest' σ' hst' hsh' ho' hok.1 hok.2
    (by rw [marks_length] at hV'; omega)

/-- Copy `gateWord g = listWord intWord (ofFn g.weight) ++ intWord g.threshold`. -/
def copyGate (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (copyIntList ε s o R) (copyInt ε s o R)

theorem copyGate_spec {n : ℕ} (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (V : ℕ)
    (hVcap : V + 4 ≤ cap) (gt : NormalizedThresholdGate n) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ enc ε (gateWord gt) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength n + 1) ≤ cap) (hlen : n ≤ cap)
    (hcapw : n + V + 6 * natBitLength n + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (gateWord gt)).length ≤ V) :
    WExec cap (copyGate ε s o R) σ
      ((appendO σ o (R 7) (marks (gateWord gt))).seth s (pre.length + stp ε * (gateWord gt).length))
      (copyListCost n ((List.ofFn gt.weight).map fun z => 60 * (Interfaces.intWord z).length + 121) + 1 +
        (60 * (Interfaces.intWord gt.threshold).length + 121)) := by
  have hsplit : enc ε (gateWord gt) = enc ε (listWord Interfaces.intWord (List.ofFn gt.weight)) ++
      enc ε (Interfaces.intWord gt.threshold) := by
    unfold gateWord; exact NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append ε _ _
  have hml : (marks (gateWord gt)).length = (marks (listWord Interfaces.intWord (List.ofFn gt.weight))).length +
      (marks (Interfaces.intWord gt.threshold)).length := by unfold gateWord; rw [marksApp, List.length_append]
  have hA := copyIntList_spec cap ε s o hso R V hVcap (List.ofFn gt.weight) pre (enc ε (Interfaces.intWord gt.threshold) ++ rest)
    σ (by rw [hst, hsplit]; simp [List.append_assoc]) hsh ho hz (by simpa using hcap) (by simpa using hlen)
    (by simp; omega) (by omega)
  set σ1 := (appendO σ o (R 7) (marks (listWord Interfaces.intWord (List.ofFn gt.weight)))).seth s
    (pre.length + stp ε * (listWord Interfaces.intWord (List.ofFn gt.weight)).length) with hσ1
  have hB := copyInt_spec cap ε s o hso R gt.threshold (pre ++ enc ε (listWord Interfaces.intWord (List.ofFn gt.weight))) rest σ1
    (by simp only [hσ1, WState.seth_st, appendO_st]; rw [Function.update_of_ne hso, hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)), hz 1 (by decide)])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), hz 2 (by decide)])
    (by
      have e1 : σ1.val (R 7) = σ.val (R 7) + 2 * (listWord Interfaces.intWord (List.ofFn gt.weight)).length := by
        simp [hσ1, appendO, marks_length]
      rw [e1]; rw [marks_length, marks_length, marks_length] at hml; rw [marks_length] at hV; omega)
  refine WExec.cast cap (WExec.seq hA hB) ?_ (by rw [List.length_ofFn])
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hso, gateWord, WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
    · by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, ho, gateWord, marksApp]; ring
      · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), gateWord, marksApp]
    · by_cases hj : j = s
      · subst hj; simp [hσ1, appendO, Function.update_of_ne hjo]
      · simp [hσ1, appendO, Function.update_of_ne hjo, Function.update_of_ne hj]
  · funext r; by_cases hr7 : r = R 7
    · subst hr7; simp [hσ1, appendO, gateWord, marksApp]; ring
    · simp [hσ1, appendO, Function.update_of_ne hr7]

/-- `R` with its count register replaced by `m`. -/
def withCount (R : Fin 8 ↪ Fin nr) (m : Fin nr) (hm : ∀ i : Fin 8, R i ≠ m) : Fin 8 ↪ Fin nr where
  toFun i := if i = 0 then m else R i
  inj' := by
    intro i j h
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj] at h
    · rw [hi, hj]
    · exact absurd h.symm (hm j)
    · exact absurd h (hm i)
    · exact h

@[simp] theorem withCount_zero (R : Fin 8 ↪ Fin nr) (m : Fin nr) (hm : ∀ i : Fin 8, R i ≠ m) :
    withCount R m hm 0 = m := by simp [withCount]

theorem withCount_ne (R : Fin 8 ↪ Fin nr) (m : Fin nr) (hm : ∀ i : Fin 8, R i ≠ m) (i : Fin 8) (hi : i ≠ 0) :
    withCount R m hm i = R i := by simp [withCount, hi]

/-- Copy `listWord gateWord gs` (outer count `m`, the gates use `R`). -/
def copyGateList (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (m : Fin nr) (hm : ∀ i : Fin 8, R i ≠ m) :
    WM ns nr := copyList ε s o (withCount R m hm) (copyGate ε s o R)

theorem copyGateList_spec {n : ℕ} (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (m : Fin nr)
    (hm : ∀ i : Fin 8, R i ≠ m) (V : ℕ) (hVcap : V + 4 ≤ cap) (gs : List (NormalizedThresholdGate n))
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (listWord gateWord gs) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hm0 : σ.val m = 0) (hcapn : 2 ^ (natBitLength n + 1) ≤ cap) (hlenn : n ≤ cap)
    (hcapwn : n + V + 6 * natBitLength n + 6 ≤ cap)
    (hcap : 2 ^ (natBitLength gs.length + 1) ≤ cap) (hlen : gs.length ≤ cap)
    (hcapw : gs.length + V + 6 * natBitLength gs.length + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (listWord gateWord gs)).length ≤ V) :
    WExec cap (copyGateList ε s o R m hm) σ
      ((appendO σ o (R 7) (marks (listWord gateWord gs))).seth s (pre.length + stp ε * (listWord gateWord gs).length))
      (copyListCost gs.length (gs.map fun gt => copyListCost n ((List.ofFn gt.weight).map
        fun z => 60 * (Interfaces.intWord z).length + 121) + 1 + (60 * (Interfaces.intWord gt.threshold).length + 121))) := by
  have hW7 : withCount R m hm 7 = R 7 := withCount_ne R m hm 7 (by decide)
  have hmR : ∀ i : Fin 8, m ≠ R i := fun i e => hm i e.symm
  have hz' : ∀ i : Fin 8, i ≠ 7 → σ.val (withCount R m hm i) = 0 := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0; simp [hm0]
    · rw [withCount_ne R m hm i h0]; exact hz i hi
  have h := copyList_spec cap ε s o hso (withCount R m hm) (copyGate ε s o R) gateWord
    (fun gt => copyListCost n ((List.ofFn gt.weight).map fun z => 60 * (Interfaces.intWord z).length + 121) + 1 +
      (60 * (Interfaces.intWord gt.threshold).length + 121))
    (fun σ => ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0) V
    (fun σ x h i hi => by simpa using h i hi)
    (fun σ x h i hi => by rw [withCount_zero]; simp [Function.update_of_ne (hm i), h i hi])
    (fun σ w h i hi => by rw [hW7]; simp [appendO, Function.update_of_ne (Rne R hi), h i hi])
    gs ?_ pre rest σ hz hst hsh ho hz' hcap hlen (by rw [hW7]; omega) (by rw [hW7]; exact hV)
  · rw [hW7] at h; exact h
  · intro gt _ pre' rest' σ' hok hst' hsh' ho' hV'
    rw [hW7] at hV' ⊢
    exact copyGate_spec cap ε s o hso R V hVcap gt pre' rest' σ' hst' hsh' ho' hok hcapn hlenn hcapwn hV'

def copyBitList (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr := copyList ε s o R (copyNat ε s o R)

theorem copyBitList_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (V : ℕ)
    (_hVcap : V + 2 ≤ cap) (bs : List Bool) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ enc ε (listWord bitWord bs) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (hcap : 2 ^ (natBitLength bs.length + 1) ≤ cap) (hlen : bs.length ≤ cap)
    (hcapw : bs.length + V + 6 * natBitLength bs.length + 6 ≤ cap)
    (hV : σ.val (R 7) + (marks (listWord bitWord bs)).length ≤ V) :
    WExec cap (copyBitList ε s o R) σ
      ((appendO σ o (R 7) (marks (listWord bitWord bs))).seth s (pre.length + stp ε * (listWord bitWord bs).length))
      (copyListCost bs.length (bs.map fun b => 60 * (bitWord b).length + 60)) := by
  refine copyList_spec cap ε s o hso R (copyNat ε s o R) bitWord (fun b => 60 * (bitWord b).length + 60)
    (fun σ => σ.val (R 1) = 0 ∧ σ.val (R 2) = 0) V (fun σ x h => by simpa using h)
    (fun σ x h => by
      simp [Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 0 by decide)),
        Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 0 by decide)), h.1, h.2])
    (fun σ w h => by
      simp [appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)),
        Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), h.1, h.2])
    bs ?_ pre rest σ ⟨hz 1 (by decide), hz 2 (by decide)⟩ hst hsh ho hz hcap hlen (by omega) hV
  intro b _ pre' rest' σ' hok hst' hsh' ho' hV'
  exact copyNat_spec cap ε s o hso R (if b then 1 else 0) pre' rest' σ' (by simpa [bitWord] using hst') hsh' ho'
    hok.1 hok.2 (by rw [marks_length] at hV'; simp [bitWord] at hV' ⊢; omega)

/-- Copy `circuitWord C` (the gate list's count `m`, the inner lists' count `R 0`). -/
def copyCircuit (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (m : Fin nr) (hm : ∀ i : Fin 8, R i ≠ m) :
    WM ns nr :=
  .seq (copyGateList ε s o R m hm) (.seq (copyIntList ε s o R) (copyBitList ε s o R))

/-- The cost of copying one circuit. -/
def copyCircuitCost {n : ℕ} (C : NCircuit n) : ℕ :=
  copyListCost C.gates.length (C.gates.map fun gt => copyListCost n ((List.ofFn gt.weight).map
    fun z => 60 * (Interfaces.intWord z).length + 121) + 1 + (60 * (Interfaces.intWord gt.threshold).length + 121)) + 1 +
  (copyListCost C.coeffs.length (C.coeffs.map fun z => 60 * (Interfaces.intWord z).length + 121) + 1 +
    copyListCost C.table.length (C.table.map fun b => 60 * (bitWord b).length + 60))

/-- The capacity hypotheses for copying one circuit with output budget `V`. -/
def CopyFits {n : ℕ} (cap V : ℕ) (C : NCircuit n) : Prop :=
  V + 4 ≤ cap ∧ 2 ^ (natBitLength n + 1) ≤ cap ∧ n ≤ cap ∧ n + V + 6 * natBitLength n + 6 ≤ cap ∧
    (∀ m ∈ [C.gates.length, C.coeffs.length, C.table.length],
      2 ^ (natBitLength m + 1) ≤ cap ∧ m ≤ cap ∧ m + V + 6 * natBitLength m + 6 ≤ cap)

theorem copyCircuit_spec {n : ℕ} (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (m : Fin nr)
    (hm : ∀ i : Fin 8, R i ≠ m) (V : ℕ) (C : NCircuit n) (hfit : CopyFits cap V C) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (circuitWord C) ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.sh o = (σ.st o).length) (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0) (hm0 : σ.val m = 0)
    (hV : σ.val (R 7) + (marks (circuitWord C)).length ≤ V) :
    WExec cap (copyCircuit ε s o R m hm) σ
      ((appendO σ o (R 7) (marks (circuitWord C))).seth s (pre.length + stp ε * (circuitWord C).length))
      (copyCircuitCost C) := by
  obtain ⟨hVc, hcn, hln, hwn, hlists⟩ := hfit
  obtain ⟨hg2, hgl, hgw⟩ := hlists C.gates.length (by simp)
  obtain ⟨hc2, hcl, hcw⟩ := hlists C.coeffs.length (by simp)
  obtain ⟨ht2, htl, htw⟩ := hlists C.table.length (by simp)
  have hsplit : enc ε (circuitWord C) = enc ε (listWord gateWord C.gates) ++ enc ε (listWord Interfaces.intWord C.coeffs) ++
      enc ε (listWord bitWord C.table) := by
    unfold circuitWord
    rw [NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append]
  have hml : (marks (circuitWord C)).length = 2 * (listWord gateWord C.gates).length +
      2 * (listWord Interfaces.intWord C.coeffs).length + 2 * (listWord bitWord C.table).length := by
    rw [marks_length]; simp [circuitWord]; ring
  rw [hml] at hV
  have hA := copyGateList_spec cap ε s o hso R m hm V hVc C.gates pre
    (enc ε (listWord Interfaces.intWord C.coeffs) ++ enc ε (listWord bitWord C.table) ++ rest) σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) hsh ho hz hm0 hcn hln hwn hg2 hgl hgw
    (by rw [marks_length]; omega)
  set σ1 := (appendO σ o (R 7) (marks (listWord gateWord C.gates))).seth s
    (pre.length + stp ε * (listWord gateWord C.gates).length) with hσ1
  have hz1 : ∀ i : Fin 8, i ≠ 7 → σ1.val (R i) = 0 := by
    intro i hi; simp [hσ1, appendO, Function.update_of_ne (Rne R hi), hz i hi]
  have hv1 : σ1.val (R 7) = σ.val (R 7) + 2 * (listWord gateWord C.gates).length := by
    simp [hσ1, appendO, marks_length]
  have hB := copyIntList_spec cap ε s o hso R V hVc C.coeffs (pre ++ enc ε (listWord gateWord C.gates))
    (enc ε (listWord bitWord C.table) ++ rest) σ1
    (by simp only [hσ1, WState.seth_st, appendO_st]; rw [Function.update_of_ne hso, hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho]) hz1 hc2 hcl (by rw [hv1]; omega)
    (by rw [hv1, marks_length]; omega)
  set σ2 := (appendO σ1 o (R 7) (marks (listWord Interfaces.intWord C.coeffs))).seth s
    ((pre ++ enc ε (listWord gateWord C.gates)).length + stp ε * (listWord Interfaces.intWord C.coeffs).length) with hσ2
  have hz2 : ∀ i : Fin 8, i ≠ 7 → σ2.val (R i) = 0 := by
    intro i hi; simp [hσ2, appendO, Function.update_of_ne (Rne R hi), hz1 i hi]
  have hv2 : σ2.val (R 7) = σ1.val (R 7) + 2 * (listWord Interfaces.intWord C.coeffs).length := by
    simp [hσ2, appendO, marks_length]
  have hC := copyBitList_spec cap ε s o hso R V (by omega) C.table
    (pre ++ enc ε (listWord gateWord C.gates) ++ enc ε (listWord Interfaces.intWord C.coeffs)) rest σ2
    (by simp only [hσ2, hσ1, WState.seth_st, appendO_st]; rw [Function.update_of_ne hso, Function.update_of_ne hso, hst,
        hsplit]; simp [List.append_assoc])
    (by simp [hσ2, WireExponent3_5.PrimAsm.ParseNat.enc_length, Nat.add_assoc])
    (by simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho, Nat.add_assoc]) hz2 ht2 htl htw
    (by rw [hv2, hv1, marks_length]; omega)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB hC)) ?_ (le_refl _)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ2, hσ1, appendO, Function.update_of_ne hso, circuitWord,
        WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
    · by_cases hjo : j = o
      · subst hjo; simp [hσ2, hσ1, appendO, Function.update_of_ne hj, ho, circuitWord, marksApp]; ring
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm hso), circuitWord, marksApp]
    · by_cases hj : j = s
      · subst hj; simp [hσ2, hσ1, appendO, Function.update_of_ne hjo]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hjo, Function.update_of_ne hj]
  · funext r; by_cases hr7 : r = R 7
    · subst hr7; simp [hσ2, hσ1, appendO, circuitWord, marksApp]; ring
    · simp [hσ2, hσ1, appendO, Function.update_of_ne hr7]

end NearCubicGates.Close.Codec
