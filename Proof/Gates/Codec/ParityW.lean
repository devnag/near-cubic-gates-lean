import Proof.Gates.Codec.CallPairW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

/-- No parity. -/
def parNone (o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr := emitMarks o OP (natWord 0)

theorem parNone_spec (o : Fin (ns + 1)) (OP : Fin nr) (τ : WState ns nr) (ho : τ.sh o = (τ.st o).length)
    (hc : τ.val OP + 2 * (natWord 0).length ≤ cap) :
    WExec cap (parNone o OP) τ (appendO τ o OP (marks (listWord natWord ([] : List ℕ)))) (16 * (natWord 0).length) := by
  have e := emitMarks_spec cap o OP (natWord 0) τ ho hc
  have hl : listWord natWord ([] : List ℕ) = natWord 0 := by simp [listWord]
  rw [hl]; exact e

/-- The `writeNatM` registers printing `Rg 14`: `Rg 14`, `Rg 1 … Rg 6`, `Rg 7`. -/
def rgU (Rg : Fin 16 ↪ Fin nr) : Fin 8 ↪ Fin nr :=
  ⟨fun i => if i.val = 0 then Rg 14 else Rg ⟨i.val, by omega⟩, fun a b h => by
    have h' : Rg (if a.val = 0 then 14 else ⟨a.val, by omega⟩) = Rg (if b.val = 0 then 14 else ⟨b.val, by omega⟩) := by
      have ea : (if a.val = 0 then Rg 14 else Rg ⟨a.val, by omega⟩) = Rg (if a.val = 0 then 14 else ⟨a.val, by omega⟩) := by
        split <;> rfl
      have eb : (if b.val = 0 then Rg 14 else Rg ⟨b.val, by omega⟩) = Rg (if b.val = 0 then 14 else ⟨b.val, by omega⟩) := by
        split <;> rfl
      rw [← ea, ← eb]; exact h
    have := Rg.injective h'
    clear h h'
    fin_cases a <;> fin_cases b <;> simp_all (config := { decide := true })⟩

/-- The single outer-randomness coordinate `u` (held in `Rg 14`). -/
def parSys (o : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (emitMarks o (Rg 7) (natWord 1)) (writeNatM o (rgU Rg))

theorem parSys_spec (o : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (u : ℕ) (τ : WState ns nr)
    (ho : τ.sh o = (τ.st o).length) (hu : τ.val (Rg 14) = u)
    (hz : ∀ k : Fin 16, 1 ≤ k.val → k.val ≤ 6 → τ.val (Rg k) = 0)
    (hc : τ.val (Rg 7) + 2 * (natWord 1).length + u + 6 * natBitLength u + 6 ≤ cap) :
    WExec cap (parSys o Rg) τ (appendO τ o (Rg 7) (marks (listWord natWord [u])))
      (16 * (natWord 1).length + 1 + (natBitLength u + 10) * (100 * u + 200)) := by
  have e1 := emitMarks_spec cap o (Rg 7) (natWord 1) τ ho (by omega)
  set τ1 := appendO τ o (Rg 7) (marks (natWord 1)) with hτ1
  have h7 : ∀ k : Fin 16, k ≠ 7 → τ1.val (Rg k) = τ.val (Rg k) := fun k hk => by
    simp [hτ1, Function.update_of_ne (Rg_ne Rg hk)]
  have hR : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → τ1.val (rgU Rg i) = 0 := by
    intro i h0 h7'
    have hi : rgU Rg i = Rg ⟨i.val, by omega⟩ := by
      show (if i.val = 0 then Rg 14 else Rg ⟨i.val, by omega⟩) = _
      split_ifs with h
      · exact absurd (Fin.ext h) h0
      · rfl
    rw [hi, h7 _ (fun h => h7' (Fin.ext (by simpa using congrArg Fin.val h)))]
    exact hz _ (by simp; exact Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h)))
      (by simp; have := i.isLt; have : i.val ≠ 7 := fun h => h7' (Fin.ext h); omega)
  have e2 := writeNatM_spec cap o (rgU Rg) τ1 (hR 1 (by decide) (by decide)) (hR 2 (by decide) (by decide))
    (hR 3 (by decide) (by decide)) (hR 4 (by decide) (by decide)) (hR 5 (by decide) (by decide))
    (hR 6 (by decide) (by decide)) (by simp [hτ1, ho])
    (by
      have h0 : τ1.val (rgU Rg 0) = u := by show τ1.val (Rg 14) = u; rw [h7 14 (by decide)]; exact hu
      have h7'' : τ1.val (rgU Rg 7) = τ.val (Rg 7) + 2 * (natWord 1).length := by
        show τ1.val (Rg 7) = _; simp [hτ1, marks_length]
      rw [h0, h7'']; omega)
  have h0 : τ1.val (rgU Rg 0) = u := by show τ1.val (Rg 14) = u; rw [h7 14 (by decide)]; exact hu
  rw [h0] at e2
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  show appendO τ1 o (Rg 7) (marks (natWord u)) = _
  apply WState.eq
  · funext y; by_cases hy : y = o
    · subst hy; simp [hτ1, appendO, marks_length, ho, listWord, marksApp]; omega
    · simp [hτ1, appendO, Function.update_of_ne hy]
  · funext y; by_cases hy : y = o
    · subst hy; simp [hτ1, appendO, listWord, marksApp]
    · simp [hτ1, appendO, Function.update_of_ne hy]
  · funext r; by_cases hr : r = Rg 7
    · subst hr; simp [hτ1, appendO, listWord, marksApp, marks_length]; omega
    · simp [hτ1, appendO, Function.update_of_ne hr]
  · rfl

/-! ## A code-parity row of the supports record -/

/-- The marked words of the first `r` rows (`listWord natWord (rows j)`). -/
def rowPrefix (rows : ℕ → List ℕ) (r : ℕ) : List Bool :=
  (List.range r).flatMap fun j => marks (listWord natWord (rows j))

theorem rowPrefix_succ (rows : ℕ → List ℕ) (r : ℕ) :
    rowPrefix rows (r + 1) = rowPrefix rows r ++ marks (listWord natWord (rows r)) := by
  simp [rowPrefix, List.range_succ, List.flatMap_append]

theorem rowPrefix_split (rows : ℕ → List ℕ) {r R : ℕ} (h : r < R) :
    rowPrefix rows R = rowPrefix rows r ++ marks (listWord natWord (rows r)) ++
      (rowPrefix rows R).drop (rowPrefix rows (r + 1)).length := by
  have hpre : rowPrefix rows R = rowPrefix rows (r + 1) ++ (rowPrefix rows R).drop (rowPrefix rows (r + 1)).length := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show r + 1 ≤ R from h)
    have : rowPrefix rows (r + 1 + d) = rowPrefix rows (r + 1) ++
        (List.range' (r + 1) d).flatMap (fun j => marks (listWord natWord (rows j))) := by
      simp [rowPrefix, List.range_add, List.flatMap_append, List.range'_eq_map_range]
    rw [this, List.drop_left]
  rw [← rowPrefix_succ]
  exact hpre

/-- Skip `r` rows (`I = r` counts down): `skipList` of `skipNat` on the marked record. -/
def seekRows (S : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) : WM ns nr :=
  repLoop (Rg 9) (skipList true S (Rg 0) (Rg 1) (Rg 2) (Rg 3) (Rg 4) (skipNat true S (Rg 5) (Rg 6)))

/-- The cost of skipping one row. -/
def rowCost (row : List ℕ) : ℕ := skipListCost row.length (row.map fun x => 20 * natBitLength x + 20)

theorem seekRows_spec (S : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (rows : ℕ → List ℕ) (R r : ℕ) (hr : r ≤ R)
    (rb : ℕ) (hrb : ∀ j < R, rowCost (rows j) ≤ rb)
    (hfit : ∀ j < R, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
      ∀ x ∈ rows j, natBitLength x + 1 ≤ cap)
    (hcap : r ≤ cap) (rest : List Bool) (σ : WState ns nr) (hst : σ.st S = rowPrefix rows R ++ rest)
    (hsh : σ.sh S = 0) (hz : ∀ k : Fin 16, k.val ≤ 6 → σ.val (Rg k) = 0) (hI : σ.val (Rg 9) = r) :
    WExec cap (seekRows S Rg) σ ((σ.seth S (rowPrefix rows r).length).setv (Rg 9) 0) (r * (rb + 4) + 1) := by
  have hne : ∀ k : Fin 16, k.val ≤ 6 → Rg k ≠ Rg 9 := fun k hk => Rg_ne Rg (fun h => by
    have := congrArg Fin.val h; simp at this; omega)
  set g : ℕ → WState ns nr := fun j => (σ.seth S (rowPrefix rows j).length).setv (Rg 9) (r - j) with hg
  have hg0 : g 0 = σ := by
    apply WState.eq
    · funext x; by_cases hx : x = S
      · subst hx; simp [hg, hsh, rowPrefix]
      · simp [hg, Function.update_of_ne hx]
    · rfl
    · funext q; by_cases hq : q = Rg 9
      · subst hq; simp [hg, hI]
      · simp [hg, Function.update_of_ne hq]
    · rfl
  have hgz : ∀ j (k : Fin 16), k.val ≤ 6 → (g j).val (Rg k) = 0 := fun j k hk => by
    simp [hg, Function.update_of_ne (hne k hk), hz k hk]
  have hbody : ∀ j < r, WExec cap (skipList true S (Rg 0) (Rg 1) (Rg 2) (Rg 3) (Rg 4) (skipNat true S (Rg 5) (Rg 6)))
      ((g j).setv (Rg 9) (r - j - 1)) (g (j + 1)) rb := by
    intro j hj
    have hjR : j < R := lt_of_lt_of_le hj hr
    have hsplit := rowPrefix_split rows hjR
    set τ := (g j).setv (Rg 9) (r - j - 1) with hτ
    have hτz : ∀ k : Fin 16, k.val ≤ 6 → τ.val (Rg k) = 0 := fun k hk => by
      simp [hτ, Function.update_of_ne (hne k hk), hgz j k hk]
    have hd : [Rg 0, Rg 1, Rg 2, Rg 3, Rg 4].Nodup := by
      have h : ([0, 1, 2, 3, 4] : List (Fin 16)).Nodup := by decide
      have h2 := h.map Rg.injective
      simp only [List.map_cons, List.map_nil] at h2
      exact h2
    have e := skipList_spec cap true S (Rg 0) (Rg 1) (Rg 2) (Rg 3) (Rg 4) (skipNat true S (Rg 5) (Rg 6)) hd natWord
      (fun x => 20 * natBitLength x + 20) (fun σ' => σ'.val (Rg 5) = 0 ∧ σ'.val (Rg 6) = 0)
      (fun σ' x h => by simpa using h)
      (fun σ' x h => by
        simp only [WState.setv_val]
        rw [Function.update_of_ne (Rg_ne Rg (by decide)), Function.update_of_ne (Rg_ne Rg (by decide))]
        exact h)
      (rows j)
      (fun x hx pre rest' σ' hok hst' hsh' =>
        skipNat_spec cap true S (Rg 5) (Rg 6) (Rg_ne Rg (by decide)) x pre rest' σ' hst' hsh' hok.1 hok.2
          ((hfit j hjR).2.2 x hx))
      (rowPrefix rows j) ((rowPrefix rows R).drop (rowPrefix rows (j + 1)).length ++ rest) τ
      ⟨hτz 5 (by decide), hτz 6 (by decide)⟩
      (by
        show σ.st S = _
        rw [hst]
        conv_lhs => rw [hsplit]
        simp only [WireExponent3_5.PrimAsm.ParseNat.enc, if_true, List.append_assoc])
      (by simp [hτ, hg])
      (hτz 0 (by decide)) (hτz 1 (by decide)) (hτz 2 (by decide)) (hτz 3 (by decide)) (hτz 4 (by decide))
      (hfit j hjR).1 (hfit j hjR).2.1
    refine WExec.cast cap e ?_ (hrb j hjR)
    apply WState.eq
    · funext x; by_cases hx : x = S
      · subst hx; simp [hτ, hg, rowPrefix_succ, WireExponent3_5.PrimAsm.ParseNat.stp, marks_length]
      · simp [hτ, hg, Function.update_of_ne hx]
    · rfl
    · funext q; by_cases hq : q = Rg 9
      · subst hq; simp [hτ, hg]; omega
      · simp [hτ, hg, Function.update_of_ne hq]
    · rfl
  have e := repLoop_spec cap (Rg 9) _ r rb g (fun j _ => by simp [hg]) hcap hbody
  rw [hg0] at e
  refine WExec.cast cap e ?_ le_rfl
  simp [hg]

/-- Row `r` (index in `Rg 14`) of the supports record `S`: rewind (bound in `LS`), seek, copy. -/
def parRow (S o : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr) (LS : Fin nr) : WM ns nr :=
  .seq (rewindCW S LS (Rg 11) (Rg 10))
  (.seq (dupR (Rg 14) (Rg 9) (Rg 10))
  (.seq (seekRows S Rg) (copyList true S o (rgC Rg) (copyNat true S o (rgC Rg)))))

/-- **Row parity.** From any state whose `Rg` registers are scratch-zero (except `Rg 7` the output counter, `Rg 14 = r`
and the untouched `Rg 12, 13, 15`), with `S` holding the marked rows, `parRow` appends `marks (listWord natWord
(rows r))` and leaves the head of `S` after row `r`. -/
theorem parRow_spec (S o : Fin (ns + 1)) (hSo : S ≠ o) (Rg : Fin 16 ↪ Fin nr) (LS : Fin nr) (hLS : ∀ k, LS ≠ Rg k)
    (rows : ℕ → List ℕ) (R r : ℕ) (hr : r < R) (rb V Lb : ℕ) (hrb : ∀ j < R, rowCost (rows j) ≤ rb)
    (hfit : ∀ j < R, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
      ∀ x ∈ rows j, natBitLength x + 1 ≤ cap)
    (hrc : 2 * r ≤ cap) (hLb : 2 * Lb ≤ cap)
    (hrw : (rows r).length + V + 6 * natBitLength (rows r).length + 6 ≤ cap)
    (rest : List Bool) (τ : WState ns nr) (hst : τ.st S = rowPrefix rows R ++ rest) (hshL : τ.sh S ≤ Lb)
    (ho : τ.sh o = (τ.st o).length)
    (hz : ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → τ.val (Rg k) = 0)
    (hR : τ.val (Rg 14) = r) (hLv : τ.val LS = Lb)
    (hV : τ.val (Rg 7) + (marks (listWord natWord (rows r))).length ≤ V) :
    WExec cap (parRow S o Rg LS) τ
      (appendO (τ.seth S (rowPrefix rows (r + 1)).length) o (Rg 7) (marks (listWord natWord (rows r))))
      (18 * Lb + 3 + 1 + (5 * Lb + 1) + 1 + (18 * r + 3 + 1 + (r * (rb + 4) + 1 + 1 +
        copyListCost (rows r).length ((rows r).map fun x => 60 * (natWord x).length + 60)))) := by
  have hz' : ∀ k : Fin 16, k.val ≤ 6 → τ.val (Rg k) = 0 := fun k hk =>
    hz k (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
  -- rewind
  have e1 := rewindCW_spec cap S LS (Rg 11) (Rg 10) (hLS 11) (hLS 10) (Rg_ne Rg (by decide)) τ
    (hz 11 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hz 10 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [hLv]; exact hshL) (by omega)
  rw [hLv] at e1
  set τ1 := τ.seth S 0 with hτ1
  -- `I := r`
  have e2 := dupR_spec cap (Rg 14) (Rg 9) (Rg 10) (Rg_ne Rg (by decide)) (Rg_ne Rg (by decide)) (Rg_ne Rg (by decide)) τ1
    (by simp [hτ1]; exact hz 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [hτ1, hR, hz 9 (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  have hI0 : τ1.val (Rg 9) = 0 := by simp [hτ1]; exact hz 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hR1 : τ1.val (Rg 14) = r := by simp [hτ1, hR]
  rw [hI0, hR1, Nat.zero_add] at e2
  set τ2 := τ1.setv (Rg 9) r with hτ2
  -- seek
  have e3 := seekRows_spec cap S Rg rows R r hr.le rb hrb hfit (by omega) rest τ2 (by simp [hτ2, hτ1, hst])
    (by simp [hτ2, hτ1])
    (fun k hk => by
      simp [hτ2, hτ1, Function.update_of_ne (Rg_ne Rg (fun h => by
        have := congrArg Fin.val h; simp at this; omega) : Rg k ≠ Rg 9), hz' k hk])
    (by simp [hτ2])
  set τ3 := (τ2.seth S (rowPrefix rows r).length).setv (Rg 9) 0 with hτ3
  -- copy
  have hsplit := rowPrefix_split rows hr
  have hRC : ∀ i : Fin 8, i ≠ 7 → τ3.val (rgC Rg i) = 0 := fun i hi => by
    rw [rgC_val]
    have hk : (⟨i.val, by omega⟩ : Fin 16).val ≤ 6 := by
      simp; have := i.isLt; have : i.val ≠ 7 := fun h => hi (Fin.ext h); omega
    simp [hτ3, hτ2, hτ1]
    by_cases h9 : (Rg ⟨i.val, by omega⟩) = Rg 9
    · simp [h9]
    · simp [Function.update_of_ne h9, hz' _ hk]
  have e4 := copyList_spec cap true S o hSo (rgC Rg) (copyNat true S o (rgC Rg)) natWord
    (fun x => 60 * (natWord x).length + 60) (fun σ' => σ'.val (rgC Rg 1) = 0 ∧ σ'.val (rgC Rg 2) = 0) V
    (fun σ' x h => by simpa using h)
    (fun σ' x h => by
      simp only [WState.setv_val]
      rw [Function.update_of_ne ((rgC Rg).injective.ne (by decide)), Function.update_of_ne ((rgC Rg).injective.ne (by decide))]
      exact h)
    (fun σ' w h => by
      simp only [appendO_val]
      rw [Function.update_of_ne ((rgC Rg).injective.ne (by decide)), Function.update_of_ne ((rgC Rg).injective.ne (by decide))]
      exact h)
    (rows r)
    (fun x _ pre rest' σ' hok hst' hsh' ho' hV' =>
      copyNat_spec cap true S o hSo (rgC Rg) x pre rest' σ' hst' hsh' ho' hok.1 hok.2
        (by simp only [marks_length] at hV'; omega))
    (rowPrefix rows r) ((rowPrefix rows R).drop (rowPrefix rows (r + 1)).length ++ rest) τ3
    ⟨hRC 1 (by decide), hRC 2 (by decide)⟩
    (by
      show τ.st S = _
      rw [hst]
      conv_lhs => rw [hsplit]
      simp only [WireExponent3_5.PrimAsm.ParseNat.enc, if_true, List.append_assoc])
    (by simp [hτ3])
    (by simp [hτ3, hτ2, hτ1, Function.update_apply, hSo.symm, ho])
    hRC (hfit r hr).1 (hfit r hr).2.1
    (by
      have h7 : τ3.val (rgC Rg 7) = τ.val (Rg 7) := by
        rw [rgC_seven]; simp [hτ3, hτ2, hτ1, Function.update_of_ne (Rg_ne Rg (by decide) : Rg 7 ≠ Rg 9)]
      rw [h7]; simp only [marks_length] at hV; omega)
    (by
      have h7 : τ3.val (rgC Rg 7) = τ.val (Rg 7) := by
        rw [rgC_seven]; simp [hτ3, hτ2, hτ1, Function.update_of_ne (Rg_ne Rg (by decide) : Rg 7 ≠ Rg 9)]
      rw [h7]; exact hV)
  rw [rgC_seven] at e4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = S
    · subst hy; simp [hτ3, hτ2, hτ1, appendO, Function.update_apply, hSo, rowPrefix_succ,
        WireExponent3_5.PrimAsm.ParseNat.stp, marks_length]
    · by_cases hyo : y = o
      · subst hyo; simp [hτ3, hτ2, hτ1, appendO, Function.update_apply, hy]
      · simp [hτ3, hτ2, hτ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyo]
  · funext y; by_cases hyo : y = o
    · subst hyo; simp [hτ3, hτ2, hτ1, appendO, Function.update_apply, hSo.symm]
    · simp [hτ3, hτ2, hτ1, appendO, Function.update_of_ne hyo]
  · funext q
    simp only [hτ3, hτ2, hτ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases h7 : q = Rg 7
    · subst h7; simp [Rg_ne Rg (by decide : (7 : Fin 16) ≠ 9)]
    · by_cases h9 : q = Rg 9
      · subst h9; simp [h7, hz 9 (by decide) (by decide) (by decide) (by decide) (by decide)]
      · simp [h7, h9]
  · rfl

end NearCubicGates.Close.Codec
