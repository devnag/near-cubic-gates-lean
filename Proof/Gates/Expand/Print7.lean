import Proof.Gates.Expand.PrintVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

section Prog
variable (PB : Fin 14 ↪ Fin (ns + 1)) (PG : Fin 5 ↪ Fin nr) (PR : Fin 4 ↪ Fin nr) (O : Fin (ns + 1)) (OP : Fin nr)
  (I CN : Fin (ns + 1)) (CI CW : Fin nr)

def rewO : WMX ns nr := .whr OP (.seq (WMX.dec OP) (WMX.bwd O))

def printPhase : WMX ns nr :=
  .seq (natW CN O OP PR) (.seq (recLoop I (PB 0) CI CW (prRec PB PG PR O OP)) (rewO O OP))

end Prog

theorem rewO_spec (cap : ℕ) (O : Fin (ns + 1)) (OP : Fin nr) (τ : WState ns nr) :
    ∀ k ρ, k ≤ cap → (SameExcept τ ρ [O] [OP] ∧ ρ.st O = τ.st O ∧ ρ.sh O = k ∧ ρ.val OP = k) →
      Runs cap (rewO O OP) ρ (k * (3 + 2) + 1)
        (fun ρ' => SameExcept τ ρ' [O] [OP] ∧ ρ'.st O = τ.st O ∧ ρ'.sh O = 0 ∧ ρ'.val OP = 0) := by
  intro k ρ hk hρ
  refine Runs.whr (fun k ρ => k ≤ cap ∧ SameExcept τ ρ [O] [OP] ∧ ρ.st O = τ.st O ∧ ρ.sh O = k ∧ ρ.val OP = k) 3 _
    (fun ρ h => ⟨h.2.2.2.2, h.2⟩) (fun k ρ h => ⟨by rw [h.2.2.2.2]; simp, ?_⟩) k ρ ⟨hk, hρ⟩
  obtain ⟨hk, fr, hst, hsh, hv⟩ := h
  refine Runs.seq' (c2 := 1) (Runs.of (Q := fun ρ' => ρ' = ρ.setv OP (ρ.val OP - 1)) (WXExec.dec cap OP ρ (by omega)) rfl)
    (fun ρ1 h1 => ?_) (by omega)
  subst h1
  refine Runs.of (WXExec.bwd cap O _) ⟨by omega, ?_, ?_, ?_, ?_⟩
  · exact (fr.trans (sameExcept_setv _ (by simp) _)).trans (sameExcept_seth _ (by simp) _)
  · simpa using hst
  · simp [hsh]
  · simp [hv]

/-- The print phase's layout: the loop stream, its counters and the count stream apart from the block. -/
structure PPLay (PB : Fin 14 ↪ Fin (ns + 1)) (PG : Fin 5 ↪ Fin nr) (PR : Fin 4 ↪ Fin nr) (O : Fin (ns + 1))
    (OP : Fin nr) (I CN : Fin (ns + 1)) (CI CW : Fin nr) : Prop where
  pl : PLay PB PG PR O OP
  bi : ∀ i, PB i ≠ I
  bc : ∀ i, PB i ≠ CN
  io : I ≠ O
  co : CN ≠ O
  ic : I ≠ CN
  cicw : CI ≠ CW
  gci : ∀ i, PG i ≠ CI
  gcw : ∀ i, PG i ≠ CW
  pci : ∀ i, PR i ≠ CI
  pcw : ∀ i, PR i ≠ CW
  oci : OP ≠ CI
  ocw : OP ≠ CW

section Phase
variable {PB : Fin 14 ↪ Fin (ns + 1)} {PG : Fin 5 ↪ Fin nr} {PR : Fin 4 ↪ Fin nr} {O : Fin (ns + 1)} {OP : Fin nr}
  {I CN : Fin (ns + 1)} {CI CW : Fin nr} {cap Wb : ℕ}

/-- The print loop's invariant. -/
def PInv (PB : Fin 14 ↪ Fin (ns + 1)) (O : Fin (ns + 1)) (OP : Fin nr) (I : Fin (ns + 1)) (CI CW : Fin nr)
    (Wb V W : ℕ) (σ : WState ns nr) (w0 : Fin 14 → ℕ) (pre : List Bool) (orc : List ℕ) (i : ℕ)
    (τ : WState ns nr) : Prop :=
  ∃ w, MV PB Wb w τ ∧ (∀ j, 9 ≤ j.val → w j = w0 j) ∧ (∀ j, w j < 2 ^ Wb) ∧
    τ.st O = σ.st O ++ (pre ++ (orc.take i).flatMap (recOut V W)) ∧
    τ.sh O = σ.sh O + (pre ++ (orc.take i).flatMap (recOut V W)).length ∧
    τ.val OP = σ.val OP + (pre ++ (orc.take i).flatMap (recOut V W)).length ∧
    SameExcept σ τ (I :: bl PB O) [OP, CI, CW]

theorem prBodyJ (hp : PPLay PB PG PR O OP I CN CI CW) (V W : ℕ) (σ : WState ns nr) (w0 : Fin 14 → ℕ)
    (hc : PConst V W w0) (pre : List Bool) (orc : List ℕ) (junk : List Bool) (hO0 : σ.sh O = (σ.st O).length)
    (hG : ∀ k, σ.val (PG k) = 0) (hR : ∀ k, σ.val (PR k) = 0) (Lo : ℕ)
    (hLo : (pre ++ orc.flatMap (recOut V W)).length ≤ Lo) (horc : ∀ x ∈ orc, x < 2 ^ Wb)
    (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hW : 1 ≤ Wb) (hcap : 2 * Wb + 2 ≤ cap)
    (hcO : σ.val OP + Lo + 2 * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    BodySpecJ cap Wb (I := I) (Wk := PB 0) (CI := CI) (CW := CW) (prRec PB PG PR O OP) (orc.map (binary Wb))
      (PInv PB O OP I CI CW Wb V W σ w0 pre orc) (fun _ => prRecCost Wb V) junk := by
  intro i hi τ ⟨w, hw, wc, hok, hO, hOh, hOP, fr⟩ _ _ _ hcw hwh _
  have hil : i < orc.length := by simpa using hi
  set x := orc[i] with hxd
  have hx : x < 2 ^ Wb := horc x (List.getElem_mem hil)
  set τa := atRec I (PB 0) CI τ (orc.map (binary Wb))[i] ((i + 1) * (2 * Wb + 1)) with hτa
  have fa : SameExcept τ τa [I, PB 0] [CI] := by
    rw [hτa]; unfold atRec
    exact SameExcept.trans (SameExcept.trans (sameExcept_sets τ (by simp) _) (sameExcept_seth _ (by simp) _))
      (sameExcept_setv _ (by simp) _)
  have hMVa : MV PB Wb (Function.update w 0 x) τa := by
    intro j
    by_cases e : j = 0
    · subst e
      simp only [Function.update_self]
      exact ⟨by simp [hτa, atRec, Function.update_of_ne (hp.bi 0), hxd], by
        simp [hτa, atRec, Function.update_of_ne (hp.bi 0), hwh]⟩
    · rw [Function.update_of_ne e]
      exact fa.numOn (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hp.bi j, fun h' => e (PB.injective h')⟩) (hw j)
  have nO : O ∉ [I, PB 0] := by simp [hp.io.symm, (hp.pl.bo 0).symm]
  have vreg : ∀ r, r ∉ [OP, CI, CW] → τa.val r = σ.val r := by
    intro r hr
    rw [fa.val (by simp at hr ⊢; exact hr.2.1), fr.val hr]
  have hG' : ∀ k, τa.val (PG k) = 0 := fun k => by
    rw [vreg _ (by simp [hp.pl.go k, hp.gci k, hp.gcw k]), hG k]
  have hR' : ∀ k, τa.val (PR k) = 0 := fun k => by
    rw [vreg _ (by simp [hp.pl.po k, hp.pci k, hp.pcw k]), hR k]
  have z : Regs0 PG PR τa := ⟨hG' 1, hG' 2, hG' 3, hR'⟩
  have hRS : RS PB PG O OP Wb τa τa (Function.update w 0 x) [] 0 0 :=
    ⟨hMVa, by simp, by simp, by simp, hG' 0, hG' 4, SameExcept.refl _ _ _⟩
  have hc' : PConst V W (Function.update w 0 x) := by
    have e : ∀ j : Fin 14, 9 ≤ j.val → Function.update w 0 x j = w0 j := by
      intro j hj; rw [Function.update_of_ne (by rintro rfl; simp at hj), wc j hj]
    exact ⟨by rw [e 9 (by decide), hc.tm], by rw [e 10 (by decide), hc.m], by rw [e 11 (by decide), hc.one],
      by rw [e 12 (by decide), hc.h], by rw [e 13 (by decide), hc.zero]⟩
  have hokA : ∀ j, Function.update w 0 x j < 2 ^ Wb := by
    intro j; by_cases e : j = 0
    · subst e; simpa using hx
    · rw [Function.update_of_ne e]; exact hok j
  have hO0a : τa.sh O = (τa.st O).length := by
    rw [fa.sh nO, fa.st nO, hOh, hO]; simp [hO0]
  have hsplit : (orc.flatMap (recOut V W)).length = ((orc.take (i + 1)).flatMap (recOut V W)).length +
      ((orc.drop (i + 1)).flatMap (recOut V W)).length := by
    rw [← List.length_append, ← List.flatMap_append, List.take_append_drop]
  have hts := WordPrograms.flatMap_take_succ' orc (recOut V W) i hil
  rw [← hxd] at hts
  have hlen : (pre ++ (orc.take (i + 1)).flatMap (recOut V W)).length ≤ Lo := by
    refine le_trans ?_ hLo
    simp only [List.length_append]; omega
  have hOPa : τa.val OP = σ.val OP + (pre ++ (orc.take i).flatMap (recOut V W)).length := by
    rw [fa.val (by simp [hp.oci]), hOP]
  obtain ⟨τ', hrun, w', hRS', wc', _, hok'⟩ := prRec_spec z hp.pl V W x hRS hc' (by simp) hokA hTW hO0a hW hcap
    (by rw [hOPa]; rw [hts] at hlen; simp only [List.length_append, List.nil_append] at hlen ⊢; omega)
  obtain ⟨hw', hO', hOh', hOP', hF', hGL', s3⟩ := hRS'
  have s3' : SameExcept τa τ' (bl PB O) [OP] := by
    refine ⟨s3.1, fun r hr => ?_, s3.2.2⟩
    by_cases e0 : r = PG 0
    · subst e0; rw [hF', hG' 0]
    · by_cases e4 : r = PG 4
      · subst e4; rw [hGL', hG' 4]
      · exact s3.2.1 r (by simp at hr ⊢; exact ⟨hr, e0, e4⟩)
  have nI : I ∉ bl PB O := by
    simp only [bl, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hp.io, fun h => hp.bi 0 h.symm, fun h => hp.bi 1 h.symm, fun h => hp.bi 2 h.symm,
      fun h => hp.bi 3 h.symm, fun h => hp.bi 4 h.symm, fun h => hp.bi 5 h.symm, fun h => hp.bi 6 h.symm,
      fun h => hp.bi 7 h.symm, fun h => hp.bi 8 h.symm⟩
  refine ⟨τ', hrun, ⟨w', hw', fun j hj => ?_, hok', ?_, ?_, ?_, ?_⟩, ⟨s3'.st nI, s3'.sh nI, s3'.val (by simp [hp.oci.symm]),
    s3'.val (by simp [hp.ocw.symm]), (hw' 0).2, by rw [(hw' 0).1]; simp [frame_length]⟩⟩
  · rw [wc' j hj, Function.update_of_ne (by rintro rfl; simp at hj), wc j hj]
  · rw [hO', fa.st nO, hO, hts]; simp [List.append_assoc]
  · rw [hOh', fa.sh nO, hOh, hts]; simp; ring
  · rw [hOP', hOPa, hts]; simp; ring
  · refine (fr.trans (se_sub fa (by simp [List.cons_subset, bl]) (by simp))).trans (se_sub s3' (by
      intro y hy; exact List.mem_cons_of_mem _ hy) (by simp))

def printCost (Wb V n Lo : ℕ) : ℕ :=
  natWCost Wb + 1 + (((∑ _i ∈ Finset.range n, (prRecCost Wb V + (50 * Wb + 30))) + 3) + 1 + (Lo * (3 + 2) + 1))

/-- **The print phase.** -/
theorem printPhase_spec (hp : PPLay PB PG PR O OP I CN CI CW) (V W : ℕ) (σ : WState ns nr) (w0 : Fin 14 → ℕ)
    (hw : MV PB Wb w0 σ) (hc : PConst V W w0) (hok : ∀ j, w0 j < 2 ^ Wb) (cnt : ℕ) (hCN : NumOn σ CN Wb cnt)
    (hcnt : cnt < 2 ^ Wb) (orc : List ℕ) (junk : List Bool) (hI : σ.st I = recStream (orc.map (binary Wb)) ++ junk)
    (hIh : σ.sh I = 0) (hCI : σ.val CI = 0) (hCW : σ.val CW = 0) (hOe : σ.st O = []) (hOh : σ.sh O = 0)
    (hOP : σ.val OP = 0) (hG : ∀ k, σ.val (PG k) = 0) (hR : ∀ k, σ.val (PR k) = 0) (horc : ∀ x ∈ orc, x < 2 ^ Wb)
    (hTW : 2 * 2 ^ V * 2 ^ W ≤ 2 ^ Wb) (hW : 1 ≤ Wb) (Lo : ℕ)
    (hLo : (natWord cnt ++ orc.flatMap (recOut V W)).length ≤ Lo) (hcap : 2 * Wb + 2 ≤ cap)
    (hcO : Lo + 2 * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) (hcapI : orc.length * (2 * Wb + 1) + 2 * Wb + 2 ≤ cap) :
    Runs cap (printPhase PB PG PR O OP I CN CI CW) σ (printCost Wb V orc.length Lo)
      (fun τ => τ.st O = natWord cnt ++ orc.flatMap (recOut V W) ∧ τ.sh O = 0 ∧ (∃ w, MV PB Wb w τ) ∧
        SameExcept σ τ (O :: bl PB O) []) := by
  have hO0 : σ.sh O = (σ.st O).length := by rw [hOh, hOe]; rfl
  refine Runs.seq (natW_spec (cap := cap) hp.pl.po hp.co σ Wb cnt hCN hcnt hW hR hO0 hcap (by
    have := natWord_length cnt; have := lenF_le cnt Wb hcnt hW; omega)) (fun σ1 h1 => ?_)
  obtain ⟨f1, hO1, hOh1, hOP1⟩ := h1
  have hb := prBodyJ (cap := cap) (Wb := Wb) hp V W σ w0 hc (natWord cnt) orc junk hO0 hG hR Lo
    (by simpa using hLo) horc hTW hW hcap (by rw [hOP]; omega)
  have hw1 : ∀ x ∈ orc.map (binary Wb), x.length = Wb := by
    intro x hx; obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx; simp
  have nIO : I ∉ [O] := by simp [hp.io]
  have hInv0 : PInv PB O OP I CI CW Wb V W σ w0 (natWord cnt) orc 0 σ1 :=
    ⟨w0, hw.frame' f1 (fun i => by simp [hp.pl.bo i]), fun _ _ => rfl, hok, by simpa using hO1,
      by simpa using hOh1, by simpa using hOP1, se_sub f1 (by simp [bl]) (by simp)⟩
  obtain ⟨τ, ⟨w, hwτ, _, _, hOτ, hOhτ, hOPτ, frτ⟩, hstτ, hcwτ, hloop⟩ :=
    recLoopJ_spec (cap := cap) (L := Wb) (hp.bi 0).symm hp.cicw hw1 hW (by simpa using hcapI) hb σ1 hInv0
      (by rw [f1.st nIO, hI]) (by rw [f1.sh nIO, hIh]) (by rw [f1.val (by simp [hp.oci.symm]), hCI])
      (by rw [f1.val (by simp [hp.ocw.symm]), hCW]) (hw.frame' f1 (fun i => by simp [hp.pl.bo i]) 0).2
      (by rw [(hw.frame' f1 (fun i => by simp [hp.pl.bo i]) 0).1]; simp [frame_length])
  rw [List.length_map, List.take_length] at hOτ hOhτ hOPτ
  rw [List.length_map] at hloop
  refine Runs.seq ⟨_, hloop, rfl⟩ (fun ρ hρ => ?_)
  subst hρ
  set ρ := (τ.setv CI 0).seth I 0 with hρd
  have fρ : SameExcept τ ρ [I] [CI] :=
    SameExcept.trans (sameExcept_setv _ (by simp) _) (sameExcept_seth _ (by simp) _)
  have nOI : O ∉ [I] := by simp [hp.io.symm]
  have hk : ρ.sh O = (natWord cnt ++ orc.flatMap (recOut V W)).length := by rw [fρ.sh nOI, hOhτ, hOh]; simp
  have hkv : ρ.val OP = (natWord cnt ++ orc.flatMap (recOut V W)).length := by
    rw [fρ.val (by simp [hp.oci]), hOPτ, hOP]; simp
  refine Runs.cost (c := (natWord cnt ++ orc.flatMap (recOut V W)).length * (3 + 2) + 1) ?_ ?_
  swap
  · have := Nat.mul_le_mul_right (3 + 2) hLo; omega
  refine (rewO_spec cap O OP ρ _ ρ (by omega) ⟨SameExcept.refl _ _ _, rfl, hk, hkv⟩).post (fun ρ' h' => ?_)
  obtain ⟨f', hst', hsh', hv'⟩ := h'
  refine ⟨?_, hsh', ⟨w, ?_⟩, ?_⟩
  · rw [hst', fρ.st nOI, hOτ, hOe]; simp
  · exact (hwτ.frame' fρ (fun i => by simp [hp.bi i])).frame' f' (fun i => by simp [hp.pl.bo i])
  · refine ⟨fun x hx => ?_, fun r _ => ?_, by rw [f'.cell, fρ.cell, frτ.cell]⟩
    · have hxO : x ∉ [O] := by simp at hx ⊢; exact hx.1
      by_cases e : x = I
      · subst e
        refine ⟨?_, ?_⟩
        · rw [f'.st hxO, hρd]; simp [hstτ, hI]
        · rw [f'.sh hxO, hρd]; simp [hIh]
      · have hxI : x ∉ [I] := by simp [e]
        have := frτ.1 x (by simp [bl] at hx ⊢; exact ⟨e, hx⟩)
        exact ⟨by rw [f'.st hxO, fρ.st hxI, this.1], by rw [f'.sh hxO, fρ.sh hxI, this.2]⟩
    · by_cases eOP : r = OP
      · subst eOP; rw [hv', hOP]
      · rw [f'.val (by simp [eOP])]
        by_cases eCI : r = CI
        · subst eCI; simp [hρd, hCI]
        · rw [fρ.val (by simp [eCI])]
          by_cases eCW : r = CW
          · subst eCW; rw [hcwτ, hCW]
          · exact frτ.val (by simp [eOP, eCI, eCW])

end Phase

end NearCubicGates.Close.Expand
