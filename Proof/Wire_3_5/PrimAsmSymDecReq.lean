import Proof.Wire_3_5.PrimAsmCellUnit
import Proof.Wire_3_5.PrimAsmDataSetup

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-! ## The decode registers -/

def dN : Fin LNR := ⟨320, by decide⟩
def dA : Fin LNR := ⟨321, by decide⟩
def dNC : Fin LNR := ⟨322, by decide⟩
def dF : Fin LNR := ⟨323, by decide⟩
def dC : Fin LNR := ⟨324, by decide⟩
def dP : Fin LNR := ⟨325, by decide⟩
def dT : Fin LNR := ⟨326, by decide⟩
def dK : Fin LNR := ⟨327, by decide⟩

variable (cap : ℕ) (x : ℕ)

/-! ## Skipping the codes -/

/-- Skip `K` framed natWord fields on the request stream. -/
def skipCodesW : WM (LNS x) LNR := .whr dK (.seq (.dec dK) (skipNatM true (sk x 0) dF dC))

theorem enc_take_succ (codes : List ℕ) (k : ℕ) (hk : k < codes.length) :
    enc true ((codes.take (k + 1)).flatMap RepairRepresentation.natWord) =
      enc true ((codes.take k).flatMap RepairRepresentation.natWord) ++
        enc true (RepairRepresentation.natWord (codes.get ⟨k, hk⟩)) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [ParseNat.enc, if_true, Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, RepairOrdinary.Streaming.marks_append, List.get_eq_getElem]

theorem enc_drop (codes : List ℕ) (k : ℕ) (hk : k < codes.length) :
    enc true ((codes.drop k).flatMap RepairRepresentation.natWord) =
      enc true (RepairRepresentation.natWord (codes.get ⟨k, hk⟩)) ++
        enc true ((codes.drop (k + 1)).flatMap RepairRepresentation.natWord) := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [ParseNat.enc, if_true, List.flatMap_cons, RepairOrdinary.Streaming.marks_append, List.get_eq_getElem]

/-- **Skipping `a` codes**: from the head at the codes' start, the head moves past all of them; `dK` ends at `0`. -/
theorem skipCodes_spec (codes : List ℕ) (pre rest : List Bool) (Kb : ℕ) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (σ : WState (LNS x) LNR)
    (hst : σ.st (sk x 0) = pre ++ enc true (codes.flatMap RepairRepresentation.natWord) ++ rest)
    (hsh : σ.sh (sk x 0) = pre.length) (hK : σ.val dK = codes.length) (hf : σ.val dF = 0) (hc : σ.val dC = 0)
    (hcap : Kb + 1 ≤ cap) (hcapK : codes.length ≤ cap) :
    WExec cap (skipCodesW x) σ
      ((σ.seth (sk x 0) (pre.length + (enc true (codes.flatMap RepairRepresentation.natWord)).length)).setv dK 0)
      (codes.length * (20 * Kb + 20 + 4) + 1) := by
  let S : ℕ → WState (LNS x) LNR := fun k =>
    (σ.seth (sk x 0) (pre.length + (enc true ((codes.take k).flatMap RepairRepresentation.natWord)).length)).setv dK
      (codes.length - k)
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext i
      by_cases hi : i = sk x 0
      · subst hi; simp [S, hsh, ParseNat.enc]
      · simp [S, Function.update_of_ne hi]
    · rfl
    · funext r
      by_cases hr : r = dK
      · subst hr; simp [S, hK]
      · simp [S, Function.update_of_ne hr]
    · rfl
  have hSn : S codes.length =
      (σ.seth (sk x 0) (pre.length + (enc true (codes.flatMap RepairRepresentation.natWord)).length)).setv dK 0 := by
    simp [S]
  have hloop := UnionMachine.Round.wloop cap dK (skipNatM true (sk x 0) dF dC) (20 * Kb + 20) codes.length S
    (fun k _ => by simp [S])
    hcapK
    (fun k hk => by
      have hdF : dF ≠ dK := by decide
      have hdC : dC ≠ dK := by decide
      have hx := skipNatM_spec cap true (sk x 0) dF dC (by decide) (codes.get ⟨k, hk⟩)
        (pre ++ enc true ((codes.take k).flatMap RepairRepresentation.natWord))
        (enc true ((codes.drop (k + 1)).flatMap RepairRepresentation.natWord) ++ rest)
        ((S k).setv dK (codes.length - k - 1))
        (by
          simp only [S, WState.setv_st, WState.seth_st]
          have e : enc true (codes.flatMap RepairRepresentation.natWord) =
              enc true ((codes.take k).flatMap RepairRepresentation.natWord) ++
                enc true ((codes.drop k).flatMap RepairRepresentation.natWord) := by
            conv_lhs => rw [← List.take_append_drop k codes]
            simp only [ParseNat.enc, if_true, List.flatMap_append, RepairOrdinary.Streaming.marks_append]
          rw [hst, e, enc_drop codes k hk]
          simp only [List.append_assoc])
        (by simp [S])
        (by simp [S, Function.update_of_ne hdF, hf])
        (by simp [S, Function.update_of_ne hdC, hc])
        (by have := hKb _ (List.get_mem codes ⟨k, hk⟩); omega)
      refine WExec.mono (WExec.cast cap hx ?_ le_rfl) (by
        have := hKb _ (List.get_mem codes ⟨k, hk⟩); omega)
      apply WState.eq
      · funext i
        by_cases hi : i = sk x 0
        · subst hi
          simp only [S, WState.setv_sh, WState.seth_sh, Function.update_self]
          rw [enc_take_succ codes k hk, List.length_append, List.length_append,
            ParseNat.enc_length true (RepairRepresentation.natWord _)]
          omega
        · simp [S, Function.update_of_ne hi]
      · rfl
      · funext r
        by_cases hr : r = dK
        · subst hr; simp [S]; omega
        · simp [S, Function.update_of_ne hr]
      · rfl)
  rw [hS0, hSn] at hloop
  exact hloop

/-! ## The request's numbers -/

/-- **The request parse**: `n` into `dN`, skip the mode bit, `a` into `dA`, skip the `a` codes, `|cc|` into `dNC`. -/
def reqParseW : WM (LNS x) LNR :=
  .seq (readNatM true (sk x 0) dF dC dN dP dT) (.seq (.fwd (sk x 0)) (.seq (.fwd (sk x 0))
    (.seq (readNatM true (sk x 0) dF dC dA dP dT) (.seq (FinalPass.Hash4.wcopyR dA dK dT)
      (.seq (skipCodesW x) (readNatM true (sk x 0) dF dC dNC dP dT))))))

/-- The parse's cost bound. -/
def reqParseCost (n a nc Kb : ℕ) : ℕ :=
  (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (1 + 1 + (1 + 1 +
    ((natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) + 1 + (18 * a + 3 + 1 +
      (a * (20 * Kb + 20 + 4) + 1 + 1 + (natBitLength nc + 2) * (40 * 2 ^ natBitLength nc + 40))))))

theorem reqParse_spec (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (σ : WState (LNS x) LNR)
    (hst : σ.st (sk x 0) = frame (Data.reqW n mb codes cc tl)) (hsh : σ.sh (sk x 0) = 0)
    (z0 : σ.val dN = 0) (z1 : σ.val dA = 0) (z2 : σ.val dNC = 0) (z3 : σ.val dF = 0) (z4 : σ.val dC = 0)
    (z5 : σ.val dP = 0) (z6 : σ.val dT = 0) (z7 : σ.val dK = 0)
    (hcap : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + n + codes.length + 1 ≤ cap) :
    ∃ τ c, WExec cap (reqParseW x) σ τ c ∧ τ.val dN = n ∧ τ.val dA = codes.length ∧ τ.val dNC = cc.length ∧
      τ.val dF = 0 ∧ τ.val dC = 0 ∧ τ.val dP = 0 ∧ τ.val dT = 0 ∧ τ.val dK = 0 ∧
      (∀ r, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dK → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      (∀ i, i ≠ sk x 0 → τ.sh i = σ.sh i) ∧ τ.cell = σ.cell ∧ c ≤ reqParseCost n codes.length cc.length Kb := by
  have he := Data.enc_reqW n mb codes cc tl
  rw [he] at hst
  have q1 := Nat.one_le_two_pow (n := natBitLength n)
  have q2 := Nat.one_le_two_pow (n := natBitLength codes.length)
  have q3 := Nat.one_le_two_pow (n := natBitLength cc.length)
  -- 1: n
  have e1 := readNatM_spec cap true (sk x 0) dF dC dN dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n []
    (enc true [mb] ++ (enc true (RepairRepresentation.natWord codes.length) ++
      (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false]))))))
    σ (by rw [hst]; rfl) (by simp [hsh]) z3 z4 z5 z6 (by rw [z0]; omega)
  obtain ⟨σ1, h1⟩ : ∃ y, y = (σ.seth (sk x 0) (([] : List Bool).length +
      stp true * (RepairRepresentation.natWord n).length)).setv dN (σ.val dN + n) := ⟨_, rfl⟩
  rw [← h1] at e1
  have k1 : ∀ r, r ≠ dN → σ1.val r = σ.val r := fun r hr => by rw [h1]; simp [Function.update_of_ne hr]
  have s1 : σ1.st = σ.st := by rw [h1]; rfl
  have p1 : σ1.sh (sk x 0) = (enc true (RepairRepresentation.natWord n)).length := by
    rw [h1]; simp [ParseNat.enc_length]
  have o1 : ∀ i, i ≠ sk x 0 → σ1.sh i = σ.sh i := fun i hi => by rw [h1]; simp [Function.update_of_ne hi]
  -- 2: the mode bit
  have e2 := WExec.fwd (cap := cap) (sk x 0) σ1
  have e3 := WExec.fwd (cap := cap) (sk x 0) (σ1.seth (sk x 0) (σ1.sh (sk x 0) + 1))
  obtain ⟨σ2, h2⟩ : ∃ y, y = (σ1.seth (sk x 0) (σ1.sh (sk x 0) + 1)).seth (sk x 0)
      ((σ1.seth (sk x 0) (σ1.sh (sk x 0) + 1)).sh (sk x 0) + 1) := ⟨_, rfl⟩
  rw [← h2] at e3
  have v2 : σ2.val = σ1.val := by rw [h2]; rfl
  have s2 : σ2.st = σ.st := by rw [h2, ← s1]; rfl
  have p2 : σ2.sh (sk x 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [mb]).length := by
    rw [h2]; simp [p1, ParseNat.enc_length, stp]
  have o2 : ∀ i, i ≠ sk x 0 → σ2.sh i = σ.sh i := fun i hi => by
    rw [h2]; simp [Function.update_of_ne hi]; exact o1 i hi
  -- 3: a
  have e4 := readNatM_spec cap true (sk x 0) dF dC dA dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) codes.length
    (enc true (RepairRepresentation.natWord n) ++ enc true [mb])
    (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
      (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false]))))
    σ2 (by rw [s2, hst]; simp only [List.append_assoc]) p2
    (by rw [v2, k1 _ (by decide), z3]) (by rw [v2, k1 _ (by decide), z4]) (by rw [v2, k1 _ (by decide), z5])
    (by rw [v2, k1 _ (by decide), z6]) (by rw [v2, k1 _ (by decide), z1]; omega)
  obtain ⟨σ3, h3⟩ : ∃ y, y = (σ2.seth (sk x 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [mb]).length +
      stp true * (RepairRepresentation.natWord codes.length).length)).setv dA (σ2.val dA + codes.length) := ⟨_, rfl⟩
  rw [← h3] at e4
  have k3 : ∀ r, r ≠ dA → σ3.val r = σ2.val r := fun r hr => by rw [h3]; simp [Function.update_of_ne hr]
  have vA : σ3.val dA = codes.length := by rw [h3]; simp [v2, k1 _ (show dA ≠ dN by decide), z1]
  have s3 : σ3.st = σ.st := by rw [h3, ← s2]; rfl
  have p3 : σ3.sh (sk x 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [mb] ++
      enc true (RepairRepresentation.natWord codes.length)).length := by
    rw [h3]; simp [ParseNat.enc_length]; omega
  have o3 : ∀ i, i ≠ sk x 0 → σ3.sh i = σ.sh i := fun i hi => by
    rw [h3]; simp [Function.update_of_ne hi]; exact o2 i hi
  -- 4: K := a
  have e5 := FinalPass.Hash4.wcopyR_spec cap dA dK dT (by decide) (by decide) (by decide) σ3
    (by rw [k3 _ (by decide), v2, k1 _ (by decide), z7]) (by rw [k3 _ (by decide), v2, k1 _ (by decide), z6])
    (by rw [vA]; omega)
  obtain ⟨σ4, h4⟩ : ∃ y, y = σ3.setv dK (σ3.val dA) := ⟨_, rfl⟩
  rw [← h4] at e5
  have k4 : ∀ r, r ≠ dK → σ4.val r = σ3.val r := fun r hr => by rw [h4]; simp [Function.update_of_ne hr]
  -- 5: skip the codes
  have e6 := skipCodes_spec cap x codes (enc true (RepairRepresentation.natWord n) ++ enc true [mb] ++
      enc true (RepairRepresentation.natWord codes.length))
    (enc true (RepairRepresentation.natWord cc.length) ++ (enc true (cc.flatMap RepairRepresentation.natWord) ++
      (enc true tl ++ [false]))) Kb hKb σ4
    (by rw [h4]; show σ3.st (sk x 0) = _; rw [s3, hst]; simp only [List.append_assoc])
    (by rw [h4]; exact p3) (by rw [h4]; simp [vA])
    (by rw [k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z3])
    (by rw [k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z4]) (by omega) (by omega)
  obtain ⟨σ5, h5⟩ : ∃ y, y = (σ4.seth (sk x 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [mb] ++
      enc true (RepairRepresentation.natWord codes.length)).length +
        (enc true (codes.flatMap RepairRepresentation.natWord)).length)).setv dK 0 := ⟨_, rfl⟩
  rw [← h5] at e6
  have k5 : ∀ r, r ≠ dK → σ5.val r = σ4.val r := fun r hr => by rw [h5]; simp [Function.update_of_ne hr]
  have s5 : σ5.st = σ.st := by rw [h5, h4, ← s3]; rfl
  have o5 : ∀ i, i ≠ sk x 0 → σ5.sh i = σ.sh i := fun i hi => by
    rw [h5, h4]; simp [Function.update_of_ne hi]; exact o3 i hi
  -- 6: |cc|
  have e7 := readNatM_spec cap true (sk x 0) dF dC dNC dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cc.length
    (enc true (RepairRepresentation.natWord n) ++ enc true [mb] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord))
    (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false]))
    σ5 (by rw [s5, hst]; simp only [List.append_assoc]) (by rw [h5]; simp; omega)
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z3])
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z4])
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z5])
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z6])
    (by rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), v2, k1 _ (by decide), z2]; omega)
  obtain ⟨σ6, h6⟩ : ∃ y, y = (σ5.seth (sk x 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [mb] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord)).length +
        stp true * (RepairRepresentation.natWord cc.length).length)).setv dNC (σ5.val dNC + cc.length) := ⟨_, rfl⟩
  rw [← h6] at e7
  have k6 : ∀ r, r ≠ dNC → σ6.val r = σ5.val r := fun r hr => by rw [h6]; simp [Function.update_of_ne hr]
  have kk : ∀ r, r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ dK → σ6.val r = σ.val r := fun r a1 a2 a3 a4 => by
    rw [k6 r a3, k5 r a4, k4 r a4, k3 r a2, v2, k1 r a1]
  refine ⟨σ6, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, kk, ?_, ?_, ?_, ?_⟩
  · rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), v2, h1]; simp [z0]
  · rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), vA]
  · rw [h6]; simp [k5 _ (show dNC ≠ dK by decide), k4 _ (show dNC ≠ dK by decide), k3 _ (show dNC ≠ dA by decide),
      v2, k1 _ (show dNC ≠ dN by decide), z2]
  · rw [kk _ (by decide) (by decide) (by decide) (by decide), z3]
  · rw [kk _ (by decide) (by decide) (by decide) (by decide), z4]
  · rw [kk _ (by decide) (by decide) (by decide) (by decide), z5]
  · rw [kk _ (by decide) (by decide) (by decide) (by decide), z6]
  · rw [k6 _ (by decide), h5]; simp
  · rw [h6, ← s5]; rfl
  · intro i hi; rw [h6]; simp [Function.update_of_ne hi]; exact o5 i hi
  · rw [h6, h5, h4, h3, h2, h1]; rfl
  · unfold reqParseCost
    rw [vA] at e5
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
