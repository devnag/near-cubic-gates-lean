import Proof.Gates.Expand.PolyTabStage9g

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc enc_length stp)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- A monomial's fields. -/
def fl (t : List ℕ × ℕ × ℕ) : List ℕ := t.1.length :: (t.1 ++ [t.2.1, t.2.2])

/-- A monomial's occurrence records (`sZ 46`). -/
def blk46 (Wb K : ℕ) (ys : List ℕ) (t : List ℕ × ℕ × ℕ) : List Bool :=
  frame (binary Wb t.1.length) ++ revOut Wb K ys t.1 t.1.length

/-- A monomial's coefficient record (`sZ 56`). -/
def blk56 (Wc : ℕ) (t : List ℕ × ℕ × ℕ) : List Bool := frame (binary Wc (2 * t.2.2 + t.2.1))

def monoLoop : WX := .whr (rX 32) (.seq (WMX.dec (rX 32)) monoBody)

def st9 : WX :=
  .seq (readBin U2 RB 1 2) <| .seq (toReg (U2 1) (U2 8) (U2 9) (rX 32) (rX 3) (rX 4) (rX 6)) <|
  .seq monoLoop (.seq (closeOutX (sZ 46) (rX 37)) (closeOutX (sZ 56) (rX 38)))

theorem encN_fl (t : List ℕ × ℕ × ℕ) :
    encN (fl t) = enc true (natWord t.1.length) ++ encN t.1 ++ enc true (natWord t.2.1) ++ enc true (natWord t.2.2) := by
  simp [fl, encN_cons, encN_append, List.append_assoc, encN]

theorem FZ.upd {f : Fin 64 → ℕ} {K : ℕ} (h : FZ f K) (j : Fin 64) (hj : j.val ∉ [0, 1, 9, 29, 28, 30, 35, 3, 4, 6, 7, 31,
    36, 5, 27]) (v : ℕ) : FZ (Function.update f j v) K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  have n : ∀ i : Fin 64, j.val ≠ i.val → i ≠ j := fun i h e => h (by rw [e])
  exact ⟨by rw [Function.update_of_ne (n 0 hj.1)]; exact h.z0, by rw [Function.update_of_ne (n 1 hj.2.1)]; exact h.z1,
    by rw [Function.update_of_ne (n 9 hj.2.2.1)]; exact h.z9, by rw [Function.update_of_ne (n 29 hj.2.2.2.1)]; exact h.z29,
    by rw [Function.update_of_ne (n 28 hj.2.2.2.2.1)]; exact h.z28,
    by rw [Function.update_of_ne (n 30 hj.2.2.2.2.2.1)]; exact h.z30,
    by rw [Function.update_of_ne (n 35 hj.2.2.2.2.2.2.1)]; exact h.z35,
    by rw [Function.update_of_ne (n 3 hj.2.2.2.2.2.2.2.1)]; exact h.z3,
    by rw [Function.update_of_ne (n 4 hj.2.2.2.2.2.2.2.2.1)]; exact h.z4,
    by rw [Function.update_of_ne (n 6 hj.2.2.2.2.2.2.2.2.2.1)]; exact h.z6,
    by rw [Function.update_of_ne (n 7 hj.2.2.2.2.2.2.2.2.2.2.1)]; exact h.z7,
    by rw [Function.update_of_ne (n 31 hj.2.2.2.2.2.2.2.2.2.2.2.1)]; exact h.z31,
    by rw [Function.update_of_ne (n 36 hj.2.2.2.2.2.2.2.2.2.2.2.2.1)]; exact h.z36,
    by rw [Function.update_of_ne (n 5 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.1)]; exact h.z5,
    by rw [Function.update_of_ne (n 27 hj.2.2.2.2.2.2.2.2.2.2.2.2.2.2)]; exact h.k27⟩

/-- The bounds every monomial must meet. -/
structure MonoOKs (Wb Wc ℓ M X K : ℕ) (ys : List ℕ) (t : List ℕ × ℕ × ℕ) : Prop where
  hM : t.1.length ≤ M
  hmW : t.1.length < 2 ^ Wb
  hlt : ∀ x ∈ t.1, x < 2 ^ Wb
  hX : ∀ x ∈ t.1, x ≤ X
  hys : ∀ x ∈ t.1, x * K + K ≤ ys.length
  hsg : t.2.1 ≤ 1
  hmag : 2 * t.2.2 + 1 < 2 ^ Wc
  ℓm : natBitLength t.1.length ≤ ℓ
  ℓx : ∀ x ∈ t.1, natBitLength x ≤ ℓ
  ℓs : natBitLength t.2.1 ≤ ℓ
  ℓg : natBitLength t.2.2 ≤ ℓ

/-- The cap requirements of one monomial. -/
def capMono (Wb Wc ℓ M X K Y : ℕ) : ℕ :=
  ℓ + 2 * Wb + 2 * Wc + 2 * M + 4 + (M + 1) * (2 * Wb + 1) + 2 * M + (Y + 1) * (2 * Wb + 1) + 2 * Y + 2 * Wb +
    X * K + 2 * X + 2 * K + 2

section Loop
variable {Wb Wc : ℕ} {inp : List Bool} {σA : WState (NSx te qa) NRk}

theorem monoBody_spec (cap : ℕ) (hW : 1 ≤ Wb) (hWc : 1 ≤ Wc) (ys : List ℕ) (ℓ M X K : ℕ) (t : List ℕ × ℕ × ℕ)
    (ht : MonoOKs Wb Wc ℓ M X K ys t) (pre post : List Bool) (hinp : inp = pre ++ encN (fl t) ++ post)
    (o46 o56 L5 : List Bool) (f : Fin 64 → ℕ) (hf : FZ f K) (q2 q3 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA pre.length o46 o56 [] L5 f q2 q3 τ)
    (hcap : capMono Wb Wc ℓ M X K ys.length ≤ cap) (hcap46 : o46.length + 2 * Wb + 2 + M * (K * (2 * Wb + 1)) + 1 ≤ cap)
    (hcap56 : o56.length + 2 * Wc + 2 ≤ cap) :
    Runs cap monoBody τ (mnCost Wb Wc ℓ M X K ys.length)
      (MS Wb Wc inp (recStream (ys.map (binary Wb))) σA (pre.length + (encN (fl t)).length) (o46 ++ blk46 Wb K ys t)
        (o56 ++ blk56 Wc t) [] (overlay (vrecs Wb t.1 ++ [false]) L5) f (fun _ => True) (fun _ => True)) := by
  obtain ⟨xs, sg, mag⟩ := t
  have hA : inp = pre ++ enc true (natWord xs.length) ++ encN xs ++ (enc true (natWord sg) ++ enc true (natWord mag) ++
      post) := by rw [hinp, encN_fl]; simp [List.append_assoc]
  unfold capMono at hcap
  obtain ⟨τ1, e1, m1⟩ := monoA_spec cap hW xs pre _ ℓ M K hA f hf q2 q3 τ h ht.hM ht.hmW ht.hlt ht.ℓm ht.ℓx
    (by omega) (by omega) (by omega)
  have hl46 : (o46 ++ frame (binary Wb xs.length)).length = o46.length + (2 * Wb + 1) := by
    simp [frame_length, binary_length]
  obtain ⟨τ2, e2, m2⟩ := monoB_spec cap hW _ xs ys K X M f hf _ q3 τ1 m1 ht.hM ht.hys ht.hX ht.hlt (by omega)
    (by rw [hl46]; omega)
  have eA : (pre ++ enc true (natWord xs.length) ++ encN xs).length =
      pre.length + 2 * (natWord xs.length).length + (encN xs).length := by
    simp only [List.length_append, encT_length]
  rw [← eA] at m2
  obtain ⟨τ3, e3, m3⟩ := monoC_spec cap hW hWc _ post sg mag ℓ ht.hsg ht.hmag (by rw [hinp, encN_fl]; simp [List.append_assoc])
    f hf.z5 hf.z3 hf.z4 hf.z6 hf.z29 _ q3 τ2 [] m2 ht.ℓs ht.ℓg (by omega) hcap56
  refine ⟨τ3, WXExec.seq e1 (WXExec.seq e2 e3), ?_⟩
  have eH : (pre ++ enc true (natWord xs.length) ++ encN xs).length + 2 * (natWord sg).length +
      2 * (natWord mag).length = pre.length + (encN (fl (xs, sg, mag))).length := by
    rw [encN_fl]; simp only [List.length_append, encT_length]; ring
  rw [eH] at m3
  simpa [blk46, blk56, List.append_assoc] using m3

theorem monoLoop_spec (cap : ℕ) (hW : 1 ≤ Wb) (hWc : 1 ≤ Wc) (ys : List ℕ) (ℓ M X K : ℕ) (ts : List (List ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, MonoOKs Wb Wc ℓ M X K ys t) (pre post : List Bool)
    (hinp : inp = pre ++ encN (ts.flatMap fl) ++ post) (f : Fin 64 → ℕ) (hf : FZ f K) (q2 q3 : (Fin 10 → ℕ) → Prop)
    (L5 : List Bool) (τ : WSt)
    (h : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA pre.length [] [] [] L5 f q2 q3 τ) (h32 : f 32 = ts.length)
    (hcap : capMono Wb Wc ℓ M X K ys.length ≤ cap)
    (hcap46 : (ts.flatMap (blk46 Wb K ys)).length + 2 * Wb + 2 + M * (K * (2 * Wb + 1)) + 1 ≤ cap)
    (hcap56 : (ts.flatMap (blk56 Wc)).length + 2 * Wc + 2 ≤ cap) (hcapN : ts.length ≤ cap) :
    Runs cap monoLoop τ (ts.length * (mnCost Wb Wc ℓ M X K ys.length + 4) + 1) (fun ρ => ∃ L5' : List Bool,
      MS Wb Wc inp (recStream (ys.map (binary Wb))) σA (pre.length + (encN (ts.flatMap fl)).length)
        (ts.flatMap (blk46 Wb K ys)) (ts.flatMap (blk56 Wc)) [] L5' (Function.update f 32 0) (fun _ => True)
        (fun _ => True) ρ) := by
  set n := ts.length with hn
  let Inv : ℕ → WSt → Prop := fun k ρ => ∃ L5' : List Bool,
    MS Wb Wc inp (recStream (ys.map (binary Wb))) σA (pre.length + (encN ((ts.take k).flatMap fl)).length)
      ((ts.take k).flatMap (blk46 Wb K ys)) ((ts.take k).flatMap (blk56 Wc)) [] L5' (Function.update f 32 (n - k))
      (fun _ => True) (fun _ => True) ρ
  obtain ⟨ρ, eρ, hρ, -⟩ := Runs.count (cap := cap) (K := rX 32) (body := monoBody) (mnCost Wb Wc ℓ M X K ys.length) n
    Inv hcapN (fun k hk μ ⟨L5', hμ⟩ _ => by
      have m0 := (hμ.setv 32 (by decide) (n - k - 1)).congr (g := Function.update f 32 (n - k - 1)) (fun j _ => by
        by_cases hj : j = 32
        · subst hj; simp
        · simp [Function.update_apply, hj])
      have htk : ts[k] ∈ ts := List.getElem_mem hk
      have ek : ts.take (k + 1) = ts.take k ++ [ts[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      have hinp' : inp = (pre ++ encN ((ts.take k).flatMap fl)) ++ encN (fl ts[k]) ++
          (encN ((ts.drop (k + 1)).flatMap fl) ++ post) := by
        rw [hinp]
        conv_lhs => rw [← List.take_append_drop (k + 1) ts]
        rw [ek, List.flatMap_append, List.flatMap_append, encN_append, encN_append]
        simp [List.append_assoc]
      have hp46 : ((ts.take k).flatMap (blk46 Wb K ys)).length ≤ (ts.flatMap (blk46 Wb K ys)).length := by
        have := congrArg List.length (congrArg (List.flatMap (blk46 Wb K ys)) (List.take_append_drop k ts))
        rw [List.flatMap_append, List.length_append] at this; omega
      have hp56 : ((ts.take k).flatMap (blk56 Wc)).length ≤ (ts.flatMap (blk56 Wc)).length := by
        have := congrArg List.length (congrArg (List.flatMap (blk56 Wc)) (List.take_append_drop k ts))
        rw [List.flatMap_append, List.length_append] at this; omega
      obtain ⟨τ', e', m'⟩ := monoBody_spec cap hW hWc ys ℓ M X K ts[k] (hts _ htk) _ _ hinp' _ _ L5' _
        (hf.upd 32 (by decide) _) _ _ _ (by rw [List.length_append]; exact m0) hcap (by omega) (by omega)
      refine ⟨τ', e', ?_, ?_⟩
      · simp only [Inv]
        refine ⟨overlay (vrecs Wb ts[k].1 ++ [false]) L5', ?_⟩
        rw [ek, List.flatMap_append, List.flatMap_append, List.flatMap_append, encN_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append] at m' ⊢
        rw [← Nat.add_assoc]
        exact m'.congr fun j _ => by
          by_cases hj : j = 32
          · subst hj; simp; omega
          · simp [Function.update_apply, hj]
      · rw [m'.x 32 (by decide)]; simp)
    τ (by
      simp only [Inv, Nat.sub_zero, List.take_zero, List.flatMap_nil]
      have e : (encN ([] : List ℕ)).length = 0 := by simp [encN]
      rw [e, Nat.add_zero]
      exact ⟨L5, ((h.upd_self 32 n h32).withQ2 (fun _ _ => trivial)).withQ3 (fun _ _ => trivial)⟩) (by rw [h.x 32 (by decide), h32])
  refine ⟨ρ, eρ, ?_⟩
  have e : ts.take n = ts := List.take_of_length_le (le_of_eq hn.symm)
  obtain ⟨L5', hL⟩ := hρ
  simp only [e, Nat.sub_self] at hL
  exact ⟨L5', hL⟩

end Loop

end NearCubicGates.Close.Expand.PolyTab
