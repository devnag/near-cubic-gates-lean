import Proof.Gates.Expand.PolyTabStage9e

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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc)
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def vBody : WX := .seq (readBin U2 RB 1 2) (appendRecX (U2 1) (sS 5) (rX 29) (rX 34))
def varLoop : WX := .whr (rX 36) (.seq (WMX.dec (rX 36)) vBody)

/-- The variable records. -/
def vrecs (Wb : ℕ) (xs : List ℕ) : List Bool := xs.flatMap fun x => frame (binary Wb x)

theorem vrecs_succ (Wb : ℕ) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    vrecs Wb (xs.take (k + 1)) = vrecs Wb (xs.take k) ++ frame (binary Wb xs[k]) := by
  unfold vrecs
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem vrecs_length (Wb : ℕ) (xs : List ℕ) : (vrecs Wb xs).length = xs.length * (2 * Wb + 1) := by
  unfold vrecs
  rw [flatMap_len_const _ _ (2 * Wb + 1) (fun x _ => by rw [frame_length, binary_length])]

theorem vrecs_rec (Wb : ℕ) (xs : List ℕ) : vrecs Wb xs ++ [false] = recStream (xs.map (binary Wb)) := by
  unfold vrecs recStream; simp [List.flatMap_map]

def vCost (Wb ℓ : ℕ) : ℕ := readBinCost Wb ℓ + 1 + (40 * Wb + 11)

section Wrap
variable {Wb Wc : ℕ} {inp VT : List Bool} {σA : WState (NSx te qa) NRk} {hd : ℕ} {o46 o56 oV L5 : List Bool}
  {q2 q3 : (Fin 10 → ℕ) → Prop}

theorem ms_clrV (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (j : Fin 64)
    (hj : XR j) (x : ℕ) (hx : f j = x) (hcap : x ≤ cap) :
    Runs cap (.wm (WM.clear (rX j))) τ (3 * x + 1) (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j 0) q2 q3) :=
  (ms_clr cap h j hj (by rw [hx]; exact hcap)).cost (by rw [hx])

theorem ms_mulV (cap : ℕ) {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ)
    (a a2 b c : Fin 64) (hd5 : [a, a2, b, c, 7].Nodup) (ha : XR a) (ha2 : XR a2) (hb : XR b) (hc : XR c)
    (x y z : ℕ) (hx : f a = x) (hy : f b = y) (hz : f c = z)
    (h2 : f a2 = 0) (h7 : f 7 = 0) (hcap : z + x * y ≤ cap) (hcapA : 2 * x ≤ cap) :
    Runs cap (mulR (rX a) (rX a2) (rX b) (rX c) (rX 7)) τ (x * (18 * y + 3 + 8) + 7 * x + 3)
      (MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f c (z + x * y)) q2 q3) := by
  have := ms_mul cap h a a2 b c hd5 ha ha2 hb hc h2 h7 (by rw [hx, hy, hz]; exact hcap) (by rw [hx]; exact hcapA)
  rw [hx, hy, hz] at this; exact this

theorem MS.upd_self {f : Fin 64 → ℕ} {τ : WSt} (h : MS Wb Wc inp VT σA hd o46 o56 oV L5 f q2 q3 τ) (j : Fin 64)
    (v : ℕ) (hv : f j = v) : MS Wb Wc inp VT σA hd o46 o56 oV L5 (Function.update f j v) q2 q3 τ :=
  h.congr (fun i _ => by
    by_cases hi : i = j
    · subst hi; simp [hv]
    · simp [Function.update_apply, hi])

end Wrap

section Loops
variable {Wb Wc : ℕ} {inp VT : List Bool} {σA : WState (NSx te qa) NRk} {o46 o56 L5 : List Bool} {hd : ℕ}
  {q3 : (Fin 10 → ℕ) → Prop}

theorem varLoop_spec (cap : ℕ) (hW : 1 ≤ Wb) (xs : List ℕ) (A B : List Bool) (ℓ : ℕ) (hinp : inp = A ++ encN xs ++ B)
    (f : Fin 64 → ℕ) (q2 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp VT σA A.length o46 o56 [] L5 f q2 q3 τ) (h36 : f 36 = xs.length)
    (h29 : f 29 = 0) (hlt : ∀ x ∈ xs, x < 2 ^ Wb) (hℓ : ∀ x ∈ xs, natBitLength x ≤ ℓ) (hcap : ℓ + 1 ≤ cap)
    (hcapW : 2 * Wb + 1 ≤ cap) (hcapV : (xs.length + 1) * (2 * Wb + 1) + 2 ≤ cap) :
    Runs cap varLoop τ (xs.length * (vCost Wb ℓ + 4) + 1)
      (MS Wb Wc inp VT σA (A.length + (encN xs).length) o46 o56 (vrecs Wb xs) L5 (Function.update f 36 0)
        (fun _ => True) q3) := by
  set n := xs.length with hn
  let Inv : ℕ → WSt → Prop := fun k ρ => MS Wb Wc inp VT σA (A.length + (encN (xs.take k)).length) o46 o56
    (vrecs Wb (xs.take k)) L5 (Function.update f 36 (n - k)) (fun _ => True) q3 ρ
  have hn36 : n ≤ cap := by nlinarith
  obtain ⟨ρ, eρ, hρ, -⟩ := Runs.count (cap := cap) (K := rX 36) (body := vBody) (vCost Wb ℓ) n Inv hn36
    (fun k hk μ hμ _ => by
      have h1 := (hμ.setv 36 (by decide) (n - k - 1)).congr (g := Function.update f 36 (n - k - 1))
        (fun j _ => by by_cases hj : j = 36 <;> simp [Function.update_apply, hj])
      have hkx : xs[k] ∈ xs := List.getElem_mem hk
      have hinp' : inp = (A ++ encN (xs.take k)) ++ enc true (natWord xs[k]) ++ (encN (xs.drop (k + 1)) ++ B) := by
        rw [hinp, encN_split xs k hk]; simp [List.append_assoc]
      have hl := vrecs_length Wb (xs.take k)
      have hkl : (xs.take k).length = k := by simp; omega
      obtain ⟨τ1, e1, hτ1⟩ := ms_read2 cap hW _ _ q3 _ h1 xs[k] _ _ hinp' (by simp) (by have := hℓ _ hkx; omega) hcapW
      rw [Nat.mod_eq_of_lt (hlt _ hkx)] at hτ1
      obtain ⟨τ2, e2, hτ2⟩ := ms_appV cap _ q3 xs[k] τ1 hτ1 (by simp [h29]) (by rw [hl, hkl]; nlinarith)
      refine ⟨τ2, WXExec.mono (WXExec.seq e1 e2) ?_, ?_, ?_⟩
      · have := readBinCost_mono Wb (hℓ _ hkx); unfold vCost; omega
      · have e1 : (A ++ encN (List.take k xs)).length + 2 * (natWord xs[k]).length =
            A.length + (encN (xs.take (k + 1))).length := by
          rw [encN_take_succ xs k hk, List.length_append]; ring
        rw [e1, ← vrecs_succ Wb xs k hk] at hτ2
        exact hτ2.withQ2 (fun _ _ => trivial)
      · rw [hτ2.x 36 (by decide)]; simp)
    τ (by
      have e1 : A.length + (encN (xs.take 0)).length = A.length := by simp [encN]
      have e2 : vrecs Wb (xs.take 0) = [] := by simp [vrecs]
      show MS Wb Wc inp VT σA (A.length + (encN (xs.take 0)).length) o46 o56 (vrecs Wb (xs.take 0)) L5
        (Function.update f 36 (n - 0)) (fun _ => True) q3 τ
      rw [e1, e2]
      exact (h.withQ2 (fun _ _ => trivial)).congr (fun j _ => by
        by_cases hj : j = 36
        · subst hj; simp [h36]
        · simp [Function.update_apply, hj])) (by rw [h.x 36 (by decide), h36])
  refine ⟨ρ, eρ, ?_⟩
  have e : xs.take n = xs := List.take_of_length_le (le_of_eq hn.symm)
  simp only [Inv, e, Nat.sub_self] at hρ
  exact hρ

def revCost (Wb N X K Y : ℕ) : ℕ :=
  (N * (40 * Wb + 40) + 10 * N * (2 * Wb + 1) + 10) + 1 + ((X * (83 * Wb + 30) + 41 * Wb + 14) + 1 +
    ((X * (18 * K + 3 + 8) + 7 * X + 3) + 1 + ((3 * X + 1) + 1 +
    ((K * (copyStep Wb Y + 8) + 7 * K + 3) + 1 + (3 * (X * K + K) + 1)))))

theorem revCost_le (Wb N X K Y n x : ℕ) (hn : n < N) (hx : x ≤ X) :
    ((n + 1) * (40 * Wb + 40) + 10 * (n + 1) * (2 * Wb + 1) + 10) + 1 + ((x * (83 * Wb + 30) + 41 * Wb + 14) + 1 +
    ((x * (18 * K + 3 + 8) + 7 * x + 3) + 1 + ((3 * x + 1) + 1 +
    ((K * (copyStep Wb Y + 8) + 7 * K + 3) + 1 + (3 * (0 + x * K + K) + 1))))) ≤ revCost Wb N X K Y := by
  have a1 := Nat.mul_le_mul_right (40 * Wb + 40) (show n + 1 ≤ N by omega)
  have a2 := Nat.mul_le_mul_right (2 * Wb + 1) (Nat.mul_le_mul_left 10 (show n + 1 ≤ N by omega))
  have a3 := Nat.mul_le_mul_right (83 * Wb + 30) hx
  have a4 := Nat.mul_le_mul_right (18 * K + 3 + 8) hx
  have a5 := Nat.mul_le_mul_right K hx
  unfold revCost; omega

/-- The occurrence records copied after `k` steps of the reversed loop. -/
def revOut (Wb K : ℕ) (ys xs : List ℕ) (k : ℕ) : List Bool := (xs.reverse.take k).flatMap fun x => segRecs Wb ys (x * K) K

theorem revOut_length (Wb K : ℕ) (ys xs : List ℕ) (k : ℕ) (hys : ∀ x ∈ xs, x * K + K ≤ ys.length) (hk : k ≤ xs.length) :
    (revOut Wb K ys xs k).length = k * (K * (2 * Wb + 1)) := by
  unfold revOut
  rw [flatMap_len_const _ _ (K * (2 * Wb + 1)) (fun y hy => by
    rw [segRecs_length Wb ys _ K (hys y (List.mem_reverse.mp (List.mem_of_mem_take hy)))])]
  simp; omega

theorem revOut_succ (Wb K : ℕ) (ys xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    revOut Wb K ys xs (k + 1) = revOut Wb K ys xs k ++ segRecs Wb ys (xs[xs.length - k - 1]'(by omega) * K) K := by
  unfold revOut
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
  simp [List.getElem_reverse, show xs.length - 1 - k = xs.length - k - 1 by omega]

/-- The reversed loop's first half: fetch `x`, `rX 30 := x·K`. -/
def revA : WX :=
  .seq (getAt (sS 5) (sS 6) (rX 0) (rX 1) (rX 31) (rX 9)) <|
  .seq (toReg (sS 6) (U2 8) (U2 9) (rX 35) (rX 3) (rX 4) (rX 6)) <|
  .seq (mulR (rX 35) (rX 28) (rX 27) (rX 30) (rX 7)) (.wm (WM.clear (rX 35)))

def revB : WX :=
  .seq (copyN (sS 4) (sS 6) (sZ 46) (rX 0) (rX 1) (rX 30) (rX 9) (rX 29) (rX 37) (rX 27) (rX 28))
    (.wm (WM.clear (rX 30)))

def revBody : WX := .seq revA revB
def revLoop : WX := .whr (rX 31) (.seq (WMX.dec (rX 31)) revBody)

def revACost (Wb N X K : ℕ) : ℕ :=
  (N * (40 * Wb + 40) + 10 * N * (2 * Wb + 1) + 10) + 1 + ((X * (83 * Wb + 30) + 41 * Wb + 14) + 1 +
    ((X * (18 * K + 3 + 8) + 7 * X + 3) + 1 + (3 * X + 1)))

theorem revStepA (cap : ℕ) (hW : 1 ≤ Wb) (xs : List ℕ) (VT junk o46' : List Bool) (K X : ℕ) (g : Fin 64 → ℕ)
    (q2 : (Fin 10 → ℕ) → Prop) (i : ℕ) (hi : i < xs.length) (μ : WSt)
    (hμ : MS Wb Wc inp VT σA hd o46' o56 [] (recStream (xs.map (binary Wb)) ++ junk) g q2 q3 μ)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (h9 : g 9 = 0) (h31 : g 31 = i) (h28 : g 28 = 0)
    (h30 : g 30 = 0) (h35 : g 35 = 0) (h3 : g 3 = 0) (h4 : g 4 = 0) (h6 : g 6 = 0) (h7 : g 7 = 0) (h27 : g 27 = K)
    (hX : xs[i] ≤ X) (hlt : xs[i] < 2 ^ Wb)
    (hcap : (xs.length + 1) * (2 * Wb + 1) + 2 * xs.length + 2 * Wb + X * K + 2 * X + 2 ≤ cap) :
    Runs cap revA μ (revACost Wb xs.length X K)
      (MS Wb Wc inp VT σA hd o46' o56 [] (recStream (xs.map (binary Wb)) ++ junk) (Function.update g 30 (xs[i] * K))
        q2 q3) := by
  have hxc : xs[i] ≤ cap := by nlinarith
  obtain ⟨τ1, e1, m1, n1⟩ := ms_getAt cap hW xs junk i hi _ hμ h0 h1 h9 h31 (by nlinarith)
  obtain ⟨τ2, e2, m2⟩ := ms_toReg6 cap xs[i] 35 (by decide) (by decide) τ1 m1 n1 h3 h4 h6 hlt (by omega)
    (by rw [h35]; omega)
  obtain ⟨τ3, e3, m3⟩ := ms_mulV cap m2 35 28 27 30 (by decide) (by decide) (by decide) (by decide) (by decide)
    xs[i] K 0 (by simp [h35]) (by simp [h27]) (by simp [h30]) (by simp [h28]) (by simp [h7]) (by nlinarith) (by omega)
  obtain ⟨τ4, e4, m4⟩ := ms_clrV cap m3 35 (by decide) xs[i] (by simp [h35]) hxc
  refine ⟨τ4, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) ?_, m4.congr fun j _ => ?_⟩
  · have a1 := Nat.mul_le_mul_right (40 * Wb + 40) (show i + 1 ≤ xs.length by omega)
    have a2 := Nat.mul_le_mul_right (2 * Wb + 1) (Nat.mul_le_mul_left 10 (show i + 1 ≤ xs.length by omega))
    have a3 := Nat.mul_le_mul_right (83 * Wb + 30) hX
    have a4 := Nat.mul_le_mul_right (18 * K + 3 + 8) hX
    unfold revACost; omega
  · by_cases j35 : j = 35
    · subst j35; simp [h35]
    · by_cases j30 : j = 30
      · subst j30; simp
      · simp only [Function.update_of_ne j35, Function.update_of_ne j30]

theorem revStepB (cap : ℕ) (hW : 1 ≤ Wb) (ys : List ℕ) (L5' o46' : List Bool) (K c0 : ℕ) (g : Fin 64 → ℕ)
    (q2 : (Fin 10 → ℕ) → Prop) (μ : WSt) (hK : c0 + K ≤ ys.length)
    (hμ : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd o46' o56 [] L5' g q2 q3 μ)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (h9 : g 9 = 0) (h29 : g 29 = 0) (h28 : g 28 = 0) (h30 : g 30 = c0) (h27 : g 27 = K)
    (hcap : (ys.length + 1) * (2 * Wb + 1) + 2 * ys.length + 2 * K + 2 ≤ cap)
    (hcapO : o46'.length + K * (2 * Wb + 1) + 1 ≤ cap) :
    Runs cap revB μ (K * (copyStep Wb ys.length + 8) + 7 * K + 3 + 1 + (3 * (c0 + K) + 1))
      (MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd (o46' ++ segRecs Wb ys c0 K) o56 [] L5'
        (Function.update g 30 0) q2 q3) := by
  obtain ⟨τ5, e5, m5⟩ := ms_copyN cap hW ys c0 K hK μ hμ h0 h1 h9 h29 h28 h30 h27 (by nlinarith) hcapO
  obtain ⟨τ6, e6, m6⟩ := ms_clrV cap m5 30 (by decide) (c0 + K) (by simp) (by nlinarith)
  exact ⟨τ6, WXExec.seq e5 e6, m6.congr fun j _ => by
    by_cases j30 : j = 30
    · subst j30; simp
    · simp only [Function.update_of_ne j30]⟩

/-- One step of the reversed loop. -/
theorem revStep (cap : ℕ) (hW : 1 ≤ Wb) (xs ys : List ℕ) (junk : List Bool) (K X : ℕ) (f : Fin 64 → ℕ)
    (q2 : (Fin 10 → ℕ) → Prop) (k : ℕ) (hk : k < xs.length) (μ : WSt)
    (hμ : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd (o46 ++ revOut Wb K ys xs k) o56 []
      (recStream (xs.map (binary Wb)) ++ junk) (Function.update f 31 (xs.length - k - 1)) q2 q3 μ)
    (h0 : f 0 = 0) (h1 : f 1 = 0) (h9 : f 9 = 0) (h29 : f 29 = 0) (h28 : f 28 = 0)
    (h30 : f 30 = 0) (h35 : f 35 = 0) (h3 : f 3 = 0) (h4 : f 4 = 0) (h6 : f 6 = 0) (h7 : f 7 = 0) (h27 : f 27 = K)
    (hys : ∀ x ∈ xs, x * K + K ≤ ys.length) (hX : ∀ x ∈ xs, x ≤ X) (hlt : ∀ x ∈ xs, x < 2 ^ Wb)
    (hcap : (xs.length + 1) * (2 * Wb + 1) + 2 * xs.length + (ys.length + 1) * (2 * Wb + 1) + 2 * ys.length +
      2 * Wb + X * K + 2 * X + 2 * K + 2 ≤ cap)
    (hcapO : o46.length + xs.length * (K * (2 * Wb + 1)) + 1 ≤ cap) :
    Runs cap revBody μ (revCost Wb xs.length X K ys.length)
      (MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd (o46 ++ revOut Wb K ys xs (k + 1)) o56 []
        (recStream (xs.map (binary Wb)) ++ junk) (Function.update f 31 (xs.length - k - 1)) q2 q3) := by
  have hi : xs.length - k - 1 < xs.length := by omega
  have hxm : xs[xs.length - k - 1] ∈ xs := List.getElem_mem hi
  have hxK := hys _ hxm
  have hxX := hX _ hxm
  have hlen := revOut_length Wb K ys xs k hys hk.le
  have hkK : (k + 1) * (K * (2 * Wb + 1)) ≤ xs.length * (K * (2 * Wb + 1)) := Nat.mul_le_mul_right _ (by omega)
  have hA := revStepA cap hW xs _ junk _ K X _ q2 _ hi μ hμ (by simp [h0]) (by simp [h1]) (by simp [h9]) (by simp)
    (by simp [h28]) (by simp [h30]) (by simp [h35]) (by simp [h3]) (by simp [h4]) (by simp [h6]) (by simp [h7])
    (by simp [h27]) hxX (hlt _ hxm) (by nlinarith)
  obtain ⟨τ1, e1, m1⟩ := hA
  obtain ⟨τ2, e2, m2⟩ := revStepB cap hW ys _ _ K (xs[xs.length - k - 1] * K) _ q2 τ1 (by omega) m1 (by simp [h0])
    (by simp [h1]) (by simp [h9]) (by simp [h29]) (by simp [h28]) (by simp) (by simp [h27]) (by nlinarith)
    (by simp only [List.length_append, hlen]; nlinarith)
  refine ⟨τ2, WXExec.mono (WXExec.seq e1 e2) ?_, ?_⟩
  · have a5 := Nat.mul_le_mul_right K hxX
    unfold revCost revACost; omega
  · rw [revOut_succ Wb K ys xs k hk, ← List.append_assoc]
    refine m2.congr fun j _ => ?_
    by_cases j30 : j = 30
    · subst j30; simp [h30]
    · simp only [Function.update_of_ne j30]

theorem revLoop_spec (cap : ℕ) (hW : 1 ≤ Wb) (xs ys : List ℕ) (junk : List Bool) (K X : ℕ) (f : Fin 64 → ℕ)
    (q2 : (Fin 10 → ℕ) → Prop) (τ : WSt)
    (h : MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd o46 o56 [] (recStream (xs.map (binary Wb)) ++ junk) f q2
      q3 τ)
    (h31 : f 31 = xs.length) (h0 : f 0 = 0) (h1 : f 1 = 0) (h9 : f 9 = 0) (h29 : f 29 = 0) (h28 : f 28 = 0)
    (h30 : f 30 = 0) (h35 : f 35 = 0) (h3 : f 3 = 0) (h4 : f 4 = 0) (h6 : f 6 = 0) (h7 : f 7 = 0) (h27 : f 27 = K)
    (hys : ∀ x ∈ xs, x * K + K ≤ ys.length) (hX : ∀ x ∈ xs, x ≤ X) (hlt : ∀ x ∈ xs, x < 2 ^ Wb)
    (hcap : (xs.length + 1) * (2 * Wb + 1) + 2 * xs.length + (ys.length + 1) * (2 * Wb + 1) + 2 * ys.length +
      2 * Wb + X * K + 2 * X + 2 * K + 2 ≤ cap)
    (hcapO : o46.length + xs.length * (K * (2 * Wb + 1)) + 1 ≤ cap) :
    Runs cap revLoop τ (xs.length * (revCost Wb xs.length X K ys.length + 4) + 1)
      (MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd (o46 ++ revOut Wb K ys xs xs.length) o56 []
        (recStream (xs.map (binary Wb)) ++ junk) (Function.update f 31 0) q2 q3) := by
  set n := xs.length with hn
  let Inv : ℕ → WSt → Prop := fun k ρ => MS Wb Wc inp (recStream (ys.map (binary Wb))) σA hd
    (o46 ++ revOut Wb K ys xs k) o56 [] (recStream (xs.map (binary Wb)) ++ junk) (Function.update f 31 (n - k)) q2 q3 ρ
  have hncap : n ≤ cap := by nlinarith
  obtain ⟨ρ, eρ, hρ, -⟩ := Runs.count (cap := cap) (K := rX 31) (body := revBody) (revCost Wb n X K ys.length) n Inv
    hncap (fun k hk μ hμ _ => by
      have m0 := (hμ.setv 31 (by decide) (n - k - 1)).congr (g := Function.update f 31 (n - k - 1)) (fun j _ => by
        by_cases hj : j = 31
        · subst hj; simp
        · simp [Function.update_apply, hj])
      refine (revStep cap hW xs ys junk K X f q2 k hk _ m0 h0 h1 h9 h29 h28 h30 h35 h3 h4 h6 h7 h27 hys hX hlt hcap
        hcapO).post fun τ' m' => ⟨?_, ?_⟩
      · exact m'.congr fun j _ => by
          by_cases hj : j = 31
          · subst hj; simp; omega
          · simp [Function.update_apply, hj]
      · rw [m'.x 31 (by decide)]; simp; omega)
    τ (by
      simp only [Inv, Nat.sub_zero]
      have e : revOut Wb K ys xs 0 = [] := by simp [revOut]
      rw [e, List.append_nil]
      exact h.upd_self 31 n h31) (by rw [h.x 31 (by decide), h31])
  exact ⟨ρ, eρ, by simpa [Inv] using hρ⟩

end Loops

end NearCubicGates.Close.Expand.PolyTab
