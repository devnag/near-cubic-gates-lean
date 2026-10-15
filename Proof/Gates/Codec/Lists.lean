import Proof.Gates.Codec.Basic

set_option autoImplicit false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

/-- Run `body` while `k ≠ 0`, decrementing `k` first. -/
def listLoop (k : Fin nr) (body : WM ns nr) : WM ns nr := .whr k (.seq (.dec k) body)

/-- **The list loop.** If `body` moves past one encoded element `g x` for every member `x` of `xs` (and preserves `ok`,
which may constrain other registers), the loop moves past `xs.flatMap g` and clears `k`. -/
theorem listLoop_spec {α : Type*} (i : Fin (ns + 1)) (k : Fin nr) (body : WM ns nr) (g : α → List Bool)
    (cost : α → ℕ) (ok : WState ns nr → Prop)
    (hok_h : ∀ σ x, ok σ → ok (σ.seth i x)) (hok_v : ∀ σ x, ok σ → ok (σ.setv k x)) (xs : List α)
    (hbody : ∀ x ∈ xs, ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st i = pre ++ g x ++ rest →
      σ.sh i = pre.length → WExec cap body σ (σ.seth i (pre.length + (g x).length)) (cost x)) :
    ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st i = pre ++ xs.flatMap g ++ rest →
      σ.sh i = pre.length → σ.val k = xs.length → xs.length ≤ cap →
      WExec cap (listLoop k body) σ ((σ.setv k 0).seth i (pre.length + (xs.flatMap g).length))
        ((xs.map fun x => cost x + 4).sum + 1) := by
  induction xs with
  | nil =>
    intro pre rest σ _ _ hsh hk _
    have e : (σ.setv k 0).seth i (pre.length + (([] : List α).flatMap g).length) = σ := by
      refine WState.eq ?_ rfl ?_ rfl
      · funext j; by_cases hj : j = i
        · subst hj; simp [hsh]
        · simp [Function.update_of_ne hj]
      · funext r; by_cases hr : r = k
        · subst hr; simp [hk]
        · simp [Function.update_of_ne hr]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hk)) (by simp)
  | cons x xs ih =>
    intro pre rest σ hσ hst hsh hk hcap
    have h1 := WExec.dec (cap := cap) k σ (by rw [hk]; simpa using hcap)
    set σ1 := σ.setv k (σ.val k - 1) with hσ1
    have hok1 : ok σ1 := hok_v σ _ hσ
    have hst1 : σ1.st i = pre ++ g x ++ (xs.flatMap g ++ rest) := by
      simp only [hσ1, WState.setv_st]; rw [hst]; simp [List.flatMap_cons, List.append_assoc]
    have h2 := hbody x (by simp) pre (xs.flatMap g ++ rest) σ1 hok1 hst1 (by simp [hσ1, hsh])
    set σ2 := σ1.seth i (pre.length + (g x).length) with hσ2
    have hok2 : ok σ2 := hok_h σ1 _ hok1
    have hst2 : σ2.st i = (pre ++ g x) ++ xs.flatMap g ++ rest := by
      simp only [hσ2, hσ1, WState.seth_st, WState.setv_st]; rw [hst]; simp [List.flatMap_cons, List.append_assoc]
    have h3 := ih (fun y hy => hbody y (by simp [hy])) (pre ++ g x) rest σ2 hok2 hst2
      (by simp [hσ2]) (by simp [hσ2, hσ1, hk]) (by simp at hcap; omega)
    have hne : σ.val k ≠ 0 := by rw [hk]; simp
    refine WExec.cast cap (WExec.whrT hne (WExec.seq h1 h2) h3) ?_ (by simp; omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext j; by_cases hj : j = i
      · subst hj; simp [hσ2, List.flatMap_cons, Nat.add_assoc]
      · simp [hσ2, hσ1, Function.update_of_ne hj]
    · funext r; by_cases hr : r = k
      · subst hr; simp [hσ2, hσ1]
      · simp [hσ2, hσ1, Function.update_of_ne hr]

theorem enc_flatMap {α : Type*} (ε : Bool) (g : α → List Bool) (xs : List α) :
    enc ε (xs.flatMap g) = xs.flatMap fun x => enc ε (g x) := by
  induction xs with
  | nil => cases ε <;> simp [WireExponent3_5.PrimAsm.ParseNat.enc, NearCubicWires.RepairOrdinary.Streaming.marks]
  | cons x xs ih => simp [List.flatMap_cons, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, ih]

/-- Move past `listWord g xs` (encoding `ε`): read the count into `k`, then loop `body`. -/
def skipList (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) (body : WM ns nr) : WM ns nr :=
  .seq (readNatM ε i f c k p t) (listLoop k body)

/-- The cost of `skipList` on a list of length `m` with element costs `cs`. -/
def skipListCost (m : ℕ) (cs : List ℕ) : ℕ :=
  (natBitLength m + 2) * (40 * 2 ^ natBitLength m + 40) + 1 + ((cs.map fun c => c + 4).sum + 1)

theorem skipList_spec {α : Type} (ε : Bool) (i : Fin (ns + 1)) (f c k p t : Fin nr) (body : WM ns nr)
    (hd : [f, c, k, p, t].Nodup) (g : α → List Bool) (cost : α → ℕ) (ok : WState ns nr → Prop)
    (hok_h : ∀ σ x, ok σ → ok (σ.seth i x)) (hok_v : ∀ σ x, ok σ → ok (σ.setv k x))
    (xs : List α)
    (hbody : ∀ x ∈ xs, ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st i = pre ++ enc ε (g x) ++ rest →
      σ.sh i = pre.length → WExec cap body σ (σ.seth i (pre.length + stp ε * (g x).length)) (cost x))
    (pre rest : List Bool) (σ : WState ns nr) (hok : ok σ)
    (hst : σ.st i = pre ++ enc ε (listWord g xs) ++ rest) (hsh : σ.sh i = pre.length)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hk : σ.val k = 0) (hp : σ.val p = 0) (ht : σ.val t = 0)
    (hcap : 2 ^ (natBitLength xs.length + 1) ≤ cap) (hlen : xs.length ≤ cap) :
    WExec cap (skipList ε i f c k p t body) σ (σ.seth i (pre.length + stp ε * (listWord g xs).length))
      (skipListCost xs.length (xs.map cost)) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at hd
  obtain ⟨⟨hfc, hfk, hfp, hft⟩, ⟨hck, hcp, hct⟩, ⟨hkp, hkt⟩, hpt⟩ := hd
  have hsplit : enc ε (listWord g xs) = enc ε (natWord xs.length) ++ xs.flatMap fun x => enc ε (g x) := by
    unfold listWord; rw [NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append, enc_flatMap]
  have h1 := readNatM_spec cap ε i f c k p t hfc hfk hfp hft hck hcp hct (Ne.symm hkp) hpt hkt xs.length
    pre ((xs.flatMap fun x => enc ε (g x)) ++ rest) σ (by rw [hst, hsplit]; simp [List.append_assoc]) hsh hf hc hp ht
    (by rw [hk]; simpa using hcap)
  set σ1 := (σ.seth i (pre.length + stp ε * (natWord xs.length).length)).setv k (σ.val k + xs.length) with hσ1
  have hok1 : ok σ1 := hok_v _ _ (hok_h _ _ hok)
  have hst1 : σ1.st i = (pre ++ enc ε (natWord xs.length)) ++ (xs.flatMap fun x => enc ε (g x)) ++ rest := by
    simp only [hσ1, WState.setv_st, WState.seth_st]; rw [hst, hsplit]; simp [List.append_assoc]
  have hbody' : ∀ x ∈ xs, ∀ (pre rest : List Bool) (σ : WState ns nr), ok σ → σ.st i = pre ++ enc ε (g x) ++ rest →
      σ.sh i = pre.length → WExec cap body σ (σ.seth i (pre.length + (enc ε (g x)).length)) (cost x) := by
    intro x hx pre rest σ hσ hst' hsh'
    rw [WireExponent3_5.PrimAsm.ParseNat.enc_length]; exact hbody x hx pre rest σ hσ hst' hsh'
  have h2 := listLoop_spec cap i k body (fun x => enc ε (g x)) cost ok hok_h hok_v xs hbody'
    (pre ++ enc ε (natWord xs.length)) rest σ1 hok1 hst1 (by simp [hσ1, WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, hk]) hlen
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by unfold skipListCost; rw [List.map_map]; exact le_refl _)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j; by_cases hj : j = i
    · subst hj
      have hl : (xs.flatMap fun x => enc ε (g x)).length = stp ε * (xs.flatMap g).length := by
        rw [← enc_flatMap, WireExponent3_5.PrimAsm.ParseNat.enc_length]
      simp [hσ1, listWord, WireExponent3_5.PrimAsm.ParseNat.enc_length, hl]; ring
    · simp [hσ1, Function.update_of_ne hj]
  · funext r; by_cases hr : r = k
    · subst hr; simp [hσ1, hk]
    · simp [hσ1, Function.update_of_ne hr]

end NearCubicGates.Close.Codec
