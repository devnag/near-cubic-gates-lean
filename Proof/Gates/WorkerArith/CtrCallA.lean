import Proof.Gates.WorkerArith.CtrCallDefs
import Proof.Wire_3_5.CompilerMachineEmitPad

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ}

theorem writeTapeBit_end' (p : List Bool) (b : Bool) : writeTapeBit p p.length b = p ++ [b] := by
  induction p with
  | nil => rfl
  | cons a p ih => show a :: writeTapeBit p p.length b = a :: (p ++ [b]); rw [ih]

theorem wtb_mid : ∀ (p q : List Bool) (b : Bool), writeTapeBit (p ++ q) p.length b = p ++ b :: q.drop 1
  | [], [], b => rfl
  | [], _ :: q, b => rfl
  | a :: p, q, b => by
    show a :: writeTapeBit (p ++ q) p.length b = a :: (p ++ b :: q.drop 1)
    rw [wtb_mid p q b]

/-! ## Two ones -/

theorem twoOnesM (cap : ℕ) (G : Fin (ns + 1)) (RG : Fin nr) (σ : WState ns nr) (l : List Bool) (a : ℕ)
    (hG : σ.st G = l) (hGh : σ.sh G = l.length) (hR : σ.val RG = a) (hc : a + 2 ≤ cap) :
    WXExec cap (twoOnes G RG) σ (((σ.sets G (l ++ [true, true])).seth G (l.length + 2)).setv RG (a + 2)) 15 := by
  have e1 := WXExec.wr cap G true σ
  rw [hG, hGh, writeTapeBit_end'] at e1
  set σ1 := σ.sets G (l ++ [true]) with hσ1
  have e2 := WXExec.fwd cap G σ1
  set σ2 := σ1.seth G (σ1.sh G + 1) with hσ2
  have e3 := WXExec.wr cap G true σ2
  have h3 : writeTapeBit (σ2.st G) (σ2.sh G) true = l ++ [true, true] := by
    simp only [hσ2, hσ1, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, Function.update_self, hGh]
    have := writeTapeBit_end' (l ++ [true]) true
    simp only [List.length_append, List.length_singleton] at this
    rw [this]; simp
  rw [h3] at e3
  set σ3 := σ2.sets G (l ++ [true, true]) with hσ3
  have e4 := WXExec.fwd cap G σ3
  set σ4 := σ3.seth G (σ3.sh G + 1) with hσ4
  have e5 := WXExec.inc cap RG σ4 (by simp [hσ4, hσ3, hσ2, hσ1, hR]; omega)
  set σ5 := σ4.setv RG (σ4.val RG + 1) with hσ5
  have e6 := WXExec.inc cap RG σ5 (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hR]; omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = G
    · subst hi; simp [hσ5, hσ4, hσ3, hσ2, hσ1, hGh]; try omega
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hi]
  · funext i; by_cases hi : i = G
    · subst hi; simp [hσ5, hσ4, hσ3, hσ2, hσ1]
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hi]
  · funext r; by_cases hr : r = RG
    · subst hr; simp [hσ5, hσ4, hσ3, hσ2, hσ1, hR]
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr]
  · rfl

/-! ## The guard from the input frame -/

theorem frame_numOn (σ : WState ns nr) (X : Fin (ns + 1)) (w : List Bool) (hX : σ.st X = frame w)
    (hXh : σ.sh X = 0) : NumOn σ X w.length (NearCubicWires.RepairOrdinary.RadixSemantics.value w) :=
  ⟨by rw [hX, NearCubicWires.WireExponent3_5.CompilerMachine.Emit.binary_value_self], hXh⟩

theorem replicate_two_succ (j : ℕ) :
    List.replicate (2 * j) true ++ [true, true] = List.replicate (2 * (j + 1)) true := by
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, List.replicate_add]; rfl

/-- **Step 1.** -/
theorem guardM (cap : ℕ) (X G : Fin (ns + 1)) (K T RG : Fin nr) (hKT : K ≠ T) (hKG : K ≠ RG) (hTG : T ≠ RG)
    (σ : WState ns nr) (w : List Bool) (hX : σ.st X = frame w) (hXh : σ.sh X = 0) (hXG : X ≠ G)
    (hG : σ.st G = []) (hGh : σ.sh G = 0) (hK : σ.val K = 0) (hT : σ.val T = 0) (hR : σ.val RG = 0)
    (hc : 2 * w.length + 2 ≤ cap) :
    WXExec cap (guardP X G K T RG) σ
      (((σ.sets G (List.replicate (2 * w.length + 2) true)).seth G (2 * w.length + 2)).setv RG (2 * w.length + 2))
      (40 * w.length + 40) := by
  set n := w.length with hn
  have e1 := BinW.width_spec cap hKT n _ σ (frame_numOn σ X w hX hXh) hK hT (by omega)
  let st : ℕ → ℕ → WState ns nr := fun j v =>
    (((σ.sets G (List.replicate (2 * j) true)).seth G (2 * j)).setv RG (2 * j)).setv K v
  have hl := Runs.count (cap := cap) (K := K) (body := twoOnes G RG) 15 n (fun j τ => ∃ v, τ = st j v)
    (by omega)
    (by
      rintro k hk τ ⟨v, rfl⟩ -
      have h1 : (st k v).setv K (n - k - 1) = st k (n - k - 1) := by simp only [st]; rw [wsetv_setv]
      rw [h1]
      have e := twoOnesM cap G RG (st k (n - k - 1)) (List.replicate (2 * k) true) (2 * k)
        (by simp [st]) (by simp [st]) (by simp [st, Function.update_of_ne hKG.symm]) (by omega)
      refine ⟨_, e, ⟨n - k - 1, ?_⟩, ?_⟩
      · rw [replicate_two_succ]
        apply WState.eq
        · funext i; by_cases hi : i = G
          · subst hi; simp [st]; try ring
          · simp [st, Function.update_of_ne hi]
        · funext i; by_cases hi : i = G
          · subst hi; simp [st]
          · simp [st, Function.update_of_ne hi]
        · funext r; by_cases hr : r = RG
          · subst hr; simp [st, Function.update_of_ne hKG.symm]; try ring
          · by_cases hrK : r = K
            · subst hrK; simp [st, Function.update_of_ne hr]
            · simp [st, Function.update_of_ne hr, Function.update_of_ne hrK]
        · rfl
      · simp [st, Function.update_apply, hKG])
  obtain ⟨τ, e2, ⟨v, rfl⟩, hz⟩ := hl (σ.setv K n) ⟨n, by
      apply WState.eq
      · funext i; by_cases hi : i = G
        · subst hi; simp [st, hGh]
        · simp [st, Function.update_of_ne hi]
      · funext i; by_cases hi : i = G
        · subst hi; simp [st, hG]
        · simp [st, Function.update_of_ne hi]
      · funext r; by_cases hr : r = K
        · subst hr; simp [st]
        · by_cases hr2 : r = RG
          · subst hr2; simp [st, Function.update_apply, hKG, hKG.symm, hR]
          · simp [st, Function.update_of_ne hr, Function.update_of_ne hr2]
      · rfl⟩ (by simp)
  have hv : v = 0 := by simpa [st] using hz
  subst hv
  have e3 := twoOnesM cap G RG (st n 0) (List.replicate (2 * n) true) (2 * n) (by simp [st]) (by simp [st])
    (by simp [st, Function.update_of_ne hKG.symm]) (by omega)
  refine (WXExec.seq e1 (WXExec.seq e2 e3)).cast cap ?_ (by omega)
  rw [replicate_two_succ]
  apply WState.eq
  · funext i; by_cases hi : i = G
    · subst hi; simp [st]; try ring
    · simp [st, Function.update_of_ne hi]
  · funext i; by_cases hi : i = G
    · subst hi; simp [st]; try ring_nf
    · simp [st, Function.update_of_ne hi]
  · funext r; by_cases hr : r = RG
    · subst hr; simp [st, Function.update_of_ne hKG.symm]; try ring
    · by_cases hrK : r = K
      · subst hrK; simp [st, Function.update_of_ne hr, hK]
      · simp [st, Function.update_of_ne hr, Function.update_of_ne hrK]
  · rfl

end NearCubicGates.Close.WorkerArith
