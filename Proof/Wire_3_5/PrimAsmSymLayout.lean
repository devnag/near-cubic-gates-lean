import Proof.Wire_3_5.PrimAsmDockW

/-! # PA (d)-SYM, part 17: the SYM writer cell's register-program layout

One register-language layout `WState (LNS x) LNR` carries a whole SYM cell (`x` = the walk-bank producer's scratch
count). Streams (`sk`): `0` the request word (kept), `1` the output (kept), `2` the unit counter (kept), `3` the POP
record, `4` the labels' dummy stream, `5 … 16` C5's twelve table-builder streams (`5` / `7` the walk coordinates, `6`
the table), `17 … 23` the walk bank's tapes `2 … 8`, `24 … 28` the walk-bank producer's inputs (seed index word,
rulers), `29 … 76` the POP row machine's work tapes, `161 …` the producer's scratch (`sT`). Registers: `0 … 18` C5's
builder registers, `19 … 218` the POP cell's block (`Pe`).

* `tmapT` (the producer's tapes), `tmapP` (the POP row machine's tapes), `fsC`/`frC`/`emC` (C5's builder bank), with
  their injectivity (**`tmapT_inj`**, **`tmapP_inj`**, **`gsC_inj`**, `frC_inj`).

Paper quantity: none (layout for the writer's cells). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-- The layout's stream count minus one. -/
abbrev LNS (x : ℕ) : ℕ := 160 + x

/-- The layout's register count. -/
abbrev LNR : ℕ := 512

/-- A fixed stream. -/
def sk (x : ℕ) (k : Fin 161) : Fin (LNS x + 1) := Fin.castLE (by unfold LNS; omega) k

/-- The producer's scratch streams. -/
def sT (x : ℕ) (k : Fin x) : Fin (LNS x + 1) := ⟨161 + k.val, by unfold LNS; omega⟩

theorem sk_val (x : ℕ) (k : Fin 161) : (sk x k).val = k.val := rfl
theorem sT_val (x : ℕ) (k : Fin x) : (sT x k).val = 161 + k.val := rfl

theorem sk_inj (x : ℕ) : Function.Injective (sk x) := fun a b h => Fin.ext (by
  have hv := congrArg Fin.val h
  rwa [sk_val, sk_val] at hv)

theorem sk_ne_sT (x : ℕ) (a : Fin 161) (k : Fin x) : sk x a ≠ sT x k := by
  intro h
  have hv := congrArg Fin.val h
  rw [sk_val, sT_val] at hv
  have := a.isLt
  omega

/-- The walk-bank producer's ports: `0`, `1` the walk coordinates (`5`, `7`), `2 … 8` the bank (`17 … 23`), `9 … 13`
the inputs (`24 … 28`). -/
def portT : Fin 14 → Fin 161 := ![5, 7, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem portT_inj : Function.Injective portT := by decide

/-- The producer's tapes. -/
def tmapT (x : ℕ) : Fin (14 + x) → Fin (LNS x + 1) :=
  Fin.addCases (motive := fun _ => Fin (LNS x + 1)) (fun j => sk x (portT j)) (sT x)

theorem tmapT_inj (x : ℕ) : Function.Injective (tmapT x) := by
  intro a b
  refine Fin.addCases (fun a1 => ?_) (fun a2 => ?_) a <;> refine Fin.addCases (fun b1 => ?_) (fun b2 => ?_) b <;>
    intro h
  · simp only [tmapT, Fin.addCases_left] at h
    rw [portT_inj (sk_inj x h)]
  · simp only [tmapT, Fin.addCases_left, Fin.addCases_right] at h
    exact absurd h (sk_ne_sT x _ _)
  · simp only [tmapT, Fin.addCases_left, Fin.addCases_right] at h
    exact absurd h.symm (sk_ne_sT x _ _)
  · simp only [tmapT, Fin.addCases_right] at h
    have hv := congrArg Fin.val h
    rw [sT_val, sT_val] at hv
    exact congrArg _ (Fin.ext (by omega))

/-- The POP row machine's tapes: its input on the record stream `3`, its output tape `45` on the output stream `1`,
the others on `29 + j`. -/
def portP (j : Fin 48) : Fin 161 :=
  ⟨if j.val = 0 then 3 else if j.val = 45 then 1 else 29 + j.val, by split_ifs <;> omega⟩

theorem portP_val (j : Fin 48) : (portP j).val = if j.val = 0 then 3 else if j.val = 45 then 1 else 29 + j.val := rfl

theorem portP_inj : Function.Injective portP := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [portP_val, portP_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def tmapP (x : ℕ) (j : Fin 48) : Fin (LNS x + 1) := sk x (portP j)

theorem tmapP_inj (x : ℕ) : Function.Injective (tmapP x) := fun _ _ h => portP_inj (sk_inj x h)

/-- C5's builder streams on `5 … 16`. -/
def fsC (x : ℕ) (i : Fin 12) : Fin (LNS x + 1) := sk x ⟨5 + i.val, by omega⟩

/-- The builder's extra tapes (the walk bank's `2 … 8`) on `17 … 23`. -/
def emC (x : ℕ) (k : Fin 7) : Fin (LNS x + 1) := sk x ⟨17 + k.val, by omega⟩

/-- C5's builder registers on `0 … 18`. -/
def frC : Fin 19 → Fin LNR := Fin.castLE (by norm_num)

theorem frC_inj : Function.Injective frC := Fin.castLE_injective _

theorem gsC_inj (x : ℕ) : Function.Injective (gs (fsC x) (emC x)) := by
  intro a b h
  have hv : ∀ c, (gs (fsC x) (emC x) c).val = if c.val < 12 then 5 + c.val else 17 + (c.val - 12) := by
    intro c
    refine Fin.addCases (fun c1 => ?_) (fun c2 => ?_) c
    · simp only [gs, Fin.addCases_left, fsC, sk_val, Fin.val_castAdd]
      rw [if_pos c1.isLt]
    · simp only [gs, Fin.addCases_right, emC, sk_val, Fin.val_natAdd]
      rw [if_neg (by omega)]
      omega
  have h2 := congrArg Fin.val h
  rw [hv, hv] at h2
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at h2 <;> omega

/-- The POP cell's register block on `19 … 218`. -/
def Pe : Fin 200 ↪ Fin LNR := ⟨fun i => ⟨19 + i.val, by unfold LNR; omega⟩, fun _ _ h => Fin.ext (by
  have := congrArg Fin.val h
  simp only at this
  omega)⟩

theorem Pe_val (i : Fin 200) : (Pe i).val = 19 + i.val := rfl

theorem frC_ne_Pe (r : Fin 19) (i : Fin 200) : frC r ≠ Pe i := by
  intro h
  have hv := congrArg Fin.val h
  rw [Pe_val] at hv
  have hr : (frC r).val = r.val := rfl
  rw [hr] at hv
  have := r.isLt
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
