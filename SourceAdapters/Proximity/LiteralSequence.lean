import SourceAdapters.Proximity.LiteralStep

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": the block literal count is a
constant depending only on q. This finite-control iteration reads every
actual local literal from the computed block output; its program depends
on the count alone, never on the literal data. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LiteralStep

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open SourceRequests (State Script)
open QueryStep (rowReg boundReg paddedAddress)
open AddressTranslation (translatedAddress)

def rawLiteral (literal : Bool × ℕ) : List Bool := literal.1 :: frame literal.2.bits

def rawWords (literals : List (Bool × ℕ)) : List Bool := literals.flatMap rawLiteral

def globalWords {N : ℕ} (addresses : Fin N → Bool × ℕ) (row q : ℕ)
    (literals : List (Bool × ℕ)) : List Bool := literals.flatMap (globalWord addresses row q)

@[simp] theorem rawLiteral_length (literal : Bool × ℕ) :
    (rawLiteral literal).length = 2 * literal.2.bits.length + 2 := by
  simp [rawLiteral, frame_length]

def steps (m : Fin MM) : ℕ → Script
  | 0 => .op (.zero t0)
  | n + 1 => .seq (step m) (steps m n)

theorem literal_steps (C : Ctx) (m : Fin MM) {N : ℕ} (addresses : Fin N → Bool × ℕ)
    (row q Λ : ℕ) (literals : List (Bool × ℕ)) (a : State) (hc : Cst a) (pre tail : List Bool)
    (hin : a.kout = pre ++ rawWords literals ++ tail) (hip : a.kc = pre.length)
    (hwidth : ∀ literal ∈ literals, literal.2.bits.length + 1 ≤ C.Wd) (hW : 2 ≤ C.Wd)
    (hrow : a.env rowReg = row) (hq : a.env boundReg = q)
    (hstore : a.ram m = QueryRows.rowFields addresses q) (hcursor : a.rc m ≤ 2 * q)
    (hpositions : 2 * q ≤ 2 ^ C.Wd)
    (hsource : ∀ j < q, 2 * (paddedAddress addresses j).2 < 2 ^ C.Wd)
    (haux : ∀ literal ∈ literals, 2 * Nat.pair row (literal.2 - q) + 1 < 2 ^ C.Wd)
    (hvalue : ∀ literal ∈ literals,
      natBitLength (translatedAddress addresses row q literal.2).2 + 2 < 2 ^ C.Wd)
    (hlocal : ∀ literal ∈ literals, literal.2.bits.length ≤ Λ)
    (hglobal : ∀ literal ∈ literals, natBitLength (translatedAddress addresses row q literal.2).2 ≤ Λ) :
    Hs C (steps m literals.length) a (literals.length * (stepCost q Λ + 1) + 1)
      (fun b => Written m q a b (pre.length + (rawWords literals).length)
        (globalWords addresses row q literals)) := by
  induction literals generalizing a pre with
  | nil =>
    refine ⟨_, 1, Ex.op (OpEx.zero (C := C) t0 a), by simp, ?_⟩
    refine ⟨rfl, by simp [globalWords], rfl, rfl, rfl, ?_, fun _ _ => rfl,
      hcursor, Fr.set a 0 (by decide)⟩
    simpa [rawWords] using hip
  | cons literal literals ih =>
    have e1 := literal_step C m addresses row q Λ literal a hc pre (rawWords literals ++ tail)
      (by simpa [rawWords, rawLiteral, List.append_assoc] using hin) hip (hwidth literal (by simp)) hW
      hrow hq hstore hcursor hpositions hsource (haux literal (by simp)) (hvalue literal (by simp))
      (hlocal literal (by simp)) (hglobal literal (by simp))
    refine Hs.mono (Hs.seq (t2 := literals.length * (stepCost q Λ + 1) + 1) e1 (fun b hb => ?_))
      (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega) (fun _ h => h)
    have ei := ih b (hb.constants hc) (pre ++ rawLiteral literal)
      (by rw [hb.kout_eq]; simpa [rawWords, List.append_assoc] using hin)
      (by rw [hb.cursor_eq, List.length_append, rawLiteral_length]; omega)
      (fun l hl => hwidth l (by simp [hl]))
      ((hb.vars rowReg (by decide)).trans hrow) ((hb.vars boundReg (by decide)).trans hq)
      (by rw [hb.ram_eq]; exact hstore) hb.cursor_bound
      (fun l hl => haux l (by simp [hl])) (fun l hl => hvalue l (by simp [hl]))
      (fun l hl => hlocal l (by simp [hl])) (fun l hl => hglobal l (by simp [hl]))
    refine ei.mono le_rfl (fun d hd => ?_)
    refine ⟨hd.ip_eq.trans hb.ip_eq, ?_, hd.ram_eq.trans hb.ram_eq,
      hd.kin_eq.trans hb.kin_eq, hd.kout_eq.trans hb.kout_eq, ?_,
      fun s hs => (hd.other_cursor s hs).trans (hb.other_cursor s hs), hd.cursor_bound,
      hb.vars.trans hd.vars⟩
    · rw [hd.out_eq, hb.out_eq]
      simp [globalWords, List.append_assoc]
    · rw [hd.cursor_eq]
      simp [rawWords, Nat.add_assoc]

end NearCubicGates.Adapters.Proximity.LiteralStep
