import SourceAdapters.Proximity.ReadLiteral
import SourceAdapters.Proximity.AddressTranslation
import SourceAdapters.Proximity.LiteralFields

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": one actual sequential local-literal
read, address translation, polarity conversion and exact trimming-request output. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.LiteralStep

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open SourceRequests (State Script)
open QueryStep (rowReg boundReg paddedAddress)
open AddressTranslation (translatedAddress)

def scratch : List (Fin VV) :=
  ReadLiteral.scratch ++ AddressTranslation.scratch ++ LiteralFields.scratch

def step (m : Fin MM) : Script :=
  .seq ReadLiteral.readLiteral (.seq (AddressTranslation.translate m) LiteralFields.fields)

def globalWord {N : ℕ} (addresses : Fin N → Bool × ℕ) (row q : ℕ) (literal : Bool × ℕ) : List Bool :=
  let address := translatedAddress addresses row q literal.2
  LiteralFields.literalWord address.1 address.2 literal.1

structure Written (m : Fin MM) (q : ℕ) (a b : State) (cursor : ℕ) (word : List Bool) : Prop where
  ip_eq : b.ip = a.ip
  out_eq : b.out = a.out ++ word
  ram_eq : b.ram = a.ram
  kin_eq : b.kin = a.kin
  kout_eq : b.kout = a.kout
  cursor_eq : b.kc = cursor
  other_cursor : ∀ s, s ≠ m → b.rc s = a.rc s
  cursor_bound : b.rc m ≤ 2 * q
  vars : Fr a b scratch

theorem Written.constants {m : Fin MM} {q cursor : ℕ} {a b : State} {word : List Bool}
    (h : Written m q a b cursor word) (hc : Cst a) : Cst b :=
  Cst.of_fr hc h.vars (by decide)

def stepCost (q Λ : ℕ) : ℕ := 12 * q + 50 * Λ + 247

theorem literal_step (C : Ctx) (m : Fin MM) {N : ℕ} (addresses : Fin N → Bool × ℕ)
    (row q Λ : ℕ) (literal : Bool × ℕ) (a : State) (hc : Cst a) (pre tail : List Bool)
    (hin : a.kout = pre ++ literal.1 :: (frame literal.2.bits ++ tail)) (hip : a.kc = pre.length)
    (hwidth : literal.2.bits.length + 1 ≤ C.Wd) (hW : 2 ≤ C.Wd)
    (hrow : a.env rowReg = row) (hq : a.env boundReg = q)
    (hstore : a.ram m = QueryRows.rowFields addresses q) (hcursor : a.rc m ≤ 2 * q)
    (hpositions : 2 * q ≤ 2 ^ C.Wd)
    (hsource : ∀ j < q, 2 * (paddedAddress addresses j).2 < 2 ^ C.Wd)
    (haux : 2 * Nat.pair row (literal.2 - q) + 1 < 2 ^ C.Wd)
    (hvalue : natBitLength (translatedAddress addresses row q literal.2).2 + 2 < 2 ^ C.Wd)
    (hlocal : literal.2.bits.length ≤ Λ)
    (hglobal : natBitLength (translatedAddress addresses row q literal.2).2 ≤ Λ) :
    Hs C (step m) a (stepCost q Λ) (fun b =>
      Written m q a b (pre.length + 2 * literal.2.bits.length + 2)
        (globalWord addresses row q literal)) := by
  have e1 := ReadLiteral.read_literal C a hc pre tail literal.1 literal.2 hin hip hwidth
  refine Hs.mono (Hs.seq (t2 := 12 * q + 20 + (40 *
      natBitLength (translatedAddress addresses row q literal.2).2 + 213) + 1) e1 (fun b hb => ?_))
    (by unfold stepCost; omega) (fun _ h => h)
  have e2 := AddressTranslation.translate_address C m addresses row q literal.2 b (hb.constants hc)
    ((hb.vars rowReg (by decide)).trans hrow) ((hb.vars boundReg (by decide)).trans hq) hb.value_eq
    (by rw [hb.ram_eq]; exact hstore) (by rw [hb.rc_eq]; exact hcursor) hpositions hsource haux
  refine Hs.seq e2 (fun d hd => ?_)
  have hdC : Cst d := Cst.of_fr (hb.constants hc) hd.vars (by decide)
  have e3 := LiteralFields.fields_run C d hdC
    (translatedAddress addresses row q literal.2).1 literal.1
    (translatedAddress addresses row q literal.2).2 hd.kind_eq hd.address_eq
    ((hd.vars SourceResults.tagReg (by decide)).trans hb.sign_eq) hW hvalue
  refine e3.mono le_rfl (fun f hf => ?_)
  rcases hf with ⟨hfrest, hfout, hfvars⟩
  have hfi := congrArg Prod.fst hfrest
  have hfm := congrArg (fun x => x.2.1) hfrest
  have hfr := congrArg (fun x => x.2.2.1) hfrest
  have hfk := congrArg (fun x => x.2.2.2.1) hfrest
  have hfko := congrArg (fun x => x.2.2.2.2.1) hfrest
  have hfkc := congrArg (fun x => x.2.2.2.2.2) hfrest
  refine ⟨hfi.trans (hd.ip_eq.trans hb.ip_eq), ?_, hfm.trans (hd.ram_eq.trans hb.ram_eq),
    hfk.trans (hd.kin_eq.trans hb.kin_eq), hfko.trans (hd.kout_eq.trans hb.kout_eq),
    hfkc.trans (hd.kc_eq.trans hb.cursor_eq), ?_, ?_, ?_⟩
  · rw [hfout, hd.out_eq, hb.out_eq]
    rfl
  · intro s hs
    exact (congrFun hfr s).trans ((hd.other_cursor s hs).trans (congrFun hb.rc_eq s))
  · change f.rc = d.rc at hfr
    rw [hfr]
    exact hd.cursor_bound
  · exact (hb.vars.weaken (fun _ h => List.mem_append_left _ (List.mem_append_left _ h))).trans
      ((hd.vars.weaken (fun _ h => List.mem_append_left _ (List.mem_append_right _ h))).trans
      (hfvars.weaken (fun _ h => List.mem_append_right _ h)))

end NearCubicGates.Adapters.Proximity.LiteralStep
