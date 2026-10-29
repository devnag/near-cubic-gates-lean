import SourceAdapters.Compile.BoundedEncoding
import Proof.Wire_3_5.PrimAsmParseNat

/-!
proof of `lem:multitape-refuter`, Step 3: transition-table selection and literal finite tape
updates. The 2^t read-symbol rows are explicitly enumerated, exactly as in
VerifierEncoding.code; no exponential enumeration of configurations occurs.
-/
namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def headSelection {t s width : ℕ} (tape : Fin t)
    (values : Fin width → BoolExpr (windowBits t s width)) :
    BoolExpr (windowBits t s width) :=
  anyExpression (List.ofFn (fun position =>
    .and (.input (headIndex tape position)) (values position)))

@[simp] theorem headSelection_eval {t s width : ℕ} (a : MachineWindow t s width)
    (tape : Fin t) (values : Fin width → BoolExpr (windowBits t s width)) :
    (headSelection tape values).eval a.encode = (values (a.heads tape)).eval a.encode := by
  apply Bool.eq_iff_iff.mpr
  simp [headSelection, BoolExpr.eval]

def scanMask {t : ℕ} (mask : Fin (2^t)) : Fin t → Bool :=
  fun tape => mask.val.testBit tape.val

theorem scanMask_surjective (t : ℕ) : Function.Surjective (@scanMask t) := by
  intro scans
  have hlt : CanonicalBinary.bitsValue (List.ofFn scans) < 2^t := by
    simpa using WireExponent3_5.PrimAsm.ParseNat.bitsValue_lt (List.ofFn scans)
  refine ⟨⟨CanonicalBinary.bitsValue (List.ofFn scans), hlt⟩, ?_⟩
  funext tape
  change (CanonicalBinary.bitsValue (List.ofFn scans)).testBit tape.val = scans tape
  rw [NearCubicGates.Close.Succinct.testBit_bitsValue]
  simp [List.getD_eq_getElem?_getD]

/-- Select a local expression by the literal finite machine table. -/
def tableSelection {t s width : ℕ}
    (values : Fin s → (Fin t → Bool) → BoolExpr (windowBits t s width)) :
    BoolExpr (windowBits t s width) :=
  anyExpression (List.ofFn (fun state : Fin s =>
    anyExpression (List.ofFn (fun mask : Fin (2^t) =>
      .and (rowExpression state (scanMask mask)) (values state (scanMask mask))))))

@[simp] theorem tableSelection_eval {t s width : ℕ} (a : MachineWindow t s width)
    (values : Fin s → (Fin t → Bool) → BoolExpr (windowBits t s width)) :
    (tableSelection values).eval a.encode = (values a.control a.scanned).eval a.encode := by
  apply Bool.eq_iff_iff.mpr
  simp only [tableSelection, anyExpression_true, List.mem_ofFn, exists_exists_eq_and,
    BoolExpr.eval, Bool.and_eq_true, rowExpression_eval]
  constructor
  · rintro ⟨state, mask, ⟨hs, hm⟩, hv⟩
    simpa [← hs, hm] using hv
  · intro hv
    obtain ⟨mask, hm⟩ := scanMask_surjective t a.scanned
    exact ⟨a.control, mask, ⟨rfl, hm⟩, hm ▸ hv⟩

/-- Check that every unit head movement remains in the finite window. -/
def actionFitsExpression {t s width : ℕ} (action : Action t s) :
    BoolExpr (windowBits t s width) :=
  allExpression (List.ofFn (fun tape : Fin t => headSelection tape
    (fun position => .const (decide ((action.move tape).apply position.val < width)))))

@[simp] theorem actionFitsExpression_eval {t s width : ℕ} (a : MachineWindow t s width)
    (action : Action t s) : (actionFitsExpression action).eval a.encode = true ↔
      ∀ tape, (action.move tape).apply (a.heads tape).val < width := by
  simp [actionFitsExpression, BoolExpr.eval]

/-- Each output cell is a two-way multiplexer at the unique current head. -/
def writtenCellExpression {t s width : ℕ} (action : Action t s)
    (tape : Fin t) (position : Fin width) : BoolExpr (windowBits t s width) :=
  match action.write tape with
  | none => .input (cellIndex tape position)
  | some value =>
      .or (.and (.input (headIndex tape position)) (.const value))
        (.and (.not (.input (headIndex tape position))) (.input (cellIndex tape position)))

def actionExpression {t s width : ℕ} (action : Action t s) :
    Fin (windowBits t s width) → BoolExpr (windowBits t s width) :=
  Fin.addCases (fun q => .const (decide (action.nextControl = q)))
    (Fin.addCases
      (fun index => let pair := finProdFinEquiv.symm index
        headSelection pair.1 (fun old =>
          .const (decide ((action.move pair.1).apply old.val = pair.2.val))))
      (fun index => let pair := finProdFinEquiv.symm index
        writtenCellExpression action pair.1 pair.2))

@[simp] theorem actionExpression_eval {t s width : ℕ} (a : MachineWindow t s width)
    (action : Action t s) (hfit : ∀ tape, (action.move tape).apply (a.heads tape).val < width)
    (index : Fin (windowBits t s width)) :
    (actionExpression action index).eval a.encode = (a.apply action hfit).encode index := by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) index
  · intro q
    simp only [actionExpression, MachineWindow.encode, Fin.addCases_left,
      BoolExpr.eval, MachineWindow.apply]
    rfl
  · intro pair
    simp only [actionExpression, MachineWindow.encode, Fin.addCases_left,
      Fin.addCases_right, headSelection_eval, BoolExpr.eval, MachineWindow.apply,
      Fin.ext_iff]
  · intro pair
    simp only [actionExpression, MachineWindow.encode, Fin.addCases_right,
      MachineWindow.apply]
    change (writtenCellExpression action pair.divNat pair.modNat).eval a.encode = _
    cases hw : action.write pair.divNat with
    | none => simp [writtenCellExpression, hw, BoolExpr.eval]
    | some value =>
        by_cases hp : a.heads pair.divNat = pair.modNat
        · simp [writtenCellExpression, hw, BoolExpr.eval, hp]
        · simp [writtenCellExpression, hw, BoolExpr.eval, hp, Ne.symm hp]

end NearCubicGates.Adapters.Compile
