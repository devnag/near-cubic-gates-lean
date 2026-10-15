import Proof.Amplification.RecoveryCompactLayout

/-! Assemble the native155 compact tapes from their checked row and lookup
components. Only specified false backing is omitted from physical storage. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCompact
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem pad_banks {m n : Nat} (c : Fin m→Nat) (d : Fin n→Nat)
    (a : Fin m→List Bool) (b : Fin n→List Bool) :
    (fun i=>ZeroPadding.pad (Fin.addCases c d i) (Fin.addCases a b i))=
      Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (c i) (a i)) (fun i=>ZeroPadding.pad (d i) (b i)) := by
  funext i
  refine Fin.addCases (m:=m) (n:=n) (motive:=fun j=>
    ZeroPadding.pad (Fin.addCases c d j) (Fin.addCases a b j)=
      Fin.addCases (m:=m) (n:=n) (motive:=fun _=>List Bool)
        (fun i=>ZeroPadding.pad (c i) (a i)) (fun i=>ZeroPadding.pad (d i) (b i)) j)
    (by intro j; simp only [Fin.addCases_left])
    (by intro j; simp only [Fin.addCases_right]) i

def childTapes (bits word table : List Bool) : Fin 68→List Bool :=
  Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
    (baseTapes bits word table) (lookupTapes bits table 0)
def childCaps (bits word : List Bool) : Fin 68→Nat :=
  Fin.addCases (m:=52) (n:=16) (motive:=fun _=>Nat) (baseCaps bits word) (lookupCaps bits)

theorem child_layout (bits word table : List Bool) :
    (fun i=>ZeroPadding.pad (childCaps bits word i) (childTapes bits word table i))=
      (children bits word table).tapes := by
  unfold childCaps childTapes
  rw [pad_banks (m:=52) (n:=16),lookup_layout]
  have hb := congrArg Configuration.tapes (base_layout bits word table (0 : Fin 1))
  change (fun i=>ZeroPadding.pad (baseCaps bits word i) (baseTapes bits word table i))=_ at hb
  rw [hb]
  rfl

def tapes (bits word innerBits outerBits : List Bool) (n m : Nat) : Fin 155→List Bool :=
  Fin.addCases (m:=69) (n:=86) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=68) (n:=1) (motive:=fun _=>List Bool)
      (childTapes bits word innerBits) (fun _=>CompareMachine.word n))
    (Fin.addCases (m:=84) (n:=2) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=68) (n:=16) (motive:=fun _=>List Bool)
        (childTapes bits word outerBits) (lookupTapes bits innerBits n))
      ![CompareMachine.word m,frame (RecoveryColdHeader.zeroWord bits)])
def caps (bits word : List Bool) : Fin 155→Nat :=
  Fin.addCases (m:=69) (n:=86) (motive:=fun _=>Nat)
    (Fin.addCases (m:=68) (n:=1) (motive:=fun _=>Nat) (childCaps bits word) (fun _=>0))
    (Fin.addCases (m:=84) (n:=2) (motive:=fun _=>Nat)
      (Fin.addCases (m:=68) (n:=16) (motive:=fun _=>Nat) (childCaps bits word) (lookupCaps bits))
      (fun _=>0))
def heads (i : Fin 155) : Nat := if i.val=49 ∨ i.val=68 ∨ i.val=118 ∨ i.val=153 then 1 else 0

theorem native_layout {s : Nat} (bits word innerBits outerBits : List Bool) (n m : Nat) (q : Fin s) :
    ZeroPadding.config (caps bits word) ⟨q,heads,tapes bits word innerBits outerBits n m⟩=
      (state bits word innerBits outerBits n m).cfg q := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · change (fun i=>ZeroPadding.pad (caps bits word i) (tapes bits word innerBits outerBits n m i))=_
    unfold caps tapes
    rw [pad_banks (m:=69) (n:=86),pad_banks (m:=68) (n:=1),
      pad_banks (m:=84) (n:=2),pad_banks (m:=68) (n:=16)]
    rw [child_layout,child_layout,lookup_layout]
    simp only [ZeroPadding.pad_zero]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryColdCompact
