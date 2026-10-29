import SourceAdapters.Machine.StackTape

/-!
# The stack machine simulating an ordinary program

`app:short-pcp-proof`, "The exact Lean interface": "A fixed multitape implementation can be simulated by finitely many stackOf in polynomial time,
giving the Mathlib TM2 machine required by the interface; clearing work stackOf and restoring its final control
state also take polynomial time."

For an ordinary program `p` (`RepairOrdinary.Program`, `L/Statement.lean:535`) this module builds the bundled
Mathlib TM2 machine `stackMachine p : Turing.FinTM2`:

* stackOf: the input stack, the output stack, and two `Option Bool` stackOf per ordinary tape (`StackTape`);
* `frameRev`/`frameEmit` (the framing front end): the TM2 starts with the RAW input on the input stack
  (`Turing.initList`), the ordinary machine expects `frame w` on tape 0 (`Program.inputTapes`);
* `sim q`: one TM2 step per ordinary step (peek every scanned cell, then write and move every tape);
* `gather`/`emit`: the output tape is moved onto the output stack, trailing blanks dropped;
* `wipe`: every tape stack is emptied, the variable is restored to `initialState`, and the machine halts
  (`Turing.haltList` demands exactly this).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Machine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary Turing

/-- The stackOf. -/
inductive Stack (T : ℕ) where
  | inp
  | out
  | lft (i : Fin T)
  | rgt (i : Fin T)
  deriving DecidableEq, Fintype

/-- The stack alphabets. -/
abbrev Sym {T : ℕ} : Stack T → Type
  | .inp => Bool
  | .out => Bool
  | .lft _ => Option Bool
  | .rgt _ => Option Bool

/-- The function labels. -/
inductive Label (Q : ℕ) where
  | frameRev
  | frameEmit
  | sim (q : Fin Q)
  | gather
  | emit
  | wipe
  deriving DecidableEq, Fintype

/-- The finite variable: the scanned bits, one transferred cell, one flag. -/
structure Var (T : ℕ) where
  scan : Fin T → Bool
  cell : Option (Option Bool)
  flag : Bool
  deriving DecidableEq, Fintype

instance {T : ℕ} : Inhabited (Var T) := ⟨⟨fun _ => false, none, false⟩⟩

/-- The initial (and final) variable. -/
def Var.init (T : ℕ) : Var T := ⟨fun _ => false, none, false⟩

abbrev SStmt (T Q : ℕ) := TM2.Stmt (Sym (T := T)) (Label Q) (Var T)


/-- The standard form of a stack contents: input stack, output stack, and the two stackOf of every tape. -/
def stackOf {T : ℕ} (i o : List Bool) (tp : Fin T → List (Option Bool) × List (Option Bool)) :
    ∀ k : Stack T, List (Sym k)
  | .inp => i
  | .out => o
  | .lft j => (tp j).1
  | .rgt j => (tp j).2

section StackOf
variable {T : ℕ} (i o : List Bool) (tp : Fin T → List (Option Bool) × List (Option Bool))

@[simp] theorem stackOf_inp : stackOf i o tp .inp = i := rfl
@[simp] theorem stackOf_out : stackOf i o tp .out = o := rfl
@[simp] theorem stackOf_lft (j : Fin T) : stackOf i o tp (.lft j) = (tp j).1 := rfl
@[simp] theorem stackOf_rgt (j : Fin T) : stackOf i o tp (.rgt j) = (tp j).2 := rfl

@[simp] theorem update_stackOf_inp (x : List Bool) :
    Function.update (stackOf i o tp) Stack.inp x = stackOf x o tp := by
  funext k; cases k <;> simp [Function.update, stackOf]

@[simp] theorem update_stackOf_out (x : List Bool) :
    Function.update (stackOf i o tp) Stack.out x = stackOf i x tp := by
  funext k; cases k <;> simp [Function.update, stackOf]

@[simp] theorem update_stackOf_lft (j : Fin T) (x : List (Option Bool)) :
    Function.update (stackOf i o tp) (Stack.lft j) x = stackOf i o (Function.update tp j (x, (tp j).2)) := by
  funext k
  cases k with
  | lft j' =>
    by_cases h : j' = j
    · subst h; simp [Function.update, stackOf]
    · simp [Function.update, stackOf, h]
  | rgt j' =>
    by_cases h : j' = j
    · subst h; simp [Function.update, stackOf]
    · simp [Function.update, stackOf, h]
  | _ => simp [Function.update, stackOf]

@[simp] theorem update_stackOf_rgt (j : Fin T) (x : List (Option Bool)) :
    Function.update (stackOf i o tp) (Stack.rgt j) x = stackOf i o (Function.update tp j ((tp j).1, x)) := by
  funext k
  cases k with
  | lft j' =>
    by_cases h : j' = j
    · subst h; simp [Function.update, stackOf]
    · simp [Function.update, stackOf, h]
  | rgt j' =>
    by_cases h : j' = j
    · subst h; simp [Function.update, stackOf]
    · simp [Function.update, stackOf, h]
  | _ => simp [Function.update, stackOf]

end StackOf

/-! ## The program -/

open TM2.Stmt

section Program
variable {T Q : ℕ} (M : LocalBitMultitape.Machine T Q)

/-- The scanned bit of a peeked right stack. -/
def topCell (x : Option (Option Bool)) : Bool := (x.getD none).getD false

/-- The write of tape `i` chosen by the rule at control `q` on the recorded scanned bits. -/
def wr (q : Fin Q) (s : Var T) (i : Fin T) : Option Bool := (M.rule q s.scan).bind fun a => a.write i

/-- The move of tape `i`. -/
def mv (q : Fin Q) (s : Var T) (i : Fin T) : HeadMove :=
  match M.rule q s.scan with
  | some a => a.move i
  | none => .stay

/-- The next control. -/
def nxt (q : Fin Q) (s : Var T) : Fin Q :=
  match M.rule q s.scan with
  | some a => a.nextControl
  | none => q

/-- Record the scanned bit of tape `i`. -/
def readOne (i : Fin T) (st : SStmt T Q) : SStmt T Q :=
  peek (.rgt i) (fun s x => { s with scan := Function.update s.scan i (topCell x) }) st

/-- Move the head of tape `i`. -/
def moveOp (q : Fin Q) (i : Fin T) (st : SStmt T Q) : SStmt T Q :=
  branch (fun s => decide (mv M q s i = .left))
    (pop (.lft i) (fun s x => { s with cell := x })
      (branch (fun s => s.cell.isSome) (push (.rgt i) (fun s => s.cell.getD none) st) st))
    (branch (fun s => decide (mv M q s i = .right))
      (pop (.rgt i) (fun s x => { s with cell := x }) (push (.lft i) (fun s => s.cell.getD none) st))
      st)

/-- Write, then move, tape `i`. -/
def tapeOp (q : Fin Q) (i : Fin T) (st : SStmt T Q) : SStmt T Q :=
  branch (fun s => (wr M q s i).isSome)
    (pop (.rgt i) (fun s _ => s) (push (.rgt i) (fun s => wr M q s i) (moveOp M q i st)))
    (moveOp M q i st)

/-- One ordinary step at control `q`. -/
def simStmt (q : Fin Q) : SStmt T Q :=
  if M.halted q then goto fun _ => .gather
  else (List.finRange T).foldr readOne
    (branch (fun s => (M.rule q s.scan).isSome)
      ((List.finRange T).foldr (tapeOp M q) (goto fun s => .sim (nxt M q s)))
      halt)

/-- Reverse the raw input onto the left stack of tape 0, then put the frame terminator on its right stack. -/
def frameRevStmt (t0 : Fin T) : SStmt T Q :=
  pop .inp (fun s x => { s with cell := x.map some }) <|
    branch (fun s => s.cell.isSome)
      (push (.lft t0) (fun s => s.cell.getD none) (goto fun _ => .frameRev))
      (push (.rgt t0) (fun _ => some false) (goto fun _ => .frameEmit))

/-- Emit `1 b` for every reversed input bit `b` onto the right stack of tape 0. -/
def frameEmitStmt (t0 : Fin T) : SStmt T Q :=
  pop (.lft t0) (fun s x => { s with cell := x }) <|
    branch (fun s => s.cell.isSome)
      (push (.rgt t0) (fun s => s.cell.getD none)
        (push (.rgt t0) (fun _ => some true) (goto fun _ => .frameEmit)))
      (goto fun _ => .sim M.start)

/-- Move the right stack of the output tape onto its left stack. -/
def gatherStmt (o : Fin T) : SStmt T Q :=
  pop (.rgt o) (fun s x => { s with cell := x }) <|
    branch (fun s => s.cell.isSome)
      (push (.lft o) (fun s => s.cell.getD none) (goto fun _ => .gather))
      (goto fun _ => .emit)

/-- Move the (reversed) output tape onto the output stack, dropping trailing blanks. -/
def emitStmt (o : Fin T) : SStmt T Q :=
  pop (.lft o) (fun s x => { s with cell := x }) <|
    peek .out (fun s x => { s with flag := x.isSome }) <|
      branch (fun s => s.cell.isSome)
        (branch (fun s => s.flag || (s.cell.getD none).isSome)
          (push .out (fun s => (s.cell.getD none).getD false) (goto fun _ => .emit))
          (goto fun _ => .emit))
        (goto fun _ => .wipe)

/-- Pop once from both stackOf of tape `i`, recording whether anything was there. -/
def wipeOne (i : Fin T) (st : SStmt T Q) : SStmt T Q :=
  pop (.lft i) (fun s x => { s with flag := s.flag || x.isSome })
    (pop (.rgt i) (fun s x => { s with flag := s.flag || x.isSome }) st)

/-- Pop every tape stack once; repeat while something was popped; then restore the variable and halt. -/
def wipeStmt : SStmt T Q :=
  load (fun s => { s with flag := false }) <|
    (List.finRange T).foldr wipeOne <|
      branch (fun s => s.flag) (goto fun _ => .wipe) (load (fun _ => Var.init T) halt)

/-- The program. -/
def prog (t0 o : Fin T) : Label Q → SStmt T Q
  | .frameRev => frameRevStmt t0
  | .frameEmit => frameEmitStmt M t0
  | .sim q => simStmt M q
  | .gather => gatherStmt o
  | .emit => emitStmt o
  | .wipe => wipeStmt

end Program

/-- Tape 0 of a program. -/
def tape0 (p : Program) : Fin p.tapeCount := ⟨0, by have := p.twoTapes; omega⟩

/-- **The bundled Mathlib TM2 machine** of an ordinary program (`app:short-pcp-proof`, "The exact Lean interface"). -/
def stackMachine (p : Program) : FinTM2 where
  K := Stack p.tapeCount
  k₀ := .inp
  k₁ := .out
  Γ := Sym
  Λ := Label p.stateCount
  main := .frameRev
  σ := Var p.tapeCount
  initialState := Var.init _
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog p.machine (tape0 p) p.outputTape

end NearCubicGates.Adapters.Machine
