import Proof.Gates.ENP.TableDispatch
import Proof.Gates.ENP.TableLoop
import Proof.Gates.ENP.TableSpecParts

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TEmit

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.EmitNat NearCubicGates.Close.CheckedPCPP.NodeEmit
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.Bindings.MW20

local notation "sCW" => (0 : Fin 4)
local notation "sG" => (1 : Fin 4)
local notation "sARGS" => (2 : Fin 4)
local notation "rR7" => (7 : Fin 40)
local notation "rTN" => (8 : Fin 40)
local notation "rL" => (9 : Fin 40)
local notation "rTT" => (10 : Fin 40)
local notation "rM" => (11 : Fin 40)
local notation "rKK" => (12 : Fin 40)
local notation "rZ" => (13 : Fin 40)
local notation "rBZ" => (14 : Fin 40)
local notation "rLC4" => (15 : Fin 40)
local notation "rA" => (16 : Fin 40)
local notation "rJJ" => (17 : Fin 40)
local notation "rX" => (18 : Fin 40)
local notation "rY" => (19 : Fin 40)
local notation "rBB" => (20 : Fin 40)
local notation "rW" => (21 : Fin 40)
local notation "rNP" => (22 : Fin 40)
local notation "rF1" => (23 : Fin 40)
local notation "rF2" => (24 : Fin 40)
local notation "rCA" => (25 : Fin 40)
local notation "rSC" => (26 : Fin 40)
local notation "rRF" => (27 : Fin 40)
local notation "rRC" => (28 : Fin 40)
local notation "rRV" => (29 : Fin 40)
local notation "rRP" => (30 : Fin 40)
local notation "rRT" => (31 : Fin 40)
local notation "rTAG" => (32 : Fin 40)
local notation "rLC1" => (33 : Fin 40)
local notation "rIMG" => (34 : Fin 40)
local notation "rLC2" => (35 : Fin 40)
local notation "rLC3" => (36 : Fin 40)
local notation "rIMG2" => (37 : Fin 40)
local notation "rT2" => (38 : Fin 40)
local notation "rTMP" => (39 : Fin 40)

/-! ## The seed program -/

/-- The template of `¬ C(z)`: `not IMG`. -/
def tNot : NodeT 40 := ![([], 2), ([rIMG], 0), ([], 0)]

/-- Close seed `z`: read the output index `o`, write `not (img o)` and `and (base − 1) (NP − 1)`. -/
def closeSeed (ε : Bool) : WMX 3 40 :=
  .seq (imgStep ε) <| .seq (.wm (nodeW sG Rw rTN tNot)) <| .seq (WMX.inc rNP) <| .seq (clearReg rIMG) <|
  .seq (.wm (setR rF1 rTN [rBZ] 0)) <| .seq (WMX.dec rF1) <|
  .seq (.wm (setR rF2 rTN [rNP] 0)) <| .seq (WMX.dec rF2) <|
  .seq (.wm (nodeW sG Rw rTN tAnd)) <| .seq (WMX.inc rNP) <| .seq (clearReg rF1) (clearReg rF2)

/-- Skip the header `ℓ, m` of the word. -/
def skipHeader (ε : Bool) : WMX 3 40 :=
  .seq (.wm (readNatM ε sCW rRF rRC rRV rRP rRT)) <| .seq (clearReg rRV) <|
  .seq (.wm (readNatM ε sCW rRF rRC rRV rRP rRT)) (clearReg rRV)

def seedBody (ε : Bool) : WMX 3 40 :=
  .seq (copyReg rNP rBZ rT2) <|
  .seq (repK rM rLC4 (nodeBody ε)) <|
  .seq (closeSeed ε) <|
  .seq (WMX.inc rZ) <| .seq (clearReg rBZ) <|
  .seq (copyReg rR7 rTMP rT2) <| .seq (.wm (WM.rewind sCW rTMP)) (skipHeader ε)

/-- **The seeds loop**: `SC` seeds. -/
def seedsLoop (ε : Bool) : WMX 3 40 := .whr rSC (.seq (WMX.dec rSC) (seedBody ε))

/-- The header length of the word. -/
def hdr {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) : ℕ := (natWord ℓ).length + (natWord C.nodes.length).length

/-- The native bytes of the start region. -/
def startBytes (ℓ : ℕ) : List Bool := (TCirc.start ℓ).flatMap PCPPRequestNodeSchema.native

def preVal (ℓ m r7 : ℕ) : Fin 40 → ℕ := fun r =>
  if r = rL then ℓ else if r = rM then m else if r = rTT then TCirc.T ℓ else if r = rKK then TCirc.K ℓ
  else if r = rNP then TCirc.S ℓ else if r = rR7 then r7 else if r = rSC then TCirc.T ℓ else 0

/-- The registers after the loop: as before, `NP = |nodes|`, `Z = T`, `SC = 0`. -/
def postVal (ℓ m np r7 : ℕ) : Fin 40 → ℕ := fun r =>
  if r = rL then ℓ else if r = rM then m else if r = rTT then TCirc.T ℓ else if r = rKK then TCirc.K ℓ
  else if r = rNP then np else if r = rR7 then r7 else if r = rZ then TCirc.T ℓ else 0

def preSeeds {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool) : WState 3 40 where
  sh := ![hdr C, (marks (startBytes ℓ)).length, 0, 0]
  st := ![(OracleOutput.word ⟨ℓ, C⟩) ++ post, marks (startBytes ℓ), [], []]
  val := preVal ℓ C.nodes.length (marks (startBytes ℓ)).length
  cell := false

def postSeeds {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post junk : List Bool) : WState 3 40 where
  sh := ![hdr C, (marks (tGraph C)).length, 0, 0]
  st := ![(OracleOutput.word ⟨ℓ, C⟩) ++ post, marks (tGraph C), junk, []]
  val := postVal ℓ C.nodes.length (TCirc.tCircuit C).nodes.length (marks (tGraph C)).length
  cell := false

def SeedsRuns : Prop :=
  ∃ K e : ℕ, ∀ {ℓ : ℕ} (C : OracleCircuit ℓ ℓ) (post : List Bool), ∃ c0 n,
    n ≤ K * (2 ^ ℓ + ((OracleOutput.word ⟨ℓ, C⟩) ++ post).length + 1) ^ e ∧
    ∀ cap, c0 ≤ cap → ∃ junk, WXExec cap (seedsLoop false) (preSeeds C post) (postSeeds C post junk) n

def TProgOf : Prop := SeedsRuns → TBytesSpec → Nonempty TProg

end NearCubicGates.Close.ENP.TEmit
