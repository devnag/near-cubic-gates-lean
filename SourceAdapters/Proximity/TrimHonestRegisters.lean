import SourceAdapters.Proximity.TrimHonestData
import SourceAdapters.Proximity.RowQueries
import SourceAdapters.Proximity.RowTable

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": honest constructor resources disjoint from the retained
source-call parameters and its scratch. All stores are actual Cells RAMs. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicGates.Close.Cells

def proofStore : Fin MM := 3
def inputStore : Fin MM := 4
def auxiliaryStore : Fin MM := 5
def scheduleStore : Fin MM := 6
def keyStore : Fin MM := 7
def answerStore : Fin MM := 8
def rowStore : Fin MM := 9

def inputLength : Fin VV := 45
def proofLength : Fin VV := 46
def auxiliaryLength : Fin VV := 47
def scheduleLength : Fin VV := 48
def scheduleIndex : Fin VV := 49
def addressReg : Fin VV := 50
def halfReg : Fin VV := 51
def rankReg : Fin VV := 52
def valueReg : Fin VV := 53
def answerIndex : Fin VV := 54
def localIndex : Fin VV := 55
def localBound : Fin VV := 56
def pairScratch : Fin VV := 57
def pairResult : Fin VV := 58
def evenReg : Fin VV := 59

end NearCubicGates.Adapters.Proximity.TrimHonest
