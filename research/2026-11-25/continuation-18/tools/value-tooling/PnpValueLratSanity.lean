import PEqualNP.Library.LRAT.Checker

-- Self-chosen contradictory CNF sanity sample; not a project task submission.
-- Token layout follows upstream Checker.lean (Apache-2.0).
namespace PnpValueLratSanity
open PEqualNP.Library.LRAT

def F : List (List Nat) := [[2,4],[2,5],[3,4],[3,5]]
def keys : List Nat := [1,2,3,4]
def tokens : List Nat := [4,5,0,1,2,3,5,2,0,4,5,0,6,0,5,2,4,5,2]
def words : List Nat := [192621661274874412]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem token_unsat : ¬ FormulaSat F :=
  check_sound F keys tokens (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem packed_unsat : ¬ FormulaSat F :=
  checkW_sound F keys 3 words (by decide +kernel)

end PnpValueLratSanity
#print axioms PnpValueLratSanity.token_unsat
#print axioms PnpValueLratSanity.packed_unsat
