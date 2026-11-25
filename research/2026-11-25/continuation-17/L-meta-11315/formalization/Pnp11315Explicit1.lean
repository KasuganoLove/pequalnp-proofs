import Pnp11315States

namespace PEqualNP.Outside.L_meta_11315.Signed

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem explicit_1 : optimized 8 state_1.1 state_1.2 = false := by
  decide +kernel

theorem branch_1 :
  let q := (children 3 rows).getD 1 (0, [])
  optimized 8 q.1 q.2 = false := by
  dsimp only
  rw [state_eq_1]
  exact explicit_1

end PEqualNP.Outside.L_meta_11315.Signed
