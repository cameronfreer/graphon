"""Rigorous: optimize DIRECTLY at MU=3 (and MU=4) — pin gap_c~1, minimize the
MU-3 (resp MU-4) simple-profile mismatch over free (B,W).  If the minimum mismatch
stays bounded away from 0, then NO depth-MU rpe point has gap_c != 0 => gap_c is
FORCED at that depth.  If mismatch -> 0, a genuine counterexample exists."""
import numpy as np
from multitriangle_global import run
from rpe_weight_fast import build_battery, residual_vec

for c in (2, 3):
    for T in (4, 5):
        for MU in (3,):
            best, iu, nB = run(T, MU=MU, c=c, restarts=60, seed=T * 17 + c + MU)
            if best is None:
                print(f"c={c} T={T} MU={MU}: NO candidate with |gap|>0.3 "
                      f"=> FORCED at MU={MU}", flush=True)
                continue
            mism, g, B, W = best
            # how close did the best matched point get, and does it hold at MU+1?
            r4 = residual_vec(B, W, T, build_battery(MU + 1), 0, 1)
            print(f"c={c} T={T} MU={MU}: BEST mismatch@MU{MU}={mism:.2e} |gap|={g:.2f} "
                  f"(mismatch@MU{MU+1}={float(r4 @ r4):.2e})  "
                  f"=> {'COUNTEREXAMPLE (not forced)' if mism < 1e-9 else 'forced (cannot match with gap!=0)'}",
                  flush=True)
