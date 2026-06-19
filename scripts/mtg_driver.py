"""Decisive global test: can simple-profile equivalence (depth MU) coexist with a
nonzero internal-multi-edge gap_c?  Pin gap_c~1, drive profile mismatch to 0 over
free (B,W); re-test survivors at higher MU."""
import numpy as np
from multitriangle_global import run
from rpe_weight_fast import build_battery, residual_vec

for c in (2, 3):
    for T in (4, 5):
        best, iu, nB = run(T, MU=2, c=c, restarts=80, seed=T * 7 + c)
        if best is None:
            print(f"c={c} T={T} MU=2: NO candidate (cannot pin gap while matching) "
                  f"=> FORCED at MU=2", flush=True)
            continue
        mism, g, B, W = best
        hi = {}
        for MU2 in (3, 4):
            r = residual_vec(B, W, T, build_battery(MU2), 0, 1)
            hi[MU2] = float(r @ r)
        surv = mism < 1e-9 and all(v < 1e-7 for v in hi.values())
        print(f"c={c} T={T}: MU2-mismatch={mism:.2e} |gap|={g:.2f} | "
              f"MU3={hi[3]:.2e} MU4={hi[4]:.2e} | SURVIVES(real CE)={surv}", flush=True)
